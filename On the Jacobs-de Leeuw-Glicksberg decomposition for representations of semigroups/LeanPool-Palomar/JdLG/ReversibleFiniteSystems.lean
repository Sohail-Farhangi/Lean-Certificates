/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleConvolution
public import JdLG.ReversibleCoefficients
public import JdLG.ReversibleIrreducible
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Density of irreducible finite unitary systems -/

@[expose] public section

open MeasureTheory Set Submodule
open scoped ENNReal

namespace JdLG

section Systems

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A subspace spanned by an irreducible finite unitary system. The injective
map from Euclidean space sends its standard basis to the paper's independent tuple. -/
def SpannedByIrreducibleUnitarySystem (ρ : S →ₙ* (E →L[𝕜] E)) (W : Submodule 𝕜 E) : Prop :=
  W ≠ ⊥ ∧
    (∃ n : ℕ, ∃ (U : S →ₙ* (EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n)))
      (J : EuclideanSpace 𝕜 (Fin n) →L[𝕜] E),
      Function.Injective J ∧ J.range = W ∧ ∀ s x, ρ s (J x) = J (U s x)) ∧
    ∀ V ≤ W, (∀ s, ∀ x ∈ V, ρ s x ∈ V) → V = ⊥ ∨ V = W

end Systems

section Image

variable {G 𝕜 H E : Type*} [Group G] [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The nonzero image of an irreducible finite-dimensional unitary subspace
under an intertwiner is spanned by an irreducible finite unitary system. -/
theorem spannedByIrreducibleUnitarySystem_map
    (U : G →* (H ≃ₗᵢ[𝕜] H)) (ρ : G →* (E →L[𝕜] E)) (T : H →L[𝕜] E)
    (hT : ∀ g x, T (U g x) = ρ g (T x))
    (A : Submodule 𝕜 H) [FiniteDimensional 𝕜 A] (hA : UnitaryIrreducibleOn U A)
    (hnz : A.map T.toLinearMap ≠ ⊥) :
    SpannedByIrreducibleUnitarySystem ρ.toMulHom (A.map T.toLinearMap) := by
  let W := A.map T.toLinearMap
  have hpull (V : Submodule 𝕜 E) (hV : ∀ g, ∀ x ∈ V, ρ g x ∈ V) :
      A ⊓ V.comap T.toLinearMap = ⊥ ∨ A ⊓ V.comap T.toLinearMap = A := by
    apply hA.2.2 _ inf_le_left
    intro g x hx
    refine ⟨hA.2.1 _ _ hx.1, ?_⟩
    change T (U g x) ∈ V
    rw [hT]
    exact hV _ _ hx.2
  have hZ : A ⊓ (⊥ : Submodule 𝕜 E).comap T.toLinearMap = ⊥ := by
    rcases hpull ⊥ (fun g x hx ↦ by
      rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]) with h | h
    · exact h
    exfalso
    apply hnz
    apply le_antisymm _ bot_le
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ A ⊓ (⊥ : Submodule 𝕜 E).comap T.toLinearMap := by
      rwa [h]
    exact hx'.2
  let B := T.comp A.subtypeL
  have hB : Function.Injective B := by
    apply (injective_iff_map_eq_zero B).2
    intro x hx
    have hx' : (x : H) ∈ A ⊓ (⊥ : Submodule 𝕜 E).comap T.toLinearMap :=
      ⟨x.2, (Submodule.mem_bot 𝕜).2 hx⟩
    rw [hZ, Submodule.mem_bot] at hx'
    exact Subtype.ext hx'
  let e := (stdOrthonormalBasis 𝕜 A).repr
  let U' := unitarySubmoduleAction U A hA.2.1
  let V : G →* (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 A)) ≃ₗᵢ[𝕜]
      EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 A))) :=
    { toFun := fun g ↦ e.symm.trans ((U' g).trans e)
      map_one' := by apply LinearIsometryEquiv.ext; intro z; simp
      map_mul' := fun g h ↦ by apply LinearIsometryEquiv.ext; intro z; simp [map_mul] }
  let J := B.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hj : J.range = W := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact ⟨e.symm z, (e.symm z).2, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨e ⟨z, hz⟩, by change T (e.symm (e ⟨z, hz⟩) : H) = T z; simp⟩
  refine ⟨hnz, ⟨_, V.toMulHom, J, hB.comp e.symm.injective, hj, ?_⟩, ?_⟩
  · intro g z
    change ρ g (T (e.symm z : H)) =
      T (e.symm (e (U' g (e.symm z))) : H)
    rw [e.symm_apply_apply]
    exact (hT g (e.symm z)).symm
  · intro D hDW hD
    rcases hpull D hD with h | h
    · left
      apply le_antisymm _ bot_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hDW hy
      have hx' : x ∈ A ⊓ D.comap T.toLinearMap := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at hx'
      simp [hx']
    · right
      apply le_antisymm hDW
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ A ⊓ D.comap T.toLinearMap := by
        rwa [h]
      exact hx'.2

end Image

section Density

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [SecondCountableTopologyEither G 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Right translation on scalar Haar L² is strongly continuous. -/
theorem continuous_haarRightTranslation_apply (φ : HaarL2 G 𝕜) :
    Continuous fun g : G ↦ haarRightTranslation (𝕜 := 𝕜) g φ := by
  let μ := normalizedHaar G
  let : μ.Regular := by unfold μ normalizedHaar; infer_instance
  let P : C(G, 𝕜) →L[𝕜] HaarL2 G 𝕜 := ContinuousMap.toLp 2 μ 𝕜
  have hd : DenseRange P := ContinuousMap.toLp_denseRange 𝕜 μ 𝕜 (by simp)
  have hp (f : C(G, 𝕜)) : P f = continuousToHaarL2 (𝕜 := 𝕜) f := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp μ f (𝕜 := 𝕜)).trans
      (continuousToHaarL2_coeFn (𝕜 := 𝕜) f).symm
  let R := haarRightTranslation (𝕜 := 𝕜) (G := G) (F := 𝕜)
  apply continuous_orbit_of_isometricApprox (fun g ↦ R g) (fun g ↦ (R g).isometry)
  intro δ hδ
  obtain ⟨_, ⟨f, rfl⟩, hf⟩ := Metric.mem_closure_iff.1 (hd φ) δ hδ
  refine ⟨P f, hf, ?_⟩
  have h (g : G) : R g (P f) = P (rightTranslate g f) :=
    congrArg (R g) (hp f) |>.trans
      ((haarRightTranslation_toLp g f).trans (hp (rightTranslate g f)).symm)
  simp_rw [h]
  exact P.continuous.comp (continuous_rightTranslate f)

/-- The compact-group span statement underlying equation (6). Every vector is
a norm limit of linear combinations of vectors in irreducible finite unitary
systems. The averaging intertwiners send finite-dimensional Haar subspaces
to such systems. -/
theorem iSup_spannedByIrreducibleUnitarySystem_topologicalClosure_eq_top
    (ρ : G →* (E →L[𝕜] E)) (hρ : ∀ x, Continuous fun g ↦ ρ g x)
    (C : ℝ) (hC : ∀ g, ‖ρ g‖ ≤ C) :
    (⨆ W : {W : Submodule 𝕜 E // SpannedByIrreducibleUnitarySystem ρ.toMulHom W},
      W.1).topologicalClosure = ⊤ := by
  let J := {W : Submodule 𝕜 E | SpannedByIrreducibleUnitarySystem ρ.toMulHom W}
  let B : Submodule 𝕜 E := ⨆ W : J, W.1
  let U := haarRightTranslation (G := G) (𝕜 := 𝕜) (F := 𝕜)
  let I := {A : Submodule 𝕜 (HaarL2 G 𝕜) | FiniteDimensional 𝕜 A ∧ UnitaryIrreducibleOn U A}
  let A : Submodule 𝕜 (HaarL2 G 𝕜) := ⨆ W : I, W.1
  have htotal : A.topologicalClosure = ⊤ :=
    iSup_finiteDimensional_irreducible_topologicalClosure_eq_top U
      continuous_haarRightTranslation_apply
  apply eq_top_iff.2
  intro x _
  change x ∈ closure (B : Set E)
  have hmaple : A.map (orbitConvolution ρ hρ C hC x).toLinearMap ≤ B := by
    rw [show A = ⨆ W : I, W.1 from rfl, Submodule.map_iSup]
    refine iSup_le fun W ↦ ?_
    let : FiniteDimensional 𝕜 W.1 := W.2.1
    let T := orbitConvolution ρ hρ C hC x
    by_cases h : W.1.map T.toLinearMap = ⊥
    · change W.1.map T.toLinearMap ≤ B
      rw [h]
      exact bot_le
    · have hW := spannedByIrreducibleUnitarySystem_map U ρ T
        (orbitConvolution_intertwines ρ hρ C hC x) W.1 W.2.2 h
      exact le_iSup (fun b : J ↦ b.1) ⟨W.1.map T.toLinearMap, hW⟩
  have hmap : MapsTo (orbitConvolution ρ hρ C hC x) (A : Set (HaarL2 G 𝕜)) B :=
    fun φ hφ ↦ hmaple ⟨φ, hφ, rfl⟩
  have hwhole (φ : HaarL2 G 𝕜) : φ ∈ closure (A : Set (HaarL2 G 𝕜)) := by
    change φ ∈ A.topologicalClosure
    rw [htotal]
    exact Submodule.mem_top
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨φ, hφ⟩ := exists_orbitConvolution_close ρ hρ C hC x (ε / 2) (by positivity)
  have hW := (hmap.closure (orbitConvolution ρ hρ C hC x).continuous) (hwhole φ)
  obtain ⟨y, hy, hny⟩ := Metric.mem_closure_iff.1 hW (ε / 2) (by positivity)
  refine ⟨y, hy, (dist_triangle _ (orbitConvolution ρ hρ C hC x φ) _).trans_lt ?_⟩
  have hxclose : dist x (orbitConvolution ρ hρ C hC x φ) < ε / 2 := by
    rw [dist_comm, dist_eq_norm]
    exact hφ
  linarith

end Density

end JdLG
