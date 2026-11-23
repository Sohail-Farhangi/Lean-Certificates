/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleSpan

/-! # The ambient reversible-span identity -/

@[expose] public section

open Set

namespace JdLG

section Embedding

variable {S 𝕜 E F : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {π : S →ₙ* (E →L[𝕜] E)} {ρ : S →ₙ* (F →L[𝕜] F)}

/-- An injective equivariant bounded linear map preserves an irreducible finite
unitary system and its span. -/
theorem SpannedByIrreducibleUnitarySystem.map_of_injective
    {W : Submodule 𝕜 E} (hW : SpannedByIrreducibleUnitarySystem π W)
    (A : E →L[𝕜] F) (hA : Function.Injective A)
    (hinter : ∀ s x, ρ s (A x) = A (π s x)) :
    SpannedByIrreducibleUnitarySystem ρ (W.map A.toLinearMap) := by
  obtain ⟨hnz, ⟨n, U, J, hJ, hJW, hunit⟩, hirr⟩ := hW
  refine ⟨?_, ⟨n, U, A.comp J, hA.comp hJ, ?_, fun s x ↦ ?_⟩, ?_⟩
  · intro h
    apply hnz
    apply le_antisymm _ bot_le
    intro x hx
    have ha : A x ∈ W.map A.toLinearMap := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at ha
    exact (Submodule.mem_bot 𝕜).2 (hA (ha.trans A.map_zero.symm))
  · change (A.toLinearMap.comp J.toLinearMap).range = W.map A.toLinearMap
    rw [LinearMap.range_comp]
    exact congrArg (Submodule.map A.toLinearMap) hJW
  · change ρ s (A (J x)) = A (J (U s x))
    rw [hinter, hunit]
  · intro V hV hinv
    let Z := W ⊓ V.comap A.toLinearMap
    have hZinv (s : S) (x : E) (hx : x ∈ Z) : π s x ∈ Z := by
      refine ⟨?_, ?_⟩
      · have hxW : x ∈ W := hx.1
        rw [← hJW] at hxW ⊢
        obtain ⟨z, rfl⟩ := hxW
        exact ⟨U s z, (hunit s z).symm⟩
      · change A (π s x) ∈ V
        rw [← hinter]
        exact hinv s _ hx.2
    rcases hirr Z inf_le_left hZinv with h | h
    · left
      apply le_antisymm _ bot_le
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hV hy
      have hx' : x ∈ Z := ⟨hx, hy⟩
      rw [h, Submodule.mem_bot] at hx'
      simp [hx']
    · right
      apply le_antisymm hV
      rintro _ ⟨x, hx, rfl⟩
      have hz : x ∈ Z := by rwa [h]
      exact hz.2

end Embedding

section Ambient

variable {S E : Type*} [Semigroup S] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [CompleteSpace E] {π : S →ₙ* (E →L[ℂ] E)}
  (K : GroupIdeal (weakOperatorClosure π))

omit [CompleteSpace E] in
/-- All operators in the weak closure preserve the Euclidean length in the
coordinates of a finite unitary system. -/
theorem finiteUnitarySystem_closureAction_on_sphere
    (n : ℕ) (U : S →ₙ* (EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)))
    (J : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (hU : ∀ s x, π s (J x) = J (U s x))
    (T : weakOperatorClosure π) (x : EuclideanSpace ℂ (Fin n)) :
    ∃ y : EuclideanSpace ℂ (Fin n), ‖y‖ = ‖x‖ ∧ J y = closureAction π T (J x) := by
  let D : Set E := J '' Metric.sphere 0 ‖x‖
  have hD : IsCompact D := (isCompact_sphere _ _).image J.continuous
  let W := toWeakSpace ℂ E '' D
  have hW : IsClosed W := (hD.image (toWeakSpaceCLM ℂ E).continuous).isClosed
  let eval : (E →WOT[ℂ] E) → WeakSpace ℂ E := fun a ↦ toWeakSpace ℂ E (a (J x))
  have he : Continuous eval := WeakBilin.continuous_of_continuous_eval _
    (ContinuousLinearMapWOT.continuous_dual_apply (J x))
  have himage : range (weakRepresentation π) ⊆ eval ⁻¹' W := by
    rintro _ ⟨s, rfl⟩
    have hs : U s x ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) ‖x‖ := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (U s).norm_map x
    exact ⟨J (U s x), ⟨U s x, hs, rfl⟩, congrArg (toWeakSpace ℂ E) (hU s x).symm⟩
  have ht := closure_minimal himage (hW.preimage he) T.2
  obtain ⟨_, ⟨y, hy, rfl⟩, hyT⟩ := ht
  refine ⟨y, ?_, (toWeakSpace ℂ E).injective hyT⟩
  simpa only [Metric.mem_sphere, dist_zero_right] using hy

omit [CompleteSpace E] in
/-- Every finite unitary system of the original semigroup lies in the reversible subspace. -/
theorem GroupIdeal.spannedByIrreducibleUnitarySystem_le_reversible
    {W : Submodule ℂ E} (hW : SpannedByIrreducibleUnitarySystem π W) :
    W ≤ K.reversibleSubmodule := by
  obtain ⟨_, ⟨n, U, J, hJ, hJW, hinter⟩, _⟩ := hW
  intro y hy
  rw [← hJW] at hy
  obtain ⟨x, rfl⟩ := hy
  let P := K.projection (closureAction π)
  obtain ⟨z, _, hz⟩ := finiteUnitarySystem_closureAction_on_sphere n U J hinter K.identity x
  have hP (w : E) : P (P w) = P w := K.projection_apply_apply _ w
  have hker : P (J (x - z)) = 0 := by
    change J z = P (J x) at hz
    rw [map_sub J, map_sub P, hz, hP, sub_self]
  obtain ⟨w, hw, hweq⟩ :=
    finiteUnitarySystem_closureAction_on_sphere n U J hinter K.identity (x - z)
  have hw0 : w = 0 := hJ (hweq.trans (hker.trans J.map_zero.symm))
  have hxz : x = z := sub_eq_zero.1 (norm_eq_zero.1 (by simpa [hw0] using hw.symm))
  exact (K.mem_reversibleSubmodule _).2 (hz.symm.trans (congrArg J hxz.symm))

/-- Equation (6) in the ambient Banach space. The reversible subspace is the
norm-closed linear span of the irreducible finite unitary systems of the
original semigroup. -/
theorem GroupIdeal.reversibleSubmodule_eq_irreducibleUnitarySystem_span (hK : IsCompact K.carrier) :
    K.reversibleSubmodule =
      (⨆ W : {W : Submodule ℂ E // SpannedByIrreducibleUnitarySystem π W},
        W.1).topologicalClosure := by
  let I := {W : Submodule ℂ E | SpannedByIrreducibleUnitarySystem π W}
  let B : Submodule ℂ E := ⨆ W : I, W.1
  let R := K.reversibleSubmodule
  have hBR : B ≤ R :=
    iSup_le fun W ↦ K.spannedByIrreducibleUnitarySystem_le_reversible W.2
  have hR : B.topologicalClosure ≤ R := by
    change closure (B : Set E) ⊆ (R : Set E)
    exact closure_minimal hBR K.isClosed_reversibleSubmodule
  change R = B.topologicalClosure
  apply le_antisymm _ hR
  intro x hx
  let y : R := ⟨x, hx⟩
  let A : Submodule ℂ R :=
    ⨆ W : {W : Submodule ℂ R // SpannedByIrreducibleUnitarySystem K.reversibleAction W}, W.1
  have htotal : A.topologicalClosure = ⊤ :=
    K.iSup_spannedByIrreducibleUnitarySystem_reversibleAction hK
  have hy : y ∈ closure (A : Set R) := by
    change y ∈ A.topologicalClosure
    rw [htotal]
    exact Submodule.mem_top
  have hm : Submodule.map R.subtype A ≤ B := by
    change Submodule.map R.subtype (⨆ W : {W : Submodule ℂ R //
      SpannedByIrreducibleUnitarySystem K.reversibleAction W}, W.1) ≤ B
    rw [Submodule.map_iSup]
    refine iSup_le fun W ↦ ?_
    have hW := W.2.map_of_injective R.subtypeL Subtype.val_injective (fun _ _ ↦ rfl)
    exact le_iSup (fun V : I ↦ V.1) ⟨W.1.map R.subtype, hW⟩
  have hmap : MapsTo (fun y : R ↦ (y : E)) (A : Set R) B :=
    fun z hz ↦ hm ⟨z, hz, rfl⟩
  exact (hmap.closure continuous_subtype_val) hy

end Ambient

end JdLG
