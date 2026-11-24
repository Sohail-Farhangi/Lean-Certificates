/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.RealCompactAverage
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section
noncomputable section

namespace SixProblems.RealRepresentation

open MeasureTheory MeasureTheory.Measure InnerProductSpace Module.End Set

section Invariant

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (U : G →* (H ≃ₗᵢ[ℝ] H))

def IsInvariantSubmodule (K : Submodule ℝ H) : Prop :=
  ∀ g : G, ∀ x ∈ K, U g x ∈ K

theorem IsInvariantSubmodule.sup {U : G →* (H ≃ₗᵢ[ℝ] H)} {K L : Submodule ℝ H}
    (hK : IsInvariantSubmodule U K) (hL : IsInvariantSubmodule U L) :
    IsInvariantSubmodule U (K ⊔ L) := by
  intro g x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨U g a, hK g a ha, U g b, hL g b hb, rfl⟩

theorem IsInvariantSubmodule.closure {U : G →* (H ≃ₗᵢ[ℝ] H)} {K : Submodule ℝ H}
    (hK : IsInvariantSubmodule U K) : IsInvariantSubmodule U K.topologicalClosure := by
  intro g x hx
  have hImage : U g '' (K : Set H) ⊆ K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hK g a ha
  exact closure_mono hImage (image_closure_subset_closure_image (U g).continuous ⟨x, hx, rfl⟩)

theorem IsInvariantSubmodule.orthogonal {U : G →* (H ≃ₗᵢ[ℝ] H)} {K : Submodule ℝ H}
    (hK : IsInvariantSubmodule U K) : IsInvariantSubmodule U Kᗮ := by
  intro g x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hg : U g (U g⁻¹ y) = y := by
    change (U g * U g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    ⟪y, U g x⟫_ℝ = ⟪U g (U g⁻¹ y), U g x⟫_ℝ := by rw [hg]
    _ = ⟪U g⁻¹ y, x⟫_ℝ := (U g).inner_map_map _ _
    _ = 0 := hx _ (hK g⁻¹ y hy)

/-- Restriction of a unitary group action to an invariant subspace. -/
noncomputable def unitarySubmoduleAction (W : Submodule ℝ H)
    (hW : ∀ g x, x ∈ W → U g x ∈ W) : G →* (W ≃ₗᵢ[ℝ] W) where
  toFun g :=
    { toLinearEquiv :=
        { (U g).toLinearMap.restrict (hW g) with
          invFun := fun x => ⟨U g⁻¹ x, hW g⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (show (U g⁻¹ * U g) x = x by
            rw [← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun x => Subtype.ext (show (U g * U g⁻¹) x = x by
            rw [← map_mul, mul_inv_cancel, map_one]; rfl) }
      norm_map' := fun x => (U g).norm_map x }
  map_one' := by
    ext x
    change U 1 x = (x : H)
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change U (g * h) x = U g (U h x)
    rw [map_mul]
    rfl


end Invariant

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A nonzero strongly continuous unitary representation of a compact group
has a nonzero finite-dimensional invariant subspace. -/
theorem exists_finiteDimensional_invariantSubmodule_of_compact [Nontrivial H]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    ∃ W : Submodule ℝ H, W ≠ ⊥ ∧ FiniteDimensional ℝ W ∧ IsInvariantSubmodule ρ W := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let A := compactRepresentationAverage m ρ v
  have hA := isCompactOperator_compactRepresentationAverage m ρ v (hρ v)
  have hSym := isSymmetric_compactRepresentationAverage m ρ v (hρ v)
  have hne := compactRepresentationAverage_ne_zero m ρ hv (hρ v)
  have he : ¬ ∀ z, HasEigenvalue A.toLinearMap z → z = 0 :=
    fun h ↦ hne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hA hSym).mp h)
  push Not at he
  obtain ⟨z, hz, hzero⟩ := he
  let W := eigenspace A.toLinearMap z
  refine ⟨W, hasEigenvalue_iff.mp hz,
    ContinuousLinearMap.finite_dimensional_eigenspace hA z hzero, fun k w hw ↦ ?_⟩
  have hw' := mem_eigenspace_iff.mp hw
  apply mem_eigenspace_iff.mpr
  change A (ρ k w) = z • ρ k w
  rw [← compactRepresentationAverage_commutes m ρ v (hρ v), show A w = z • w from hw', map_smul]

/-- Finite-dimensional invariant subspaces have dense linear span in a
strongly continuous unitary representation of a compact group. -/
theorem eq_top_of_contains_finiteInvariantSubmodules
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (P : Submodule ℝ H) (hP : IsClosed (P : Set H))
    (h : ∀ (V : Submodule ℝ H), FiniteDimensional ℝ V → IsInvariantSubmodule ρ V → V ≤ P) :
    P = ⊤ := by
  let A : Set H := {x | ∃ V : Submodule ℝ H, FiniteDimensional ℝ V ∧ IsInvariantSubmodule ρ V ∧ x ∈ V}
  let Q := (Submodule.span ℝ A).topologicalClosure
  have hQP : Q ≤ P := Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro x ⟨V,hfin,hV,hx⟩; exact h V hfin hV hx)) hP
  have hQA (x : H) (hx : x ∈ A) : x ∈ Q :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hx)
  have hQinv : IsInvariantSubmodule ρ Q := by
    apply IsInvariantSubmodule.closure
    intro g x hmem
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨V,hfin,hV,hxV⟩ := hx
      exact Submodule.subset_span ⟨V,hfin,hV,hV g x hxV⟩
    | zero => simp
    | add x y _ _ hx hy => exact map_add (ρ g) x y ▸ Submodule.add_mem _ hx hy
    | smul c x _ hx => exact map_smul (ρ g) c x ▸ Submodule.smul_mem _ c hx
  have hQ : Q = ⊤ := by
    let : CompleteSpace Q := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let D := Qᗮ
    apply Submodule.orthogonal_eq_bot_iff.mp
    by_contra hD
    let : Nontrivial D := Submodule.nontrivial_iff_ne_bot.mpr hD
    let V := unitarySubmoduleAction ρ D hQinv.orthogonal
    have hV (x : D) : Continuous (fun k ↦ V k x) := (hρ x).subtype_mk _
    obtain ⟨W,hWne,hWfin,hWinv⟩ := exists_finiteDimensional_invariantSubmodule_of_compact m V hV
    obtain ⟨x,hx,hxne⟩ : ∃ x ∈ W, x ≠ 0 := by
      by_contra! he
      exact hWne ((Submodule.eq_bot_iff W).mpr he)
    let W' := W.map D.subtype
    have hWinv' : IsInvariantSubmodule ρ W' := by
      rintro k _ ⟨y,hy,rfl⟩
      exact ⟨V k y, hWinv k y hy, rfl⟩
    let : FiniteDimensional ℝ W := hWfin
    have he : (D.subtype.comp W.subtype).range = W' := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hWfin' : FiniteDimensional ℝ W' := he ▸ inferInstanceAs
      (FiniteDimensional ℝ (D.subtype.comp W.subtype).range)
    have hxQ : (x : H) ∈ Q := hQA x ⟨W',hWfin',hWinv',⟨x,hx,rfl⟩⟩
    exact hxne (Subtype.ext (inner_self_eq_zero.mp (x.property _ hxQ)))
  exact top_unique (hQ ▸ hQP)

/-- A vector in a compact representation can be approximated in norm by a
vector belonging to a single finite-dimensional invariant subspace. -/
theorem exists_finiteInvariant_approximation
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (x : H) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Submodule ℝ H, FiniteDimensional ℝ V ∧ IsInvariantSubmodule ρ V ∧
      ∃ y : V, ‖x - (y : H)‖ < ε := by
  let P : Submodule ℝ H := {
    carrier := {x | ∃ V : Submodule ℝ H, FiniteDimensional ℝ V ∧ IsInvariantSubmodule ρ V ∧ x ∈ V}
    zero_mem' := ⟨⊥,inferInstance,by simp [IsInvariantSubmodule],Submodule.zero_mem _⟩
    add_mem' := by
      rintro x y ⟨V,hV,hVI,hx⟩ ⟨W,hW,hWI,hy⟩
      let := hV
      let := hW
      exact ⟨V ⊔ W,inferInstance,hVI.sup hWI,Submodule.mem_sup.mpr ⟨x,hx,y,hy,rfl⟩⟩
    smul_mem' := by
      rintro c x ⟨V,hV,hVI,hx⟩
      exact ⟨V,hV,hVI,V.smul_mem c hx⟩ }
  have hP := eq_top_of_contains_finiteInvariantSubmodules m ρ hρ P.topologicalClosure
    (Submodule.isClosed_topologicalClosure _) (fun V hfin hVI y hy ↦
      Submodule.le_topologicalClosure _ ⟨V,hfin,hVI,hy⟩)
  have hx : x ∈ closure (P : Set H) := (congrArg (fun Q : Submodule ℝ H ↦ x ∈ Q) hP).mpr trivial
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨V,hfin,hVI,hyV⟩ := hy
  exact ⟨V,hfin,hVI,⟨y,hyV⟩,by simpa only [dist_eq_norm] using hxy⟩

end SixProblems.RealRepresentation
