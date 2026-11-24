/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactRepresentationAverage
public import Mixing.MaximalSpectralVector

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure InnerProductSpace Mixing Module.End Set

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonzero strongly continuous unitary representation of a compact group
has a nonzero finite-dimensional invariant subspace. -/
theorem exists_finiteDimensional_invariantSubmodule_of_compact [Nontrivial H]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    ∃ W : Submodule ℂ H, W ≠ ⊥ ∧ FiniteDimensional ℂ W ∧ IsInvariantSubmodule ρ W := by
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

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [TopologicalSpace K] [CompleteSpace H] in
/-- Irreducibility of an invariant submodule, expressed using submodules of
the ambient representation. -/
def IrreducibleInvariantSubmodule (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (W : Submodule ℂ H) : Prop :=
  W ≠ ⊥ ∧ IsInvariantSubmodule ρ W ∧
    ∀ L ≤ W, IsInvariantSubmodule ρ L → L = ⊥ ∨ L = W

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [TopologicalSpace K] [CompleteSpace H] in
theorem exists_irreducibleInvariantSubmodule_le (ρ : K →* (H ≃ₗᵢ[ℂ] H))
    (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hW : IsInvariantSubmodule ρ W) (hne : W ≠ ⊥) :
    ∃ L ≤ W, IrreducibleInvariantSubmodule ρ L := by
  classical
  let P (n : ℕ) := ∃ L ≤ W, L ≠ ⊥ ∧ IsInvariantSubmodule ρ L ∧ Module.finrank ℂ L = n
  have hp : ∃ n, P n := ⟨_, W, le_rfl, hne, hW, rfl⟩
  obtain ⟨L,hL,hLne,hLI,hfin⟩ := Nat.find_spec hp
  refine ⟨L,hL,hLne,hLI,fun V hV hVI ↦ ?_⟩
  let : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hL
  by_cases hb : V = ⊥
  · exact Or.inl hb
  · refine Or.inr (le_antisymm hV ?_)
    by_contra hVL
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hV hVL)
    exact Nat.find_min hp (hfin ▸ hlt) ⟨V,hV.trans hL,hb,hVI,rfl⟩

/-- Finite-dimensional invariant subspaces have dense linear span in a
strongly continuous unitary representation of a compact group. -/
theorem eq_top_of_contains_finiteInvariantSubmodules
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (P : Submodule ℂ H) (hP : IsClosed (P : Set H))
    (h : ∀ (V : Submodule ℂ H), FiniteDimensional ℂ V → IsInvariantSubmodule ρ V → V ≤ P) :
    P = ⊤ := by
  let A : Set H := {x | ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧ IsInvariantSubmodule ρ V ∧ x ∈ V}
  let Q := (Submodule.span ℂ A).topologicalClosure
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
    let : FiniteDimensional ℂ W := hWfin
    have he : (D.subtype.comp W.subtype).range = W' := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hWfin' : FiniteDimensional ℂ W' := he ▸ inferInstanceAs
      (FiniteDimensional ℂ (D.subtype.comp W.subtype).range)
    have hxQ : (x : H) ∈ Q := hQA x ⟨W',hWfin',hWinv',⟨x,hx,rfl⟩⟩
    exact hxne (Subtype.ext (inner_self_eq_zero.mp (x.property _ hxQ)))
  exact top_unique (hQ ▸ hQP)

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [TopologicalSpace K] [CompleteSpace H] in
theorem finiteInvariantSubmodule_le_of_contains_irreducible (ρ : K →* (H ≃ₗᵢ[ℂ] H))
    (P : Submodule ℂ H)
    (hP : ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → IrreducibleInvariantSubmodule ρ W → W ≤ P)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : IsInvariantSubmodule ρ V) : V ≤ P := by
  suffices h : ∀ (n : ℕ) (L : Submodule ℂ H), FiniteDimensional ℂ L →
      Module.finrank ℂ L = n → IsInvariantSubmodule ρ L → L ≤ P from
    h _ V inferInstance rfl hV
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro L hfin hn hL
    let : FiniteDimensional ℂ L := hfin
    by_cases hL0 : L = ⊥
    · rw [hL0]; exact bot_le
    obtain ⟨W,hWL,hW⟩ := exists_irreducibleInvariantSubmodule_le ρ L hL hL0
    let : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWL
    let : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    let D := L ⊓ Wᗮ
    have hD : IsInvariantSubmodule ρ D := fun g x hx ↦
      ⟨hL g x hx.1, hW.2.1.orthogonal g x hx.2⟩
    have hDL : D < L := lt_of_le_of_ne inf_le_left fun he ↦ by
      apply hW.1
      apply (Submodule.eq_bot_iff W).mpr
      intro x hx
      have hx' : x ∈ D := he ▸ hWL hx
      exact inner_self_eq_zero.mp (hx'.2 x hx)
    have hd : D ≤ P := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hDL) D
      (Submodule.finiteDimensional_of_le hDL.le) rfl hD
    have hw : W ≤ P := hP W inferInstance hW
    intro x hx
    let w := W.starProjection x
    have hwW : w ∈ W := W.starProjection_apply_mem x
    have hdiff : x - w ∈ D :=
      ⟨L.sub_mem hx (hWL hwW), Submodule.sub_starProjection_mem_orthogonal x⟩
    have hsum := P.add_mem (hw hwW) (hd hdiff)
    rwa [add_sub_cancel] at hsum

/-- The finite-dimensional irreducible invariant subspaces of a strongly
continuous unitary representation of a compact group span a dense subspace. -/
theorem eq_top_of_contains_irreducibleInvariantSubmodules
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (P : Submodule ℂ H) (hP : IsClosed (P : Set H))
    (h : ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → IrreducibleInvariantSubmodule ρ W → W ≤ P) :
    P = ⊤ := by
  apply eq_top_of_contains_finiteInvariantSubmodules m ρ hρ P hP
  intro V hfin hV
  let : FiniteDimensional ℂ V := hfin
  exact finiteInvariantSubmodule_le_of_contains_irreducible ρ P h V hV

end SixProblems
