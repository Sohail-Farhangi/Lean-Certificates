/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.MixingFamilies
public import Mixing.UltrafilterLimits
public import Mixing.NormalOperatorSeries

/-! # Range series and strict inclusion between mixing families -/

@[expose] public section

open Set Filter
open scoped Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Remark 5. The closed span of the ranges of a nonempty ultrafilter family
is exactly the set of sums whose successive pieces are in the closed range of
the selected operator and in the kernels of all earlier operators. -/
theorem ultrafilter_mem_closed_span_range_iff_hasSum [IsMulCommutative G]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (P : Set (Ultrafilter G)) (hP : P.Nonempty) (x : H) :
    x ∈ (Submodule.span ℂ (⋃ p : P, ((ultrafilterOperator U p).range : Set H))).topologicalClosure ↔
      ∃ (p : ℕ → P) (ξ : ℕ → H), HasSum ξ x ∧ ∀ n,
        ξ n ∈ (ultrafilterOperator U (p n)).range.topologicalClosure ∧
        ∀ j < n, ξ n ∈ (ultrafilterOperator U (p j)).ker := by
  let _ : Nonempty P := nonempty_subtype.mpr hP
  simp only [Submodule.span_iUnion, Submodule.span_eq]
  refine mem_closure_iSup_range_iff_exists_hasSum_rangeClosure_ker
    (fun p : P => ultrafilterOperator U p) (fun p => ultrafilterOperator_normal U p)
    (fun p q => ultrafilterOperator_commute_pair U p q) ?_ x
  intro p q
  rw [← ultrafilterOperator_inverse]
  exact ultrafilterOperator_commute_pair U p (inverseUltrafilter q)

section Characters

variable {C : Type*} [Group C] [TopologicalSpace C] [T2Space C] [CompactSpace C]
  [IsTopologicalGroup C] (χ : G →* C)

theorem ultrafilterExtend_groupHom_inverse (p : Ultrafilter G) :
    Ultrafilter.extend χ (inverseUltrafilter p) = (Ultrafilter.extend χ p)⁻¹ := by
  rw [inverseUltrafilter, ultrafilterExtend_comp_map]
  apply ultrafilter_extend_eq_iff.mpr
  change Tendsto (fun g : G => χ g⁻¹) (p : Filter G) _
  simpa only [Function.comp_def, map_inv] using
    ((continuous_inv.tendsto _).comp (tendsto_ultrafilterExtend χ p))

theorem ultrafilterExtend_eq_one_of_mem_delta {P : Set (Ultrafilter G)} {q : Ultrafilter G}
    (hq : q ∈ ultrafilterDelta P) : Ultrafilter.extend χ q = 1 := by
  obtain ⟨p, _, rfl⟩ := hq
  change Ultrafilter.extend χ.toMulHom (inverseUltrafilter p * p) = 1
  rw [ultrafilterExtend_mul continuous_const_mul continuous_mul_const]
  change Ultrafilter.extend χ (inverseUltrafilter p) * Ultrafilter.extend χ p = 1
  rw [ultrafilterExtend_groupHom_inverse, inv_mul_cancel]

theorem ultrafilterDelta_subset_closedSignedUltrafilterIdeal (P : Set (Ultrafilter G)) :
    ultrafilterDelta P ⊆ closedSignedUltrafilterIdeal P := by
  rintro _ ⟨p, hp, rfl⟩
  apply subset_closure
  refine ⟨pure 1, inverseUltrafilter p * p, pure 1, ?_, ?_⟩
  · exact (signedUltrafilterSemigroup P).mul_mem
      (Subsemigroup.subset_closure (Or.inr ⟨p, hp, rfl⟩))
      (Subsemigroup.subset_closure (Or.inl hp))
  · apply Ultrafilter.coe_inj.mp
    ext s
    change (∀ᶠ a in ((inverseUltrafilter p * p : Ultrafilter G) : Filter G), a ∈ s) ↔
      ∀ᶠ a in ((pure 1 * (inverseUltrafilter p * p) * pure 1 : Ultrafilter G) : Filter G), a ∈ s
    simp [Ultrafilter.eventually_mul]

/-- Remark 6. A nontrivial character separates the Δ-family from the closed
two-sided family generated with inverses. This lemma works in any compact
Hausdorff target group, in particular the circle. -/
theorem ultrafilterDelta_ssubset_closedSignedUltrafilterIdeal
    (P : Set (Ultrafilter G)) (hP : P.Nonempty) (hχ : ∃ g : G, χ g ≠ 1) :
    ultrafilterDelta P ⊂ closedSignedUltrafilterIdeal P := by
  refine ⟨ultrafilterDelta_subset_closedSignedUltrafilterIdeal P, ?_⟩
  intro hSubset
  · obtain ⟨p, hp⟩ := hP
    obtain ⟨g, hg⟩ := hχ
    let q := pure g * (inverseUltrafilter p * p) * pure (1 : G)
    have hq : q ∈ closedSignedUltrafilterIdeal P := by
      apply subset_closure
      refine ⟨pure g, inverseUltrafilter p * p, pure 1, ?_, rfl⟩
      exact (signedUltrafilterSemigroup P).mul_mem
        (Subsemigroup.subset_closure (Or.inr ⟨p, hp, rfl⟩))
        (Subsemigroup.subset_closure (Or.inl hp))
    have hχq : Ultrafilter.extend χ q = χ g := by
      change Ultrafilter.extend χ.toMulHom (pure g * (inverseUltrafilter p * p) * pure (1 : G)) = χ g
      rw [ultrafilterExtend_mul continuous_const_mul continuous_mul_const,
        ultrafilterExtend_mul continuous_const_mul continuous_mul_const]
      change Ultrafilter.extend χ (pure g) * Ultrafilter.extend χ (inverseUltrafilter p * p) *
        Ultrafilter.extend χ (pure 1) = χ g
      rw [ultrafilter_extend_pure, ultrafilter_extend_pure, map_one,
        ultrafilterExtend_eq_one_of_mem_delta χ (show inverseUltrafilter p * p ∈ ultrafilterDelta P
          from ⟨p, hp, rfl⟩), mul_one, mul_one]
    exact hg (hχq.symm.trans (ultrafilterExtend_eq_one_of_mem_delta χ (hSubset hq)))

end Characters

end Mixing
