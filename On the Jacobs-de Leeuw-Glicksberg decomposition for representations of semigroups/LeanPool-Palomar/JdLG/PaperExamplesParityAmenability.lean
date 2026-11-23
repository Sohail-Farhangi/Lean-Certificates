/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParityMean
public import JdLG.UltrafilterMoreOre
public import JdLG.UltrafilterMoreQuotientFacts

/-!
# Ambient amenability in the parity example

The count-grid probability gives left reversibility and a left invariant
mean. Cancellativity embeds the semigroup into its group of right quotients,
and pulling back sets extends the mean to the ambient group.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

instance : Nonempty Point := ⟨evenPoint⟩

instance : IsCancelMul Point where
  mul_left_cancel := left_multiplication_injective
  mul_right_cancel := right_multiplication_injective

/-- The literal parity semigroup is left amenable for counting measure. -/
noncomputable def parityLeftSetMean : LeftInvariantSetMean Point where
  mass := parityMean
  nonneg A := (parityMean_mem_unitInterval A).1
  empty := parityMean_empty
  univ := parityMean_univ
  add_disjoint := parityMean_union
  invariant := parityMean_left_invariant

/-- Example 4.4 embeds the parity semigroup into an amenable group. The ambient
group is its group of right quotients, equipped with the extended left mean. -/
theorem parity_embeds_in_amenable_group :
    ∃ (G : Type) (_ : Group G) (ι : Point →ₙ* G),
      IsGroupOfRightQuotients ι ∧ Nonempty (LeftInvariantSetMean G) := by
  obtain ⟨G, hG, ι, hι⟩ := exists_groupOfRightQuotients
    (leftReversible_of_leftInvariantSetMean parityLeftSetMean)
  exact ⟨G, hG, ι, hι, ⟨parityLeftSetMean.extendRightQuotients hι⟩⟩

end JdLG.PaperExamplesParity
