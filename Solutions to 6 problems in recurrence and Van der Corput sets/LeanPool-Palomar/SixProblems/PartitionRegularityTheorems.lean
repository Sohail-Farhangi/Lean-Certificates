/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.NiceEquivalence
public import SixProblems.PartitionRegularity

/-! # Partition regularity of nice van der Corput sets -/

@[expose] public section

namespace SixProblems

variable {G : Type} [Group G] [Countable G] [Infinite G]

/-- **Theorem 3.3.** The union of two sets that fail the nice van der Corput
condition also fails that condition. -/
theorem theorem3_3 {A B : Set G} (hA : ¬ NiceVdC A) (hB : ¬ NiceVdC B) :
    ¬ NiceVdC (A ∪ B) := by
  intro h
  exact theorem3_3_positiveDefinite (hA ∘ niceVdC_iff_nonnegativePD.mpr)
    (hB ∘ niceVdC_iff_nonnegativePD.mpr) (niceVdC_iff_nonnegativePD.mp h)

/-- **Corollary 3.4.** A finite union that is nice van der Corput contains a
member of the union that is nice van der Corput. -/
theorem corollary3_4 {m : ℕ} (D : Fin m → Set G) (hD : NiceVdC (⋃ i, D i)) :
    ∃ i, NiceVdC (D i) := by
  have hPD : NonnegativeOnPositiveDefinite (⋃ i ∈ (Finset.univ : Finset (Fin m)), D i) := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using niceVdC_iff_nonnegativePD.mp hD
  obtain ⟨i, _, hi⟩ := corollary3_4_positiveDefinite Finset.univ D hPD
  exact ⟨i, niceVdC_iff_nonnegativePD.mpr hi⟩

/-- The consequence for nice recurrence stated in Remark 3.5. -/
theorem niceRecurrence_partitionRegular {m : ℕ} (D : Fin m → Set G)
    (hD : NiceRecurrence (⋃ i, D i)) : ∃ i, NiceRecurrence (D i) := by
  have hPD := nonnegativePD_of_ergodicNiceRecurrence hasBoundedErgodicPDApproximation
    (ergodicNiceRecurrence_of_niceRecurrence hD)
  obtain ⟨i, hi⟩ := corollary3_4 D (niceVdC_iff_nonnegativePD.mpr hPD)
  exact ⟨i, niceRecurrence_of_niceVdC hi⟩

end SixProblems
