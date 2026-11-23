/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.FolnerBanachDensities

/-! # Complementation for Banach density -/

@[expose] public section

open MeasureTheory Set

namespace JdLG.MeasuredMean

variable {S : Type*} [Semigroup S] [MeasurableSpace S] {μ : Measure S}

/-- Lower left Banach density is one minus upper left Banach density of the
complement, whenever an invariant mean exists. -/
theorem lowerBanachDensity_eq_one_sub_upperBanachDensity_compl
    (m : MeasuredMean μ) (hm : m.IsLeftInvariant) {A : Set S} (hA : MeasurableSet A) :
    lowerBanachDensity (measure := μ) A hA = 1 - upperBanachDensity μ Aᶜ hA.compl := by
  let values (B : Set S) (hB : MeasurableSet B) :=
    {r : ℝ | ∃ n : MeasuredMean μ, n.IsLeftInvariant ∧ n.mass B hB = r}
  have hnonempty (B : Set S) (hB : MeasurableSet B) : (values B hB).Nonempty :=
    ⟨_, m, hm, rfl⟩
  have hbelow (B : Set S) (hB : MeasurableSet B) : BddBelow (values B hB) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, _, rfl⟩
    exact n.mass_nonneg hB
  have habove (B : Set S) (hB : MeasurableSet B) : BddAbove (values B hB) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, _, rfl⟩
    exact n.mass_le_one hB
  change sInf (values A hA) = 1 - sSup (values Aᶜ hA.compl)
  apply le_antisymm
  · rw [le_sub_comm]
    apply csSup_le (hnonempty Aᶜ hA.compl)
    rintro _ ⟨n, hn, rfl⟩
    have h := csInf_le (hbelow A hA) (show n.mass A hA ∈ values A hA from ⟨n, hn, rfl⟩)
    linarith [n.mass_compl_add hA]
  · apply le_csInf (hnonempty A hA)
    rintro _ ⟨n, hn, rfl⟩
    have h := le_csSup (habove Aᶜ hA.compl)
      (show n.mass Aᶜ hA.compl ∈ values Aᶜ hA.compl from ⟨n, hn, rfl⟩)
    linarith [n.mass_compl_add hA]

end JdLG.MeasuredMean

