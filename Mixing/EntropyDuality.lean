/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EntropyDisjointnessReduction
public import Mixing.ZeroEntropyJoinings

@[expose] public section
noncomputable section

namespace Mixing

open MeasureTheory

variable {G : Type} {X Y : Type*} [CommGroup G] [Countable G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]

/-- Completely positive entropy implies disjointness from each
standard Borel zero-entropy system. -/
theorem disjoint_of_completelyPositiveEntropy_zeroEntropy
    {S : System G X} {T : System G Y} (hCPE : S.HasCompletelyPositiveEntropy)
    (hT : T.HasZeroEntropy) : Disjoint S T := by
  let := nonempty_of_isProbabilityMeasure S.measure
  let := nonempty_of_isProbabilityMeasure T.measure
  exact disjoint_of_completelyPositiveEntropy_of_zeroEntropyCopies hCPE
    (fun _ h ↦ h.independentCopiesSystem_hasZeroEntropy hT)

/-- The entropy characterization of disjointness in Theorem 1.1(iv). -/
theorem theorem1_1_iv (S : System G X) :
    S.HasCompletelyPositiveEntropy ↔
      ∀ (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] (T : System G Y),
        T.HasZeroEntropy → Disjoint S T :=
  ⟨fun h _ _ _ _ hT ↦ disjoint_of_completelyPositiveEntropy_zeroEntropy h hT,
    hasCompletelyPositiveEntropy_of_disjoint_zeroEntropy S⟩

end Mixing
