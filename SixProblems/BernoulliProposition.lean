/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.BernoulliErgodic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing

/-- Proposition 2.1, including the preservation of ergodicity. A finite set
of group elements represents a tuple of distinct translates. -/
theorem proposition2_1 {G X : Type} [Group G] [Countable G] [Infinite G]
    [MeasurableSpace X] [StandardBorelSpace X] (S : System G X)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ∃ (Y : Type) (mY : MeasurableSpace Y) (_ : @StandardBorelSpace Y mY)
      (T : @System G Y _ mY) (C : Set Y),
      MeasurableSet C ∧
      (∀ J : Finset G, (T.measure {y | ∀ g ∈ J, y ∈ T.act g ⁻¹' C}).toReal =
        ∫ x, ∏ g ∈ J, f (S.act g x) ∂S.measure) ∧
      (S.IsErgodic → T.IsErgodic) := by
  exact ⟨X × (G → ℝ), inferInstance, inferInstance, S.prod (bernoulliShift G unitIntervalLaw),
    bernoulliThreshold f, measurableSet_bernoulliThreshold hf,
    bernoulliThreshold_pattern S hf hf0 hf1, bernoulli_prod_isErgodic unitIntervalLaw S⟩

end SixProblems
