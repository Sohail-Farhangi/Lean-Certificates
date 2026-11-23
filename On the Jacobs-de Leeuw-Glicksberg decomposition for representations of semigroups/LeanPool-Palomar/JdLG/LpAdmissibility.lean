/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.LpSmoothness
public import JdLG.LpUniformConvexity
public import JdLG.UniformConvexReflexivity
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Admissibility for contractions on complex Lᵖ -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace JdLG

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complex Lᵖ over any measure space is reflexive when 1 < p < ∞. -/
theorem surjective_inclusionInDoubleDual_complexLp (hp : 1 < p) (hp_top : p ≠ ∞) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (Lp ℂ p μ)) := by
  let h := uniformConvexSpace_complexLp μ hp hp_top
  exact surjective_inclusionInDoubleDual_of_uniformConvex

/-- The complex dual of Lᵖ over an arbitrary measure space is strictly convex when 1 < p < ∞. -/
theorem strictConvexSpace_dual_complexLp (hp : 1 < p) (hp_top : p ≠ ∞) :
    StrictConvexSpace ℝ (StrongDual ℂ (Lp ℂ p μ)) :=
  strictConvexSpace_dual_of_reflexive_of_unique_support
    (surjective_inclusionInDoubleDual_complexLp μ hp hp_top)
    (eq_of_norming_complexLp μ hp hp_top)

/-- The Lᵖ case of Theorem 1.2(v).
Every semigroup of contractions acting on complex Lᵖ, with 1 < p < ∞, is JdLG-admissible. -/
theorem admissible_of_complexLp_contractions
    {S : Type*} [Semigroup S] [Nonempty S] (hp : 1 < p) (hp_top : p ≠ ∞)
    (π : S →ₙ* (Lp ℂ p μ →L[ℂ] Lp ℂ p μ)) (hπ : ∀ s, ‖π s‖ ≤ 1) :
    IsJdLGAdmissible π := by
  let hstrict := strictConvexSpace_dual_complexLp μ hp hp_top
  exact admissible_of_complexLp_contractions_of_reflexive_strictConvexDual μ hp hp_top
    (surjective_inclusionInDoubleDual_complexLp μ hp hp_top) π hπ

end JdLG
