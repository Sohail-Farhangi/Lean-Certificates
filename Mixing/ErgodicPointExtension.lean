/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ErgodicFiniteFibres
public import Mixing.FactorJoiningLift
public import Mixing.StandardGeneratedFactor
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # The ergodic point-extension conclusion of Theorem 5.2 -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory

namespace Mixing

variable {G X : Type*} [CommGroup G] [Countable G] [MeasurableSpace X]
variable [MetricSpace X] [SecondCountableTopology X] [BorelSpace X] [StandardBorelSpace X] [Nonempty X]

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- The generated factor of an ergodic partially rigid system has a single
finite number of points in almost every conditional support. Those points
have equal conditional weights, with the bound from Theorem 5.2. -/
theorem theorem5_2_ergodicPointExtension (S : System G X) (hS : S.IsErgodic)
    (p : Ultrafilter G) {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (hRigid : S.IsPartiallyRigidAlong p a) :
    let T := S.standardGeneratedFactor p
    let F := S.standardGeneratedFactorMap p
    let κ := F.conditionalKernel
    ∃ n : ℕ, 0 < n ∧ n ≤ ⌊a⁻¹⌋₊ ∧
      ∀ᵐ y ∂T.measure, ∃ s : Finset X, (s : Set X) = (κ y).support ∧
        (κ y) (s : Set X)ᶜ = 0 ∧ s.card = n ∧
          ∀ x ∈ s, F.toFun x = y ∧ κ y {x} = (n : ℝ≥0∞)⁻¹ := by
  let T := S.standardGeneratedFactor p
  let F := S.standardGeneratedFactorMap p
  change ∃ n : ℕ, 0 < n ∧ n ≤ ⌊a⁻¹⌋₊ ∧
    ∀ᵐ y ∂T.measure, ∃ s : Finset X, (s : Set X) = (F.conditionalKernel y).support ∧
      (F.conditionalKernel y) (s : Set X)ᶜ = 0 ∧ s.card = n ∧
      ∀ x ∈ s, F.toFun x = y ∧ F.conditionalKernel y {x} = (n : ℝ≥0∞)⁻¹
  obtain ⟨n, hn, haBound, hUniform⟩ := ae_uniform_fibre_support_of_ergodic hS F
    F.conditionalKernel F.comp_conditionalKernel F.ae_conditionalKernel_fibre
    F.ae_conditionalKernel_equivariant (ENNReal.ofReal a) (theorem5_2_finiteFibres S p ha ha₁ hRigid)
  have hb : ((n : ℝ≥0∞) * ENNReal.ofReal a).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top haBound)
      ENNReal.one_ne_top).mpr haBound
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal ha.le, ENNReal.toReal_one] at hb
  have hnBound : n ≤ ⌊a⁻¹⌋₊ :=
    Nat.le_floor (by rw [← one_div]; exact (le_div_iff₀ ha).mpr hb)
  exact ⟨n, hn, hnBound, hUniform⟩

end Mixing
