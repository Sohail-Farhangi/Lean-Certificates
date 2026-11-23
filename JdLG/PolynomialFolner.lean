/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PolynomialWeakMixing
public import JdLG.FolnerCriteria
public import JdLG.PaperExamplesRigidityAWS

/-! # The linear weak-mixing hypothesis from the JdLG weak part -/

@[expose] public section

open Filter MeasureTheory Finset Set
open scoped Topology ENNReal BigOperators InnerProductSpace

namespace JdLG

local notation "Z" => Multiplicative ℤ

/-- Uniform probabilities on the initial integer intervals of length N+1. -/
noncomputable def integerIntervalProbability (N : ℕ) : Measure Z :=
  ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (Multiplicative.ofAdd (n : ℤ))

theorem integerIntervalProbability_isProbability (N : ℕ) :
    IsProbabilityMeasure (integerIntervalProbability N) := by
  constructor
  rw [integerIntervalProbability, smul_apply]
  simp only [FunLike.coe_sum, Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

theorem integral_integerIntervalProbability (f : Z → ℝ) (N : ℕ) :
    (∫ t, f t ∂integerIntervalProbability N) =
      scalarCesaro (fun n ↦ f (Multiplicative.ofAdd (n : ℤ))) (N + 1) := by
  rw [integerIntervalProbability, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, scalarCesaro]

/-- The positive initial integer intervals are left Følner for arbitrary real
tests bounded by one. -/
theorem integerIntervalProbability_leftFolner :
    LeftFolnerProbabilities integerIntervalProbability atTop := by
  intro s ε hε
  let k := s.toAdd.natAbs
  have hLim : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)⁻¹ * ((k : ℝ) + k)) atTop (𝓝 0) := by
    have hInv : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, zero_mul] using
      (hInv.comp (tendsto_add_atTop_nat 1)).mul_const ((k : ℝ) + k)
  filter_upwards [hLim.eventually (gt_mem_nhds hε)] with N hN
  intro f _ hf
  rw [integral_integerIntervalProbability, integral_integerIntervalProbability]
  let u (n : ℕ) := f (Multiplicative.ofAdd (n : ℤ))
  let v (n : ℕ) := f (s * Multiplicative.ofAdd (n : ℤ))
  change ‖scalarCesaro v (N + 1) - scalarCesaro u (N + 1)‖ < ε
  by_cases h : 0 ≤ s.toAdd
  · have hs : s.toAdd = (k : ℤ) := Int.eq_natAbs_of_nonneg h
    have hEq : v = fun n ↦ u (n + k) := by
      funext n
      change f (Multiplicative.ofAdd (s.toAdd + (n : ℤ))) =
        f (Multiplicative.ofAdd ((n + k : ℕ) : ℤ))
      rw [hs, Nat.cast_add, add_comm]
    rw [hEq]
    have hBound := norm_scalarCesaro_shift_sub_le u 1 (fun n ↦ hf (Multiplicative.ofAdd (n : ℤ)))
      (N + 1) k
    exact hBound.trans_lt (by simpa only [mul_one] using hN)
  · have hs : s.toAdd = -(k : ℤ) := Int.eq_neg_natAbs_of_nonpos (le_of_not_ge h)
    have hEq : u = fun n ↦ v (n + k) := by
      funext n
      change f (Multiplicative.ofAdd (n : ℤ)) =
        f (Multiplicative.ofAdd (s.toAdd + ((n + k : ℕ) : ℤ)))
      rw [hs, Nat.cast_add, add_comm (n : ℤ), neg_add_cancel_left]
    rw [norm_sub_rev, hEq]
    have hBound := norm_scalarCesaro_shift_sub_le v 1
      (fun n ↦ hf (s * Multiplicative.ofAdd (n : ℤ)))
      (N + 1) k
    exact hBound.trans_lt (by simpa only [mul_one] using hN)

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Almost weak stability of a unitary vector implies vanishing of its linear
absolute self-coefficient Cesàro averages, by the measured Følner criterion. -/
theorem tendsto_abs_self_coeff_of_integer_action_aws (U : Z →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hx : IsAlmostWeaklyStable (closureAction (PaperExamplesRigid.unitaryIntegerAction U)) x) :
    Tendsto (scalarCesaro fun n : ℕ ↦ ‖inner ℂ x (U (Multiplicative.ofAdd (n : ℤ)) x)‖)
      atTop (𝓝 0) := by
  let ρ := PaperExamplesRigid.unitaryIntegerAction U
  have hadm : IsJdLGAdmissible ρ := PaperExamplesRigid.unitaryIntegerAction_admissible _
  let : CompactSpace (weakOperatorClosure ρ) := isCompact_iff_compactSpace.mp hadm.1
  let : MeasurableSpace (weakOperatorClosure ρ) := borel _
  let : BorelSpace (weakOperatorClosure ρ) := ⟨rfl⟩
  let : Countable Z := inferInstanceAs (Countable ℤ)
  have hρ : Measurable (closureInclusion ρ) := measurable_of_countable _
  have h := (stable_iff_folnerCoefficientMoments ρ hρ integerIntervalProbability
      integerIntervalProbability_isProbability integerIntervalProbability_leftFolner
      hadm x 1 zero_lt_one).1 hx (innerSL ℂ x)
  apply (tendsto_add_atTop_iff_nat 1).mp
  simp only [Real.rpow_one, integral_integerIntervalProbability] at h
  exact h

theorem tendsto_abs_self_coeff_of_unitary_aws (U : H ≃ₗᵢ[ℂ] H) (x : H)
    (hx : IsAlmostWeaklyStable
      (closureAction (PaperExamplesRigid.unitaryIntegerAction (unitaryIntegerPowers U))) x) :
    Tendsto (scalarCesaro fun n : ℕ ↦ ‖inner ℂ x ((U ^ (n : ℤ)) x)‖) atTop (𝓝 0) := by
  simpa only [unitaryIntegerPowers_ofAdd] using
    tendsto_abs_self_coeff_of_integer_action_aws (unitaryIntegerPowers U) x hx

/-- Equation (20) for vectors in the almost weakly stable part of a unitary
operator, with no Cesàro hypothesis assumed. -/
theorem tendsto_abs_coeff_perfect_powers_of_unitary_aws (U : H ≃ₗᵢ[ℂ] H) (x y : H)
    (hx : IsAlmostWeaklyStable
      (closureAction (PaperExamplesRigid.unitaryIntegerAction (unitaryIntegerPowers U))) x)
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (scalarCesaro fun n ↦ ‖inner ℂ ((U ^ (((n : ℤ) + 1) ^ k)) x) y‖)
      atTop (𝓝 0) :=
  tendsto_abs_coeff_perfect_powers U x y (tendsto_abs_self_coeff_of_unitary_aws U x hx) k hk

end Unitary

end JdLG
