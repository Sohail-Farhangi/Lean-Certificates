/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace Mixing

open Filter
open scoped BigOperators Topology

/-- The Rudin–Shapiro signs, obtained by appending one binary digit. -/
def rudinShapiro (n : ℕ) : ℝ :=
  if n = 0 then 1 else
    if n % 2 = 0 then rudinShapiro (n / 2)
    else (-1) ^ (n / 2) * rudinShapiro (n / 2)
termination_by n
decreasing_by all_goals omega

@[simp] theorem rudinShapiro_zero : rudinShapiro 0 = 1 := by
  rw [rudinShapiro]
  simp

theorem rudinShapiro_even (n : ℕ) : rudinShapiro (2 * n) = rudinShapiro n := by
  rcases n with rfl | n
  · rfl
  rw [rudinShapiro]
  simp [show 2 * (n + 1) ≠ 0 by omega, show 2 * (n + 1) / 2 = n + 1 by omega]

theorem rudinShapiro_odd (n : ℕ) :
    rudinShapiro (2 * n + 1) = (-1) ^ n * rudinShapiro n := by
  rw [rudinShapiro]
  simp [show (2 * n + 1) / 2 = n by omega]

theorem rudinShapiro_sq (n : ℕ) : rudinShapiro n ^ 2 = 1 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      simp
    have hlt : n / 2 < n := by omega
    have hpow : ((-1 : ℝ) ^ (n / 2)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [rudinShapiro, ite_eq_right hz]
    split_ifs
    · exact ih _ hlt
    · rw [mul_pow, hpow, ih _ hlt, one_mul]

/-- Dyadic autocorrelation of the Rudin–Shapiro signs. -/
def rudinShapiroCorrelation (n k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2 ^ n), rudinShapiro j * rudinShapiro (j + k)) / (2 : ℝ) ^ n

/-- The signed companion needed for the dyadic correlation recurrence. -/
def rudinShapiroSignedCorrelation (n k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2 ^ n), (-1 : ℝ) ^ j * (rudinShapiro j * rudinShapiro (j + k))) /
    (2 : ℝ) ^ n

private theorem sum_range_pairs (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (2 * N), f j) =
      ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ _ (2 * n),
      Finset.sum_range_succ _ n, ih]
    ring

private theorem negative_one_pow_even (n : ℕ) : (-1 : ℝ) ^ (2 * n) = 1 := by
  rw [pow_mul]
  norm_num

private theorem negative_one_pow_odd (n : ℕ) : (-1 : ℝ) ^ (2 * n + 1) = -1 := by
  rw [pow_succ, negative_one_pow_even, one_mul]

private theorem parity_product (j m : ℕ) :
    (-1 : ℝ) ^ j * (-1 : ℝ) ^ (j + m) = (-1 : ℝ) ^ m := by
  rw [← pow_add, show j + (j + m) = 2 * j + m by omega,
    pow_add, negative_one_pow_even, one_mul]

private theorem dyadic_corr_even (n m : ℕ) :
    rudinShapiroCorrelation (n + 1) (2 * m) =
      (1 + (-1 : ℝ) ^ m) * rudinShapiroCorrelation n m / 2 ∧
    rudinShapiroSignedCorrelation (n + 1) (2 * m) =
      (1 - (-1 : ℝ) ^ m) * rudinShapiroCorrelation n m / 2 := by
  have he (j : ℕ) : 2 * j + 2 * m = 2 * (j + m) := by omega
  have ho (j : ℕ) : 2 * j + 1 + 2 * m = 2 * (j + m) + 1 := by omega
  have hop (j : ℕ) :
      rudinShapiro (2 * j + 1) * rudinShapiro (2 * j + 1 + 2 * m) =
        (-1 : ℝ) ^ m * (rudinShapiro j * rudinShapiro (j + m)) := by
    rw [ho, rudinShapiro_odd, rudinShapiro_odd, ← parity_product j m]
    ring
  constructor
  · unfold rudinShapiroCorrelation
    rw [pow_succ, mul_comm (2 ^ n) 2, sum_range_pairs]
    simp_rw [he, hop, rudinShapiro_even, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [pow_succ]
    ring
  · unfold rudinShapiroSignedCorrelation rudinShapiroCorrelation
    rw [pow_succ, mul_comm (2 ^ n) 2, sum_range_pairs]
    simp_rw [he, hop, rudinShapiro_even, negative_one_pow_even, negative_one_pow_odd,
      one_mul, neg_one_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [pow_succ]
    ring

private theorem dyadic_corr_odd (n m : ℕ) :
    rudinShapiroCorrelation (n + 1) (2 * m + 1) =
      ((-1 : ℝ) ^ m * rudinShapiroSignedCorrelation n m +
        rudinShapiroSignedCorrelation n (m + 1)) / 2 ∧
    rudinShapiroSignedCorrelation (n + 1) (2 * m + 1) =
      ((-1 : ℝ) ^ m * rudinShapiroSignedCorrelation n m -
        rudinShapiroSignedCorrelation n (m + 1)) / 2 := by
  have he (j : ℕ) : 2 * j + (2 * m + 1) = 2 * (j + m) + 1 := by omega
  have ho (j : ℕ) : 2 * j + 1 + (2 * m + 1) = 2 * (j + (m + 1)) := by omega
  have hv (j : ℕ) :
      rudinShapiro (2 * j) * rudinShapiro (2 * j + (2 * m + 1)) =
        (-1 : ℝ) ^ m * ((-1 : ℝ) ^ j * (rudinShapiro j * rudinShapiro (j + m))) := by
    rw [he, rudinShapiro_even, rudinShapiro_odd, pow_add]
    ring
  have hw (j : ℕ) :
      rudinShapiro (2 * j + 1) * rudinShapiro (2 * j + 1 + (2 * m + 1)) =
        (-1 : ℝ) ^ j * (rudinShapiro j * rudinShapiro (j + (m + 1))) := by
    rw [ho, rudinShapiro_odd, rudinShapiro_even]
    ring
  constructor
  · unfold rudinShapiroCorrelation rudinShapiroSignedCorrelation
    rw [pow_succ, mul_comm (2 ^ n) 2, sum_range_pairs]
    simp_rw [hv, hw, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [pow_succ]
    ring
  · unfold rudinShapiroSignedCorrelation
    rw [pow_succ, mul_comm (2 ^ n) 2, sum_range_pairs]
    simp_rw [hv, hw, negative_one_pow_even, negative_one_pow_odd, one_mul, neg_one_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [pow_succ]
    ring

@[simp] theorem rudinShapiroCorrelation_zero (n : ℕ) : rudinShapiroCorrelation n 0 = 1 := by
  unfold rudinShapiroCorrelation
  simp_rw [add_zero, ← pow_two, rudinShapiro_sq]
  simp [Nat.cast_pow, (by positivity : (2 : ℝ) ^ n ≠ 0)]

private theorem signed_corr_succ_zero (n : ℕ) : rudinShapiroSignedCorrelation (n + 1) 0 = 0 := by
  simpa using (dyadic_corr_even n 0).2

private theorem signed_corr_succ_one (n : ℕ) :
    rudinShapiroSignedCorrelation (n + 2) 1 =
      (-1 / 2 : ℝ) ^ n * rudinShapiroSignedCorrelation 2 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he := (dyadic_corr_odd (n + 2) 0).2
    simp only [mul_zero, zero_add, pow_zero, signed_corr_succ_zero] at he
    rw [he, ih, pow_succ]
    ring

private theorem signed_corr_one_tendsto :
    Tendsto (fun n ↦ rudinShapiroSignedCorrelation n 1) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 2).1
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (r := (-1 / 2 : ℝ)) (by norm_num)).mul_const (rudinShapiroSignedCorrelation 2 1)
  rw [zero_mul] at h
  exact h.congr (fun n ↦ (signed_corr_succ_one n).symm)

/-- All off-zero dyadic autocorrelations of the Rudin–Shapiro signs vanish.
The signed companion converges to zero at every lag. -/
theorem rudinShapiro_dyadic_correlations (k : ℕ) :
    (k ≠ 0 → Tendsto (fun n ↦ rudinShapiroCorrelation n k) atTop (𝓝 0)) ∧
    Tendsto (fun n ↦ rudinShapiroSignedCorrelation n k) atTop (𝓝 0) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases h0 : k = 0
    · subst k
      refine ⟨fun h ↦ (h rfl).elim, (tendsto_add_atTop_iff_nat 1).1 ?_⟩
      simpa only [signed_corr_succ_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
    by_cases h1 : k = 1
    · subst k
      refine ⟨fun _ ↦ (tendsto_add_atTop_iff_nat 2).1 ?_, signed_corr_one_tendsto⟩
      have he (n : ℕ) :
          rudinShapiroCorrelation (n + 2) 1 = rudinShapiroSignedCorrelation (n + 1) 1 / 2 := by
        simpa only [mul_zero, zero_add, pow_zero, one_mul, signed_corr_succ_zero, zero_add]
          using (dyadic_corr_odd (n + 1) 0).1
      simp_rw [he]
      simpa using ((tendsto_add_atTop_iff_nat 1).2 signed_corr_one_tendsto).div_const 2
    by_cases he : k % 2 = 0
    · have heq : k = 2 * (k / 2) := by omega
      let m := k / 2
      have hlim := (ih m (by omega)).1 (by omega)
      have hk : k = 2 * m := heq
      rw [hk]
      refine ⟨fun _ ↦ (tendsto_add_atTop_iff_nat 1).1 ?_, (tendsto_add_atTop_iff_nat 1).1 ?_⟩
      · simp_rw [fun n ↦ (dyadic_corr_even n m).1]
        simpa using (hlim.const_mul (1 + (-1 : ℝ) ^ m)).div_const 2
      · simp_rw [fun n ↦ (dyadic_corr_even n m).2]
        simpa using (hlim.const_mul (1 - (-1 : ℝ) ^ m)).div_const 2
    · let m := k / 2
      have hk : k = 2 * m + 1 := by omega
      have hm := (ih m (by omega)).2
      have hm' := (ih (m + 1) (by omega)).2
      rw [hk]
      refine ⟨fun _ ↦ (tendsto_add_atTop_iff_nat 1).1 ?_, (tendsto_add_atTop_iff_nat 1).1 ?_⟩
      · simp_rw [fun n ↦ (dyadic_corr_odd n m).1]
        simpa using ((hm.const_mul ((-1 : ℝ) ^ m)).add hm').div_const 2
      · simp_rw [fun n ↦ (dyadic_corr_odd n m).2]
        simpa using ((hm.const_mul ((-1 : ℝ) ^ m)).sub hm').div_const 2

end Mixing
