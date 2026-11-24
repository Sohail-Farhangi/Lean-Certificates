/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroCorrelations

/-! # Binary blocks and means of the Rudin–Shapiro signs -/

@[expose] public section
noncomputable section

open Filter
open scoped BigOperators Topology

namespace Mixing

private theorem neg_one_pow_two_mul (n : ℕ) : (-1 : ℝ) ^ (2 * n) = 1 := by
  rw [pow_mul]
  norm_num

theorem neg_one_pow_mod_two (n : ℕ) : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 2) := by
  conv_lhs => rw [show n = 2 * (n/2) + n%2 by omega, pow_add, neg_one_pow_two_mul, one_mul]

/-- Appending a block of `k+1` digits multiplies the two signs and introduces
the factor from the two digits adjacent to the join. The highest digit of `r`
in that block is `r / 2^k`. -/
theorem rudinShapiro_binary_block (k q r : ℕ) (hr : r < 2 ^ (k+1)) :
    rudinShapiro (2 ^ (k+1) * q + r) =
      rudinShapiro q * rudinShapiro r * (-1 : ℝ) ^ ((q%2) * (r / 2^k)) := by
  induction k generalizing r with
  | zero =>
    have h : r = 0 ∨ r = 1 := by norm_num at hr; omega
    rcases h with rfl | rfl
    · simp [rudinShapiro_even]
    · rw [show 2 ^ ((0 : ℕ)+1) * q + 1 = 2*q+1 by norm_num, rudinShapiro_odd, neg_one_pow_mod_two]
      simp only [pow_zero, Nat.div_one, mul_one]
      rw [rudinShapiro_odd 0]
      simp [mul_comm]
  | succ k ih =>
    let B := 2^(k+1)
    let a := r/2
    have hB : 2 ^ (k+1+1) = 2*B := pow_succ' _ _
    rw [hB] at hr
    have ha : a < B := by omega
    have hDigit : a / 2^k = r / 2^(k+1) := by
      rw [show a = r/2 from rfl, Nat.div_div_eq_div_mul, ← pow_succ']
    have hEvenExponent : (-1 : ℝ) ^ (B*q+a) = (-1 : ℝ) ^ a := by
      rw [pow_add, show B*q = 2*(2^k*q) by dsimp [B]; rw [pow_succ', mul_assoc],
        neg_one_pow_two_mul, one_mul]
    have hI := ih a ha
    change rudinShapiro (B*q+a) = _ at hI
    rw [hDigit] at hI
    rw [hB]
    by_cases he : r%2 = 0
    · have heq : r = 2*a := by omega
      rw [show 2*B*q+r = 2*(B*q+a) by rw [heq]; ring, rudinShapiro_even, hI]
      rw [show rudinShapiro r = rudinShapiro a by rw [heq, rudinShapiro_even]]
    · have heq : r = 2*a+1 := by omega
      rw [show 2*B*q+r = 2*(B*q+a)+1 by rw [heq]; ring, rudinShapiro_odd, hEvenExponent, hI]
      rw [show rudinShapiro r = (-1 : ℝ)^a * rudinShapiro a by rw [heq, rudinShapiro_odd]]
      ring

private theorem sum_range_binary_pairs (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (2 * N), f j) =
      ∑ j ∈ Finset.range N, (f (2*j) + f (2*j+1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ _ (2*n), Finset.sum_range_succ _ n, ih]
    ring

/-- Mean of the signs over a dyadic prefix. -/
def rudinShapiroMean (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2^n), rudinShapiro j) / (2 : ℝ)^n

/-- The signed mean detects the final digit of the integer index. -/
def rudinShapiroSignedMean (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2^n), (-1 : ℝ)^j * rudinShapiro j) / (2 : ℝ)^n

theorem rudinShapiro_mean_recurrences (n : ℕ) :
    rudinShapiroMean (n+1) = (rudinShapiroMean n + rudinShapiroSignedMean n) / 2 ∧
    rudinShapiroSignedMean (n+1) = (rudinShapiroMean n - rudinShapiroSignedMean n) / 2 := by
  unfold rudinShapiroMean rudinShapiroSignedMean
  rw [pow_succ (2 : ℕ), mul_comm (2^n) 2, sum_range_binary_pairs, sum_range_binary_pairs]
  have hp (j : ℕ) : (-1 : ℝ) ^ (2*j+1) = -1 := by
    rw [pow_succ, neg_one_pow_two_mul, one_mul]
  simp_rw [rudinShapiro_even, rudinShapiro_odd, neg_one_pow_two_mul, hp, one_mul, neg_one_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, pow_succ]
  constructor <;> ring

private theorem rudinShapiro_mean_two_step (n : ℕ) :
    rudinShapiroMean (n+2) = rudinShapiroMean n / 2 ∧
    rudinShapiroSignedMean (n+2) = rudinShapiroSignedMean n / 2 := by
  obtain ⟨h₁, h₂⟩ := rudinShapiro_mean_recurrences (n+1)
  obtain ⟨h₃, h₄⟩ := rudinShapiro_mean_recurrences n
  rw [h₃, h₄] at h₁ h₂
  constructor <;> linarith

private theorem rudinShapiro_mean_bound (n : ℕ) :
    ‖rudinShapiroMean n‖ ≤ (1/2 : ℝ)^(n/2) ∧
    ‖rudinShapiroSignedMean n‖ ≤ (1/2 : ℝ)^(n/2) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    obtain _ | _ | k := n
    · norm_num [rudinShapiroMean, rudinShapiroSignedMean]
    · have h₀ : rudinShapiroMean 0 = 1 ∧ rudinShapiroSignedMean 0 = 1 := by
        norm_num [rudinShapiroMean, rudinShapiroSignedMean]
      obtain ⟨h₁, h₂⟩ := rudinShapiro_mean_recurrences 0
      rw [h₀.1, h₀.2] at h₁ h₂
      norm_num [h₁, h₂]
    · obtain ⟨h₁, h₂⟩ := rudinShapiro_mean_two_step k
      obtain ⟨h₃, h₄⟩ := ih k (by omega)
      change ‖rudinShapiroMean (k+2)‖ ≤ _ ∧ ‖rudinShapiroSignedMean (k+2)‖ ≤ _
      rw [h₁, h₂, show (k+2)/2 = k/2+1 by omega, pow_succ, norm_div, norm_div]
      norm_num only [Real.norm_ofNat]
      constructor <;> linarith

/-- The ordinary and parity-weighted Rudin–Shapiro signs both have mean zero
along dyadic prefixes. -/
theorem rudinShapiro_dyadic_means :
    Tendsto rudinShapiroMean atTop (𝓝 0) ∧ Tendsto rudinShapiroSignedMean atTop (𝓝 0) := by
  have hNat : Tendsto (fun n : ℕ => n/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop (2*n)] with k hk
    omega
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1/2 : ℝ)) (by norm_num)).comp hNat
  exact ⟨tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) (fun n => (rudinShapiro_mean_bound n).1) h),
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) (fun n => (rudinShapiro_mean_bound n).2) h)⟩

end Mixing
