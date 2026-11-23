/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRigidSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Binary rigidity phases for a lacunary sequence

Successive rounding to finer grids gives an injective family of
rigidity phases. The same error bound works for every binary input.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter
open scoped Topology

/-- The integer corresponding to a binary digit. -/
def binaryDigit (b : Bool) : ℤ := if b then 1 else 0

theorem binaryDigit_injective : Function.Injective binaryDigit := by
  intro a b h
  cases a <;> cases b <;> simp_all [binaryDigit]

/-- The integer digit lies between zero and one after casting to the reals. -/
theorem cast_binaryDigit_bounds (b : Bool) :
    0 ≤ (binaryDigit b : ℝ) ∧ (binaryDigit b : ℝ) ≤ 1 := by
  cases b <;> norm_num [binaryDigit]

/-- Integer numerators obtained by rounding to the next grid and choosing a
binary offset at each stage. -/
noncomputable def gridNumerator (r : ℕ → ℝ) (b : ℕ → Bool) : ℕ → ℤ
  | 0 => binaryDigit (b 0)
  | n + 1 => ⌊r (n + 1) * ((gridNumerator r b n : ℝ) / r n)⌋ +
      binaryDigit (b (n + 1))

/-- The successive quotients on the grids with spacing `1 / r n`. -/
noncomputable def gridApproximation (r : ℕ → ℝ) (b : ℕ → Bool) (n : ℕ) : ℝ :=
  (gridNumerator r b n : ℝ) / r n

private theorem gridApproximation_step (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (b : ℕ → Bool) (n : ℕ) :
    dist (gridApproximation r b n) (gridApproximation r b (n + 1)) ≤ 1 / r (n + 1) := by
  let x := r (n + 1) * gridApproximation r b n
  have h₁ : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le _
  have h₂ : x - 1 ≤ ((⌊x⌋ : ℤ) : ℝ) := (Int.sub_one_lt_floor _).le
  have h₃ := cast_binaryDigit_bounds (b (n + 1))
  have heq : gridApproximation r b (n + 1) =
      (((⌊x⌋ : ℤ) : ℝ) + (binaryDigit (b (n + 1)) : ℝ)) / r (n + 1) := by
    simp only [gridApproximation, gridNumerator, Int.cast_add, x]
  rw [Real.dist_eq, abs_le, heq, le_div_iff₀ (hr _)]
  constructor
  · have hp : -(1 : ℝ) / r (n + 1) ≤ gridApproximation r b n -
        (((⌊x⌋ : ℤ) : ℝ) + (binaryDigit (b (n + 1)) : ℝ)) / r (n + 1) := by
      rw [show gridApproximation r b n = x / r (n + 1) by
        dsimp [x]
        rw [mul_div_cancel_left₀ _ (hr _).ne'], ← sub_div, div_le_div_iff_of_pos_right (hr _)]
      linarith
    simpa only [neg_div] using hp
  · rw [show gridApproximation r b n = x / r (n + 1) by
      dsimp [x]
      rw [mul_div_cancel_left₀ _ (hr _).ne'], ← sub_div, div_mul_cancel₀ _ (hr _).ne']
    linarith

private theorem grid_growth (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (m j : ℕ) : r m * 2 ^ j ≤ r (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, Nat.add_succ]
    exact (mul_le_mul_of_nonneg_right ih (by norm_num)).trans
      ((show r (m + j) * 2 ≤ 8 * r (m + j) by linarith [hr (m + j)]).trans (hg (m + j)))

private theorem grid_geometric_step (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (b : ℕ → Bool) (m j : ℕ) :
    dist (gridApproximation r b (j + m)) (gridApproximation r b (j + 1 + m)) ≤
      (2 / r (m + 1)) / 2 / 2 ^ j := by
  rw [show j + 1 + m = j + m + 1 by omega]
  apply (gridApproximation_step r hr b (j + m)).trans
  have hgr : r (m + 1) * 2 ^ j ≤ r (j + m + 1) := by
    rw [show j + m + 1 = m + 1 + j by omega]
    exact grid_growth r hg hr (m + 1) j
  calc
    1 / r (j + m + 1) ≤ 1 / (r (m + 1) * 2 ^ j) :=
      one_div_le_one_div_of_le (mul_pos (hr _) (by positivity)) hgr
    _ = _ := by
      have h : r (m + 1) ≠ 0 := (hr _).ne'
      field_simp

/-- Each sequence of grid approximations has a real limit. -/
theorem exists_grid_limit (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (b : ℕ → Bool) :
    ∃ x, Tendsto (gridApproximation r b) atTop (𝓝 x) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_le_geometric_two (C := 2 / r 1)
  intro j
  simpa only [add_zero, zero_add] using grid_geometric_step r hg hr b 0 j

/-- The real phase encoded by a binary input. -/
noncomputable def rigidityPhase (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (b : ℕ → Bool) : ℝ :=
  (exists_grid_limit r hg hr b).choose

theorem rigidityPhase_limit (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (b : ℕ → Bool) :
    Tendsto (gridApproximation r b) atTop (𝓝 (rigidityPhase r hg hr b)) :=
  (exists_grid_limit r hg hr b).choose_spec

theorem rigidityPhase_distance (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (b : ℕ → Bool) (n : ℕ) :
    dist (gridApproximation r b n) (rigidityPhase r hg hr b) ≤ 2 / r (n + 1) := by
  have ht := (rigidityPhase_limit r hg hr b).comp (tendsto_add_atTop_nat n)
  simpa only [zero_add] using dist_le_of_le_geometric_two_of_tendsto₀
    (C := 2 / r (n + 1)) (grid_geometric_step r hg hr b n) ht

/-- Each binary phase is uniformly close to an integer when multiplied by
the grid denominators. -/
theorem rigidityPhase_error (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (b : ℕ → Bool) (n : ℕ) :
    |r n * rigidityPhase r hg hr b - (gridNumerator r b n : ℝ)| ≤ 2 * r n / r (n + 1) := by
  have hd := rigidityPhase_distance r hg hr b n
  rw [dist_comm, Real.dist_eq] at hd
  have heq : r n * gridApproximation r b n = (gridNumerator r b n : ℝ) := by
    rw [gridApproximation, mul_div_cancel₀ _ (hr n).ne']
  calc
    _ = r n * |rigidityPhase r hg hr b - gridApproximation r b n| := by
      rw [← heq, ← mul_sub, abs_mul, abs_of_pos (hr n)]
    _ ≤ r n * (2 / r (n + 1)) := mul_le_mul_of_nonneg_left hd (hr n).le
    _ = _ := by rw [← mul_div_assoc, mul_comm (r n) 2]

/-- For diverging successive ratios the phase discrepancy converges to zero. -/
theorem rigidityPhase_scaled_tendsto_integer (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n)
    (hRatio : Tendsto (fun n ↦ r (n + 1) / r n) atTop atTop) (b : ℕ → Bool) :
    Tendsto (fun n ↦ r n * rigidityPhase r hg hr b - (gridNumerator r b n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hu : Tendsto (fun n ↦ 2 / (r (n + 1) / r n)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hRatio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ ↦ norm_nonneg _
  · refine Eventually.of_forall fun n ↦ ?_
    rw [Real.norm_eq_abs, div_div_eq_mul_div]
    exact rigidityPhase_error r hg hr b n

/-- Two binary inputs cannot encode the same phase. Their grid numerators are
uniquely determined by the common phase, and recover the binary offsets. -/
theorem rigidityPhase_injective (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) : Function.Injective (rigidityPhase r hg hr) := by
  intro b c h
  have hnum (n : ℕ) : gridNumerator r b n = gridNumerator r c n := by
    let x := r n * rigidityPhase r hg hr b
    have hb := rigidityPhase_error r hg hr b n
    have hc := rigidityPhase_error r hg hr c n
    rw [← h] at hc
    have hdiff : |(gridNumerator r b n : ℝ) - (gridNumerator r c n : ℝ)| ≤ (1 / 2 : ℝ) := calc
      _ = |(x - (gridNumerator r c n : ℝ)) - (x - (gridNumerator r b n : ℝ))| := by
        congr 1
        ring
      _ ≤ |x - (gridNumerator r c n : ℝ)| + |x - (gridNumerator r b n : ℝ)| := abs_sub _ _
      _ ≤ 2 * (2 * r n / r (n + 1)) := by
        dsimp [x]
        linarith
      _ ≤ _ := by
        rw [← mul_div_assoc, div_le_iff₀ (hr _)]
        linarith [hg n]
    obtain ⟨hlo, hhi⟩ := abs_le.1 hdiff
    have hlt : gridNumerator r b n < gridNumerator r c n + 1 := by
      exact_mod_cast (show (gridNumerator r b n : ℝ) < (gridNumerator r c n : ℝ) + 1 by linarith)
    have hgt : gridNumerator r c n < gridNumerator r b n + 1 := by
      exact_mod_cast (show (gridNumerator r c n : ℝ) < (gridNumerator r b n : ℝ) + 1 by linarith)
    omega
  funext n
  apply binaryDigit_injective
  cases n with
  | zero => exact hnum 0
  | succ n =>
    have hs := hnum (n + 1)
    simp only [gridNumerator, hnum n] at hs
    omega

end JdLG.PaperExamplesRigid
