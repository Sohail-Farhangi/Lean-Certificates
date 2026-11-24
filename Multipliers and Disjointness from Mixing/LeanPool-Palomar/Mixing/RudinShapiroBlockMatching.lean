/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroBlocks

/-! # Agreement between Rudin–Shapiro blocks two blocks apart -/

@[expose] public section
noncomputable section

open Filter
open scoped BigOperators Topology

namespace Mixing

/-- A scalar average over a dyadic prefix. -/
def dyadicScalarAverage (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (2^n), f j) / (2 : ℝ)^n

theorem dyadicScalarAverage_sub (f g : ℕ → ℝ) (n : ℕ) :
    dyadicScalarAverage (fun j => f j - g j) n = dyadicScalarAverage f n - dyadicScalarAverage g n := by
  simp only [dyadicScalarAverage, Finset.sum_sub_distrib, sub_div]

theorem dyadicScalarAverage_add (f g : ℕ → ℝ) (n : ℕ) :
    dyadicScalarAverage (fun j => f j + g j) n = dyadicScalarAverage f n + dyadicScalarAverage g n := by
  simp only [dyadicScalarAverage, Finset.sum_add_distrib, add_div]

theorem dyadicScalarAverage_mul_const (f : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    dyadicScalarAverage (fun j => c * f j) n = c * dyadicScalarAverage f n := by
  unfold dyadicScalarAverage
  rw [← Finset.mul_sum, mul_div_assoc]

private theorem dyadicScalarAverage_tendsto_shift_one (f : ℕ → ℝ) (l : ℝ) (C : ℝ)
    (hC : ∀ j, ‖f j‖ ≤ C) (h : Tendsto (dyadicScalarAverage f) atTop (𝓝 l)) :
    Tendsto (dyadicScalarAverage (fun j => f (j+1))) atTop (𝓝 l) := by
  have hDiff (n : ℕ) : dyadicScalarAverage (fun j => f (j+1)) n =
      dyadicScalarAverage f n + (f (2^n) - f 0) / (2 : ℝ)^n := by
    unfold dyadicScalarAverage
    have he := (Finset.sum_range_succ' f (2^n)).symm.trans (Finset.sum_range_succ f (2^n))
    rw [← add_div]
    congr 1
    linarith
  have hBound : ∀ n : ℕ, ‖f (2^n) - f 0‖ ≤ 2*C := fun n => (norm_sub_le _ _).trans (by linarith [hC (2^n), hC 0])
  have hDec := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
  have hZero : Tendsto (fun n : ℕ => (f (2^n) - f 0) / (2 ^ n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
      hDec.zero_mul_isBoundedUnder_le ⟨2*C, eventually_map.mpr (Eventually.of_forall hBound)⟩
  exact (by simpa only [add_zero] using h.add hZero :
    Tendsto (fun n => dyadicScalarAverage f n + (f (2^n) - f 0) / (2 : ℝ)^n) atTop (𝓝 l)).congr
      (fun n => (hDiff n).symm)

private theorem dyadicScalarAverage_tendsto_shift_two (f : ℕ → ℝ) (hFnorm : ∀ j, ‖f j‖ ≤ 1)
    (h : Tendsto (dyadicScalarAverage f) atTop (𝓝 0)) :
    Tendsto (dyadicScalarAverage (fun j => f (j+2))) atTop (𝓝 0) :=
  dyadicScalarAverage_tendsto_shift_one _ _ _ (fun j => hFnorm (j+1))
    (dyadicScalarAverage_tendsto_shift_one f 0 1 hFnorm h)

private theorem neg_one_pow_add_two (q : ℕ) : (-1 : ℝ)^(q+2) = (-1 : ℝ)^q := by
  rw [pow_add]
  norm_num

theorem rudinShapiro_norm (q : ℕ) : ‖rudinShapiro q‖ = 1 := by
  have h := rudinShapiro_sq q
  rw [← Real.norm_of_nonneg (by positivity : 0 ≤ rudinShapiro q ^ 2), norm_pow] at h
  nlinarith [norm_nonneg (rudinShapiro q)]

private theorem rudinShapiro_lagTwo_means :
    Tendsto (dyadicScalarAverage (fun j => rudinShapiro (j+2))) atTop (𝓝 0) ∧
    Tendsto (dyadicScalarAverage (fun j => (-1 : ℝ)^j * rudinShapiro (j+2))) atTop (𝓝 0) := by
  refine ⟨dyadicScalarAverage_tendsto_shift_two _ (fun j => (rudinShapiro_norm j).le)
    rudinShapiro_dyadic_means.1, ?_⟩
  have hNorm (j : ℕ) : ‖(-1 : ℝ)^j * rudinShapiro j‖ ≤ 1 := by
    rw [norm_mul, norm_pow, rudinShapiro_norm]
    norm_num
  have h := dyadicScalarAverage_tendsto_shift_two _ hNorm rudinShapiro_dyadic_means.2
  simpa only [neg_one_pow_add_two] using h

private theorem eq_one_or_neg_one_of_sq {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 := by
  rcases mul_eq_zero.mp (show (x-1)*(x+1) = 0 by nlinarith) with h₀ | h₁
  · left; linarith
  · right; linarith

private theorem two_sign_expansion (W : ℝ → ℝ → ℝ) (x y : ℝ) (hx : x^2 = 1) (hy : y^2 = 1) :
    W x y = (W 1 1 + W 1 (-1) + W (-1) 1 + W (-1) (-1))/4 +
      (W 1 1 + W 1 (-1) - W (-1) 1 - W (-1) (-1))/4 * x +
      (W 1 1 - W 1 (-1) + W (-1) 1 - W (-1) (-1))/4 * y +
      (W 1 1 - W 1 (-1) - W (-1) 1 + W (-1) (-1))/4 * (x*y) := by
  rcases eq_one_or_neg_one_of_sq hx with rfl | rfl <;>
    rcases eq_one_or_neg_one_of_sq hy with rfl | rfl <;> ring

/-- The lag-two sign correlation tends to zero even after restricting to any
of the four possible types of the first block. -/
theorem rudinShapiro_weighted_lagTwo_correlation (W : ℝ → ℝ → ℝ) :
    Tendsto (dyadicScalarAverage (fun q =>
      W ((-1 : ℝ)^q) (rudinShapiro q) * (rudinShapiro q * rudinShapiro (q+2)))) atTop (𝓝 0) := by
  let a := (W 1 1 + W 1 (-1) + W (-1) 1 + W (-1) (-1))/4
  let b := (W 1 1 + W 1 (-1) - W (-1) 1 - W (-1) (-1))/4
  let c := (W 1 1 - W 1 (-1) + W (-1) 1 - W (-1) (-1))/4
  let d := (W 1 1 - W 1 (-1) - W (-1) 1 + W (-1) (-1))/4
  have hW (q : ℕ) : W ((-1 : ℝ)^q) (rudinShapiro q) * (rudinShapiro q * rudinShapiro (q+2)) =
      a*(rudinShapiro q * rudinShapiro (q+2)) + b*((-1 : ℝ)^q * (rudinShapiro q * rudinShapiro (q+2))) +
      c*rudinShapiro (q+2) + d*((-1 : ℝ)^q * rudinShapiro (q+2)) := by
    have hx : ((-1 : ℝ)^q)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have he := two_sign_expansion W ((-1 : ℝ)^q) (rudinShapiro q) hx (rudinShapiro_sq q)
    change W ((-1 : ℝ)^q) (rudinShapiro q) = a + b*(-1 : ℝ)^q + c*rudinShapiro q +
      d*((-1 : ℝ)^q * rudinShapiro q) at he
    rw [he]
    rcases eq_one_or_neg_one_of_sq (rudinShapiro_sq q) with hr | hr <;> rw [hr] <;> ring
  have hA : Tendsto (dyadicScalarAverage (fun q => rudinShapiro q * rudinShapiro (q+2))) atTop (𝓝 0) :=
    (rudinShapiro_dyadic_correlations 2).1 (by decide)
  have hB : Tendsto (dyadicScalarAverage (fun q => (-1 : ℝ)^q * (rudinShapiro q * rudinShapiro (q+2)))) atTop (𝓝 0) :=
    (rudinShapiro_dyadic_correlations 2).2
  have hLim := (((hA.const_mul a).add (hB.const_mul b)).add
    (rudinShapiro_lagTwo_means.1.const_mul c)).add (rudinShapiro_lagTwo_means.2.const_mul d)
  simp only [mul_zero, add_zero] at hLim
  have hAvg (n : ℕ) := congrArg (fun f => dyadicScalarAverage f n) (funext hW)
  simp only [dyadicScalarAverage_add, dyadicScalarAverage_mul_const] at hAvg
  exact hLim.congr (fun n => (hAvg n).symm)

/-- Agreement two blocks apart has weight one half in each initial block type. -/
theorem rudinShapiro_weighted_blockAgreement (W : ℝ → ℝ → ℝ) :
    Tendsto (dyadicScalarAverage (fun q =>
      (if rudinShapiro (q+2) = rudinShapiro q then 1 else 0) * W ((-1 : ℝ)^q) (rudinShapiro q) -
        (1/2 : ℝ) * W ((-1 : ℝ)^q) (rudinShapiro q))) atTop (𝓝 0) := by
  have he (q : ℕ) :
      (if rudinShapiro (q+2) = rudinShapiro q then 1 else 0) * W ((-1 : ℝ)^q) (rudinShapiro q) -
        (1/2 : ℝ) * W ((-1 : ℝ)^q) (rudinShapiro q) =
      (1/2 : ℝ) * (W ((-1 : ℝ)^q) (rudinShapiro q) * (rudinShapiro q * rudinShapiro (q+2))) := by
    rcases eq_one_or_neg_one_of_sq (rudinShapiro_sq q) with hq | hq <;>
      rcases eq_one_or_neg_one_of_sq (rudinShapiro_sq (q+2)) with hq' | hq' <;>
      rw [hq, hq'] <;> norm_num <;> ring
  have h := (rudinShapiro_weighted_lagTwo_correlation W).const_mul (1/2)
  rw [mul_zero] at h
  apply h.congr
  intro n
  rw [← dyadicScalarAverage_mul_const]
  exact congrArg (fun f => dyadicScalarAverage f n) (funext fun q => (he q).symm)

/-- Blocks whose starting signs agree two blocks apart are identical. -/
theorem rudinShapiro_same_two_blocks (k q r : ℕ) (hr : r < 2^(k+1))
    (hq : rudinShapiro (q+2) = rudinShapiro q) :
    rudinShapiro (2^(k+1)*(q+2)+r) = rudinShapiro (2^(k+1)*q+r) := by
  rw [rudinShapiro_binary_block k (q+2) r hr, rudinShapiro_binary_block k q r hr, hq,
    show (q+2)%2 = q%2 by omega]

end Mixing
