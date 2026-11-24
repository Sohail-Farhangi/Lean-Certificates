/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroOrbit
public import Mixing.RudinShapiroBlockMatching

/-! # Half-rigidity estimates for finite-coordinate Rudin–Shapiro tests -/

@[expose] public section
noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Mixing

private theorem word_shift_iterate (n : ℕ) : (signWordShift 1)^[n] = signWordShift n := by
  induction n with
  | zero => simpa using signWordShift_zero.symm
  | succ n ih => rw [Function.iterate_succ', ih, Nat.cast_succ, add_comm, signWordShift_add]

private theorem sum_range_blocks (f : ℕ → ℝ) (B Q : ℕ) :
    (∑ j ∈ Finset.range (B*Q), f j) = ∑ q ∈ Finset.range Q, ∑ r ∈ Finset.range B, f (B*q+r) := by
  induction Q with
  | zero => simp
  | succ Q ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

private theorem dyadicScalarAverage_blocks (f : ℕ → ℝ) (k n : ℕ) (hn : k+1 ≤ n) :
    dyadicScalarAverage f n =
      dyadicScalarAverage (fun q => (∑ r ∈ Finset.range (2^(k+1)), f (2^(k+1)*q+r)) / (2:ℝ)^(k+1)) (n-(k+1)) := by
  have he : n = (k+1) + (n-(k+1)) := by omega
  have hN : 2^n = 2^(k+1)*2^(n-(k+1)) := by nth_rw 1 [he]; rw [pow_add]
  have hR : (2:ℝ)^n = 2^(k+1)*2^(n-(k+1)) := by nth_rw 1 [he]; rw [pow_add]
  unfold dyadicScalarAverage
  rw [hN, sum_range_blocks, hR, ← Finset.sum_div, div_div]

private def modelWord (k r : ℕ) (s t : ℝ) : SignWords :=
  fun i => decide (t * rudinShapiro ((r : ℤ)+i).toNat * s ^ (((r : ℤ)+i).toNat / 2^k) = 1)

private theorem block_modelWord (k q r i : ℕ) (hi : r+i < 2^(k+1)) :
    (signWordShift (2^(k+1)*q+r : ℕ) rudinShapiroWord) i =
      modelWord k r ((-1:ℝ)^q) (rudinShapiro q) i := by
  have he : ((i : ℤ) + ↑(2^(k+1)*q+r : ℕ)).toNat = 2^(k+1)*q+(r+i) := by omega
  have hri : ((r : ℤ) + (i : ℤ)).toNat = r+i := by omega
  simp only [signWordShift, rudinShapiroWord, modelWord, he, hri]
  rw [rudinShapiro_binary_block k q (r+i) hi, neg_one_pow_mod_two q, ← pow_mul]

private theorem block_shiftWord_eq (k q r i : ℕ) (hi : r+i < 2^(k+1))
    (hMatch : rudinShapiro (q+2) = rudinShapiro q) :
    (signWordShift (2^(k+1)*2 : ℕ) (signWordShift (2^(k+1)*q+r : ℕ) rudinShapiroWord)) i =
      (signWordShift (2^(k+1)*q+r : ℕ) rudinShapiroWord) i := by
  have he : (((i : ℤ) + ↑(2^(k+1)*2 : ℕ)) + ↑(2^(k+1)*q+r : ℕ)).toNat =
      2^(k+1)*(q+2)+(r+i) := by
    rw [Nat.mul_add]
    omega
  have hri : ((i : ℤ) + ↑(2^(k+1)*q+r : ℕ)).toNat = 2^(k+1)*q+(r+i) := by omega
  simp only [signWordShift, rudinShapiroWord, he, hri]
  rw [rudinShapiro_same_two_blocks k q (r+i) hi hMatch]

/-- `f` is determined by the coordinates `0, …, w-1`. Such tests include all
cylinders supported on a finite interval starting at zero. -/
def DependsOnPrefix (w : ℕ) (f : SignWords → ℝ) : Prop :=
  ∀ x y, (∀ i : ℕ, i < w → x i = y i) → f x = f y

private theorem sum_prefix_le_sum_prefix_sub_add_width (f : ℕ → ℝ) (hf : ∀ n, f n ≤ 1)
    (B w : ℕ) : (∑ j ∈ Finset.range B, f j) ≤ (∑ j ∈ Finset.range (B-w), f j) + w := by
  have hB : B = (B-w)+min w B := by omega
  nth_rw 1 [hB]
  rw [Finset.sum_range_add]
  apply add_le_add_right
  exact (Finset.sum_le_sum (fun j _ => hf ((B-w)+j))).trans (by simp)

private theorem finite_block_correlation_bound (f : C(SignWords, ℝ)) (w : ℕ)
    (hf : DependsOnPrefix w f) (h₀ : ∀ x, 0 ≤ f x) (h₁ : ∀ x, f x ≤ 1) (k q : ℕ) :
    let B : ℕ := 2^(k+1)
    let x (r : ℕ) := signWordShift (B*q+r : ℕ) rudinShapiroWord
    let W (s t : ℝ) := (∑ r ∈ Finset.range (B-w), (f (modelWord k r s t))^2) / (B:ℝ)
    (1/2:ℝ) * ((∑ r ∈ Finset.range B, (f (x r))^2) / (B:ℝ)) ≤
      ((∑ r ∈ Finset.range B, f (x r) * f (signWordShift (2^(k+1)*2 : ℕ) (x r))) / (B:ℝ)) -
        ((if rudinShapiro (q+2) = rudinShapiro q then 1 else 0) * W ((-1:ℝ)^q) (rudinShapiro q) -
          (1/2:ℝ)*W ((-1:ℝ)^q) (rudinShapiro q)) + ((w:ℝ)/(B:ℝ))/2 := by
  dsimp only
  let B : ℕ := 2^(k+1)
  let x (r : ℕ) := signWordShift (B*q+r : ℕ) rudinShapiroWord
  let m (r : ℕ) := f (modelWord k r ((-1:ℝ)^q) (rudinShapiro q))
  have hModel (r : ℕ) (hr : r < B-w) : f (x r) = m r := by
    apply hf
    intro i hi
    exact block_modelWord k q r i (by omega)
  have hSum : (∑ r ∈ Finset.range B, (f (x r))^2) ≤ (∑ r ∈ Finset.range (B-w), (m r)^2) + w := by
    have h := sum_prefix_le_sum_prefix_sub_add_width (fun r => (f (x r))^2)
      (fun r => by nlinarith [h₀ (x r), h₁ (x r), mul_nonneg (h₀ (x r)) (sub_nonneg.mpr (h₁ (x r)))]) B w
    refine h.trans_eq (congrArg (fun z : ℝ => z+w) (Finset.sum_congr rfl fun r hr => ?_))
    rw [hModel r (Finset.mem_range.mp hr)]
  have hPair : (if rudinShapiro (q+2) = rudinShapiro q then 1 else 0) *
      (∑ r ∈ Finset.range (B-w), (m r)^2) ≤
        ∑ r ∈ Finset.range B, f (x r) * f (signWordShift (2^(k+1)*2 : ℕ) (x r)) := by
    by_cases hh : rudinShapiro (q+2) = rudinShapiro q
    · rw [ite_eq_left hh, one_mul]
      have he (r : ℕ) (hr : r ∈ Finset.range (B-w)) :
          (m r)^2 = f (x r) * f (signWordShift (2^(k+1)*2 : ℕ) (x r)) := by
        have hr' := Finset.mem_range.mp hr
        have hx : f (signWordShift (2^(k+1)*2 : ℕ) (x r)) = f (x r) :=
          hf _ _ (fun i hi => block_shiftWord_eq k q r i (by omega) hh)
        rw [hx, hModel r hr', pow_two]
      rw [Finset.sum_congr rfl he]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le B w))
        (fun r _ _ => mul_nonneg (h₀ _) (h₀ _))
    · rw [ite_eq_right hh, zero_mul]
      exact Finset.sum_nonneg (fun r _ => mul_nonneg (h₀ _) (h₀ _))
  have hB : (0:ℝ) < (B:ℝ) := by dsimp [B]; positivity
  have hSum' := div_le_div_of_nonneg_right hSum hB.le
  have hPair' := div_le_div_of_nonneg_right hPair hB.le
  rw [add_div] at hSum'
  rw [mul_div_assoc] at hPair'
  change (1/2:ℝ) * ((∑ r ∈ Finset.range B, (f (x r))^2) / (B:ℝ)) ≤
      ((∑ r ∈ Finset.range B, f (x r) * f (signWordShift (2^(k+1)*2 : ℕ) (x r))) / (B:ℝ)) -
        ((if rudinShapiro (q+2) = rudinShapiro q then 1 else 0) *
          ((∑ r ∈ Finset.range (B-w), (m r)^2) / (B:ℝ)) -
          (1/2:ℝ)*((∑ r ∈ Finset.range (B-w), (m r)^2) / (B:ℝ))) + ((w:ℝ)/(B:ℝ))/2
  linarith

/-- The arithmetic half-rigidity inequality for the measured orbit law. The
error is bounded by half the fraction of omitted boundary positions. -/
theorem rudinShapiro_prefix_correlation_lower_bound (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (f : C(SignWords, ℝ)) (w : ℕ) (hf : DependsOnPrefix w f)
    (h₀ : ∀ x, 0 ≤ f x) (h₁ : ∀ x, f x ≤ 1) (k : ℕ) :
    (1/2:ℝ) * (∫ x, (f x)^2 ∂(rudinShapiroOrbitLaw p : Measure SignWords)) ≤
      (∫ x, f x * f (signWordShift (2^(k+1)*2 : ℕ) x) ∂(rudinShapiroOrbitLaw p : Measure SignWords)) +
        ((w:ℝ)/(2:ℝ)^(k+1))/2 := by
  let B : ℕ := 2^(k+1)
  let F : C(SignWords,ℝ) := f*f
  let H : C(SignWords,ℝ) := f * f.comp ⟨signWordShift (B*2 : ℕ), signWordShift_continuous _⟩
  let W (s t : ℝ) := (∑ r ∈ Finset.range (B-w), (f (modelWord k r s t))^2) / (B:ℝ)
  let D (q : ℕ) := (if rudinShapiro (q+2) = rudinShapiro q then 1 else 0) * W ((-1:ℝ)^q) (rudinShapiro q) -
    (1/2:ℝ)*W ((-1:ℝ)^q) (rudinShapiro q)
  let e : ℝ := ((w:ℝ)/(B:ℝ))/2
  have hD : Tendsto (fun n => dyadicScalarAverage D (n-(k+1))) (p : Filter ℕ) (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => n-(k+1)) (p : Filter ℕ) atTop :=
      (tendsto_atTop.mpr (fun m => (eventually_ge_atTop (m+(k+1))).mono fun n hn => by omega)).mono_left hp
    exact (rudinShapiro_weighted_blockAgreement W).comp hsub
  have hF := tendsto_integral_dyadicOrbitLaw (signWordShift 1) rudinShapiroWord p F
  have hH := tendsto_integral_dyadicOrbitLaw (signWordShift 1) rudinShapiroWord p H
  simp_rw [word_shift_iterate] at hF hH
  have hLimF := hF.const_mul (1/2:ℝ)
  have hLimH := (hH.sub hD).add_const e
  have hI : (1/2:ℝ) * (∫ x, F x ∂(rudinShapiroOrbitLaw p : Measure SignWords)) ≤
      (∫ x, H x ∂(rudinShapiroOrbitLaw p : Measure SignWords)) - 0 + e := by
    apply le_of_tendsto_of_tendsto hLimF hLimH
    filter_upwards [hp (eventually_ge_atTop (k+1))] with n hn
    change (1/2:ℝ) * dyadicScalarAverage (fun j => F (signWordShift j rudinShapiroWord)) n ≤
      dyadicScalarAverage (fun j => H (signWordShift j rudinShapiroWord)) n - dyadicScalarAverage D (n-(k+1)) + e
    rw [dyadicScalarAverage_blocks _ k n hn, dyadicScalarAverage_blocks _ k n hn,
      ← dyadicScalarAverage_mul_const, ← dyadicScalarAverage_sub]
    have hAvgConst : dyadicScalarAverage (fun _ => e) (n-(k+1)) = e := by
      unfold dyadicScalarAverage
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    rw [← hAvgConst, ← dyadicScalarAverage_add]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro q hq
    have h := finite_block_correlation_bound f w hf h₀ h₁ k q
    dsimp only at h
    change _ ≤ _
    simpa only [F, H, B, D, W, e, ContinuousMap.mul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, pow_two,
      Nat.cast_pow, Nat.cast_ofNat] using h
  simpa only [F, H, e, B, ContinuousMap.mul_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, pow_two, sub_zero,
    Nat.cast_pow, Nat.cast_ofNat] using hI

end Mixing
