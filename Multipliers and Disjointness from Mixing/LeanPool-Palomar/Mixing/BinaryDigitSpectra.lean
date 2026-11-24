/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorSpectral
public import Mixing.StationaryGaussian
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.Instances.ZMultiples

/-! # Centered binary digit spectral measures -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

namespace Mixing.BinaryDigitSpectra

/-- The size of a centered binary digit at place k+1. -/
noncomputable def weight (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 2)

/-- Keep the binary digits belonging to the indicated mask. -/
noncomputable def maskedWeight (A : Set ℕ) (k : ℕ) : ℝ := by
  classical
  exact if k ∈ A then weight k else 0

private theorem weight_summable : Summable weight := by
  have h : Summable (fun k : ℕ => (1 / 2 : ℝ)^k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  change Summable (fun k => (1 / 2 : ℝ) ^ (k + 2))
  simp only [pow_add]
  exact h.mul_right _

noncomputable def contribution (A : Set ℕ) (ω : ℕ → Bool) (k : ℕ) : ℝ :=
  if ω k then maskedWeight A k else -maskedWeight A k

/-- A finite centered binary expansion with the chosen mask of digits. -/
noncomputable def digitPrefix (A : Set ℕ) (N : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ k ∈ Finset.range N, contribution A ω k

/-- The random centered binary expansion with the chosen mask. -/
noncomputable def expansion (A : Set ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑' k, contribution A ω k

private theorem contribution_summable (A : Set ℕ) (ω : ℕ → Bool) : Summable (contribution A ω) := by
  apply Summable.of_norm_bounded weight_summable
  intro k
  classical
  have hw : 0 ≤ weight k := by unfold weight; positivity
  unfold contribution maskedWeight
  by_cases h : k ∈ A <;> cases h' : ω k <;> simp [h, Real.norm_eq_abs, abs_of_nonneg hw, hw]

theorem prefix_tendsto (A : Set ℕ) (ω : ℕ → Bool) :
    Tendsto (fun N => digitPrefix A N ω) atTop (𝓝 (expansion A ω)) :=
  (contribution_summable A ω).hasSum.tendsto_sum_nat

private theorem prefix_measurable (A : Set ℕ) (N : ℕ) : Measurable (digitPrefix A N) := by
  apply Finset.measurable_fun_sum
  intro k _
  exact (Measurable.of_discrete (f := fun b : Bool => if b then maskedWeight A k else -maskedWeight A k)).comp
    (measurable_pi_apply k)

theorem expansion_measurable (A : Set ℕ) : Measurable (expansion A) :=
  measurable_of_tendsto_metrizable (prefix_measurable A) (tendsto_pi_nhds.mpr (prefix_tendsto A))

/-- The probability spectral measure of the chosen centered binary digits. -/
noncomputable def maskMeasure (A : Set ℕ) : Measure UnitAddCircle :=
  cantorDigitProduct.map (fun ω => (expansion A ω : UnitAddCircle))

theorem circleExpansion_measurable (A : Set ℕ) :
    Measurable (fun ω => (expansion A ω : UnitAddCircle)) :=
  (AddCircle.continuous_mk' (1 : ℝ)).measurable.comp (expansion_measurable A)

instance (A : Set ℕ) : IsProbabilityMeasure (maskMeasure A) :=
  (Measure.isProbabilityMeasure_map_iff (circleExpansion_measurable A).aemeasurable).mpr inferInstance

/-- The characteristic function of the masked expansion at a real frequency. -/
noncomputable def transform (A : Set ℕ) (t : ℝ) : ℂ :=
  ∫ ω, cantorCharacter (t * expansion A ω) ∂cantorDigitProduct

/-- The expectation contributed by an individual fair centered digit. -/
noncomputable def factor (A : Set ℕ) (t : ℝ) (k : ℕ) : ℂ :=
  (cantorCharacter (t * maskedWeight A k) + cantorCharacter (-(t * maskedWeight A k))) / 2

theorem factor_eq_cos (A : Set ℕ) (t : ℝ) (k : ℕ) :
    factor A t k = (Real.cos (2 * Real.pi * (t * maskedWeight A k)) : ℂ) := by
  rw [Complex.ofReal_cos]
  unfold factor cantorCharacter Complex.cos
  push_cast
  congr 1
  rw [add_comm]
  congr 1 <;> congr 1 <;> ring

private theorem cantorCharacter_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    cantorCharacter (∑ j ∈ s, f j) = ∏ j ∈ s, cantorCharacter (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, cantorCharacter_add, ih]

private theorem prefix_integral (A : Set ℕ) (t : ℝ) (N : ℕ) :
    (∫ ω, cantorCharacter (t * digitPrefix A N ω) ∂cantorDigitProduct) =
      ∏ k ∈ Finset.range N, factor A t k := by
  classical
  let s := Finset.range N
  let f (k : s) (b : Bool) := cantorCharacter (t * (if b then maskedWeight A k else -maskedWeight A k))
  let g (ω : s → Bool) := ∏ k : s, f k (ω k)
  have hg : Measurable g := Finset.measurable_fun_prod _ (fun k _ =>
    (Measurable.of_discrete (f := f k)).comp (measurable_pi_apply k))
  have hω (ω : ℕ → Bool) : cantorCharacter (t * digitPrefix A N ω) = g (s.restrict ω) := by
    unfold digitPrefix
    rw [Finset.mul_sum, cantorCharacter_sum]
    exact (Finset.prod_attach s (fun k => cantorCharacter (t * contribution A ω k))).symm
  simp_rw [hω]
  unfold cantorDigitProduct
  rw [MeasureTheory.integral_restrict_infinitePi _ hg.aestronglyMeasurable]
  change (∫ ω : s → Bool, ∏ k : s, f k (ω k) ∂Measure.pi (fun _ : s => cantorDigitLaw)) = _
  rw [integral_fintype_prod_eq_prod]
  conv_rhs => rw [← Finset.prod_attach s]
  apply Finset.prod_congr rfl
  intro k _
  unfold f cantorDigitLaw factor
  rw [integral_bernoulliMeasure]
  norm_num [Complex.real_smul]
  ring

theorem transform_tendsto_prod (A : Set ℕ) (t : ℝ) :
    Tendsto (fun N => ∏ k ∈ Finset.range N, factor A t k) atTop (𝓝 (transform A t)) := by
  have hm : Measurable (fun x : ℝ => cantorCharacter (t * x)) := by fun_prop
  simp_rw [← prefix_integral A t]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
    (integrable_const _) (fun _ => .of_forall fun _ => by simp) (.of_forall fun ω => ?_)
  · intro N
    exact (hm.comp (prefix_measurable A N)).aestronglyMeasurable
  · exact cantorCharacter_continuous.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (prefix_tendsto A ω))

/-- The Gaussian covariance associated to the mask is its real Fourier transform. -/
theorem covariance_maskMeasure (A : Set ℕ) (n : ℤ) :
    StationaryGaussian.covariance (maskMeasure A) n = (transform A n).re := by
  unfold StationaryGaussian.covariance GaussianPath.spectralCovariance maskMeasure transform
  rw [integral_map (circleExpansion_measurable A).aemeasurable
    (fourier (T := 1) (-n)).continuous.aestronglyMeasurable]
  apply congrArg Complex.re
  apply integral_congr_ae
  refine .of_forall fun ω => ?_
  change fourier (-n) (expansion A ω : UnitAddCircle) = cantorCharacter ((n : ℝ) * expansion A ω)
  rw [fourier_coe_apply, cantorCharacter]
  congr 1
  push_cast
  simp only [div_one]
  ring

theorem norm_transform_le_one (A : Set ℕ) (t : ℝ) : ‖transform A t‖ ≤ 1 := by
  exact (norm_integral_le_integral_norm _).trans_eq (by simp)

theorem transform_eq_ofReal_re (A : Set ℕ) (t : ℝ) : transform A t = ((transform A t).re : ℂ) := by
  have h := (Complex.continuous_im.tendsto _).comp (transform_tendsto_prod A t)
  have hz (N : ℕ) : (∏ k ∈ Finset.range N, factor A t k).im = 0 := by
    simp_rw [factor_eq_cos]
    rw [← Complex.ofReal_prod, Complex.ofReal_im]
  have h0 := tendsto_nhds_unique (h.congr (fun n => hz n)) (tendsto_const_nhds (x := (0 : ℝ)))
  rw [← Complex.re_add_im (transform A t), h0]
  simp

private theorem factor_of_notMem (A : Set ℕ) (t : ℝ) {k : ℕ} (h : k ∉ A) :
    factor A t k = 1 := by simp [factor, maskedWeight, h]

/-- Disjoint masks use disjoint independent sets of digits. -/
theorem transform_union_of_disjoint {A B : Set ℕ} (hAB : _root_.Disjoint A B) (t : ℝ) :
    transform (A ∪ B) t = transform A t * transform B t := by
  classical
  have he (k : ℕ) : factor (A ∪ B) t k = factor A t k * factor B t k := by
    by_cases ha : k ∈ A
    · have hb : k ∉ B := fun hb => Set.disjoint_left.mp hAB ha hb
      simp [factor, maskedWeight, ha, hb]
    · by_cases hb : k ∈ B
      · simp [factor, maskedWeight, ha, hb]
      · simp [factor, maskedWeight, ha, hb]
  apply tendsto_nhds_unique (transform_tendsto_prod (A ∪ B) t)
  simpa only [he, Finset.prod_mul_distrib] using (transform_tendsto_prod A t).mul (transform_tendsto_prod B t)

private theorem expansion_tail_bound {A : Set ℕ} {M : ℕ} (hA : A ⊆ Ici M) (ω : ℕ → Bool) :
    ‖expansion A ω‖ ≤ (1 / 2 : ℝ) ^ M / 2 := by
  classical
  have hSumm : Summable fun k => ‖contribution A ω k‖ := (contribution_summable A ω).norm
  have hBound (k : ℕ) : ‖contribution A ω k‖ ≤ weight k := by
    have hw : 0 ≤ weight k := by unfold weight; positivity
    have he : ‖contribution A ω k‖ = ‖maskedWeight A k‖ := by
      unfold contribution
      split <;> simp
    rw [he]
    unfold maskedWeight
    split
    · rw [Real.norm_of_nonneg hw]
    · rwa [norm_zero]
  have hZero (k : ℕ) (hk : k ∈ Finset.range M) : ‖contribution A ω k‖ = 0 := by
    have h : k ∉ A := fun ha => (Finset.mem_range.mp hk).not_ge (hA ha)
    simp [contribution, maskedWeight, h]
  have hSplit := hSumm.sum_add_tsum_nat_add M
  rw [Finset.sum_eq_zero hZero, zero_add] at hSplit
  calc
    ‖expansion A ω‖ ≤ ∑' k, ‖contribution A ω k‖ := by
      unfold expansion
      exact norm_tsum_le_tsum_norm hSumm
    _ = ∑' k, ‖contribution A ω (k + M)‖ := hSplit.symm
    _ ≤ ∑' k, weight (k + M) := ((summable_nat_add_iff M).mpr hSumm).tsum_le_tsum
      (fun k => hBound (k + M)) ((summable_nat_add_iff M).mpr weight_summable)
    _ = _ := by
      simp only [weight, Nat.add_assoc, pow_add, tsum_mul_right]
      rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)]
      ring

/-- The transform of the tail is Lipschitz with a constant tending to zero
as more initial digits are discarded. -/
theorem norm_transform_add_sub_le {A : Set ℕ} {M : ℕ} (hA : A ⊆ Ici M) (t s : ℝ) :
    ‖transform A (t + s) - transform A t‖ ≤ 2 * Real.pi * ‖s‖ * ((1 / 2 : ℝ)^M / 2) := by
  have hI (r : ℝ) : Integrable (fun ω => cantorCharacter (r * expansion A ω)) cantorDigitProduct :=
    Integrable.of_bound (cantorCharacter_continuous.measurable.comp
      (measurable_const.mul (expansion_measurable A))).aestronglyMeasurable
      1 (.of_forall fun _ => (cantorCharacter_norm _).le)
  rw [transform, transform, ← integral_sub' (hI _) (hI _)]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hb (ω : ℕ → Bool) : ‖cantorCharacter ((t + s) * expansion A ω) -
      cantorCharacter (t * expansion A ω)‖ ≤ 2 * Real.pi * ‖s‖ * ((1 / 2 : ℝ)^M / 2) := by
    rw [add_mul, cantorCharacter_add, ← mul_sub_one, norm_mul, cantorCharacter_norm, one_mul]
    have hl := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * Real.pi * (s * expansion A ω))
    change ‖cantorCharacter (s * expansion A ω) - 1‖ ≤ _ at hl
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg Real.pi_pos.le] at hl
    norm_num at hl
    exact hl.trans (by
      have hTail := expansion_tail_bound hA ω
      rw [Real.norm_eq_abs] at hTail
      rw [Real.norm_eq_abs]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hTail
        (show 0 ≤ 2 * Real.pi * |s| by positivity))
  exact (integral_mono ((hI _).sub (hI _)).norm (integrable_const _) hb).trans_eq (by simp)

private theorem transform_tail_scale (M : ℕ) (t : ℝ) :
    transform (Ici M) t = transform univ (t * (1 / 2 : ℝ)^M) := by
  have ht := (transform_tendsto_prod (Ici M) t).comp (tendsto_add_atTop_nat M)
  apply tendsto_nhds_unique ht
  refine (transform_tendsto_prod univ (t * (1 / 2 : ℝ)^M)).congr fun N => ?_
  change (∏ k ∈ Finset.range N, factor univ (t * (1 / 2 : ℝ)^M) k) =
    ∏ k ∈ Finset.range (N + M), factor (Ici M) t k
  rw [Nat.add_comm N M, Finset.prod_range_add]
  have hP : (∏ k ∈ Finset.range M, factor (Ici M) t k) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    exact factor_of_notMem _ _ (Finset.mem_range.mp hk).not_ge
  rw [hP, one_mul]
  apply Finset.prod_congr rfl
  intro k _
  have hk : M + k ∈ Ici M := Nat.le_add_right _ _
  simp only [factor_eq_cos, maskedWeight, Set.mem_univ, hk, ite_eq_left, weight, Nat.add_assoc, pow_add]
  congr 3
  ring

set_option maxHeartbeats 1000000 in
private theorem abs_transform_univ_mul_le_one (t : ℝ) :
    Real.pi * ‖t‖ * ‖transform univ t‖ ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  let y (N : ℕ) : ℝ := (1 / 2 : ℝ)^N * (Real.pi * t)
  let P (N : ℕ) : ℝ := ∏ k ∈ Finset.range N, Real.cos (y (k + 1))
  have hCos (k : ℕ) : factor univ t k = (Real.cos (y (k + 1)) : ℂ) := by
    rw [factor_eq_cos]
    simp only [y, maskedWeight, Set.mem_univ, ite_eq_left, weight, pow_succ]
    congr 2
    ring
  have hP : Tendsto P atTop (𝓝 (transform univ t).re) := by
    have hlim := (Complex.continuous_re.tendsto _).comp (transform_tendsto_prod univ t)
    simp only [hCos, ← Complex.ofReal_prod] at hlim
    exact hlim
  have hSin (N : ℕ) : (2 : ℝ)^N * Real.sin (y N) * P N = Real.sin (Real.pi * t) := by
    induction N with
    | zero => simp [y, P]
    | succ N ih =>
      have hY : y N = 2 * y (N + 1) := by simp only [y, pow_succ]; ring
      rw [hY, Real.sin_two_mul] at ih
      change (2 : ℝ)^(N+1) * Real.sin (y (N+1)) *
        (∏ k ∈ Finset.range (N+1), Real.cos (y (k + 1))) = _
      rw [pow_succ, Finset.prod_range_succ]
      convert ih using 1
      ring
  have hY : Tendsto y atTop (𝓝[≠] 0) := by
    rw [nhdsWithin, tendsto_inf, tendsto_principal]
    refine ⟨?_, .of_forall fun n => ?_⟩
    · simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).mul_const (Real.pi * t)
    · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero Real.pi_ne_zero ht)
  have hSinLim : Tendsto (fun N => (2 : ℝ)^N * Real.sin (y N)) atTop (𝓝 (Real.pi * t)) := by
    have h := (Real.tendsto_sin_div_nhdsNE_zero.comp hY).const_mul (Real.pi * t)
    rw [mul_one] at h
    refine h.congr fun N => ?_
    change Real.pi * t * (Real.sin (y N) / y N) = _
    have hy : (2 : ℝ)^N * y N = Real.pi * t := by
      dsimp only [y]
      rw [← mul_assoc, ← mul_pow]
      ring_nf
    have hy0 : y N ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero Real.pi_ne_zero ht)
    calc
      _ = ((2 : ℝ)^N * Real.sin (y N)) * (y N / y N) := by rw [← hy]; ring
      _ = _ := by rw [div_self hy0, mul_one]
  have h := tendsto_nhds_unique (hSinLim.mul hP)
    ((tendsto_const_nhds (x := Real.sin (Real.pi * t))).congr fun n => (hSin n).symm)
  have hAbs := (congrArg abs h).le.trans (Real.abs_sin_le_one _)
  rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le] at hAbs
  have hNorm : ‖transform univ t‖ = |(transform univ t).re| := by
    have he := transform_eq_ofReal_re univ t
    calc
      _ = ‖((transform univ t).re : ℂ)‖ := congrArg norm he
      _ = _ := Complex.norm_real _
  simpa only [Real.norm_eq_abs, hNorm] using hAbs

private theorem norm_transform_tail_tendsto_zero (M : ℕ) :
    Tendsto (fun n : ℤ => ‖transform (Ici M) (n : ℝ)‖) cofinite (𝓝 0) := by
  have hNorm : Tendsto (fun n : ℤ => ‖(n : ℝ)‖) cofinite atTop :=
    tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c : ℝ := Real.pi * (1 / 2 : ℝ)^M
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [hNorm.eventually_gt_atTop (1 / (c * ε))] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), transform_tail_scale]
  have h := abs_transform_univ_mul_le_one ((n : ℝ) * (1 / 2 : ℝ)^M)
  rw [norm_mul, Real.norm_of_nonneg (show 0 ≤ (1 / 2 : ℝ)^M by positivity)] at h
  have hn' : 1 < ‖(n : ℝ)‖ * (c * ε) :=
    (div_lt_iff₀ (mul_pos hc hε)).mp hn
  by_contra! hBad
  have h₀ := mul_le_mul_of_nonneg_left hBad (mul_nonneg hc.le (norm_nonneg (n : ℝ)))
  have he : c * ‖(n : ℝ)‖ * ‖transform univ ((n : ℝ) * (1 / 2 : ℝ)^M)‖ ≤ 1 := by
    convert h using 1; simp only [c]; ring
  linarith [show c * ‖(n : ℝ)‖ * ε = ‖(n : ℝ)‖ * (c * ε) by ring]

private theorem transform_eq_prefix_mul_tail (A : Set ℕ) (M : ℕ) (t : ℝ) :
    transform A t = transform (A ∩ Iio M) t * transform (A ∩ Ici M) t := by
  have h : _root_.Disjoint (A ∩ Iio M) (A ∩ Ici M) :=
    Set.disjoint_left.mpr fun x ha hb => (show x < M from ha.2).not_ge (show M ≤ x from hb.2)
  have he : (A ∩ Iio M) ∪ (A ∩ Ici M) = A := by
    ext
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, ← and_or_left]
    simp only [or_iff_not_imp_left, not_lt, imp_self, and_true]
  rw [← transform_union_of_disjoint h, he]

private theorem norm_transform_le_tail (A : Set ℕ) (M : ℕ) (t : ℝ) :
    ‖transform A t‖ ≤ ‖transform (A ∩ Ici M) t‖ := by
  rw [transform_eq_prefix_mul_tail A M t, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_transform_le_one _ _)

private theorem norm_mul_le_norm_mul_add_errors {a b c d : ℂ} (ha : ‖c‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ ‖c * d‖ + ‖a - c‖ + ‖b - d‖ := by
  have he : a * b = c * d + (a - c) * b + c * (b - d) := by ring
  calc
    _ ≤ ‖c * d + (a - c) * b‖ + ‖c * (b - d)‖ := he ▸ norm_add_le _ _
    _ ≤ (‖c * d‖ + ‖(a - c) * b‖) + ‖c * (b - d)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by
      simp only [norm_mul]
      exact add_le_add (add_le_add le_rfl (mul_le_of_le_one_right (norm_nonneg _) hb))
        (mul_le_of_le_one_left (norm_nonneg _) ha)

set_option maxHeartbeats 1000000 in
/-- Mixed products of shifted Fourier coefficients of complementary masks
vanish at infinity. The error made by removing the shifts on the tails is
controlled by the sum of the remaining binary weights. -/
theorem transform_shifted_mul_compl_tendsto_zero (A : Set ℕ) (j k : ℤ) :
    Tendsto (fun n : ℤ => transform A ((n : ℝ) + j) * transform Aᶜ ((n : ℝ) + k)) cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hChoose : Tendsto (fun M : ℕ =>
      2 * Real.pi * (‖(j : ℝ)‖ + ‖(k : ℝ)‖) * ((1 / 2 : ℝ)^M / 2)) atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).div_const 2
        |>.const_mul (2 * Real.pi * (‖(j : ℝ)‖ + ‖(k : ℝ)‖)))
  obtain ⟨M, hM⟩ := (hChoose.eventually_lt_const (half_pos hε)).exists
  filter_upwards [(norm_transform_tail_tendsto_zero M).eventually_lt_const (half_pos hε)] with n hn
  rw [dist_zero_right, norm_mul]
  let S := A ∩ Ici M
  let T := Aᶜ ∩ Ici M
  have hD : _root_.Disjoint S T := Set.disjoint_left.mpr fun _ hs ht => ht.1 hs.1
  have hST : S ∪ T = Ici M := by
    ext x
    change (x ∈ A ∧ x ∈ Ici M) ∨ (x ∉ A ∧ x ∈ Ici M) ↔ x ∈ Ici M
    tauto
  have he : transform S (n : ℝ) * transform T (n : ℝ) = transform (Ici M) (n : ℝ) := by
    rw [← transform_union_of_disjoint hD, hST]
  have hBound (s : ℝ) (B : Set ℕ) (hB : B ⊆ Ici M) :
      ‖transform B ((n : ℝ) + s) - transform B (n : ℝ)‖ ≤
        2 * Real.pi * ‖s‖ * ((1 / 2 : ℝ)^M / 2) := norm_transform_add_sub_le hB n s
  calc
    _ ≤ ‖transform S ((n : ℝ) + j)‖ * ‖transform T ((n : ℝ) + k)‖ :=
      mul_le_mul (norm_transform_le_tail A M _) (norm_transform_le_tail Aᶜ M _)
        (norm_nonneg _) (norm_nonneg _)
    _ ≤ ‖transform (Ici M) (n : ℝ)‖ +
        ‖transform S ((n : ℝ) + j) - transform S (n : ℝ)‖ +
        ‖transform T ((n : ℝ) + k) - transform T (n : ℝ)‖ := by
      rw [← norm_mul, ← he]
      exact norm_mul_le_norm_mul_add_errors (norm_transform_le_one _ _) (norm_transform_le_one _ _)
    _ < ε := by
      have h₁ := hBound j S Set.inter_subset_right
      have h₂ := hBound k T Set.inter_subset_right
      have hSum : 2 * Real.pi * ‖(j : ℝ)‖ * ((1 / 2 : ℝ)^M / 2) +
          2 * Real.pi * ‖(k : ℝ)‖ * ((1 / 2 : ℝ)^M / 2) < ε / 2 := by
        convert hM using 1; ring
      linarith

private theorem norm_factor_le_one (A : Set ℕ) (t : ℝ) (k : ℕ) : ‖factor A t k‖ ≤ 1 := by
  rw [factor_eq_cos, Complex.norm_real]
  exact Real.abs_cos_le_one _

/-- One selected digit bounds the entire Fourier product. -/
theorem norm_transform_le_factor (A : Set ℕ) (t : ℝ) (k : ℕ) :
    ‖transform A t‖ ≤ ‖factor A t k‖ := by
  classical
  apply le_of_tendsto (transform_tendsto_prod A t).norm
  filter_upwards [eventually_gt_atTop k] with N hN
  have hk : k ∈ Finset.range N := Finset.mem_range.mpr hN
  rw [← Finset.insert_erase hk, Finset.prod_insert (Finset.notMem_erase _ _), norm_mul, norm_prod]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => norm_factor_le_one A t i))

private theorem twopow_mul_weight {r k : ℕ} (hk : k + 2 ≤ r) :
    (2 : ℝ)^r * weight k = ((2 : ℤ)^(r - (k+2)) : ℝ) := by
  rw [weight]
  norm_num only [Int.cast_ofNat]
  have he : (2 : ℝ)^r = (2 : ℝ)^(r - (k+2)) * (2 : ℝ)^(k+2) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [he, mul_assoc, ← mul_pow]
  norm_num

private theorem factor_shift_dyadic_of_small (A : Set ℕ) (t : ℝ) {r k : ℕ}
    (hk : k + 2 ≤ r) : factor A (t + (2 : ℝ)^r) k = factor A t k := by
  classical
  by_cases ha : k ∈ A
  · let m : ℤ := (2 : ℤ)^(r - (k+2))
    have hm : (2 : ℝ)^r * weight k = (m : ℝ) := by
      dsimp only [m]
      rw [Int.cast_pow]
      exact twopow_mul_weight hk
    have h₁ : cantorCharacter ((t + (2 : ℝ)^r) * weight k) = cantorCharacter (t * weight k) := by
      rw [add_mul, hm, cantorCharacter_add, cantorCharacter_int, mul_one]
    have h₂ : cantorCharacter (-((t + (2 : ℝ)^r) * weight k)) = cantorCharacter (-(t * weight k)) := by
      rw [add_mul, hm, neg_add_rev, cantorCharacter_add, ← Int.cast_neg, cantorCharacter_int, one_mul]
    simp only [factor, maskedWeight, ha, ite_eq_left, h₁, h₂]
  · rw [factor_of_notMem _ _ ha, factor_of_notMem _ _ ha]

/-- If a mask has a long gap, a large dyadic frequency acts almost
as the identity on every fixed shifted Fourier coefficient. -/
theorem norm_transform_shift_dyadic_sub_le (A : Set ℕ) (t : ℝ) (r M : ℕ)
    (hGap : ∀ k ∈ A, k < M → k + 2 ≤ r) :
    ‖transform A (t + (2 : ℝ)^r) - transform A t‖ ≤
      2 * Real.pi * (2 : ℝ)^r * ((1 / 2 : ℝ)^M / 2) := by
  classical
  let P := A ∩ Iio M
  let T := A ∩ Ici M
  have he : transform P (t + (2 : ℝ)^r) = transform P t := by
    apply tendsto_nhds_unique (transform_tendsto_prod P (t + (2 : ℝ)^r))
    refine (transform_tendsto_prod P t).congr fun N => ?_
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k ∈ P
    · exact (factor_shift_dyadic_of_small P t (hGap k hk.1 hk.2)).symm
    · rw [factor_of_notMem _ _ hk, factor_of_notMem _ _ hk]
  rw [transform_eq_prefix_mul_tail A M (t + (2 : ℝ)^r), transform_eq_prefix_mul_tail A M t]
  change ‖transform P (t + (2 : ℝ)^r) * transform T (t + (2 : ℝ)^r) -
    transform P t * transform T t‖ ≤ _
  rw [he, ← mul_sub, norm_mul]
  have hL := norm_transform_add_sub_le (A := T) Set.inter_subset_right t ((2 : ℝ)^r)
  rw [Real.norm_of_nonneg (show 0 ≤ (2 : ℝ)^r by positivity)] at hL
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_transform_le_one _ _)).trans hL

end Mixing.BinaryDigitSpectra
