/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Fourier transform of the uniform base-four Cantor measure -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace Mixing

/-- A fair Bernoulli law on the two base-four digits. -/
noncomputable def cantorDigitLaw : Measure Bool :=
  bernoulliMeasure false true ⟨1 / 2, by norm_num, by norm_num⟩

instance : IsProbabilityMeasure cantorDigitLaw := by
  unfold cantorDigitLaw
  infer_instance

/-- The law of the independent digits of a point in the uniform Cantor distribution. -/
noncomputable def cantorDigitProduct : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ ↦ cantorDigitLaw

instance : IsProbabilityMeasure cantorDigitProduct := by
  unfold cantorDigitProduct
  infer_instance

/-- The contribution of the digit at position `k+1`. -/
noncomputable def cantorWeight (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ (k + 1)

/-- Partial base-four expansion with digits 0 and 1. -/
noncomputable def cantorPrefix (N : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ k ∈ Finset.range N, if ω k then cantorWeight k else 0

/-- Base-four expansion with digits 0 and 1. -/
noncomputable def cantorValue (ω : ℕ → Bool) : ℝ :=
  ∑' k, if ω k then cantorWeight k else 0

private theorem cantorWeight_summable : Summable cantorWeight := by
  have h : Summable (fun k : ℕ ↦ (1 / 4 : ℝ)^k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  change Summable (fun k : ℕ ↦ (1 / 4 : ℝ)^(k + 1))
  simpa only [pow_succ] using h.mul_right (1 / 4)

private theorem cantorValue_summable (ω : ℕ → Bool) :
    Summable (fun k ↦ if ω k then cantorWeight k else 0) := by
  refine cantorWeight_summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_)
  · split
    · unfold cantorWeight
      positivity
    · exact le_rfl
  · split
    · exact le_rfl
    · unfold cantorWeight
      positivity

theorem cantorPrefix_tendsto (ω : ℕ → Bool) :
    Tendsto (fun N ↦ cantorPrefix N ω) atTop (𝓝 (cantorValue ω)) :=
  (cantorValue_summable ω).hasSum.tendsto_sum_nat

private theorem cantorPrefix_measurable (N : ℕ) : Measurable (cantorPrefix N) := by
  unfold cantorPrefix
  exact Finset.measurable_fun_sum _ (fun k _ ↦
    (Measurable.of_discrete (f := fun d : Bool ↦ if d then cantorWeight k else 0)).comp
      (measurable_pi_apply k))

theorem cantorValue_measurable : Measurable cantorValue :=
  measurable_of_tendsto_metrizable cantorPrefix_measurable
    (tendsto_pi_nhds.mpr cantorPrefix_tendsto)

/-- The pushforward of fair independent digits under their base-four expansion. -/
noncomputable def cantorMeasure : Measure ℝ := Measure.map cantorValue cantorDigitProduct

instance : IsProbabilityMeasure cantorMeasure :=
  (Measure.isProbabilityMeasure_map_iff cantorValue_measurable.aemeasurable).mpr inferInstance

theorem cantorValue_mem_Icc (ω : ℕ → Bool) : cantorValue ω ∈ Set.Icc 0 (1 / 3) := by
  have hw (k : ℕ) : 0 ≤ cantorWeight k := by unfold cantorWeight; positivity
  refine ⟨tsum_nonneg (fun k ↦ by split <;> simp [hw]), ?_⟩
  calc
    cantorValue ω ≤ ∑' k, cantorWeight k :=
      (cantorValue_summable ω).tsum_le_tsum (fun k ↦ by split <;> simp [hw])
        cantorWeight_summable
    _ = 1 / 3 := by
      simp_rw [cantorWeight, pow_succ]
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1 / 4 : ℝ))
        (by norm_num)]
      norm_num

theorem cantorMeasure_ae_mem_Icc : ∀ᵐ x ∂cantorMeasure, x ∈ Set.Icc 0 (1 / 3) := by
  exact (ae_map_iff cantorValue_measurable.aemeasurable measurableSet_Icc).mpr
    (.of_forall cantorValue_mem_Icc)

/-- The negative-sign Fourier character, as a function of its real argument. -/
noncomputable def cantorCharacter (r : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-2 * Real.pi * r : ℝ) : ℂ))

@[fun_prop]
theorem cantorCharacter_continuous : Continuous cantorCharacter := by
  unfold cantorCharacter
  fun_prop

@[simp] theorem cantorCharacter_zero : cantorCharacter 0 = 1 := by
  simp [cantorCharacter]

theorem cantorCharacter_add (t s : ℝ) :
    cantorCharacter (t + s) = cantorCharacter t * cantorCharacter s := by
  unfold cantorCharacter
  rw [mul_add, Complex.ofReal_add, mul_add, Complex.exp_add]

@[simp] theorem cantorCharacter_norm (t : ℝ) : ‖cantorCharacter t‖ = 1 := by
  simp [cantorCharacter, Complex.norm_exp, Complex.mul_re]

@[simp] theorem cantorCharacter_int (n : ℤ) : cantorCharacter (n : ℝ) = 1 := by
  unfold cantorCharacter
  rw [← Complex.exp_int_mul_two_pi_mul_I (-n)]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_intCast,
    Int.cast_neg]
  ring

/-- Fourier transform at a real frequency, agreeing with the paper's transform at integers. -/
noncomputable def cantorFourier (t : ℝ) : ℂ :=
  ∫ x, cantorCharacter (t * x) ∂cantorMeasure

/-- One factor in the infinite Fourier product. -/
noncomputable def cantorFourierFactor (t : ℝ) (k : ℕ) : ℂ :=
  (1 + cantorCharacter (t * cantorWeight k)) / 2

private theorem cantorCharacter_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    cantorCharacter (∑ j ∈ s, f j) = ∏ j ∈ s, cantorCharacter (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, cantorCharacter_add, ih]

private theorem cantorPrefix_integral (t : ℝ) (N : ℕ) :
    (∫ ω, cantorCharacter (t * cantorPrefix N ω) ∂cantorDigitProduct) =
      ∏ k ∈ Finset.range N, cantorFourierFactor t k := by
  classical
  let s := Finset.range N
  let f (k : s) (b : Bool) := cantorCharacter (t * (if b then cantorWeight k else 0))
  let g (ω : s → Bool) := ∏ k : s, f k (ω k)
  have hg : Measurable g :=
    Finset.measurable_fun_prod _ (fun k _ ↦
      (Measurable.of_discrete (f := f k)).comp (measurable_pi_apply k))
  have hω (ω : ℕ → Bool) : cantorCharacter (t * cantorPrefix N ω) = g (s.restrict ω) := by
    unfold cantorPrefix
    rw [Finset.mul_sum, cantorCharacter_sum]
    exact (Finset.prod_attach s
      (fun k ↦ cantorCharacter (t * (if ω k then cantorWeight k else 0)))).symm
  simp_rw [hω]
  unfold cantorDigitProduct
  rw [MeasureTheory.integral_restrict_infinitePi _ hg.aestronglyMeasurable]
  change (∫ ω : s → Bool, ∏ k : s, f k (ω k) ∂Measure.pi (fun _ : s ↦ cantorDigitLaw)) = _
  rw [integral_fintype_prod_eq_prod]
  conv_rhs => rw [← Finset.prod_attach s]
  apply Finset.prod_congr rfl
  intro k _
  unfold f cantorDigitLaw cantorFourierFactor
  rw [integral_bernoulliMeasure]
  norm_num [Complex.real_smul]
  ring

/-- The finite Fourier products converge to the integral for the distribution. -/
theorem cantorFourier_tendsto_prod (t : ℝ) :
    Tendsto (fun N ↦ ∏ k ∈ Finset.range N, cantorFourierFactor t k)
      atTop (𝓝 (cantorFourier t)) := by
  have hmeas : Measurable (fun x : ℝ ↦ cantorCharacter (t * x)) := by fun_prop
  rw [cantorFourier, cantorMeasure,
    integral_map cantorValue_measurable.aemeasurable hmeas.aestronglyMeasurable]
  simp_rw [← cantorPrefix_integral t]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) ?_
    (integrable_const _) (fun _ ↦ .of_forall fun _ ↦ by simp) (.of_forall fun ω ↦ ?_)
  · intro N
    exact (hmeas.comp (cantorPrefix_measurable N)).aestronglyMeasurable
  · exact cantorCharacter_continuous.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (cantorPrefix_tendsto ω))

theorem cantorFourier_continuous : Continuous cantorFourier := by
  rw [continuous_iff_continuousAt]
  intro t
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    (.of_forall fun u ↦ ?_) (.of_forall fun _ ↦ .of_forall fun _ ↦ by simp)
    (integrable_const _) (.of_forall fun x ↦ ?_)
  · exact (show Measurable (fun x : ℝ ↦ cantorCharacter (u * x)) by fun_prop).aestronglyMeasurable
  · exact cantorCharacter_continuous.continuousAt.tendsto.comp
      (tendsto_id.mul tendsto_const_nhds)


@[simp] theorem cantorFourier_zero : cantorFourier 0 = 1 := by
  simp [cantorFourier]

private theorem cantorFourierFactor_dev_summable (t : ℝ) :
    Summable (fun k ↦ ‖cantorFourierFactor t k - 1‖) := by
  refine (cantorWeight_summable.mul_left (Real.pi * ‖t‖)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun k ↦ ?_
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * Real.pi * (t * cantorWeight k))
  change ‖cantorCharacter (t * cantorWeight k) - 1‖ ≤ _ at h
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (show 0 ≤ cantorWeight k by unfold cantorWeight; positivity)] at h
  unfold cantorFourierFactor
  rw [show (1 + cantorCharacter (t * cantorWeight k)) / 2 - 1 =
    (cantorCharacter (t * cantorWeight k) - 1) / 2 by ring, norm_div]
  norm_num [Complex.norm_ofNat] at h ⊢
  nlinarith

private theorem cantorFourierFactor_multipliable (t : ℝ) :
    Multipliable (cantorFourierFactor t) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (cantorFourierFactor_dev_summable t)

/-- Equation (11). The Fourier transform is the convergent product of the digit averages. -/
theorem cantorFourier_hasProd (t : ℝ) : HasProd (cantorFourierFactor t) (cantorFourier t) :=
  ((cantorFourierFactor_multipliable t).hasProd_iff_tendsto_nat).mpr
    (cantorFourier_tendsto_prod t)

private theorem cantorFourier_split (t : ℝ) (N : ℕ) :
    cantorFourier t =
      (∏ k ∈ Finset.range N, cantorFourierFactor t k) * cantorFourier (t * (1 / 4 : ℝ)^N) := by
  have hshift (k : ℕ) :
      cantorFourierFactor t (N + k) = cantorFourierFactor (t * (1 / 4 : ℝ)^N) k := by
    unfold cantorFourierFactor cantorWeight
    rw [show N + k + 1 = N + (k + 1) by omega, pow_add, mul_assoc]
  have h₁ := (cantorFourier_tendsto_prod t).comp (tendsto_add_atTop_nat N)
  have h₂ := (tendsto_const_nhds (x := ∏ k ∈ Finset.range N, cantorFourierFactor t k)).mul
    (cantorFourier_tendsto_prod (t * (1 / 4 : ℝ)^N))
  refine tendsto_nhds_unique h₁ (h₂.congr fun k ↦ ?_)
  change (∏ i ∈ Finset.range N, cantorFourierFactor t i) *
      (∏ i ∈ Finset.range k, cantorFourierFactor (t * (1 / 4 : ℝ)^N) i) =
    ∏ i ∈ Finset.range (k + N), cantorFourierFactor t i
  rw [Nat.add_comm k N, Finset.prod_range_add]
  simp_rw [hshift]

private theorem cantorFourier_base_four_split (m n : ℤ) (N : ℕ) :
    cantorFourier ((m : ℝ) * 4^N + n) =
      (∏ k ∈ Finset.range N, cantorFourierFactor n k) *
        cantorFourier ((m : ℝ) + n * (1 / 4 : ℝ)^N) := by
  rw [cantorFourier_split ((m : ℝ) * 4^N + n) N]
  have htail : ((m : ℝ) * 4^N + n) * (1 / 4 : ℝ)^N = m + n * (1 / 4 : ℝ)^N := by
    rw [add_mul, one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  rw [htail]
  congr 1
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  have hpow : (4 : ℝ)^N = (4 : ℝ)^(N - (k + 1)) * (4 : ℝ)^(k + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by have := Finset.mem_range.mp hk; omega)]
  have hweight : (4 : ℝ)^N * cantorWeight k = (4 : ℝ)^(N - (k + 1)) := by
    rw [hpow, cantorWeight, one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have harg : ((m : ℝ) * 4^N + n) * cantorWeight k =
      ((m * (4 : ℤ)^(N - (k + 1)) : ℤ) : ℝ) + n * cantorWeight k := by
    push_cast
    rw [add_mul, mul_assoc, hweight]
  unfold cantorFourierFactor
  rw [harg, cantorCharacter_add, cantorCharacter_int, one_mul]

/-- Multiplication of an integer frequency by four preserves the Fourier coefficient. -/
theorem cantorFourier_four_mul (m : ℤ) :
    cantorFourier (4 * (m : ℝ)) = cantorFourier m := by
  simpa [mul_comm (m : ℝ) 4, cantorFourierFactor] using cantorFourier_base_four_split m 0 1

/-- The two-block limit for the digit expansions, used in Examples 5 and 6. -/
theorem cantorFourier_tendsto_four_pow_add (m n : ℤ) :
    Tendsto (fun j : ℕ ↦ cantorFourier ((m * (4 : ℤ)^j + n : ℤ) : ℝ))
      atTop (𝓝 (cantorFourier n * cantorFourier m)) := by
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    cantorFourier_base_four_split]
  have hzero : Tendsto (fun j : ℕ ↦ (1 / 4 : ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have harg : Tendsto (fun j : ℕ ↦ (m : ℝ) + n * (1 / 4 : ℝ)^j) atTop (𝓝 (m : ℝ)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (x := (m : ℝ))).add ((tendsto_const_nhds (x := (n : ℝ))).mul hzero)
  exact (cantorFourier_tendsto_prod n).mul
    (cantorFourier_continuous.continuousAt.tendsto.comp harg)

private theorem cantorCharacter_eq_neg_one_iff (t : ℝ) :
    cantorCharacter t = -1 ↔ ∃ b : ℤ, t = (b : ℝ) + 1 / 2 := by
  rw [cantorCharacter, ← Complex.exp_pi_mul_I, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a - 1, ?_⟩
    have him := congrArg Complex.im ha
    simp [Complex.mul_im, Complex.mul_re] at him
    apply mul_left_cancel₀ Real.pi_ne_zero
    push_cast
    linear_combination -(1 / 2 : ℝ) * him
  · rintro ⟨b, rfl⟩
    refine ⟨-b - 1, ?_⟩
    push_cast
    ring

private theorem cantorFourierFactor_zero_iff (n : ℤ) (k : ℕ) :
    cantorFourierFactor n k = 0 ↔ ∃ b : ℤ, n = (4 : ℤ)^k * (4 * b + 2) := by
  have hcancel (b : ℤ) : (((4 : ℤ)^k * (4 * b + 2) : ℤ) : ℝ) * cantorWeight k =
      (b : ℝ) + 1 / 2 := by
    push_cast
    rw [cantorWeight, one_div, inv_pow, pow_succ]
    field_simp
    ring
  have hw : cantorWeight k ≠ 0 := by unfold cantorWeight; positivity
  have hadd (c : ℂ) : 1 + c = 0 ↔ c = -1 := by
    rw [add_comm, eq_neg_iff_add_eq_zero]
  rw [cantorFourierFactor, div_eq_zero_iff, or_iff_left (by norm_num), hadd,
    cantorCharacter_eq_neg_one_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by exact_mod_cast mul_right_cancel₀ hw (hb.trans (hcancel b).symm)⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, hcancel b⟩

/-- The base-four zero criterion. The first nonzero digit corresponds to the odd multiple of two
remaining after removing powers of four. This form works directly with signed frequencies. -/
theorem cantorFourier_zero_iff (n : ℤ) :
    cantorFourier n = 0 ↔ ∃ k : ℕ, ∃ b : ℤ, n = (4 : ℤ)^k * (4 * b + 2) := by
  constructor
  · intro hzero
    by_contra h
    have hnonzero (k : ℕ) : cantorFourierFactor n k ≠ 0 :=
      fun hk ↦ h ⟨k, (cantorFourierFactor_zero_iff n k).mp hk⟩
    have htprod : (∏' k, cantorFourierFactor n k) ≠ 0 := by
      simpa only [add_sub_cancel] using
        tprod_one_add_ne_zero_of_summable (f := fun k ↦ cantorFourierFactor n k - 1)
          (by simpa only [add_sub_cancel] using hnonzero) (cantorFourierFactor_dev_summable n)
    exact htprod ((cantorFourier_hasProd n).tprod_eq.trans hzero)
  · rintro ⟨k, b, hb⟩
    have hk := (cantorFourierFactor_zero_iff n k).mpr ⟨b, hb⟩
    have hEventually : ∀ᶠ N : ℕ in atTop, (∏ j ∈ Finset.range N, cantorFourierFactor n j) = 0 :=
      (eventually_gt_atTop k).mono fun N hN ↦ Finset.prod_eq_zero (Finset.mem_range.mpr hN) hk
    exact tendsto_nhds_unique (cantorFourier_tendsto_prod n)
      (tendsto_const_nhds.congr' (hEventually.mono fun _ h ↦ h.symm))


theorem cantorFourier_eq_zero_mod_four_two (b : ℤ) :
    cantorFourier ((4 * b + 2 : ℤ) : ℝ) = 0 :=
  (cantorFourier_zero_iff _).mpr ⟨0, b, by simp⟩

theorem cantorFourier_ne_zero_of_odd {n : ℤ} (hn : Odd n) :
    cantorFourier n ≠ 0 := by
  intro hz
  obtain ⟨k, b, hb⟩ := (cantorFourier_zero_iff n).mp hz
  obtain ⟨a, ha⟩ := hn
  have he : n = 2 * ((4 : ℤ)^k * (2 * b + 1)) := by
    rw [hb]
    ring
  omega

theorem cantorFourier_neg_eq_zero_iff (n : ℤ) :
    cantorFourier ((-n : ℤ) : ℝ) = 0 ↔ cantorFourier n = 0 := by
  simp only [cantorFourier_zero_iff]
  constructor
  · rintro ⟨k, b, hb⟩
    refine ⟨k, -b - 1, ?_⟩
    linear_combination -hb
  · rintro ⟨k, b, hb⟩
    refine ⟨k, -b - 1, ?_⟩
    linear_combination -hb

end Mixing
