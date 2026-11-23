/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! A finite Fourier bound from closed upper rectangles. The proof writes each
coordinate character as an integral over one threshold, expands the product,
and applies the rectangle bound inside the resulting integrals. -/

@[expose] public section

open Finset Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace VdC

noncomputable section
open Classical

private abbrev Interval := Icc (0 : ℝ) 1

private def intervalUniform : Measure Interval := Measure.comap Subtype.val volume

private theorem intervalUniform_map : intervalUniform.map (Subtype.val : Interval → ℝ) =
    volume.restrict (Icc (0 : ℝ) 1) :=
  map_comap_subtype_coe measurableSet_Icc volume

private instance : IsProbabilityMeasure intervalUniform := by
  constructor
  rw [intervalUniform, comap_subtype_coe_apply measurableSet_Icc, Set.image_univ,
    Subtype.range_coe, Real.volume_Icc]
  norm_num

private def cubeUniform (ι : Type) [Fintype ι] : Measure (ι → Interval) :=
  Measure.pi fun _ ↦ intervalUniform

private instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (cubeUniform ι) := by
  unfold cubeUniform
  infer_instance

private def upperRectangle {ι : Type} (s : Finset ι) (t : ι → Interval) : Set (ι → Interval) :=
  {x | ∀ i ∈ s, (x i : ℝ) ≤ t i}

private theorem upperRectangle_measurable {ι : Type} [Fintype ι] (s : Finset ι) (t : ι → Interval) :
    MeasurableSet (upperRectangle s t) := by
  classical
  have he : upperRectangle s t = ⋂ i ∈ s, {x : ι → Interval | (x i : ℝ) ≤ t i} := by
    ext x; simp [upperRectangle]
  rw [he]
  apply MeasurableSet.biInter s.countable_toSet
  intro i _
  exact measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply _)) measurable_const

private def upperKernel {ι : Type} [Fintype ι] (w : ι → Interval → ℂ)
    (x t : ι → Interval) : ℂ :=
  ∏ i, ((if (x i : ℝ) ≤ t i then w i (t i) else 0) + 1)

private theorem upperKernel_measurable {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (hw : ∀ i, Measurable (w i)) :
    Measurable (uncurry (upperKernel w)) := by
  unfold upperKernel uncurry
  apply Finset.measurable_prod
  intro i _
  apply Measurable.add ?_ measurable_const
  apply Measurable.ite ?_ ((hw i).comp ((measurable_pi_apply i).comp measurable_snd)) measurable_const
  exact measurableSet_le (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst))
    (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd))

private theorem upperKernel_norm_le {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i) (x t : ι → Interval) :
    ‖upperKernel w x t‖ ≤ ∏ i, (B i + 1) := by
  unfold upperKernel
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
  intro i _
  split
  · exact (norm_add_le _ _).trans (by simpa using add_le_add_right (hB i (t i)) 1)
  · simp only [zero_add, norm_one]
    linarith [(norm_nonneg _).trans (hB i (t i))]

private theorem upperKernel_expand {ι : Type} [Fintype ι] (w : ι → Interval → ℂ) (x t : ι → Interval) :
    upperKernel w x t = ∑ s : Finset ι,
      (if x ∈ upperRectangle s t then (1 : ℂ) else 0) * ∏ i ∈ s, w i (t i) := by
  classical
  unfold upperKernel
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_const_one, mul_one]
  by_cases h : x ∈ upperRectangle s t
  · rw [ite_eq_left h, one_mul]
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_left (h i hi)
  · rw [ite_eq_right h, zero_mul]
    have h' : ∃ i ∈ s, ¬ (x i : ℝ) ≤ t i := by
      change ¬ (∀ i ∈ s, _) at h
      push Not at h
      simpa only [not_le] using h
    obtain ⟨i, hi, hki⟩ := h'
    exact Finset.prod_eq_zero hi (ite_eq_right hki)

private theorem upperKernel_integral_expand {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (μ : Measure (ι → Interval)) [IsFiniteMeasure μ] (t : ι → Interval) :
    (∫ x, upperKernel w x t ∂μ) = ∑ s : Finset ι,
      Complex.ofReal (μ.real (upperRectangle s t)) * ∏ i ∈ s, w i (t i) := by
  classical
  let c (s : Finset ι) : ℂ := ∏ i ∈ s, w i (t i)
  have hintegral (s : Finset ι) : Integrable (fun x : ι → Interval ↦
      (if x ∈ upperRectangle s t then (1 : ℂ) else 0) * c s) μ := by
    have h : Integrable ((upperRectangle s t).indicator fun _ ↦ (1 : ℂ)) μ :=
      (integrable_const _).indicator (upperRectangle_measurable s t)
    simpa only [Set.indicator] using h.mul_const (c s)
  simp_rw [upperKernel_expand]
  rw [integral_finsetSum _ (fun s _ ↦ hintegral s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const]
  change (∫ x, (upperRectangle s t).indicator (fun _ ↦ (1 : ℂ)) x ∂μ) * c s = _
  rw [integral_indicator (upperRectangle_measurable s t), setIntegral_const, Complex.real_smul, mul_one]

private theorem upperKernel_integral_sub_bound {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i)
    (μ ν : Measure (ι → Interval)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (D : ℝ) (hD : 0 ≤ D) (t : ι → Interval)
    (hd : ∀ s, |μ.real (upperRectangle s t) - ν.real (upperRectangle s t)| ≤ D) :
    ‖(∫ x, upperKernel w x t ∂μ) - (∫ x, upperKernel w x t ∂ν)‖ ≤ D * ∏ i, (B i + 1) := by
  classical
  rw [upperKernel_integral_expand, upperKernel_integral_expand, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Fintype.prod_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  simp only [Finset.prod_const_one, mul_one, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, norm_prod]
  exact mul_le_mul (hd s) (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hB i _))
    (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hD

private theorem upperKernel_integrable_prod {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (hw : ∀ i, Measurable (w i))
    (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i) (μ ν : Measure (ι → Interval))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : Integrable (uncurry (upperKernel w)) (μ.prod ν) := by
  refine (integrable_const (∏ i, (B i + 1))).mono' (upperKernel_measurable w hw).aestronglyMeasurable ?_
  exact ae_of_all _ fun p ↦ upperKernel_norm_le w B hB p.1 p.2

private theorem product_test_bound_of_upper_rectangles {ι : Type} [Fintype ι]
    (w f : ι → Interval → ℂ) (hw : ∀ i, Measurable (w i))
    (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i)
    (hprimitive : ∀ i (x : Interval), (∫ t : Interval, ((if (x : ℝ) ≤ t then w i t else 0) + 1) ∂intervalUniform) = f i x)
    (μ ν : Measure (ι → Interval)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ s t, |μ.real (upperRectangle s t) - ν.real (upperRectangle s t)| ≤ D) :
    ‖(∫ x : ι → Interval, ∏ i, f i (x i) ∂μ) - (∫ x : ι → Interval, ∏ i, f i (x i) ∂ν)‖ ≤
      D * ∏ i, (B i + 1) := by
  let τ := cubeUniform ι
  have hI1 := upperKernel_integrable_prod w hw B hB μ τ
  have hI2 := upperKernel_integrable_prod w hw B hB ν τ
  have hpoint (x : ι → Interval) : (∫ t, upperKernel w x t ∂τ) = ∏ i, f i (x i) := by
    unfold upperKernel τ cubeUniform
    rw [integral_fintype_prod_eq_prod (fun i (t : Interval) ↦
      (if (x i : ℝ) ≤ t then w i t else 0) + 1)]
    simp_rw [hprimitive]
  simp_rw [← hpoint]
  have hI1' : Integrable (fun t ↦ ∫ x, upperKernel w x t ∂μ) τ := hI1.integral_prod_right
  have hI2' : Integrable (fun t ↦ ∫ x, upperKernel w x t ∂ν) τ := hI2.integral_prod_right
  rw [integral_integral_swap hI1, integral_integral_swap hI2, ← integral_sub hI1' hI2']
  simpa using norm_integral_le_of_norm_le_const (μ := τ) (ae_of_all τ fun t ↦
    upperKernel_integral_sub_bound w B hB μ ν D hD t (fun s ↦ hd s t))

private def rate (m : ℤ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)

private def realCharacter (m : ℤ) (t : ℝ) : ℂ := Complex.exp (rate m * (t : ℂ))

private theorem realCharacter_eq_fourier (m : ℤ) (t : ℝ) :
    realCharacter m t = _root_.fourier m (t : UnitAddCircle) := by
  rw [fourier_coe_apply]
  simp [realCharacter, rate]

private theorem realCharacter_zero (m : ℤ) : realCharacter m 0 = 1 := by simp [realCharacter]

private theorem realCharacter_one (m : ℤ) : realCharacter m 1 = 1 := by
  rw [realCharacter_eq_fourier, AddCircle.coe_period, fourier_eval_zero]

private def weight (m : ℤ) (t : ℝ) : ℂ := -(rate m) * realCharacter m t

private theorem continuous_weight (m : ℤ) : Continuous (weight m) := by
  unfold weight realCharacter
  fun_prop

private theorem norm_weight (m : ℤ) (t : ℝ) : ‖weight m t‖ = ‖rate m‖ := by
  have hn : ‖realCharacter m t‖ = 1 := by
    rw [realCharacter_eq_fourier, fourier_apply, Circle.norm_coe]
  rw [weight, norm_mul, norm_neg, hn, mul_one]

private theorem norm_rate (m : ℤ) : ‖rate m‖ = 2 * Real.pi * (m.natAbs : ℝ) := by
  simp [rate, abs_of_nonneg Real.pi_pos.le, Complex.norm_intCast, Int.cast_abs]

private theorem integral_intervalUniform (g : ℝ → ℂ) (hg : Measurable g) :
    (∫ t : Interval, g t ∂intervalUniform) = ∫ t in (0 : ℝ)..1, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← intervalUniform_map, integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]

private theorem weight_threshold_integral (m : ℤ) (x : Interval) :
    (∫ t : Interval, ((if (x : ℝ) ≤ t then weight m t else 0) + 1) ∂intervalUniform) = realCharacter m x := by
  let g := (Ici (x : ℝ)).indicator (weight m)
  have hg : Measurable g := (continuous_weight m).measurable.indicator measurableSet_Ici
  have hg_int : Integrable (fun t : Interval ↦ g t) intervalUniform := by
    refine (integrable_const ‖rate m‖).mono' (hg.comp measurable_subtype_coe).aestronglyMeasurable
      (ae_of_all _ fun t ↦ ?_)
    by_cases h : (x : ℝ) ≤ t <;> simp [g, h, norm_weight]
  change (∫ t : Interval, g t + 1 ∂intervalUniform) = _
  rw [integral_add hg_int (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_intervalUniform g hg, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have he : Ici (x : ℝ) ∩ Icc (0 : ℝ) 1 = Icc (x : ℝ) 1 := by
    ext t; simp only [mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, x.property.1.trans h.1, h.2⟩⟩
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le x.property.2]
  by_cases h : rate m = 0
  · simp [weight, realCharacter, h]
  have hw : (∫ t in (x : ℝ)..1, weight m t) = -(rate m) *
      ((realCharacter m 1 - realCharacter m x) / rate m) := by
    unfold weight realCharacter
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex h]
  rw [hw, realCharacter_one]
  field_simp
  ring

private theorem integral_realCharacter_zero {m : ℤ} (hm : m ≠ 0) :
    (∫ t : Interval, realCharacter m t ∂intervalUniform) = 0 := by
  rw [integral_intervalUniform _ (by unfold realCharacter; fun_prop)]
  have hr : rate m ≠ 0 := by simp [rate, Real.pi_ne_zero, Complex.I_ne_zero, hm]
  change (∫ t in (0 : ℝ)..1, Complex.exp (rate m * t)) = 0
  rw [integral_exp_mul_complex hr]
  change (realCharacter m 1 - realCharacter m 0) / rate m = 0
  simp [realCharacter_one, realCharacter_zero]

private theorem integral_productCharacter_zero {ι : Type} [Fintype ι]
    {m : ι → ℤ} (hm : m ≠ 0) : (∫ x : ι → Interval, ∏ i, realCharacter (m i) (x i) ∂cubeUniform ι) = 0 := by
  have h : ∃ i, m i ≠ 0 := by
    by_contra! hall
    exact hm (funext hall)
  obtain ⟨i, hi⟩ := h
  unfold cubeUniform
  rw [integral_fintype_prod_eq_prod (fun i (x : Interval) ↦ realCharacter (m i) x)]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (integral_realCharacter_zero hi)

private theorem upperRectangle_uniform_measure {ι : Type} [Fintype ι] (s : Finset ι) (t : ι → Interval) :
    (cubeUniform ι).real (upperRectangle s t) = ∏ i ∈ s, ((t i : Interval) : ℝ) := by
  classical
  have huniform (a : Interval) : intervalUniform {x : Interval | (x : ℝ) ≤ a} = ENNReal.ofReal a := by
    rw [intervalUniform, comap_subtype_coe_apply measurableSet_Icc]
    have he : (Subtype.val '' {x : Interval | (x : ℝ) ≤ a}) = Icc (0 : ℝ) (a : ℝ) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property.1, hy⟩
      · intro hz
        exact ⟨⟨z, ⟨hz.1, hz.2.trans a.property.2⟩⟩, hz.2, rfl⟩
    rw [he, Real.volume_Icc, sub_zero]
  have hrectangle : upperRectangle s t = univ.pi (fun i ↦ if i ∈ s then
      {x : Interval | (x : ℝ) ≤ t i} else univ) := by
    ext x
    simp [upperRectangle]
  rw [hrectangle, measureReal_def, cubeUniform, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ i, (intervalUniform (if i ∈ s then {x : Interval | (x : ℝ) ≤ t i} else univ)).toReal) = _
  have ht (i : ι) : 0 ≤ ((t i : Interval) : ℝ) := (t i).property.1
  simp only [apply_ite intervalUniform, huniform, measure_univ, apply_ite ENNReal.toReal,
    ENNReal.toReal_ofReal (ht _), ENNReal.toReal_one, Finset.prod_ite_mem, Finset.univ_inter]

private def empiricalMeasure {ι : Type} (u : ℕ → ι → Interval) (N : ℕ) : Measure (ι → Interval) :=
  ENNReal.ofReal ((N : ℝ)⁻¹) • ∑ j ∈ Finset.range N, Measure.dirac (u j)

private instance {ι : Type} (u : ℕ → ι → Interval) (N : ℕ) : IsFiniteMeasure (empiricalMeasure u N) := by
  constructor
  rw [empiricalMeasure, smul_apply, sum_apply, smul_eq_mul]
  simp [ENNReal.mul_lt_top]

private theorem integral_empiricalMeasure {ι : Type} [Fintype ι] (u : ℕ → ι → Interval) (N : ℕ)
    (f : (ι → Interval) → ℂ) :
    (∫ x, f x ∂empiricalMeasure u N) = cesaro (fun n ↦ f (u n)) N := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ ↦ integrable_dirac (eNorm_lt_top)), cesaro]
  simp only [integral_dirac, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _)),
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

private theorem empiricalMeasure_real_apply {ι : Type} [Fintype ι] (u : ℕ → ι → Interval) (N : ℕ)
    {s : Set (ι → Interval)} (hs : MeasurableSet s) :
    (empiricalMeasure u N).real s = (((Finset.range N).filter fun j ↦ u j ∈ s).card : ℝ) / N := by
  classical
  have h := integral_empiricalMeasure u N (s.indicator fun _ ↦ (1 : ℂ))
  rw [integral_indicator hs, setIntegral_const, Complex.real_smul, mul_one] at h
  apply_fun Complex.re at h
  simpa [cesaro, Set.indicator, ← Finset.sum_filter, Complex.ofReal_div,
    Complex.ofReal_natCast] using h

/-- The maximum absolute coordinate of an integer frequency. -/
def maxFourierFrequency {d : ℕ} (m : Fin d → ℤ) : ℕ :=
  (univ : Finset (Fin d)).sup fun i ↦ (m i).natAbs

def fourierDiscrepancyConstant {d : ℕ} (m : Fin d → ℤ) : ℝ :=
  (4 * Real.pi * (maxFourierFrequency m : ℝ)) ^ d

theorem fourierDiscrepancyConstant_nonneg {d : ℕ} (m : Fin d → ℤ) :
    0 ≤ fourierDiscrepancyConstant m := by unfold fourierDiscrepancyConstant; positivity

/-- The anchored-box discrepancy controls the finite Fourier coefficient at every
nonzero frequency, with the manuscript's constant `(4πM)^d`. -/
theorem finite_fourier_bound_of_upper_rectangles {d : ℕ} (m : Fin d → ℤ) (hm : m ≠ 0)
    (u : ℕ → Fin d → Icc (0 : ℝ) 1) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ (s : Finset (Fin d)) (t : Fin d → Icc (0 : ℝ) 1),
      |(((range N).filter fun j ↦ ∀ i ∈ s, (u j i : ℝ) ≤ t i).card : ℝ) / N -
        ∏ i ∈ s, (t i : ℝ)| ≤ D) :
    ‖cesaro (fun j ↦ ∏ i, _root_.fourier (m i) ((u j i : ℝ) : UnitAddCircle)) N‖ ≤
      fourierDiscrepancyConstant m * D := by
  let M : ℕ := maxFourierFrequency m
  have hMle (i : Fin d) : (m i).natAbs ≤ M :=
    Finset.le_sup (s := univ) (f := fun j : Fin d ↦ (m j).natAbs) (Finset.mem_univ i)
  have hM₀ : (1 : ℝ) ≤ M := by
    have hnz : ∃ i, m i ≠ 0 := by
      by_contra! he
      exact hm (funext he)
    obtain ⟨i, hi⟩ := hnz
    have hpos : 0 < (m i).natAbs := by simpa using hi
    exact_mod_cast (hpos.trans_le (hMle i))
  have hcomp : (∏ i, (‖rate (m i)‖ + 1)) ≤ (4 * Real.pi * (M : ℝ)) ^ d := by
    calc
      _ ≤ ∏ _ : Fin d, (4 * Real.pi * (M : ℝ)) := by
        apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
        intro i _
        have hcast : ((m i).natAbs : ℝ) ≤ M := by exact_mod_cast hMle i
        rw [norm_rate]
        calc
          _ ≤ 2 * Real.pi * (M : ℝ) + 1 := by gcongr
          _ ≤ _ := by
            have hn : 2 * Real.pi ≤ 2 * Real.pi * (M : ℝ) :=
              (mul_one _).symm.le.trans (mul_le_mul_of_nonneg_left hM₀ (by positivity))
            linarith [Real.two_le_pi]
      _ = _ := by simp
  have hb := product_test_bound_of_upper_rectangles
    (fun i t ↦ weight (m i) t) (fun i t ↦ realCharacter (m i) t)
    (fun i ↦ (continuous_weight (m i)).measurable.comp measurable_subtype_coe)
    (fun i ↦ ‖rate (m i)‖) (fun i t ↦ (norm_weight (m i) t).le) (fun i ↦ weight_threshold_integral (m i))
    (empiricalMeasure u N) (cubeUniform (Fin d)) D hD (fun s t ↦ by
      rw [empiricalMeasure_real_apply u N (upperRectangle_measurable s t), upperRectangle_uniform_measure]
      have heq : ((range N).filter fun j ↦ u j ∈ upperRectangle s t) =
          (range N).filter (fun j ↦ ∀ i ∈ s, (u j i : ℝ) ≤ t i) := by
        apply Finset.filter_congr
        intro j _
        rfl
      rw [heq]
      exact hd s t)
  rw [integral_empiricalMeasure, integral_productCharacter_zero hm, sub_zero] at hb
  calc
    _ ≤ (∏ i, (‖rate (m i)‖ + 1)) * D := by simpa only [realCharacter_eq_fourier, mul_comm D] using hb
    _ ≤ _ := mul_le_mul_of_nonneg_right hcomp hD

end
end VdC
