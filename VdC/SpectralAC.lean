/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Spectrum
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Absolute continuity from square summability -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- A finite positive absolutely continuous measure has a nonnegative L¹
Radon–Nikodym density. -/
theorem exists_integrable_density (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (hμ : μ ≪ circleHaar) :
    ∃ g : UnitAddCircle → ℝ, Integrable g circleHaar ∧ (∀ x, 0 ≤ g x) ∧
      μ = circleHaar.withDensity (fun x => ENNReal.ofReal (g x)) := by
  let f := μ.rnDeriv circleHaar
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have heq : circleHaar.withDensity f = μ := Measure.withDensity_rnDeriv_eq _ _ hμ
  have hfin : (∫⁻ x, f x ∂circleHaar) ≠ ∞ := by
    have he := congrArg (fun ν : Measure UnitAddCircle => ν Set.univ) heq
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
    exact he ▸ measure_ne_top μ Set.univ
  refine ⟨fun x => (f x).toReal, integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfin,
    fun _ => ENNReal.toReal_nonneg, ?_⟩
  rw [← heq]
  symm
  apply withDensity_congr_ae
  refine ofReal_toReal_ae_eq ?_
  exact ae_lt_top hf hfin

private theorem positiveDensity_finite {g : UnitAddCircle → ℝ}
    (hg : Integrable g circleHaar) :
    IsFiniteMeasure (circleHaar.withDensity (fun x => ENNReal.ofReal (g x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := hg.real_toNNReal.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => NNReal.coe_nonneg _))] at h
  simpa using h

theorem measureFourier_withDensity_ofReal {g : UnitAddCircle → ℝ}
    (hg : Integrable g circleHaar) (n : ℤ) :
    measureFourier (circleHaar.withDensity (fun x => ENNReal.ofReal (g x))) n =
      ∫ x, fourier (-n) x * (↑((g x).toNNReal : ℝ) : ℂ) ∂circleHaar := by
  have hm : AEMeasurable (fun x => (g x).toNNReal) circleHaar :=
    continuous_real_toNNReal.measurable.comp_aemeasurable hg.aemeasurable
  unfold measureFourier
  change (∫ x, fourier (-n) x ∂circleHaar.withDensity (fun x => ((g x).toNNReal : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul₀ hm]
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm _ _

private theorem fourier_translate_integrable {f : UnitAddCircle → ℂ}
    (hf : Integrable f circleHaar) (n : ℤ) :
    Integrable (fun x => fourier n x * f x) circleHaar :=
  hf.fourier_smul n

private theorem fourier_real_part_of_density {g : UnitAddCircle → ℂ}
    (hg : Integrable g circleHaar) (μ : Measure UnitAddCircle)
    (hG : ∀ n, (∫ x, fourier (-n) x * g x ∂circleHaar) = measureFourier μ n) (n : ℤ) :
    (∫ x, fourier (-n) x * (↑(g x).re : ℂ) ∂circleHaar) = measureFourier μ n := by
  have h1 := fourier_translate_integrable hg (-n)
  have hconj : Integrable (fun x => conj (g x)) circleHaar :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hg
  have h2 := fourier_translate_integrable hconj (-n)
  have hG2 : (∫ x, fourier (-n) x * conj (g x) ∂circleHaar) = measureFourier μ n := by
    have hc (x : UnitAddCircle) : fourier (-n) x * conj (g x) = conj (fourier n x * g x) := by
      rw [map_mul, fourier_neg]
    simp_rw [hc, integral_conj]
    simpa only [neg_neg, measureFourier_neg, starRingEnd_apply, star_star] using
      congrArg (fun z : ℂ => conj z) (hG (-n))
  have hpoint (x : UnitAddCircle) : (↑(g x).re : ℂ) =
      (1 / 2 : ℂ) * (g x + conj (g x)) := by
    apply Complex.ext
    · norm_num [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.div_re]
      ring
    · norm_num [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.div_im]
  calc
    _ = ∫ x, (1 / 2 : ℂ) * (fourier (-n) x * g x + fourier (-n) x * conj (g x)) ∂circleHaar := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [hpoint]; ring
    _ = _ := by
      rw [integral_const_mul, integral_add h1 h2, hG, hG2]
      ring

/-- A circle measure with square-summable Fourier coefficients is absolutely
continuous. The Fourier Hilbert basis constructs an L² density, with the real
part identified as a difference of two finite positive densities. -/
theorem fourier_l2_absolutelyContinuous (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (h : Summable (fun n : ℤ => ‖measureFourier μ n‖ ^ 2)) :
    μ ≪ circleHaar := by
  let c : lp (fun _ : ℤ => ℂ) 2 := ⟨measureFourier μ, memℓp_gen (by simpa using h)⟩
  let g : Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) := (@fourierBasis 1 _).repr.symm c
  have hg : Integrable g circleHaar := (Lp.memLp g).integrable (by norm_num)
  have hG (n : ℤ) : (∫ x, fourier (-n) x * g x ∂circleHaar) = measureFourier μ n := by
    change @fourierCoeff 1 _ _ _ _ g n = _
    exact (fourierBasis_repr g n).symm.trans
      (congrArg (fun r : lp (fun _ : ℤ => ℂ) 2 => r n)
        ((@fourierBasis 1 _).repr.apply_symm_apply c))
  let f : UnitAddCircle → ℝ := fun x => (g x).re
  have hf : Integrable f circleHaar := hg.re
  let ν := circleHaar.withDensity (fun x => ENNReal.ofReal (f x))
  let νneg := circleHaar.withDensity (fun x => ENNReal.ofReal (-f x))
  have : IsFiniteMeasure ν := positiveDensity_finite hf
  have : IsFiniteMeasure νneg := positiveDensity_finite hf.neg
  have hsplit (x : UnitAddCircle) :
      (↑((f x).toNNReal : ℝ) : ℂ) =
        (↑(f x) : ℂ) + (↑((-f x).toNNReal : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
    congr 1
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    rcases le_total 0 (f x) with hx | hx
    · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
  have hEq : μ + νneg = ν := by
    apply measure_eq_of_fourier
    intro n
    rw [measureFourier_add, show measureFourier ν n = _ from measureFourier_withDensity_ofReal hf n,
      show measureFourier νneg n = _ from measureFourier_withDensity_ofReal hf.neg n,
      ← fourier_real_part_of_density hg μ hG n]
    simp_rw [hsplit, mul_add]
    exact (integral_add (fourier_translate_integrable hf.ofReal (-n))
      (fourier_translate_integrable hf.neg.real_toNNReal.ofReal (-n))).symm
  have hac : ν ≪ circleHaar := withDensity_absolutelyContinuous _ _
  rw [← hEq] at hac
  intro s hs
  exact le_antisymm ((le_self_add.trans_eq (add_apply _ _ s).symm).trans_eq (hac hs)) bot_le

/-- Positive lags suffice because coefficients at negative lags are conjugates. -/
theorem fourier_positive_l2_absolutelyContinuous (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (h : Summable (fun n : ℕ => ‖measureFourier μ ((n + 1 : ℕ) : ℤ)‖ ^ 2)) :
    μ ≪ circleHaar := by
  apply fourier_l2_absolutelyContinuous
  rw [summable_int_iff_summable_nat_and_neg]
  have hn : Summable (fun n : ℕ => ‖measureFourier μ (n : ℤ)‖ ^ 2) :=
    (summable_nat_add_iff 1).mp h
  exact ⟨hn, by simpa only [measureFourier_neg, Complex.norm_conj] using hn⟩

end

end VdC
