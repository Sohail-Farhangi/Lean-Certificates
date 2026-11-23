/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Spectrum
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Orthogonality of mutually singular spectral measures -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate BigOperators

namespace VdC

noncomputable section

/-- The scalar Fourier data for a linear combination of two vectors. -/
def spectralQuadratic (c : Fin 2 → Fin 2 → ℤ → ℂ) (z : Fin 2 → ℂ) (n : ℤ) : ℂ :=
  ∑ i, ∑ j, z i * conj (z j) * c i j n

private theorem measureFourier_finite_smul (μ : FiniteMeasure UnitAddCircle) (t : ℝ≥0)
    (n : ℤ) :
    measureFourier (↑(t • μ) : Measure UnitAddCircle) n =
      ((t : ℝ) : ℂ) * measureFourier μ n := by
  change measureFourier ((t : ℝ≥0∞) • (↑μ : Measure UnitAddCircle)) n = _
  rw [measureFourier_smul, ENNReal.coe_toReal]

variable
  (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
  (c : Fin 2 → Fin 2 → ℤ → ℂ)
  (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic c z n)
include hM

theorem combinationMeasure_neg (w : Fin 2 → ℂ) :
    M (-w) = M w := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp [hM, spectralQuadratic]

private theorem combinationMeasure_parallelogram (v w : Fin 2 → ℂ) :
    M (v+w) + M (v-w) = (2 : ℝ≥0) • M v + (2 : ℝ≥0) • M w := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp only [FiniteMeasure.toMeasure_add, measureFourier_add, measureFourier_finite_smul,
    hM, spectralQuadratic, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, map_add, map_sub,
    NNReal.coe_ofNat, Complex.ofReal_ofNat]
  ring

private theorem combinationMeasure_scale (v w : Fin 2 → ℂ) (k : ℕ) :
    M (v + ((k : ℂ) + 1) • w) + (k : ℝ≥0) • M v =
      ((k : ℝ≥0) + 1) • M (v+w) + (((k : ℝ≥0) + 1) * (k : ℝ≥0)) • M w := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp only [FiniteMeasure.toMeasure_add, measureFourier_add, measureFourier_finite_smul,
    hM, spectralQuadratic, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul, map_natCast, map_one, NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_one, Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_mul]
  ring

private def realMass (A : Set UnitAddCircle) (μ : FiniteMeasure UnitAddCircle) : ℝ :=
  (μ : Measure UnitAddCircle).real A

omit hM in
private theorem realMass_add (A : Set UnitAddCircle) (μ ν : FiniteMeasure UnitAddCircle) :
    realMass A (μ+ν) = realMass A μ + realMass A ν := by
  exact measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)

omit hM in
private theorem realMass_smul (A : Set UnitAddCircle) (s : ℝ≥0)
    (μ : FiniteMeasure UnitAddCircle) :
    realMass A (s • μ) = (s : ℝ) * realMass A μ := by
  simp only [realMass, FiniteMeasure.toMeasure_smul, measureReal_nnreal_smul_apply]

omit hM in
private theorem realMass_nonneg (A : Set UnitAddCircle) (μ : FiniteMeasure UnitAddCircle) :
    0 ≤ realMass A μ := ENNReal.toReal_nonneg

private theorem realMass_add_lower_of_null
    (v w : Fin 2 → ℂ) (A : Set UnitAddCircle) (hw : realMass A (M w) = 0) :
    realMass A (M v) ≤ realMass A (M (v+w)) := by
  have hb (k : ℕ) :
      (k : ℝ) * realMass A (M v) ≤ ((k : ℝ) + 1) * realMass A (M (v+w)) := by
    have h := congrArg (realMass A) (combinationMeasure_scale M c hM v w k)
    simp only [realMass_add, realMass_smul, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_mul,
      NNReal.coe_one, hw, mul_zero, add_zero] at h
    linarith [realMass_nonneg A (M (v + ((k : ℂ) + 1) • w))]
  by_contra! hlt
  have hp := sub_pos.mpr hlt
  obtain ⟨k, hk⟩ := exists_nat_gt (realMass A (M (v+w)) /
    (realMass A (M v) - realMass A (M (v+w))))
  have h := (div_lt_iff₀ hp).mp hk
  nlinarith only [h, hb k]

private theorem realMass_add_of_null
    (v w : Fin 2 → ℂ) (A : Set UnitAddCircle) (hw : realMass A (M w) = 0) :
    realMass A (M (v+w)) = realMass A (M v) := by
  have h₁ := realMass_add_lower_of_null M c hM v w A hw
  have h₂ := realMass_add_lower_of_null M c hM v (-w) A (by
    rw [combinationMeasure_neg M c hM, hw])
  have hpar := congrArg (realMass A) (combinationMeasure_parallelogram M c hM v w)
  simp only [realMass_add, realMass_smul, NNReal.coe_ofNat, hw, mul_zero, add_zero] at hpar
  rw [sub_eq_add_neg] at hpar
  linarith

/-- A summand with vanishing spectral mass on A does not change the
other summand's spectral mass there. -/
theorem combinationMeasure_apply_of_null
    (v w : Fin 2 → ℂ) (A : Set UnitAddCircle) (hw : (M w : Measure UnitAddCircle) A = 0) :
    (M (v+w) : Measure UnitAddCircle) A = (M v : Measure UnitAddCircle) A := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact realMass_add_of_null M c hM v w A (by simp [realMass, Measure.real, hw])

/-- The sum of two absolutely continuous vectors is absolutely continuous. -/
theorem combinationMeasure_add_absolutelyContinuous
    (v w : Fin 2 → ℂ) (ν : Measure UnitAddCircle)
    (hv : (M v : Measure UnitAddCircle) ≪ ν) (hw : (M w : Measure UnitAddCircle) ≪ ν) :
    (M (v+w) : Measure UnitAddCircle) ≪ ν := by
  intro A hA
  rw [combinationMeasure_apply_of_null M c hM v w A (hw hA), hv hA]

private theorem realMass_add_of_mutuallySingular
    (v w : Fin 2 → ℂ)
    (hperp : ((M v) : Measure UnitAddCircle).MutuallySingular (M w)) :
    realMass Set.univ (M (v+w)) = realMass Set.univ (M v) + realMass Set.univ (M w) := by
  obtain ⟨A, hA, hv, hw⟩ := hperp
  have hv' : realMass A (M v) = 0 := by simp [realMass, Measure.real, hv]
  have hw' : realMass Aᶜ (M w) = 0 := by simp [realMass, Measure.real, hw]
  have ha := realMass_add_of_null M c hM w v A hv'
  rw [add_comm w v] at ha
  have hb := realMass_add_of_null M c hM v w Aᶜ hw'
  have hc (z : Fin 2 → ℂ) :
      realMass A (M z) + realMass Aᶜ (M z) = realMass Set.univ (M z) :=
    measureReal_add_measureReal_compl hA
  rw [← hc (v+w), ← hc v, ← hc w, ha, hb, hv', hw']
  ring

theorem combinationMeasure_mul_I (v : Fin 2 → ℂ) :
    M (Complex.I • v) = M v := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp only [hM, spectralQuadratic, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, map_mul,
    Complex.conj_I]
  ring_nf
  simp

private theorem quadratic_add_of_mutuallySingular
    (v w : Fin 2 → ℂ)
    (hperp : ((M v) : Measure UnitAddCircle).MutuallySingular (M w)) :
    spectralQuadratic c (v+w) 0 = spectralQuadratic c v 0 + spectralQuadratic c w 0 := by
  simp only [← hM, measureFourier_zero, ← Complex.ofReal_add]
  exact congrArg Complex.ofReal (realMass_add_of_mutuallySingular M c hM v w hperp)

/-- Orthogonality for two vectors whose spectra are mutually singular.
The positive measures for all linear combinations replace a Hilbert-space
quotient, and their Fourier coefficients determine their quadratic mass laws. -/
theorem correlation_measures_orthogonal
    (hsing : ((M (Pi.single (0 : Fin 2) 1)) : Measure UnitAddCircle).MutuallySingular
      (M (Pi.single (1 : Fin 2) 1)))
    (herm : conj (c 0 1 0) = c 1 0 0) :
    c 0 1 0 = 0 := by
  let v : Fin 2 → ℂ := Pi.single 0 1
  let w : Fin 2 → ℂ := Pi.single 1 1
  have hR := quadratic_add_of_mutuallySingular M c hM v w hsing
  have hIsing : ((M v) : Measure UnitAddCircle).MutuallySingular (M (Complex.I • w)) := by
    rw [combinationMeasure_mul_I M c hM]
    exact hsing
  have hI := quadratic_add_of_mutuallySingular M c hM v (Complex.I • w) hIsing
  simp [spectralQuadratic, Fin.sum_univ_two, v, w, Pi.single_apply] at hR
  simp [spectralQuadratic, Fin.sum_univ_two, v, w, Pi.single_apply, Complex.I_mul_I] at hI
  rw [← herm] at hR hI
  apply Complex.ext
  · have h := congrArg Complex.re hR
    simp [Complex.add_re] at h
    rw [Complex.zero_re]
    linarith
  · have h := congrArg Complex.re hI
    simp [Complex.add_re, Complex.mul_re] at h
    rw [Complex.zero_im]
    linarith

end

end VdC
