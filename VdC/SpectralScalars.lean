/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.SpectralSequences
public import VdC.Orthogonal
public import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! # Scalar spectral classes and conjugation -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem measureFourier_reflect (μ : Measure UnitAddCircle) (n : ℤ) :
    measureFourier (μ.map (fun x => -x)) n = conj (measureFourier μ n) := by
  rw [measureFourier, integral_map measurable_neg.aemeasurable
    (fourier (-n)).continuous.aestronglyMeasurable, measureFourier, ← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp

/-- Only the zeroth Fourier coefficient of normalized Haar measure is nonzero. -/
theorem measureFourier_circleHaar (n : ℤ) :
    measureFourier circleHaar n = if n = 0 then 1 else 0 := by
  have he : measureFourier circleHaar n = fourierCoeff (fourier (T := 1) 0) n := by
    simp only [measureFourier, circleHaar, fourierCoeff, smul_eq_mul, fourier_zero, mul_one]
  rw [he, fourierCoeff_fourier]
  simp [Pi.single_apply]

private theorem circleHaar_reflect : circleHaar.map (fun x => -x) = circleHaar := by
  have : IsFiniteMeasure (circleHaar.map (fun x => -x)) := circleHaar.isFiniteMeasure_map _
  apply measure_eq_of_fourier
  intro n
  rw [measureFourier_reflect, measureFourier_circleHaar]
  split_ifs <;> simp

private theorem circleHaar_singleton_zero : circleHaar {0} = 0 := by
  let f (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hf (n : ℕ) : f n ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    constructor
    · dsimp [f]
      positivity
    · dsimp [f]
      rw [zero_add, div_lt_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hinj : Function.Injective (fun n => (f n : UnitAddCircle)) := by
    intro m n h
    have h' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hf m) (hf n)).mp h
    simp only [f, one_div, inv_inj] at h'
    exact_mod_cast (add_right_cancel h')
  have : Infinite UnitAddCircle := Infinite.of_injective _ hinj
  by_contra h
  have htop : circleHaar Set.univ = ∞ := Set.infinite_univ.meas_eq_top
    ⟨_, h, fun x _ => by
      have hx : (fun y : UnitAddCircle => -x + y) ⁻¹' {0} = {x} := by
        ext y
        simp [eq_comm]
      have ht := measure_preimage_add (AddCircle.haarAddCircle : Measure UnitAddCircle)
        (-x) ({0} : Set UnitAddCircle)
      rw [hx] at ht
      exact ht.ge⟩
  exact measure_ne_top _ _ htop

theorem corr_conj (x y : ℕ → ℂ) (h N : ℕ) :
    corr (fun n => conj (x n)) (fun n => conj (y n)) h N = conj (corr x y h N) := by
  simp only [corr, cesaro, Complex.star_def, map_div₀, map_natCast, map_sum, map_mul,
    starRingEnd_self_apply]

/-- Conjugation corresponds to reflecting the spectrum on the circle. -/
theorem SpectrallySingular.conj {x : ℕ → ℂ} (hx : SpectrallySingular x) :
    SpectrallySingular (fun n => conj (x n)) := by
  obtain ⟨C, hC, hB⟩ := hx.1
  refine ⟨⟨C, hC, fun n => by simpa using hB n⟩, ?_⟩
  intro N r hN hr
  have hc : CorrLimits x x N (fun h => conj (r h)) := by
    intro h
    simpa only [Function.comp_def, corr_conj, starRingEnd_self_apply] using
      (Complex.continuous_conj.tendsto (r h)).comp (hr h)
  obtain ⟨μ, hμ, hsing⟩ := hx.2 N _ hN hc
  refine ⟨μ.map (fun x => -x), ?_, ?_⟩
  · intro h
    rw [FiniteMeasure.toMeasure_map, measureFourier_reflect, hμ, starRingEnd_self_apply]
  · change ((μ : Measure UnitAddCircle).map fun x => -x).MutuallySingular circleHaar
    simpa only [circleHaar_reflect] using measurableEmbedding_neg.mutuallySingular_map hsing

private theorem corr_const_mul (x : ℕ → ℂ) (c : ℂ) (h N : ℕ) :
    corr (fun n => c * x n) (fun n => c * x n) h N =
      (Complex.normSq c : ℂ) * corr x x h N := by
  unfold corr
  rw [← cesaro_mul_const]
  congr 1
  funext n
  change (c * x (n+h)) * conj (c * x n) = (Complex.normSq c : ℂ) * (x (n+h) * conj (x n))
  rw [map_mul, ← Complex.mul_conj]
  ring

private theorem zeroCorrSpectrum {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hr : CorrLimits (fun _ => 0) (fun _ => 0) N r) :
    HasSpectrum r 0 := by
  intro h
  have he : r h = 0 := tendsto_nhds_unique (hr h) (by simp [corr, cesaro])
  simp [he, measureFourier]

theorem spectrallyLebesgue_zero : SpectrallyLebesgue (fun _ => 0) :=
  ⟨⟨0, le_rfl, by simp⟩, fun _ _ _ hr => ⟨0, zeroCorrSpectrum hr, Measure.AbsolutelyContinuous.zero _⟩⟩

theorem spectrallySingular_zero : SpectrallySingular (fun _ => 0) :=
  ⟨⟨0, le_rfl, by simp⟩, fun _ _ _ hr => ⟨0, zeroCorrSpectrum hr, Measure.MutuallySingular.zero_left⟩⟩

private theorem spectrumClass_const_mul (P : Measure UnitAddCircle → Prop) {x : ℕ → ℂ}
    (hx : BoundedSeq x) (hzero : P 0)
    (hscale : ∀ (b : ℝ≥0) (μ : Measure UnitAddCircle), P μ → P (b • μ))
    (hP : ∀ N r, StrictMono N → CorrLimits x x N r →
      ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧ P μ) (c : ℂ) :
    BoundedSeq (fun n => c * x n) ∧ ∀ N r, StrictMono N →
      CorrLimits (fun n => c * x n) (fun n => c * x n) N r →
      ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧ P μ := by
  obtain ⟨C, hC, hB⟩ := hx
  refine ⟨⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun n => ?_⟩, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)
  · intro N r hN hr
    by_cases hc : c = 0
    · subst c
      simp only [zero_mul] at hr
      exact ⟨0, zeroCorrSpectrum hr, hzero⟩
    let a := Complex.normSq c
    have ha : 0 < a := Complex.normSq_pos.mpr hc
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hG : CorrLimits x x N (fun h => (a : ℂ)⁻¹ * r h) := by
      intro h
      have hh := (hr h).const_mul ((a : ℂ)⁻¹)
      simpa [corr_const_mul, a, ← mul_assoc, inv_mul_cancel₀ ha0] using hh
    obtain ⟨μ, hμ, hμP⟩ := hP N _ hN hG
    let b : ℝ≥0 := ⟨a, ha.le⟩
    refine ⟨b • μ, ?_, ?_⟩
    · intro n
      change measureFourier ((b : ℝ≥0∞) • (μ : Measure UnitAddCircle)) (n : ℤ) = r n
      rw [measureFourier_smul, ENNReal.coe_toReal, hμ]
      change (a : ℂ) * ((a : ℂ)⁻¹ * r n) = r n
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    · exact hscale b μ hμP

/-- Closure of spectral Lebesgue sequences under multiplication by a scalar. -/
theorem SpectrallyLebesgue.const_mul {x : ℕ → ℂ} (hx : SpectrallyLebesgue x) (c : ℂ) :
    SpectrallyLebesgue (fun n => c * x n) :=
  spectrumClass_const_mul (· ≪ circleHaar) hx.1 (Measure.AbsolutelyContinuous.zero _)
    (fun b _ h => h.smul_left b) hx.2 c

/-- Closure of spectrally singular sequences under multiplication by a scalar. -/
theorem SpectrallySingular.const_mul {x : ℕ → ℂ} (hx : SpectrallySingular x) (c : ℂ) :
    SpectrallySingular (fun n => c * x n) :=
  spectrumClass_const_mul (·.MutuallySingular circleHaar) hx.1 Measure.MutuallySingular.zero_left
    (fun b _ h => h.smul_nnreal b) hx.2 c

/-- The constant unit sequence has the point mass at frequency zero as
its spectrum on every permissible subsequence. -/
theorem spectrallySingular_one : SpectrallySingular (fun _ => 1) := by
  refine ⟨⟨1, zero_le_one, by simp⟩, ?_⟩
  intro N r hN hr
  let μ : FiniteMeasure UnitAddCircle := ⟨Measure.dirac 0, inferInstance⟩
  refine ⟨μ, ?_, ?_⟩
  · intro h
    change measureFourier (Measure.dirac (0 : UnitAddCircle)) (h : ℤ) = r h
    rw [measureFourier_dirac_zero]
    apply tendsto_nhds_unique _ (hr h)
    simpa [corr, Function.comp_def] using (cesaro_tendsto_const (1 : ℂ)).comp hN.tendsto_atTop
  · refine ⟨{0}ᶜ, (measurableSet_singleton 0).compl, ?_, by
      simpa using circleHaar_singleton_zero⟩
    change Measure.dirac (0 : UnitAddCircle) ({0}ᶜ : Set UnitAddCircle) = 0
    simp

theorem spectrallySingular_const (c : ℂ) : SpectrallySingular (fun _ => c) := by
  simpa only [mul_one] using spectrallySingular_one.const_mul c

end

end VdC
