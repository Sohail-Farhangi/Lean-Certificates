/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Permissible
public import VdC.Realization
public import VdC.SpectralSequences
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Compact sequences have singular spectrum. This uses small return energies
and the Riemann–Lebesgue lemma on the absolutely continuous part. -/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ComplexConjugate ENNReal FourierTransform Topology

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Riemann–Lebesgue for a circle measure absolutely continuous with respect to Haar. -/
theorem tendsto_measureFourier_zero_of_ac (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (hμ : μ ≪ circleHaar) :
    Tendsto (fun n : ℕ ↦ measureFourier μ (n : ℤ)) atTop (𝓝 0) := by
  let ρ := μ.rnDeriv circleHaar
  let f : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator
    (fun x ↦ Complex.ofReal (ρ (x : UnitAddCircle)).toReal)
  have hreal := ((Real.tendsto_integral_exp_smul_cocompact f).mono_left atTop_le_cocompact).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine hreal.congr' (Eventually.of_forall fun n ↦ ?_)
  have : μ.HaveLebesgueDecomposition circleHaar := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hρ : circleHaar.withDensity ρ = μ := Measure.withDensity_rnDeriv_eq μ circleHaar hμ
  change (∫ x : ℝ, 𝐞 (-(x * (n : ℝ))) • f x) = measureFourier μ (n : ℤ)
  rw [measureFourier, ← hρ, integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _), circleHaar,
    AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← UnitAddCircle.integral_preimage (0 : ℝ), zero_add, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [f, ρ, circleHaar, indicator_of_mem hx, Circle.smul_def, Real.fourierChar_apply,
      fourier_coe_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Int.cast_neg, Int.cast_natCast, Complex.ofReal_one, div_one]
    ring_nf
  · simp [f, hx]

/-- The squared distance of the character at time `h` from the constant character. -/
def spectralReturnEnergy (μ : Measure UnitAddCircle) (h : ℕ) : ℝ :=
  ∫ t, ‖_root_.fourier (-(h : ℤ)) t - 1‖ ^ 2 ∂μ

theorem spectralReturnEnergy_eq (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] (h : ℕ) :
    spectralReturnEnergy μ h = 2 * (μ.real univ - (measureFourier μ (h : ℤ)).re) := by
  have hpt (z : ℂ) (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
    have hz' : ‖z‖ ^ 2 = 1 := by rw [hz, one_pow]
    rw [Complex.sq_norm, Complex.normSq_apply] at hz'
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero]
    nlinarith only [hz']
  let g : C(UnitAddCircle, ℂ) := _root_.fourier (-(h : ℤ))
  have hg : Integrable g μ :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr : Integrable (fun t ↦ (g t).re) μ :=
    (Complex.continuous_re.comp g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : ∫ t, (g t).re ∂μ = (measureFourier μ (h : ℤ)).re := by
    change (∫ t, (g t).re ∂μ) = (∫ t, g t ∂μ).re
    simpa only [RCLike.re_to_complex] using (integral_re (𝕜 := ℂ) hg)
  change (∫ t, ‖g t - 1‖ ^ 2 ∂μ) = _
  calc
    _ = ∫ t, 2 * (1 - (g t).re) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun t ↦ hpt (g t) (by simp [g, fourier_apply, Circle.norm_coe])
    _ = _ := by
      rw [integral_const_mul, integral_sub (integrable_const _) hr,
        integral_const, smul_eq_mul, mul_one, he]

theorem spectralReturnEnergy_mono {ν μ : Measure UnitAddCircle} [IsFiniteMeasure μ]
    (hν : ν ≤ μ) (h : ℕ) : spectralReturnEnergy ν h ≤ spectralReturnEnergy μ h := by
  apply integral_mono_measure hν (ae_of_all _ fun _ ↦ sq_nonneg _)
  have hc : Continuous (fun t : UnitAddCircle ↦ ‖_root_.fourier (-(h : ℤ)) t - 1‖ ^ 2) :=
    ((_root_.fourier (-(h : ℤ))).continuous.sub continuous_const).norm.pow 2
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A positive measure with arbitrarily late arbitrarily small returns is singular. -/
theorem mutuallySingular_of_small_spectral_returns (μ : Measure UnitAddCircle)
    [IsFiniteMeasure μ]
    (hsmall : ∀ ε > (0 : ℝ), ∀ L : ℕ, ∃ h ≥ L, spectralReturnEnergy μ h < ε) :
    μ.MutuallySingular circleHaar := by
  let ν := circleHaar.withDensity (μ.rnDeriv circleHaar)
  have : μ.HaveLebesgueDecomposition circleHaar := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hνle : ν ≤ μ := Measure.withDensity_rnDeriv_le _ _
  have hνac : ν ≪ circleHaar := withDensity_absolutelyContinuous _ _
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνle
  have hl : Tendsto (spectralReturnEnergy ν) atTop (𝓝 (2 * ν.real univ)) := by
    have ht := Complex.continuous_re.tendsto 0 |>.comp (tendsto_measureFourier_zero_of_ac ν hνac)
    have ht' := (tendsto_const_nhds (x := ν.real univ)).sub ht |>.const_mul (2 : ℝ)
    change Tendsto (fun h ↦ spectralReturnEnergy ν h) atTop (𝓝 (2 * ν.real univ))
    simpa only [spectralReturnEnergy_eq, comp_def, Complex.zero_re, sub_zero] using ht'
  apply (Measure.withDensity_rnDeriv_eq_zero μ circleHaar).mp
  change ν = 0
  by_contra hne
  have hpos : 0 < ν.real univ := by
    apply lt_of_le_of_ne measureReal_nonneg
    intro hz
    apply hne
    exact Measure.measure_univ_eq_zero.mp
      ((measureReal_eq_zero_iff (measure_ne_top ν univ)).mp hz.symm)
  have hev : ∀ᶠ h : ℕ in atTop, ν.real univ < spectralReturnEnergy ν h :=
    hl.eventually (lt_mem_nhds (by linarith))
  obtain ⟨L, hL⟩ := eventually_atTop.mp hev
  obtain ⟨h, hh, hsmall'⟩ := hsmall _ hpos L
  exact (hL h hh).not_ge ((spectralReturnEnergy_mono hνle h).trans hsmall'.le)

/-- Compact bounded sequences have singular spectral measures on every permissible subsequence. -/
theorem spectrallySingular_of_compactSeq {y : ℕ → ℂ} (hy : CompactSeq y) :
    SpectrallySingular y := by
  refine ⟨hy.1, fun N r hN hr ↦ ?_⟩
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hy.1 hN hr
  refine ⟨μ, hμ, mutuallySingular_of_small_spectral_returns _ ?_⟩
  intro ε hε L
  obtain ⟨h, hh, hs⟩ := compactAlong_returns hy hN hr ε hε L
  refine ⟨h, hh, ?_⟩
  have hmass := hμ 0
  rw [Nat.cast_zero, measureFourier_zero] at hmass
  have hm := congrArg Complex.re hmass
  rw [Complex.ofReal_re] at hm
  simpa only [spectralReturnEnergy_eq, hμ h, hm] using hs

end

end VdC
