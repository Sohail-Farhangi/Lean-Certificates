/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.DigitLacunary
public import VdC.SpectralSeparation
public import VdC.Torus

/-! # Digit Spectrum -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

private def lacunaryCharacter (r k : ℕ) : C(UnitAddCircle, ℂ) := fourier (-(↑(r^k : ℕ) : ℤ))

private theorem testMean_lacunaryCharacter (μ : Measure UnitAddCircle) (r k : ℕ) :
    testMean μ (lacunaryCharacter r k) = measureFourier μ (↑(r^k : ℕ)) := rfl

private theorem testMean_lacunary_product (μ : Measure UnitAddCircle) (r i j : ℕ) :
    testMean μ (lacunaryCharacter r i * star (lacunaryCharacter r j)) =
      measureFourier μ ((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)) := by
  unfold testMean measureFourier
  congr 1
  ext x
  simp only [lacunaryCharacter, ContinuousMap.mul_apply, ContinuousMap.star_apply, Complex.star_def,
    ← fourier_neg, ← fourier_add]
  congr 2
  ring

private theorem testMean_centeredGram {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : C(X, ℂ)) {c : ℂ} (hf : testMean μ f = c) (hg : testMean μ g = c) :
    testMean μ ((f - ContinuousMap.const X c) * star (g - ContinuousMap.const X c)) =
      testMean μ (f * star g) - c * star c := by
  let a := ContinuousMap.const X c
  have he : (f-a) * star (g-a) = (f*star g - star c • f) - c • star g + ContinuousMap.const X (c*star c) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.star_apply,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, a, ContinuousMap.const_apply, star_sub]
    ring
  change testMean μ ((f-a) * star (g-a)) = _
  rw [he, testMean_add, testMean_sub, testMean_sub, testMean_smul, testMean_smul, testMean_const,
    testMean_star, hf, hg]
  ring

private theorem lacunaryGram_real_symm {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (f g : C(X, ℂ)) :
    (testMean μ (f * star g)).re = (testMean μ (g * star f)).re := by
  rw [show f * star g = star (g * star f) by simp [mul_comm], testMean_star]
  rfl

private def lacunaryMean (r N : ℕ) : C(UnitAddCircle, ℂ) :=
  ⟨fun x => cesaro (fun k => lacunaryCharacter r k x) N, by unfold cesaro; fun_prop⟩

private theorem tendsto_lacunary_haar_measure_square {r : ℕ} (hr : 1 < r) :
    Tendsto (fun N => ∫ x, ‖lacunaryMean r N x - 0‖ ^ 2 ∂circleHaar) atTop (𝓝 0) := by
  let D (h : ℕ) : ℝ := if h = 0 then 1 else 0
  have hD : ∀ h, 0 ≤ D h := by intro h; unfold D; split <;> norm_num
  have hlim : Tendsto D atTop (𝓝 0) := tendsto_const_nhds.congr' <|
    (eventually_gt_atTop (0 : ℕ)).mono fun h hh => by simp [D, hh.ne']
  have hpow : StrictMono (fun k : ℕ => r^k) := pow_right_strictMono₀ hr
  have hGram (i j : ℕ) : (testMean circleHaar (lacunaryCharacter r i * star (lacunaryCharacter r j))).re ≤
      D (i-j+(j-i)) := by
    rw [testMean_lacunary_product]
    have he : measureFourier circleHaar ((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)) =
        if i = j then 1 else 0 := by
      unfold measureFourier
      change testMean circleHaar (fourier (-((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)))) = _
      rw [testMean_circle_character]
      have hz : -((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)) = 0 ↔ i = j := by
        rw [neg_eq_zero, sub_eq_zero]
        exact ⟨fun h => hpow.injective (by exact_mod_cast h), fun h => by rw [h]⟩
      simp only [hz]
    rw [he]
    by_cases h : i=j
    · subst j; simp [D]
    · rw [ite_eq_right h, Complex.zero_re]
      exact hD _
  simpa only [lacunaryMean, ContinuousMap.coe_mk, sub_zero] using
    tendsto_squareIntegral_cesaro_of_gram circleHaar (lacunaryCharacter r) D hD hlim hGram

private theorem tendsto_lacunary_digit_measure_square {r m : ℕ} (hr : 1 < r)
    (μ : FiniteMeasure UnitAddCircle) (hμ : HasSpectrum (digitAutocorrelation r m hr) μ) :
    Tendsto (fun N => ∫ x, ‖lacunaryMean r N x - digitFirstCorrelation r m‖ ^ 2 ∂(μ : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  have hmass : ((μ : Measure UnitAddCircle).real Set.univ : ℂ) = 1 := by
    simpa only [Nat.cast_zero, measureFourier_zero, digitAutocorrelation_zero hr] using hμ 0
  have : IsProbabilityMeasure (μ : Measure UnitAddCircle) := by
    constructor
    have h : (μ : Measure UnitAddCircle).real Set.univ = 1 := by exact_mod_cast hmass
    have hm := congrArg ENNReal.ofReal h
    rwa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_one] at hm
  let c := digitFirstCorrelation r m
  let u k : C(UnitAddCircle, ℂ) := lacunaryCharacter r k - ContinuousMap.const UnitAddCircle c
  let D k := ‖digitAutocorrelation r m hr (r^k-1)-c*star c‖
  have hD (k : ℕ) : 0 ≤ D k := norm_nonneg _
  have hlim : Tendsto D atTop (𝓝 0) := by
    simpa [D, c] using
      ((tendsto_digitAutocorrelation_pow_sub_one (m := m) hr).sub
        (tendsto_const_nhds (x := c*star c))).norm
  have hmean (k : ℕ) : testMean (μ : Measure UnitAddCircle) (lacunaryCharacter r k) = c := by
    rw [testMean_lacunaryCharacter, hμ, digitAutocorrelation_pow hr]
  have hGram (i j : ℕ) : (testMean (μ : Measure UnitAddCircle) (u i * star (u j))).re ≤
      D (i-j+(j-i)) := by
    suffices hle : ∀ (i j : ℕ), j ≤ i →
        (testMean (μ : Measure UnitAddCircle) (u i * star (u j))).re ≤ D (i-j) by
      rcases le_total j i with hij | hji
      · simpa [Nat.sub_eq_zero_of_le hij] using hle i j hij
      · rw [lacunaryGram_real_symm, Nat.sub_eq_zero_of_le hji, zero_add]
        exact hle j i hji
    intro i j hij
    have hpow : StrictMono (fun k : ℕ => r^k) := pow_right_strictMono₀ hr
    have hnat : r^i - r^j = r^j * (r^(i-j)-1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← pow_add, Nat.add_sub_of_le hij]
    change (testMean (μ : Measure UnitAddCircle)
      ((lacunaryCharacter r i - _) * star (lacunaryCharacter r j - _))).re ≤ _
    rw [testMean_centeredGram _ _ _ (hmean i) (hmean j), testMean_lacunary_product,
      ← Nat.cast_sub (hpow.monotone hij), hμ, hnat, digitAutocorrelation_pow_mul hr]
    exact Complex.re_le_norm _
  refine (tendsto_squareIntegral_cesaro_of_gram (μ : Measure UnitAddCircle) u D hD hlim hGram).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change ‖cesaro (fun n => lacunaryCharacter r n x-c) N‖ ^ 2 = ‖cesaro (fun n => lacunaryCharacter r n x) N-c‖ ^ 2
    rw [cesaro_sub, cesaro_const c hN]

/-- The base-r digit characters have singular spectral measures. This proof uses
their carry recursion and a lacunary Fourier average that separates those measures
from Haar measure. -/
theorem spectrallySingular_digitCharacter {r m : ℕ} (hr : 1 < r) :
    SpectrallySingular (digitCharacter r m) := by
  have hb : BoundedSeq (digitCharacter r m) := ⟨1, zero_le_one, fun _ => by simp⟩
  have hfull : CorrLimits (digitCharacter r m) (digitCharacter r m) id (digitAutocorrelation r m hr) :=
    fun h => tendsto_digitAutocorrelation hr h
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hb strictMono_id hfull
  have hs := mutuallySingular_of_distinct_squared_mean_limits (μ : Measure UnitAddCircle) circleHaar
    (lacunaryMean r) (digitFirstCorrelation_ne_zero (m := m) hr)
    (tendsto_lacunary_digit_measure_square hr μ hμ) (tendsto_lacunary_haar_measure_square hr)
  refine ⟨hb, fun N q hN hq => ⟨μ, fun h => ?_, hs⟩⟩
  rw [hμ]
  exact tendsto_nhds_unique ((tendsto_digitAutocorrelation hr h).comp hN.tendsto_atTop) (hq h)

/-- The manuscript's generalized Thue–Morse digit-sum residue example. -/
theorem spectrallySingular_digitResidue {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    HasPositiveLowerDensity (digitResidue r j) ∧ SpectrallySingular (selectionWeight (digitResidue r j)) :=
  ⟨digitResidue_positive_lowerDensity hr hj,
    spectrallySingular_digitResidue_of_characters hr hj (fun _ _ _ => spectrallySingular_digitCharacter hr)⟩

theorem spectrallySingular_digitResidue_enumeration {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    StrictMono (digitResidueIndex r j) ∧ Set.range (digitResidueIndex r j) = digitResidue r j ∧
      HasPositiveLowerDensity (Set.range (digitResidueIndex r j)) ∧
      SpectrallySingular (selectionWeight (Set.range (digitResidueIndex r j))) := by
  refine ⟨strictMono_digitResidueIndex hr hj, range_digitResidueIndex hr hj, ?_⟩
  rw [range_digitResidueIndex hr hj]
  exact spectrallySingular_digitResidue hr hj

def thueMorsePositive : Set ℕ := {n | (-1 : ℂ)^digitSum 2 n = 1}

theorem thueMorsePositive_eq_digitResidue : thueMorsePositive = digitResidue 2 0 := by
  ext n
  change (-1 : ℂ)^digitSum 2 n = 1 ↔ digitSum 2 n % 2 = 0
  rw [neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1), Nat.even_iff]

/-- The positive entries of the binary Thue–Morse word give a spectrally singular
selection of positive density. -/
theorem thueMorse_positive_spectrallySingular :
    HasPositiveLowerDensity thueMorsePositive ∧ SpectrallySingular (selectionWeight thueMorsePositive) := by
  rw [thueMorsePositive_eq_digitResidue]
  exact spectrallySingular_digitResidue (by decide) (by decide)

end
end VdC
