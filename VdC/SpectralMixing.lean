/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.SpectralResults
public import VdC.CompactSpectrum

/-! # Absolutely continuous spectra give weak mixing -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

/-- The mixed Fourier coefficients vanish when the first diagonal spectrum
is absolutely continuous. Restrict away from the singular support of the
second spectrum and apply polarization and Riemann–Lebesgue. -/
theorem crossFourier_tendsto_zero_of_ac
    (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle) (c : Fin 2 → Fin 2 → ℤ → ℂ)
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic c z n)
    (hac : (M (baseVector 0) : Measure UnitAddCircle) ≪ circleHaar) :
    Tendsto (fun n : ℕ => c 0 1 (n : ℤ)) atTop (𝓝 0) := by
  let v := baseVector 0
  let w := baseVector 1
  let μy := (M w : Measure UnitAddCircle)
  have : IsFiniteMeasure μy := inferInstanceAs (IsFiniteMeasure (M w : Measure UnitAddCircle))
  have : μy.HaveLebesgueDecomposition circleHaar :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  let ν := circleHaar.withDensity (μy.rnDeriv circleHaar)
  let σ := μy.singularPart circleHaar
  have hsing : circleHaar.MutuallySingular σ := (Measure.mutuallySingular_singularPart _ _).symm
  obtain ⟨A, hA, hHa, hσ⟩ := hsing
  have hA0 : (M v : Measure UnitAddCircle) A = 0 := hac hHa
  have hAcompl : μy.restrict Aᶜ ≪ circleHaar := by
    intro S hS
    have hSa : circleHaar (S ∩ Aᶜ) = 0 :=
      measure_mono_null Set.inter_subset_left hS
    have hdec : μy = ν + σ := (Measure.rnDeriv_add_singularPart μy circleHaar).symm
    rw [Measure.restrict_apply' hA.compl, hdec, add_apply]
    rw [withDensity_absolutelyContinuous _ _ hSa, zero_add]
    exact measure_mono_null Set.inter_subset_right hσ
  have hsame (b : Fin 2 → ℂ) (hb : M b = M w) :
      (M (v+b) : Measure UnitAddCircle).restrict A = μy.restrict A := by
    apply Measure.ext
    intro S hS
    simp only [Measure.restrict_apply hS]
    rw [add_comm v b, combinationMeasure_apply_of_null M c hM b v _ (by
      exact measure_mono_null Set.inter_subset_right hA0), hb]
  have hre (b : Fin 2 → ℂ) (hb : M b = M w) :
      (M (v+b) : Measure UnitAddCircle).restrict Aᶜ ≪ circleHaar := by
    intro S hS
    have hSa : circleHaar (S ∩ Aᶜ) = 0 :=
      measure_mono_null Set.inter_subset_left hS
    have hbS : (M b : Measure UnitAddCircle) (S ∩ Aᶜ) = 0 := by
      rw [hb, ← Measure.restrict_apply' hA.compl]
      exact hAcompl hS
    rw [Measure.restrict_apply' hA.compl,
      combinationMeasure_apply_of_null M c hM v b _ hbS]
    exact hac hSa
  have hsplit (b : Fin 2 → ℂ) (hb : M b = M w) (n : ℤ) :
      measureFourier (M (v+b)) n =
        measureFourier (μy.restrict A) n +
          measureFourier ((M (v+b) : Measure UnitAddCircle).restrict Aᶜ) n := by
    have hμ := Measure.restrict_add_restrict_compl (μ := (M (v+b) : Measure UnitAddCircle)) hA
    have h := congrArg (fun ρ : Measure UnitAddCircle => measureFourier ρ n) hμ
    rw [measureFourier_add, hsame b hb] at h
    exact h.symm
  have hmw : M (-w) = M w := combinationMeasure_neg M c hM w
  have hiw : M (Complex.I • w) = M w := combinationMeasure_mul_I M c hM w
  have hmiw : M (-(Complex.I • w)) = M w :=
    (combinationMeasure_neg M c hM (Complex.I • w)).trans hiw
  let F (b : Fin 2 → ℂ) (n : ℤ) :=
    measureFourier ((M (v+b) : Measure UnitAddCircle).restrict Aᶜ) n
  have hp (n : ℤ) : 4 * c 0 1 n =
      measureFourier (M (v+w)) n - measureFourier (M (v + -w)) n +
        Complex.I * (measureFourier (M (v + Complex.I • w)) n -
          measureFourier (M (v + -(Complex.I • w))) n) := by
    simp [hM, spectralQuadratic, Fin.sum_univ_two, v, w, baseVector, Pi.single_apply,
      Complex.I_mul_I]
    ring_nf
    simp
    ring
  have hpol (n : ℤ) : 4 * c 0 1 n =
      F w n - F (-w) n + Complex.I * (F (Complex.I • w) n - F (-(Complex.I • w)) n) := by
    rw [hp, hsplit w rfl, hsplit (-w) hmw, hsplit (Complex.I • w) hiw,
      hsplit (-(Complex.I • w)) hmiw]
    dsimp only [F]
    ring
  have hF (b : Fin 2 → ℂ) (hb : M b = M w) :
      Tendsto (fun n : ℕ => F b (n : ℤ)) atTop (𝓝 0) :=
    tendsto_measureFourier_zero_of_ac _ (hre b hb)
  have h1 := (hF w rfl).sub (hF (-w) hmw)
  have h2 := ((hF (Complex.I • w) hiw).sub (hF (-(Complex.I • w)) hmiw)).const_mul Complex.I
  have h := (h1.add h2).const_mul (1 / 4 : ℂ)
  simp only [sub_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards with n
  rw [← hpol]
  ring

/-- Mixed permissible correlation limits tend to zero in the lag
when the first sequence is spectrally Lebesgue. -/
theorem SpectrallyLebesgue.cross_tendsto_zero {x y : ℕ → ℂ} (hx : SpectrallyLebesgue x)
    {N : ℕ → ℕ} {r : ℕ → ℂ} (hp : PermissibleTriple x y N) (hr : CorrLimits x y N r) :
    Tendsto r atTop (𝓝 0) := by
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hxa := pairSpectrum_ac hp.strictMono c M hc hM 0 hx
  have ht := crossFourier_tendsto_zero_of_ac M (integerCorrelation c) hM hxa
  have heq (h : ℕ) : integerCorrelation c 0 1 (h : ℤ) = r h :=
    tendsto_nhds_unique (hc 0 1 h) (hr h)
  simpa only [heq] using ht

end

end VdC
