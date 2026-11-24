/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralWeakMixing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Strong convergence of bounded spectral multipliers -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))

/-- The spectral value of the inverse generator. -/
noncomputable def chaconDecayParameter : C(RepresentationSpectrum U, ℂ) :=
  spectralCoefficient U (Multiplicative.ofAdd (-1))

theorem chaconDecayParameter_norm (z : RepresentationSpectrum U) :
    ‖chaconDecayParameter U z‖ = 1 :=
  Circle.norm_coe (spectralPointCharacter U z (Multiplicative.ofAdd (-1)))

private theorem chaconDecayParameter_bad_subsingleton :
    {z : RepresentationSpectrum U | chaconDecayParameter U z = 1}.Subsingleton := by
  intro z hz w hw
  apply spectralPointCharacter_injective U
  apply MonoidHom.ext
  intro g
  let a := Multiplicative.ofAdd (-1 : ℤ)
  have he : a ^ (-g.toAdd) = g := by
    change (-g.toAdd) • (-1 : ℤ) = g.toAdd
    simp
  have hw' : spectralPointCharacter U z a = spectralPointCharacter U w a := by
    apply Subtype.ext
    exact hz.trans hw.symm
  calc
    spectralPointCharacter U z g = spectralPointCharacter U z (a ^ (-g.toAdd)) :=
      congrArg (spectralPointCharacter U z) he.symm
    _ = spectralPointCharacter U w (a ^ (-g.toAdd)) := by simp only [map_zpow, hw']
    _ = spectralPointCharacter U w g := congrArg (spectralPointCharacter U w) he

private theorem chaconDecaySpectralMeasure_nullSingleton (hWeak : IsWeaklyMixing U) (x : H) :
    NullSingletonClass (vectorSpectralMeasure U x) := by
  let _ : Countable (Multiplicative ℤ) := by change Countable ℤ; infer_instance
  let _ := (isWeaklyMixing_iff_all_vector_measures_atomless U).mp hWeak x
  constructor
  intro z
  have h : (spectralPointDual U) ⁻¹' {spectralPointDual U z} = {z} := by
    ext w
    change spectralPointDual U w = spectralPointDual U z ↔ w = z
    exact (spectralPointDual_injective U).eq_iff
  rw [← h, ← Measure.map_apply (spectralPointDual_continuous U).measurable (measurableSet_singleton _)]
  change dualVectorSpectralMeasure U x {spectralPointDual U z} = 0
  exact measure_singleton (spectralPointDual U z)

/-- Bounded continuous spectral multipliers that tend to zero off the
trivial spectral character tend strongly to zero for weakly mixing actions. -/
theorem tendsto_chaconDecaySpectralCalculus_zero (hWeak : IsWeaklyMixing U)
    (x : H) (f : ℕ → C(RepresentationSpectrum U, ℂ))
    (hfBound : ∀ n z, ‖f n z‖ ≤ 1)
    (hfLim : ∀ z, chaconDecayParameter U z ≠ 1 → Tendsto (fun n ↦ f n z) atTop (𝓝 0)) :
    Tendsto (fun n ↦ spectralCalculus U (f n) x) atTop (𝓝 0) := by
  let μ := vectorSpectralMeasure U x
  let _ : NullSingletonClass μ := chaconDecaySpectralMeasure_nullSingleton U hWeak x
  have hbad : ∀ᵐ z ∂μ, chaconDecayParameter U z ≠ 1 := by
    apply ae_iff.mpr
    simpa only [not_not] using (chaconDecayParameter_bad_subsingleton U).measure_zero μ
  have hdc : Tendsto (fun n ↦ ∫ z, ‖f n z‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ _ : RepresentationSpectrum U, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    · intro n
      exact ((f n).continuous.norm.pow 2).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← one_pow 2]
        exact pow_le_pow_left₀ (norm_nonneg _) (hfBound n z) _
    · exact hbad.mono fun z hz ↦ by
        simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using (hfLim z hz).norm.pow 2
  have heq (n : ℕ) :
      ‖spectralCalculus U (f n) x‖ ^ 2 = ∫ z, ‖f n z‖ ^ 2 ∂μ := by
    calc
      _ = (inner ℂ (spectralVectorLinear U x (f n)) (spectralVectorLinear U x (f n))).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (∫ z, f n z * conj (f n z) ∂μ).re := by
        rw [spectralVectorLinear_inner]
      _ = _ := by
        simp_rw [Complex.mul_conj, ← Complex.sq_norm]
        rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [integral_zero] at hdc
  simp_rw [← heq] at hdc
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, sub_zero, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hdc

end Mixing
