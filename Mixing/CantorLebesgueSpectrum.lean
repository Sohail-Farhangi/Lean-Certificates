/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorSumFactor
public import Mixing.CyclicMeasure
public import Mixing.Koopman

/-! # The Lebesgue spectrum in Example 6 -/

@[expose] public section

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing

local notation "𝕋" => UnitAddCircle
local notation "𝕏" => ((UnitAddCircle × UnitAddCircle) × (UnitAddCircle × UnitAddCircle))
local notation "haar" => (AddCircle.haarAddCircle : Measure 𝕋)

section IntegerSpectrum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))

/-- A spectral point for a ℤ-representation is viewed on the unit circle by evaluating
its character at the integer generator and expressing that value as an angle. -/
noncomputable def integerSpectralAngle (z : RepresentationSpectrum U) : 𝕋 :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
    (spectralPointCharacter U z (Multiplicative.ofAdd 1))

theorem integerSpectralAngle_continuous : Continuous (integerSpectralAngle U) :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.continuous.comp
    ((spectralCoefficient U (Multiplicative.ofAdd 1)).continuous.subtype_mk _)

theorem integerSpectralAngle_fourier (n : ℤ) (z : RepresentationSpectrum U) :
    fourier n (integerSpectralAngle U z) = spectralCoefficient U (Multiplicative.ofAdd n) z := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hp : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    change n • (1 : ℤ) = n
    simp
  rw [fourier_apply, AddCircle.toCircle_zsmul, spectralCoefficient_apply]
  have he : AddCircle.toCircle (integerSpectralAngle U z) =
      spectralPointCharacter U z (Multiplicative.ofAdd 1) := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply _
  rw [he, ← map_zpow, hp]

/-- The vector spectral measure in the usual angle coordinates for ℤ. -/
noncomputable def integerVectorSpectralMeasure (f : H) : Measure 𝕋 :=
  (vectorSpectralMeasure U f).map (integerSpectralAngle U)

instance (f : H) : IsFiniteMeasure (integerVectorSpectralMeasure U f) :=
  Measure.isFiniteMeasure_map _ _

/-- Fourier moments of the vector spectral measure are the Koopman autocorrelations. -/
theorem integral_fourier_integerVectorSpectralMeasure (f : H) (n : ℤ) :
    (∫ x, fourier n x ∂integerVectorSpectralMeasure U f) =
      ⟪f, U (Multiplicative.ofAdd n) f⟫_ℂ := by
  rw [integerVectorSpectralMeasure,
    integral_map (integerSpectralAngle_continuous U).measurable.aemeasurable
      (fourier (T := 1) n).continuous.aestronglyMeasurable]
  simp_rw [integerSpectralAngle_fourier]
  rw [integral_vectorSpectralMeasure, spectralCalculus_spectralCoefficient]
  rfl

end IntegerSpectrum

/-- The character of frequency `t` of the sum of the two fibre coordinates. -/
noncomputable def example6FibreCharacterContinuous (t : ℤ) : C(𝕏, ℂ) where
  toFun := example6CantorCharacter t
  continuous_toFun := by unfold example6CantorCharacter; fun_prop

/-- The vector `f_t` in the Example 6 product system. -/
noncomputable def example6FibreCharacterLp (t : ℤ) : Lp ℂ 2 example6CantorSystem.measure :=
  ContinuousMap.toLp (E := ℂ) 2 example6CantorSystem.measure ℂ
    (example6FibreCharacterContinuous t)

theorem example6FibreCharacterLp_autocorrelation (t n : ℤ) :
    ⟪example6FibreCharacterLp t,
      example6CantorSystem.koopmanRep (Multiplicative.ofAdd n) (example6FibreCharacterLp t)⟫_ℂ =
      if t * n = 0 then 1 else 0 := by
  let g := Multiplicative.ofAdd n
  have hAe : example6FibreCharacterLp t =ᵐ[example6CantorSystem.measure] example6CantorCharacter t :=
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) example6CantorSystem.measure
      (example6FibreCharacterContinuous t)
  have hAction : example6CantorSystem.koopmanRep g (example6FibreCharacterLp t) =ᵐ[
      example6CantorSystem.measure] fun x ↦ example6CantorCharacter t (example6CantorSystem.act g x) :=
    (Lp.coeFn_compMeasurePreserving _ (example6CantorSystem.preserves g)).trans
      ((example6CantorSystem.preserves g).quasiMeasurePreserving.ae_eq_comp hAe)
  rw [← example6_cantorCharacter_autocorrelation, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hAe, hAction] with x hfx hActx
  rw [hfx, hActx, RCLike.inner_apply']

/-- Example 6's nonzero fibre characters have exactly normalized Lebesgue spectral measure. -/
theorem example6_fibreLebesgueSpectralMeasure (t : ℤ) (ht : t ≠ 0) :
    integerVectorSpectralMeasure example6CantorSystem.koopmanRep (example6FibreCharacterLp t) =
      haar := by
  apply circleMeasure_eq_of_fourier_eq
  intro n
  rw [integral_fourier_integerVectorSpectralMeasure, example6FibreCharacterLp_autocorrelation]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right (mul_ne_zero ht hn), integral_haar_fourier_zero n hn]

end Mixing
