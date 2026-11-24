/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorLebesgueSpectrum
public import Mixing.SpectralTypeTheorem

/-! # The spectral rotation criterion of Parry

This is the Hilbert-space and measure-class argument in Proposition 3.2 of
Ackelsberg–Richter–Shalom, *On the maximal spectral type of nilsystems*,
arXiv:2307.07213. The modulation hypothesis is formulated directly on the
representation. -/

@[expose] public section
noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

namespace Mixing

local notation "𝕋" => UnitAddCircle
local notation "haar" => (AddCircle.haarAddCircle : Measure 𝕋)

/-- Rotation of a measure on the circle, expressed in additive coordinates. -/
def rotateCircleMeasure (s : 𝕋) (μ : Measure 𝕋) : Measure 𝕋 :=
  μ.map (fun z => s+z)

instance (s : 𝕋) (μ : Measure 𝕋) [IsFiniteMeasure μ] : IsFiniteMeasure (rotateCircleMeasure s μ) :=
  Measure.isFiniteMeasure_map _ _

private theorem measurable_rotation (s : 𝕋) : Measurable (fun z : 𝕋 => s+z) :=
  measurable_const.add measurable_id

private theorem lintegral_rotatedCircleMeasure (μ : Measure 𝕋) [IsFiniteMeasure μ]
    (A : Set 𝕋) (hA : MeasurableSet A) :
    (∫⁻ s, rotateCircleMeasure s μ A ∂haar) = haar A * μ univ := by
  let B := (fun p : 𝕋 × 𝕋 => p.1+p.2) ⁻¹' A
  have hB : MeasurableSet B := measurable_add hA
  calc
    _ = ((haar).prod μ) B := by
      rw [Measure.prod_apply hB]
      apply lintegral_congr
      intro s
      rw [rotateCircleMeasure, Measure.map_apply (measurable_rotation s) hA]
      rfl
    _ = _ := by
      rw [Measure.prod_apply_symm hB]
      have he (z : 𝕋) : haar ((fun x => (x,z)) ⁻¹' B) = haar A :=
        (measurePreserving_add_right haar z).measure_preimage hA.nullMeasurableSet
      simp only [he, lintegral_const]

/-- A nonzero finite rotation-quasi-invariant measure has exactly the Haar
null sets. The proof averages over all rotations. -/
theorem circleMeasure_equivalent_haar_of_rotation_absolutelyContinuous
    (μ : Measure 𝕋) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hRot : ∀ s : 𝕋, rotateCircleMeasure s μ ≪ μ) : μ ≪ haar ∧ haar ≪ μ := by
  have hμMass : μ univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  constructor
  · apply Measure.AbsolutelyContinuous.mk
    intro A hA hAz
    have hInt := lintegral_rotatedCircleMeasure μ A hA
    rw [hAz, zero_mul] at hInt
    let B := (fun p : 𝕋 × 𝕋 => p.1+p.2) ⁻¹' A
    have hMeas : Measurable (fun s => rotateCircleMeasure s μ A) := by
      have hB : MeasurableSet B := measurable_add hA
      have he (s : 𝕋) : rotateCircleMeasure s μ A = μ (Prod.mk s ⁻¹' B) := by
        rw [rotateCircleMeasure, Measure.map_apply (measurable_rotation s) hA]
        rfl
      simp_rw [he]
      exact measurable_measure_prodMk_left hB
    obtain ⟨s, hs⟩ := ((lintegral_eq_zero_iff hMeas).mp hInt).exists
    change rotateCircleMeasure s μ A = 0 at hs
    let C := (fun z : 𝕋 => s+z) ⁻¹' A
    have hC := (measurable_rotation s) hA
    have hCz : μ C = 0 := by rwa [rotateCircleMeasure, Measure.map_apply (measurable_rotation s) hA] at hs
    have hBack : rotateCircleMeasure (-s) μ C = 0 := hRot (-s) hCz
    rw [rotateCircleMeasure, Measure.map_apply (measurable_rotation (-s)) hC] at hBack
    have he : (fun z : 𝕋 => -s+z) ⁻¹' C = A := by
      ext z
      change (s+(-s+z) ∈ A) ↔ z ∈ A
      rw [← add_assoc, add_neg_cancel, zero_add]
    rwa [he] at hBack
  · apply Measure.AbsolutelyContinuous.mk
    intro A hA hAz
    have he (s : 𝕋) : rotateCircleMeasure s μ A = 0 := hRot s hAz
    have hInt := lintegral_rotatedCircleMeasure μ A hA
    simp only [he, lintegral_zero] at hInt
    exact (mul_eq_zero.mp hInt.symm).resolve_right hμMass

section Representation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))

/-- A unitary implementing a phase modulation rotates all scalar spectral measures. -/
theorem integerVectorSpectralMeasure_eq_rotate_of_modulation (s : 𝕋) (B : H ≃ₗᵢ[ℂ] H)
    (hB : ∀ (n : ℤ) (x : H), U (Multiplicative.ofAdd n) (B x) =
      fourier n s • B (U (Multiplicative.ofAdd n) x)) (x : H) :
    integerVectorSpectralMeasure U (B x) = rotateCircleMeasure s (integerVectorSpectralMeasure U x) := by
  apply circleMeasure_eq_of_fourier_eq
  intro n
  rw [integral_fourier_integerVectorSpectralMeasure, hB, inner_smul_right, B.inner_map_map,
    rotateCircleMeasure, integral_map (measurable_rotation s).aemeasurable (fourier n).continuous.aestronglyMeasurable]
  simp_rw [fourier_circle_add, integral_const_mul]
  rw [integral_fourier_integerVectorSpectralMeasure]

/-- Angle of a character of the integers at the generator. -/
def integerDualAngle (χ : DiscreteDual (Multiplicative ℤ)) : 𝕋 :=
  (AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).symm
    (dualEvaluation (Multiplicative.ofAdd 1) χ)

theorem integerDualAngle_continuous : Continuous integerDualAngle :=
  (AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).symm.continuous.comp
    (dualEvaluation (Multiplicative.ofAdd (1:ℤ))).continuous

theorem integerVectorSpectralMeasure_eq_map_dual (x : H) :
    integerVectorSpectralMeasure U x = (dualVectorSpectralMeasure U x).map integerDualAngle := by
  rw [dualVectorSpectralMeasure, Measure.map_map integerDualAngle_continuous.measurable
    (spectralPointDual_continuous U).measurable]
  rfl

theorem integerVectorSpectralMeasure_absolutelyContinuous_of_maximal (x : H)
    (hx : IsMaximalSpectralVector U x) (y : H) :
    integerVectorSpectralMeasure U y ≪ integerVectorSpectralMeasure U x := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA h
  rw [integerVectorSpectralMeasure_eq_map_dual,
    Measure.map_apply integerDualAngle_continuous.measurable hA] at h ⊢
  exact hx y h

private theorem integerVectorSpectralMeasure_ne_zero (x : H) (hx : x ≠ 0) :
    integerVectorSpectralMeasure U x ≠ 0 := by
  intro h
  have he := integral_fourier_integerVectorSpectralMeasure U x 0
  rw [h, integral_zero_measure] at he
  change 0 = ⟪x, U 1 x⟫_ℂ at he
  rw [map_one] at he
  exact hx (inner_self_eq_zero.mp he.symm)

/-- Parry's criterion at the representation level. If all circle modulations
are implemented by unitaries, a nonzero representation has maximal spectral
type equal to the Lebesgue measure class. -/
theorem integer_maximalSpectralType_haar_of_modulations [SeparableSpace H] [Nontrivial H]
    (hMod : ∀ s : 𝕋, ∃ B : H ≃ₗᵢ[ℂ] H, ∀ (n : ℤ) (x : H),
      U (Multiplicative.ofAdd n) (B x) = fourier n s • B (U (Multiplicative.ofAdd n) x)) :
    ∃ x : H, IsMaximalSpectralVector U x ∧
      integerVectorSpectralMeasure U x ≪ haar ∧ haar ≪ integerVectorSpectralMeasure U x := by
  obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector U
  have hNZ : integerVectorSpectralMeasure U x ≠ 0 := by
    intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : H)
    have hc := integerVectorSpectralMeasure_absolutelyContinuous_of_maximal U x hx y
    rw [h] at hc
    exact integerVectorSpectralMeasure_ne_zero U y hy (by simpa using hc)
  refine ⟨x, hx, circleMeasure_equivalent_haar_of_rotation_absolutelyContinuous _ hNZ (fun s => ?_)⟩
  obtain ⟨B, hB⟩ := hMod s
  rw [← integerVectorSpectralMeasure_eq_rotate_of_modulation U s B hB x]
  exact integerVectorSpectralMeasure_absolutelyContinuous_of_maximal U x hx (B x)

end Representation

end Mixing
