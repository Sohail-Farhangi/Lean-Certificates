/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace SixProblems.Gaussian

noncomputable section

open MeasureTheory ProbabilityTheory Set Real ENNReal
open scoped ENNReal Real

/-- The joint law of two independent standard real Gaussians. -/
def standardPlane : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure standardPlane := by
  unfold standardPlane
  infer_instance

private def planeDensity (x : ℝ × ℝ) : ℝ≥0∞ := gaussianPDF 0 1 x.1 * gaussianPDF 0 1 x.2

private theorem standardPlane_eq_density : standardPlane = volume.withDensity planeDensity := by
  unfold standardPlane
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  rfl

private theorem planeDensity_polar (r θ : ℝ) :
    planeDensity (polarCoord.symm (r, θ)) = planeDensity (r, 0) := by
  simp only [planeDensity, polarCoord_symm_apply, gaussianPDF, gaussianPDFReal_def,
    NNReal.coe_one, mul_one, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div, neg_zero, Real.exp_zero]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_mul_mul_comm, ← Real.exp_add, mul_right_comm]
  have hsq : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
    linear_combination r^2 * (cos_sq_add_sin_sq θ)
  have he : -(r * cos θ) ^ 2 / 2 + -(r * sin θ) ^ 2 / 2 = -r ^ 2 / 2 := by linarith
  rw [he]

private def radialMass : ℝ≥0∞ := ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * planeDensity (r, 0)

private theorem sector_mass_factor {E : Set (ℝ × ℝ)} {A : Set ℝ}
    (hE : MeasurableSet E) (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (-π) π)
    (hSector : ∀ r > 0, ∀ θ ∈ Ioo (-π) π, polarCoord.symm (r, θ) ∈ E ↔ θ ∈ A) :
    standardPlane E = radialMass * volume A := by
  rw [standardPlane_eq_density, withDensity_apply _ hE, ← lintegral_indicator hE,
    ← lintegral_comp_polarCoord_symm]
  let f (r : ℝ) := ENNReal.ofReal r * planeDensity (r, 0)
  let g : ℝ → ℝ≥0∞ := A.indicator fun _ ↦ 1
  have hf : Measurable f := by
    change Measurable fun r ↦ ENNReal.ofReal r * (gaussianPDF 0 1 r * gaussianPDF 0 1 0)
    exact measurable_ofReal.mul ((measurable_gaussianPDF 0 1).mul measurable_const)
  have hg : Measurable g := measurable_const.indicator hA
  rw [polarCoord_target]
  calc
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, f p.1 * g p.2 := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      rintro ⟨r, θ⟩ ⟨hr, hθ⟩
      change ENNReal.ofReal r * E.indicator planeDensity (polarCoord.symm (r, θ)) = f r * g θ
      by_cases hθA : θ ∈ A
      · simp only [indicator_of_mem ((hSector r hr θ hθ).mpr hθA), f, g, indicator_of_mem hθA,
          mul_one, planeDensity_polar]
      · have hn : polarCoord.symm (r, θ) ∉ E := fun h ↦ hθA ((hSector r hr θ hθ).mp h)
        simp only [indicator_of_notMem hn, g, indicator_of_notMem hθA, mul_zero]
    _ = _ := by
      change (∫⁻ p : ℝ × ℝ, f p.1 * g p.2 ∂((volume : Measure ℝ).prod volume).restrict
        (Ioi 0 ×ˢ Ioo (-π) π)) = _
      rw [← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable hg.aemeasurable]
      have hAz : (∫⁻ θ in Ioo (-π) π, g θ) = volume A := by
        rw [show g = A.indicator (fun _ ↦ 1) from rfl, lintegral_indicator hA, lintegral_const,
          one_mul, Measure.restrict_restrict_of_subset hAsub, Measure.restrict_apply_univ]
      rw [hAz]
      rfl

private theorem radialMass_normalized : radialMass.toReal * (2 * π) = 1 := by
  have h := sector_mass_factor (E := univ) (A := Ioo (-π) π) MeasurableSet.univ
    measurableSet_Ioo (Subset.refl _) (fun _ _ _ hθ ↦ iff_of_true (mem_univ _) hθ)
  rw [measure_univ, Real.volume_Ioo, show π - -π = 2 * π by ring] at h
  have he := congrArg ENNReal.toReal h.symm
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_one] at he

/-- The angular part of a standard planar Gaussian is uniform on its full circle. -/
theorem standardPlane_sector {E : Set (ℝ × ℝ)} {A : Set ℝ}
    (hE : MeasurableSet E) (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (-π) π)
    (hSector : ∀ r > 0, ∀ θ ∈ Ioo (-π) π, polarCoord.symm (r, θ) ∈ E ↔ θ ∈ A) :
    (standardPlane E).toReal = (volume A).toReal / (2 * π) := by
  rw [sector_mass_factor hE hA hAsub hSector, ENNReal.toReal_mul,
    eq_div_iff (show 2 * π ≠ 0 by positivity), mul_right_comm, radialMass_normalized, one_mul]

private theorem cos_pos_iff_of_angle_range {θ : ℝ} (hl : -(π + π/2) ≤ θ) (hu : θ ≤ π + π/2) :
    0 < cos θ ↔ θ ∈ Ioo (-(π/2)) (π/2) := by
  constructor
  · intro h
    constructor
    · by_contra! ht
      have hn := cos_nonpos_of_pi_div_two_le_of_le (show π / 2 ≤ -θ by linarith) (by linarith : -θ ≤ π+π/2)
      rw [cos_neg] at hn
      linarith
    · by_contra! ht
      linarith [cos_nonpos_of_pi_div_two_le_of_le ht hu]
  · exact fun h ↦ cos_pos_of_mem_Ioo h

/-- The probability that a standard Gaussian lies in the two indicated positive
    half-planes is the angle between their boundary rays divided by `2π`. -/
theorem standardPlane_positive_wedge (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ π) :
    (standardPlane {x | 0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2}).toReal =
      (π - α) / (2 * π) := by
  have hm : MeasurableSet {x : ℝ × ℝ | 0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const ((measurable_fst.const_mul _).add (measurable_snd.const_mul _)))
  rw [standardPlane_sector (A := Ioo (α-π/2) (π/2)) hm measurableSet_Ioo]
  · rw [Real.volume_Ioo, show π/2 - (α-π/2) = π-α by ring,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hα₁)]
  · intro θ hθ
    exact ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2, pi_pos]⟩
  · intro r hr θ hθ
    change (0 < r * cos θ ∧ 0 < cos α * (r * cos θ) + sin α * (r * sin θ)) ↔ _
    have he : cos α * (r * cos θ) + sin α * (r * sin θ) = r * cos (θ - α) := by
      rw [cos_sub]
      ring
    rw [he, mul_pos_iff_of_pos_left hr, mul_pos_iff_of_pos_left hr,
      cos_pos_iff_of_angle_range (by linarith [hθ.1, pi_pos]) (by linarith [hθ.2, pi_pos])]
    constructor
    · rintro ⟨ht, hs⟩
      rw [cos_pos_iff_of_angle_range (by linarith [ht.1]) (by linarith [ht.2, pi_pos])] at hs
      exact ⟨by linarith [hs.1], ht.2⟩
    · intro h
      have ht : θ ∈ Ioo (-(π/2)) (π/2) := ⟨by linarith [h.1], h.2⟩
      refine ⟨ht, ?_⟩
      apply cos_pos_of_mem_Ioo
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

end

end SixProblems.Gaussian
