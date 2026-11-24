/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrencePolar
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

namespace SixProblems.Gaussian

noncomputable section

open MeasureTheory ProbabilityTheory Set Real Matrix WithLp
open scoped ENNReal Real RealInnerProductSpace Matrix

/-- Applying a matrix to a standard Gaussian gives covariance `A * Aᴴ`.
    The proof does not require the matrix to be invertible. -/
theorem map_stdGaussian_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (Matrix.toEuclideanCLM (𝕜 := ℝ) A) =
      multivariateGaussian (0 : EuclideanSpace ℝ ι) (A * Aᴴ) := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  change (stdGaussian (EuclideanSpace ℝ ι)).map L = _
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map, integral_id_stdGaussian, map_zero,
      integral_id_multivariateGaussian]
    exact IsGaussian.integrable_id
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  have hAdj : L.adjoint = Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ :=
    (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ)) A).symm
  calc
    _ = ⟪L.adjoint x, L.adjoint y⟫ := by
      rw [covarianceBilin_map IsGaussian.memLp_two_id L, covarianceBilin_stdGaussian,
        innerSL_apply_apply]
    _ = ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) (A*Aᴴ)) y⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_left, map_mul, mul_apply_eq_comp, ← hAdj]
    _ = _ := by
      rw [Matrix.inner_toEuclideanCLM,
        covarianceBilin_multivariateGaussian (Matrix.posSemidef_self_mul_conjTranspose A)]

private def pairToEuclidean (x : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).symm x)

private theorem pairToEuclidean_preserving :
    MeasurePreserving pairToEuclidean standardPlane (stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have h₁ : MeasurePreserving e (Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1)) standardPlane :=
    measurePreserving_piFinTwo _
  have h₂ : MeasurePreserving (toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
      (Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1)) (stdGaussian _) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact h₂.comp h₁.symm

@[simp] private theorem pairToEuclidean_zero (x : ℝ × ℝ) : pairToEuclidean x 0 = x.1 := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  exact congrArg Prod.fst (e.apply_symm_apply x)

@[simp] private theorem pairToEuclidean_one (x : ℝ × ℝ) : pairToEuclidean x 1 = x.2 := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  exact congrArg Prod.snd (e.apply_symm_apply x)

private theorem standardPlane_neg_preserving :
    MeasurePreserving (fun x : ℝ × ℝ ↦ (-x.1, -x.2)) standardPlane standardPlane := by
  have hn : MeasurePreserving (fun z : ℝ ↦ -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
  exact hn.prod hn

private theorem standardPlane_product_positive (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ π) :
    (standardPlane {x | 0 < x.1 * (cos α * x.1 + sin α * x.2)}).toReal = (π - α) / π := by
  let E : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2}
  let N : ℝ × ℝ → ℝ × ℝ := fun x ↦ (-x.1, -x.2)
  have hm : MeasurableSet E := (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_const ((measurable_fst.const_mul _).add (measurable_snd.const_mul _)))
  have hN : MeasurableSet (N ⁻¹' E) := hm.preimage standardPlane_neg_preserving.measurable
  have hd : Disjoint E (N ⁻¹' E) := Set.disjoint_left.mpr (fun x hx hy ↦ by
    have h1 : 0 < x.1 := hx.1
    have h2 : 0 < -x.1 := hy.1
    linarith)
  have hU : {x : ℝ × ℝ | 0 < x.1 * (cos α * x.1 + sin α * x.2)} = E ∪ N ⁻¹' E := by
    ext x
    change 0 < x.1 * (cos α * x.1 + sin α * x.2) ↔
      (0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2) ∨
      (0 < -x.1 ∧ 0 < cos α * (-x.1) + sin α * (-x.2))
    rw [mul_pos_iff]
    simp only [neg_pos, mul_neg, ← neg_add_rev, add_comm (sin α * x.2)]
  rw [hU, measure_union hd hN,
    standardPlane_neg_preserving.measure_preimage hm.nullMeasurableSet, ENNReal.toReal_add
      (measure_ne_top standardPlane E) (measure_ne_top standardPlane E),
    show (standardPlane E).toReal = _ from standardPlane_positive_wedge α hα₀ hα₁]
  ring

/-- Lemma 5.2 (Sheppard's formula), including both singular endpoint covariances. -/
theorem lemma5_2 (a b d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hS : (!![a,b; b,d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![a,b; b,d])
      {x | 0 < x 0 * x 1}).toReal = 1/2 + (1/π) * arcsin (b / √(a*d)) := by
  let A₀ : Matrix (Fin 2) (Fin 2) ℝ := !![a,b; b,d]
  let t := √(a*d)
  let r := b/t
  let α := arccos r
  have ht : 0 < t := sqrt_pos.mpr (mul_pos ha hd)
  have hdet : 0 ≤ a*d - b*b := by
    simpa only [Matrix.det_fin_two_of] using hS.det_nonneg
  have hbb : b^2 ≤ a*d := by nlinarith only [hdet]
  have habs : |b| ≤ t := by
    rw [← sqrt_sq_eq_abs]
    exact sqrt_le_sqrt hbb
  have hr : |r| ≤ 1 := by
    change |b/t| ≤ 1
    rw [abs_div, abs_of_pos ht, div_le_iff₀ ht, one_mul]
    exact habs
  have hα₀ : 0 ≤ α := arccos_nonneg r
  have hα₁ : α ≤ π := arccos_le_pi r
  have hcos : cos α = r := cos_arccos (abs_le.mp hr).1 (abs_le.mp hr).2
  have hAB : √a * (√d * cos α) = b := by
    rw [← mul_assoc, ← sqrt_mul ha.le, hcos]
    change t * (b/t) = b
    field_simp
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![√a,0; √d * cos α, √d * sin α]
  have hA : A*Aᴴ = A₀ := by
    ext i j
    fin_cases i <;> fin_cases j
      <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        star_trivial]
    · change √a * √a + 0*0 = a
      rw [mul_zero, add_zero, mul_self_sqrt ha.le]
    · change √a * (√d * cos α) + 0 * (√d * sin α) = b
      rw [zero_mul, add_zero, hAB]
    · change (√d * cos α) * √a + (√d * sin α) * 0 = b
      rw [mul_comm _ (√a), mul_zero, add_zero, hAB]
    · change (√d * cos α)*(√d * cos α) + (√d * sin α)*(√d * sin α) = d
      calc
        _ = √d * √d * (cos α ^ 2 + sin α ^ 2) := by ring
        _ = d := by rw [cos_sq_add_sin_sq, mul_one, mul_self_sqrt hd.le]
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let P : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := L ∘ pairToEuclidean
  have hmap : MeasurePreserving P standardPlane (multivariateGaussian 0 A₀) :=
    (show MeasurePreserving L (stdGaussian _) (multivariateGaussian 0 A₀) from
      ⟨L.continuous.measurable, by rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) A from rfl,
        map_stdGaussian_matrix, hA]⟩).comp pairToEuclidean_preserving
  have hx (z : ℝ × ℝ) : P z 0 = √a * z.1 := by
    change (L (toLp 2 ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).symm z))) 0 = _
    rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) A from rfl, Matrix.toEuclideanCLM_toLp]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A]
  have hy (z : ℝ × ℝ) : P z 1 = √d * (cos α * z.1 + sin α * z.2) := by
    change (L (toLp 2 ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).symm z))) 1 = _
    rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) A from rfl, Matrix.toEuclideanCLM_toLp]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A, mul_add, mul_assoc]
  let F : Set (EuclideanSpace ℝ (Fin 2)) := {x | 0 < x 0 * x 1}
  have hF : MeasurableSet F := measurableSet_lt measurable_const
    (((EuclideanSpace.proj 0).continuous.measurable).mul ((EuclideanSpace.proj 1).continuous.measurable))
  change ((multivariateGaussian 0 A₀) F).toReal = _
  rw [← hmap.map_eq, Measure.map_apply hmap.measurable hF]
  have hEq : P ⁻¹' F = {x | 0 < x.1 * (cos α * x.1 + sin α * x.2)} := by
    ext z
    change 0 < P z 0 * P z 1 ↔ _
    rw [hx, hy, mul_mul_mul_comm, mul_pos_iff_of_pos_left (mul_pos (sqrt_pos.mpr ha) (sqrt_pos.mpr hd))]
    rfl
  rw [hEq, standardPlane_product_positive α hα₀ hα₁]
  change (π - arccos r) / π = _
  rw [arccos_eq_pi_div_two_sub_arcsin]
  have hne : π ≠ 0 := pi_pos.ne'
  change (π - (π/2 - arcsin r)) / π = 1/2 + (1/π) * arcsin r
  field_simp
  ring

end

end SixProblems.Gaussian
