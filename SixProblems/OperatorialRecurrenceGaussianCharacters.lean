/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrenceGaussian
public import Mathlib.Probability.Distributions.Gaussian.CharFun

@[expose] public section

namespace SixProblems.Gaussian

noncomputable section

open Filter MeasureTheory ProbabilityTheory WithLp Matrix
open scoped Classical Topology RealInnerProductSpace

variable {G : Type*}

/-- The characteristic-function test of a finite collection of path coordinates. -/
def gaussianCylChar {ι : Type*} [Fintype ι]
    (j : ι → G) (a : ι → ℝ) (x : G → ℝ) : ℂ :=
  Complex.exp (((∑ i, a i * x (j i) : ℝ) : ℂ) * Complex.I)

theorem continuous_gaussianCylChar {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) :
    Continuous (gaussianCylChar j a) := by
  unfold gaussianCylChar
  fun_prop

theorem measurable_gaussianCylChar {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) :
    Measurable (gaussianCylChar j a) := by
  unfold gaussianCylChar
  fun_prop

theorem norm_gaussianCylChar {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) (x : G → ℝ) :
    ‖gaussianCylChar j a x‖ = 1 := by
  simp [gaussianCylChar, Complex.norm_exp, Complex.mul_re]

variable [Group G] [Countable G] (φ : G → ℝ) (hφ : RealPositiveDefinite φ)

/-- The variance associated to a finite Gaussian test. -/
def quadratic {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ k, a i * a k * φ ((j i)⁻¹ * j k)

theorem gaussianCylChar_integral {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) :
    (∫ x, gaussianCylChar j a x ∂gaussianPathMeasure φ hφ) =
      Complex.exp (-(quadratic φ j a : ℂ) / 2) := by
  let C : Matrix ι ι ℝ := Matrix.of fun i k ↦ φ ((j i)⁻¹ * j k)
  let a₂ : EuclideanSpace ℝ ι := toLp 2 a
  let ρ := multivariateGaussian (0 : EuclideanSpace ℝ ι) C
  have hC : C.PosSemidef := Gaussian.kernel_posSemidef_tuple
    (fun i k : G ↦ φ (i⁻¹ * k)) (groupCovariance_posSemidef φ hφ) j
  have hQ : a₂ ⬝ᵥ C *ᵥ a₂ = quadratic φ j a := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, quadratic, C, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by
      change a i * (φ ((j i)⁻¹ * j k) * a k) = _
      ring
  have hChar := charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hC a₂
  change charFun ρ a₂ = _ at hChar
  rw [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, hQ, ← neg_div] at hChar
  have hI := gaussianPath_tuple φ hφ j
  change MeasurePreserving _ _ ρ at hI
  rw [← hChar, charFun_apply, ← hI.map_eq,
    integral_map hI.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  simp [gaussianCylChar, PiLp.inner_apply, a₂]

omit [Group G] [Countable G] in
theorem gaussianCylChar_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → G) (a : ι → ℝ) (k : κ → G) (b : κ → ℝ) (x : G → ℝ) :
    gaussianCylChar j a x * gaussianCylChar k b x =
      gaussianCylChar (Sum.elim j k) (Sum.elim a b) x := by
  simp [gaussianCylChar, Fintype.sum_sum_type, Complex.ofReal_add, add_mul, Complex.exp_add]

include hφ in
omit [Countable G] in
private theorem quadratic_join {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → G) (a : ι → ℝ) (k : κ → G) (b : κ → ℝ) (g : G) :
    quadratic φ (Sum.elim j (fun l ↦ g⁻¹ * k l)) (Sum.elim a b) =
      quadratic φ j a + quadratic φ k b +
        (∑ i, ∑ l, a i * b l * φ ((j i)⁻¹ * g⁻¹ * k l)) +
        ∑ l, ∑ i, b l * a i * φ ((j i)⁻¹ * g⁻¹ * k l) := by
  have h₁ (i : ι) (l : κ) : φ ((g⁻¹ * k l)⁻¹ * j i) = φ ((j i)⁻¹ * g⁻¹ * k l) := by
    rw [← hφ.inv_eq ((j i)⁻¹ * g⁻¹ * k l)]
    simp [mul_assoc]
  have h₂ (i l : κ) : (g⁻¹ * k i)⁻¹ * (g⁻¹ * k l) = (k i)⁻¹ * k l := by group
  simp only [quadratic, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib,
    h₁, h₂]
  simp only [mul_assoc]
  ac_rfl

/-- Vanishing cross covariances yield independence in the limit for finite characteristic
    tests on the Gaussian path. -/
theorem gaussianCylChar_mul_shift_tendsto {ι κ J : Type*} [Fintype ι] [Fintype κ]
    (j : ι → G) (a : ι → ℝ) (k : κ → G) (b : κ → ℝ) (g : J → G) (L : Filter J)
    (hCov : ∀ r s : G, Tendsto (fun z ↦ φ (r * (g z)⁻¹ * s)) L (𝓝 0)) :
    Tendsto (fun z ↦ ∫ x, gaussianCylChar j a x *
      gaussianCylChar k b (gaussianShift (g z) x) ∂gaussianPathMeasure φ hφ) L
      (𝓝 ((∫ x, gaussianCylChar j a x ∂gaussianPathMeasure φ hφ) *
        (∫ x, gaussianCylChar k b x ∂gaussianPathMeasure φ hφ))) := by
  simp_rw [show ∀ (z : J) (x : G → ℝ),
    gaussianCylChar k b (gaussianShift (g z) x) =
      gaussianCylChar (fun l ↦ (g z)⁻¹ * k l) b x from fun _ _ ↦ rfl,
    gaussianCylChar_mul, gaussianCylChar_integral, quadratic_join φ hφ]
  have h₁ : Tendsto (fun z ↦ ∑ i, ∑ l, a i * b l * φ ((j i)⁻¹ * (g z)⁻¹ * k l))
      L (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ ↦ tendsto_finsetSum Finset.univ
        (fun l _ ↦ (tendsto_const_nhds (x := a i * b l)).mul (hCov (j i)⁻¹ (k l))))
  have h₂ : Tendsto (fun z ↦ ∑ l, ∑ i, b l * a i * φ ((j i)⁻¹ * (g z)⁻¹ * k l))
      L (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun l _ ↦ tendsto_finsetSum Finset.univ
        (fun i _ ↦ (tendsto_const_nhds (x := b l * a i)).mul (hCov (j i)⁻¹ (k l))))
  rw [← Complex.exp_add]
  have ht := ((show Continuous (fun s : ℝ ↦ Complex.exp (-(s : ℂ) / 2)) by fun_prop).tendsto
    (quadratic φ j a + quadratic φ k b + 0 + 0)).comp
      (((tendsto_const_nhds (x := quadratic φ j a + quadratic φ k b)).add h₁).add h₂)
  have he : Complex.exp (-(quadratic φ j a : ℂ) / 2 + -(quadratic φ k b : ℂ) / 2) =
      Complex.exp (-((quadratic φ j a + quadratic φ k b : ℝ) : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  simpa only [Function.comp_def, he, add_zero] using ht

end

end SixProblems.Gaussian
