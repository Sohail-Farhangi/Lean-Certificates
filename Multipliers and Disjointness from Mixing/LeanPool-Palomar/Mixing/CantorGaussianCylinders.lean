/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorGaussianCore
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Moments.CovarianceBilinDual

/-! # Cylindrical Gaussian characteristic functions for Example 5 -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter WithLp
open scoped BigOperators ProbabilityTheory Topology

namespace Mixing

/-- The characteristic-function test of a finite collection of path coordinates. -/
noncomputable def gaussianCylChar {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (a : ι → ℝ) (x : ℤ → ℝ) : ℂ :=
  Complex.exp (((∑ i, a i * x (j i) : ℝ) : ℂ) * Complex.I)

/-- Coordinate covariance of the cylindrical linear functional. -/
noncomputable def gaussianCylQuadratic {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ k, a i * a k * example5GaussianCovariance (j i - j k)

/-- Every finite-coordinate character has the characteristic expectation prescribed by the
Gaussian covariance, allowing repeated time indices. -/
theorem example5GaussianCylChar_integral {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (a : ι → ℝ) :
    (∫ x, gaussianCylChar j a x ∂example5GaussianMeasure) =
      Complex.exp (-((gaussianCylQuadratic j a : ℝ) : ℂ) / 2) := by
  classical
  let I := Finset.univ.image j
  let k : ι → I := fun i ↦ ⟨j i, Finset.mem_image_of_mem j (Finset.mem_univ i)⟩
  let S : Matrix I I ℝ := Matrix.of fun m n : I ↦ example5GaussianCovariance ((m : ℤ) - (n : ℤ))
  let ρ := multivariateGaussian (0 : EuclideanSpace ℝ I) S
  let R : EuclideanSpace ℝ I →L[ℝ] ℝ := ∑ i, a i • EuclideanSpace.proj (k i)
  have hR (w : EuclideanSpace ℝ I) : R w = ∑ i, a i * w (k i) := by
    simp [R, smul_eq_mul]
  have hI : MeasurePreserving (fun x : ℤ → ℝ ↦ toLp 2 (I.restrict x)) example5GaussianMeasure ρ :=
    example5Gaussian_euclidean_marginal I
  have hM : MemLp id 2 ρ := IsGaussian.memLp_two_id
  have ha (i : ι) : MemLp (fun x : EuclideanSpace ℝ I ↦ a i * x (k i)) 2 ρ :=
    ((IsGaussian.hasGaussianLaw_id.map_fun (EuclideanSpace.proj (k i))).memLp_two).const_mul (a i)
  have hCov : covarianceBilinDual ρ R R = gaussianCylQuadratic j a := by
    rw [covarianceBilinDual_eq_covariance hM]
    have hFun : (R : EuclideanSpace ℝ I → ℝ) = fun w ↦ ∑ i, a i * w (k i) := funext hR
    rw [hFun, covariance_fun_sum_fun_sum ha ha]
    unfold gaussianCylQuadratic
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right]
    change a i * (a l * cov[fun w ↦ w (k i), fun w ↦ w (k l);
      multivariateGaussian (0 : EuclideanSpace ℝ I) S]) = _
    rw [covariance_eval_multivariateGaussian (example5GaussianCovariance_psd I)]
    change a i * (a l * example5GaussianCovariance (j i - j l)) = _
    ring
  have hMean : R (∫ x, x ∂ρ) = 0 := by
    unfold ρ
    rw [integral_id_multivariateGaussian, map_zero]
  have hChar := IsGaussian.charFunDual_eq' (μ := ρ) R
  change charFunDual ρ R =
    Complex.exp (((R (∫ x, x ∂ρ) : ℝ) : ℂ) * Complex.I -
      ((covarianceBilinDual ρ R R : ℝ) : ℂ) / 2) at hChar
  rw [hMean, hCov, Complex.ofReal_zero, zero_mul, zero_sub, ← neg_div] at hChar
  rw [← hChar, charFunDual_apply, ← hI.map_eq,
    integral_map hI.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  change gaussianCylChar j a x = Complex.exp ((R (toLp 2 (I.restrict x)) : ℂ) * Complex.I)
  rw [gaussianCylChar, hR]
  rfl

private theorem gaussianCylChar_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ) (x : ℤ → ℝ) :
    gaussianCylChar j a x * gaussianCylChar k b x =
      gaussianCylChar (Sum.elim j k) (Sum.elim a b) x := by
  simp [gaussianCylChar, Fintype.sum_sum_type, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem gaussianCylQuadratic_join {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ) (n : ℤ) :
    gaussianCylQuadratic (Sum.elim j (fun l ↦ k l + n)) (Sum.elim a b) =
      gaussianCylQuadratic j a + gaussianCylQuadratic k b +
        (∑ i, ∑ l, a i * b l * example5GaussianCovariance (n + (k l - j i))) +
        ∑ l, ∑ i, b l * a i * example5GaussianCovariance (n + (k l - j i)) := by
  simp only [gaussianCylQuadratic, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib, add_sub_add_right_eq_sub]
  have hf (i : ι) (l : κ) :
      example5GaussianCovariance (j i - (k l + n)) =
        example5GaussianCovariance (n + (k l - j i)) := by
    rw [show j i - (k l + n) = -(n + (k l - j i)) by omega, example5GaussianCovariance_even]
  have hr (i : ι) (l : κ) : k l + n - j i = n + (k l - j i) := by omega
  simp_rw [hf, hr]
  ac_rfl

/-- Images of finite-coordinate characteristic tests have independent limits along the
ultrafilter in Example 5. This is the Gaussian cylinder correlation calculation. -/
theorem example5Gaussian_cylindrical_correlations {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun l : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^l)) ∈ p) :
    Tendsto (fun g : Multiplicative ℤ ↦
      ∫ x, gaussianCylChar j a x * gaussianCylChar k b (example5GaussianSystem.act g x)
        ∂example5GaussianMeasure)
      (p : Filter (Multiplicative ℤ)) (𝓝 (
        (∫ x, gaussianCylChar j a x ∂example5GaussianMeasure) *
          ∫ x, gaussianCylChar k b x ∂example5GaussianMeasure)) := by
  have hShift (g : Multiplicative ℤ) (x : ℤ → ℝ) :
      gaussianCylChar k b (example5GaussianSystem.act g x) =
        gaussianCylChar (fun l ↦ k l + g.toAdd) b x := rfl
  simp_rw [hShift, gaussianCylChar_mul, example5GaussianCylChar_integral, gaussianCylQuadratic_join]
  have h1 : Tendsto (fun g : Multiplicative ℤ ↦
      ∑ i, ∑ l, a i * b l * example5GaussianCovariance (g.toAdd + (k l - j i)))
      (p : Filter (Multiplicative ℤ)) (𝓝 0) := by
    rw [← Finset.sum_const_zero]
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    rw [← Finset.sum_const_zero]
    refine tendsto_finsetSum _ fun l _ ↦ ?_
    simpa only [mul_zero] using (tendsto_const_nhds (x := a i * b l)).mul
      (example5GaussianCovariance_tendsto_zero (k l - j i) p hp hsupp)
  have h2 : Tendsto (fun g : Multiplicative ℤ ↦
      ∑ l, ∑ i, b l * a i * example5GaussianCovariance (g.toAdd + (k l - j i)))
      (p : Filter (Multiplicative ℤ)) (𝓝 0) := by
    rw [← Finset.sum_const_zero]
    refine tendsto_finsetSum _ fun l _ ↦ ?_
    rw [← Finset.sum_const_zero]
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    simpa only [mul_zero] using (tendsto_const_nhds (x := b l * a i)).mul
      (example5GaussianCovariance_tendsto_zero (k l - j i) p hp hsupp)
  have h := ((tendsto_const_nhds (x := gaussianCylQuadratic j a + gaussianCylQuadratic k b)).add h1).add h2
  have hc : Continuous (fun s : ℝ ↦ Complex.exp (-(s : ℂ) / 2)) := by fun_prop
  have hc' := (hc.tendsto _).comp h
  have he (c d : ℝ) : Complex.exp (-((c + d : ℝ) : ℂ) / 2) =
      Complex.exp (-(c : ℂ) / 2) * Complex.exp (-(d : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [add_zero, add_zero, he] at hc'
  exact hc'

end Mixing
