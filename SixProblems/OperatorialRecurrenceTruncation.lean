/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrenceGaussian
public import SixProblems.Definitions
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

namespace SixProblems

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter WithLp
open scoped Classical Topology ProbabilityTheory ComplexConjugate

private def truncateGaussian (n : ℕ) (x : ℝ) : ℝ := (Icc (-(n : ℝ)) n).indicator id x

private theorem measurable_truncateGaussian (n : ℕ) : Measurable (truncateGaussian n) :=
  measurable_id.indicator measurableSet_Icc

private theorem truncateGaussian_odd (n : ℕ) (x : ℝ) : truncateGaussian n (-x) = -truncateGaussian n x := by
  have he : -x ∈ Icc (-(n : ℝ)) n ↔ x ∈ Icc (-(n : ℝ)) n := by
    rw [mem_Icc, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hx : x ∈ Icc (-(n : ℝ)) n
  · simp [truncateGaussian, hx, he.mpr hx]
  · have hnx : -x ∉ Icc (-(n : ℝ)) n := fun h ↦ hx (he.mp h)
    rw [truncateGaussian, truncateGaussian, indicator_of_notMem hnx, indicator_of_notMem hx, neg_zero]

private theorem abs_truncateGaussian_le (n : ℕ) (x : ℝ) : |truncateGaussian n x| ≤ |x| := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) n
  · simp [truncateGaussian, hx]
  · simp [truncateGaussian, hx]

private theorem abs_truncateGaussian_le_nat (n : ℕ) (x : ℝ) : |truncateGaussian n x| ≤ n := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) n
  · simpa [truncateGaussian, hx] using abs_le.mpr hx
  · simp [truncateGaussian, hx]

private theorem eventually_truncateGaussian_eq (x : ℝ) : ∀ᶠ n : ℕ in atTop, truncateGaussian n x = x := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : |x| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  simp [truncateGaussian, abs_le.mp hx]

theorem integral_comp_preserving {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) {g : β → E} (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hm : AEStronglyMeasurable g (μ.map f) := hf.map_eq.symm ▸ hg
  rw [← hf.map_eq, integral_map hf.measurable.aemeasurable hm]

variable {G : Type} [Group G] [Countable G]

private theorem truncateGaussian_mean (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (n : ℕ) :
    (∫ x, truncateGaussian n (x (1 : G)) ∂(gaussianPathMeasure φ hφ)) = 0 := by
  let ν := gaussianReal 0 (φ 1).toNNReal
  have hn : MeasurePreserving (fun x : ℝ ↦ -x) ν ν :=
    ⟨measurable_neg, by simp [ν, gaussianReal_map_neg]⟩
  rw [integral_comp_preserving (gaussianPath_coordinate_law φ hφ 1)
    (measurable_truncateGaussian n).aestronglyMeasurable]
  have h := integral_comp_preserving hn (measurable_truncateGaussian n).aestronglyMeasurable
  simp_rw [truncateGaussian_odd, integral_neg] at h
  linarith

/-- Truncated-coordinate correlations depend only on the covariance of the Gaussian pair. -/
private theorem truncateGaussian_corr_eq (φ : G → ℝ) (hφ : RealPositiveDefinite φ)
    (n : ℕ) {g h : G} (he : φ g = φ h) :
    (∫ x, truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1) ∂(gaussianPathMeasure φ hφ)) =
      ∫ x, truncateGaussian n (x h⁻¹) * truncateGaussian n (x 1) ∂(gaussianPathMeasure φ hφ) := by
  let a (j : G) : Bool → G := fun i ↦ if i then j⁻¹ else 1
  let k (x : EuclideanSpace ℝ Bool) := truncateGaussian n (x true) * truncateGaussian n (x false)
  have hk : Measurable k :=
    ((measurable_truncateGaussian n).comp (EuclideanSpace.proj true).continuous.measurable).mul
      ((measurable_truncateGaussian n).comp (EuclideanSpace.proj false).continuous.measurable)
  have hc (j : G) : (∫ x, truncateGaussian n (x j⁻¹) * truncateGaussian n (x 1)
      ∂(gaussianPathMeasure φ hφ)) = ∫ x, k x ∂multivariateGaussian 0
        (Matrix.of fun i l ↦ φ ((a j i)⁻¹ * a j l)) := by
    simpa only [k, a, ite_true, ite_false, Bool.false_eq_true] using
      integral_comp_preserving (gaussianPath_tuple φ hφ (a j)) hk.aestronglyMeasurable
  rw [hc g, hc h]
  have hm : (Matrix.of fun i j ↦ φ ((a g i)⁻¹ * a g j)) =
      (Matrix.of fun i j ↦ φ ((a h i)⁻¹ * a h j)) := by
    ext i j
    cases i <;> cases j <;> simp [a, hφ.inv_eq, he]
  rw [hm]

private theorem truncateGaussian_corr_tendsto (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (g : G) :
    Tendsto (fun n ↦ ∫ x, truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1)
      ∂(gaussianPathMeasure φ hφ)) atTop (𝓝 (φ g)) := by
  let μ := gaussianPathMeasure φ hφ
  have hv : (∫ x, x g⁻¹ * x 1 ∂μ) = φ g := by
    simpa only [inv_inv, mul_one] using gaussianPath_covariance φ hφ g⁻¹ 1
  rw [← hv]
  apply tendsto_integral_of_dominated_convergence (fun x : G → ℝ ↦ ‖x g⁻¹ * x 1‖)
  · intro n
    exact (((measurable_truncateGaussian n).comp (measurable_pi_apply _)).mul
      ((measurable_truncateGaussian n).comp (measurable_pi_apply _))).aestronglyMeasurable
  · exact ((gaussianPath_coordinate_memLp φ hφ g⁻¹).integrable_mul
      (gaussianPath_coordinate_memLp φ hφ 1)).norm
  · intro n
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_truncateGaussian_le n _) (abs_truncateGaussian_le n _)
      (abs_nonneg _) (abs_nonneg _)
  · filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_truncateGaussian_eq (x g⁻¹), eventually_truncateGaussian_eq (x 1)]
      with n h₁ h₂
    rw [h₁, h₂]

/-- Cutoff of the coordinate approximates its correlations uniformly in the
time parameter. If either coordinate lies outside the cutoff, the larger
squared coordinate lies outside and bounds the omitted product. -/
theorem gaussianPath_exists_bounded_centered_approximation
    (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (δ : ℝ) (hδ : 0 < δ) :
    let S := gaussianPathSystem φ hφ
    ∃ f : (G → ℝ) → ℝ, Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
      (∫ x, f x ∂S.measure) = 0 ∧ ∀ g,
        |(∫ x, f (S.act g x) * f x ∂S.measure) - φ g| < δ := by
  let S := gaussianPathSystem φ hφ
  let μ := gaussianPathMeasure φ hφ
  let tail (n : ℕ) (t : ℝ) : ℝ := (Icc (-(n : ℝ)) n)ᶜ.indicator (fun x ↦ x^2) t
  have hTailM (n : ℕ) : Measurable (tail n) :=
    (measurable_id.pow_const 2).indicator measurableSet_Icc.compl
  have hTailLe (n : ℕ) (t : ℝ) : ‖tail n t‖ ≤ t^2 := by
    by_cases ht : t ∈ Icc (-(n : ℝ)) n
    · simpa [tail, ht] using sq_nonneg t
    · simp [tail, ht, Real.norm_eq_abs]
  have hSq (j : G) : Integrable (fun x : G → ℝ ↦ (x j)^2) μ :=
    (gaussianPath_coordinate_memLp φ hφ j).integrable_sq
  have hlim : Tendsto (fun n ↦ ∫ x : G → ℝ, tail n (x 1) ∂μ) atTop (𝓝 0) := by
    rw [← integral_zero (α := G → ℝ) (G := ℝ) (μ := μ)]
    apply tendsto_integral_of_dominated_convergence (fun x : G → ℝ ↦ (x 1)^2)
    · intro n
      exact ((hTailM n).comp (measurable_pi_apply 1)).aestronglyMeasurable
    · exact hSq 1
    · exact fun n ↦ .of_forall fun x ↦ hTailLe n (x 1)
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      obtain ⟨N,hN⟩ := exists_nat_ge |x 1|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : |x 1| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      simp [tail, abs_le.mp hx]
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const (half_pos hδ)).exists
  let f (x : G → ℝ) := truncateGaussian n (x 1)
  refine ⟨f,(measurable_truncateGaussian n).comp (measurable_pi_apply 1),
    ⟨n,fun x ↦ abs_truncateGaussian_le_nat n (x 1)⟩,truncateGaussian_mean φ hφ n,?_⟩
  intro g
  have hCov : (∫ x : G → ℝ, x g⁻¹ * x 1 ∂μ) = φ g := by
    simpa only [inv_inv,mul_one] using gaussianPath_covariance φ hφ g⁻¹ 1
  have hPt (u v : ℝ) : |truncateGaussian n u * truncateGaussian n v - u*v| ≤ tail n u + tail n v := by
    by_cases hu : u ∈ Icc (-(n : ℝ)) n <;> by_cases hv : v ∈ Icc (-(n : ℝ)) n
    · simp [truncateGaussian,tail,hu,hv]
    · have hUV : |u| ≤ |v| := (abs_le.mpr hu).trans (lt_of_not_ge (fun h ↦ hv (abs_le.mp h))).le
      have hh := mul_le_mul_of_nonneg_right hUV (abs_nonneg v)
      simpa [truncateGaussian,tail,hu,hv,abs_mul,← sq, sq_abs] using hh
    · have hVU : |v| ≤ |u| := (abs_le.mpr hv).trans (lt_of_not_ge (fun h ↦ hu (abs_le.mp h))).le
      have hh := mul_le_mul_of_nonneg_left hVU (abs_nonneg u)
      simpa [truncateGaussian,tail,hu,hv,abs_mul,← sq, sq_abs] using hh
    · simp [truncateGaussian,tail,hu,hv,abs_mul]
      nlinarith [sq_nonneg (|u|-|v|),sq_abs u,sq_abs v,sq_nonneg u,sq_nonneg v]
  have hInt (j : G) : Integrable (fun x : G → ℝ ↦ tail n (x j)) μ :=
    (hSq j).mono' ((hTailM n).comp (measurable_pi_apply j)).aestronglyMeasurable
      (.of_forall fun x ↦ hTailLe n (x j))
  have hPres : (∫ x : G → ℝ, tail n (x g⁻¹) ∂μ) = ∫ x : G → ℝ, tail n (x 1) ∂μ := by
    have hp : (∫ x : G → ℝ, tail n ((S.act g x) 1) ∂S.measure) =
        ∫ x : G → ℝ, tail n (x 1) ∂S.measure :=
      integral_comp_preserving (S.preserves g) (g := fun x ↦ tail n (x 1)) ((hTailM n).comp
        (measurable_pi_apply (1 : G))).aestronglyMeasurable
    simpa only [S, gaussianPathSystem, gaussianShift, mul_one, μ] using hp
  have hCut (j : G) : MemLp (fun x : G → ℝ ↦ truncateGaussian n (x j)) 2 μ :=
    MemLp.of_bound ((measurable_truncateGaussian n).comp (measurable_pi_apply j)).aestronglyMeasurable
      n (.of_forall fun x ↦ abs_truncateGaussian_le_nat n (x j))
  change |(∫ x, truncateGaussian n (x (g⁻¹ * 1)) * truncateGaussian n (x 1) ∂μ) - φ g| < δ
  simp only [mul_one]
  have hCutInt : Integrable (fun x : G → ℝ ↦
      truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1)) μ :=
    (hCut g⁻¹).integrable_mul (hCut 1)
  have hBaseInt : Integrable (fun x : G → ℝ ↦ x g⁻¹ * x 1) μ :=
    (gaussianPath_coordinate_memLp φ hφ g⁻¹).integrable_mul (gaussianPath_coordinate_memLp φ hφ 1)
  rw [← hCov, ← integral_sub hCutInt hBaseInt]
  calc
    _ ≤ ∫ x : G → ℝ, ‖truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1) - x g⁻¹*x 1‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : G → ℝ, (tail n (x g⁻¹) + tail n (x 1)) ∂μ := by
      exact integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) ((hInt g⁻¹).fun_add (hInt 1))
        (ae_of_all _ fun x ↦ hPt (x g⁻¹) (x 1))
    _ < δ := by rw [integral_add (hInt g⁻¹) (hInt 1), hPres]; linarith

/-- A constant strictly negative positive-definite witness gives a bounded counterexample
    on its Gaussian shift. The Gaussian pair law makes the truncated correlations identical,
    so a single added constant cancels every correlation. -/
theorem not_vdC_of_negative_constant_real {H : Set G} (hne : H.Nonempty)
    (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (r : ℝ) (hr : r < 0)
    (hconst : ∀ h ∈ H, φ h = r) : ¬IsVdC H := by
  obtain ⟨g, hg⟩ := hne
  have hlim := truncateGaussian_corr_tendsto φ hφ g
  rw [hconst g hg] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hr).exists
  let S := gaussianPathSystem φ hφ
  let u : (G → ℝ) → ℝ := fun x ↦ truncateGaussian n (x 1)
  let b : ℝ := ∫ x, u (S.act g x) * u x ∂S.measure
  have hnegB : b < 0 := by
    simpa only [b, S, u, gaussianPathSystem, gaussianShift, mul_one] using hn
  let t := Real.sqrt (-b)
  have ht : 0 < t := Real.sqrt_pos.2 (neg_pos.mpr hnegB)
  let f : (G → ℝ) → ℂ := fun x ↦ ((u x+t : ℝ) : ℂ)
  have hu : Measurable u := (measurable_truncateGaussian n).comp (measurable_pi_apply 1)
  have hμ : Integrable u S.measure := Integrable.of_bound hu.aestronglyMeasurable (n : ℝ)
    (.of_forall fun x ↦ abs_truncateGaussian_le_nat n (x 1))
  have hm : (∫ x, u x ∂S.measure) = 0 := truncateGaussian_mean φ hφ n
  have hf : Measurable f := Complex.continuous_ofReal.measurable.comp (hu.add measurable_const)
  have hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨(n : ℝ) + t, fun x ↦ by
    change ‖((u x+t : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact (abs_add_le _ _).trans (add_le_add (abs_truncateGaussian_le_nat n (x 1))
      (le_of_eq (abs_of_pos ht)))⟩
  intro hV
  have hz := hV S f hf hb (fun h hh ↦ ?_)
  · change (∫ x, ((u x + t : ℝ) : ℂ) ∂S.measure) = 0 at hz
    rw [integral_complex_ofReal, integral_add hμ (integrable_const _), hm, integral_const] at hz
    simp [Measure.real, ht.ne'] at hz
  change (∫ x, (((u (S.act h x)+t : ℝ) : ℂ) * conj ((u x+t : ℝ) : ℂ)) ∂S.measure) = 0
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_eq_zero]
  have hi₁ : Integrable (fun x ↦ u (S.act h x)) S.measure :=
    (S.preserves h).integrable_comp_of_integrable hμ
  have hi₂ : Integrable (fun x ↦ u (S.act h x) * u x) S.measure :=
    Integrable.of_bound ((hu.comp (S.preserves h).measurable).mul hu).aestronglyMeasurable
      ((n : ℝ) * n) (.of_forall fun x ↦ by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_truncateGaussian_le_nat n _) (abs_truncateGaussian_le_nat n _)
          (abs_nonneg _) (Nat.cast_nonneg _))
  have he : (∫ x, u (S.act h x) * u x ∂S.measure) = b := by
    simpa only [b, S, u, gaussianPathSystem, gaussianShift, mul_one] using
      truncateGaussian_corr_eq φ hφ n ((hconst h hh).trans (hconst g hg).symm)
  have hact : (∫ x, u (S.act h x) ∂S.measure) = 0 :=
    (integral_comp_preserving (S.preserves h) hu.aestronglyMeasurable).trans hm
  have hExp : (fun x ↦ (u (S.act h x) + t) * (u x + t)) =
      fun x ↦ (u (S.act h x) * u x + u (S.act h x) * t) + (t * u x + t*t) :=
    funext fun _ ↦ by ring
  have hk : Integrable (fun _ : G → ℝ ↦ t*t) S.measure := integrable_const _
  rw [hExp, integral_add (hi₂.fun_add (hi₁.mul_const t)) ((hμ.const_mul t).fun_add hk),
    integral_add hi₂ (hi₁.mul_const t), integral_add (hμ.const_mul t) hk,
    integral_mul_const, integral_const_mul, hm, hact, he, integral_const]
  simp [Measure.real, t, Real.mul_self_sqrt (neg_nonneg.mpr hnegB.le)]

end

end SixProblems
