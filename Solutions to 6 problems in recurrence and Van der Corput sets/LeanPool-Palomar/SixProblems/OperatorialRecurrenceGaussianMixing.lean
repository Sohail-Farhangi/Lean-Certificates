/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrenceGaussianDensity
public import SixProblems.Koopman
public import SixProblems.ProductErgodicity
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

namespace SixProblems.Gaussian

noncomputable section

open MeasureTheory Mixing Filter Set TopologicalSpace ContinuousLinearMap InnerProductSpace
open scoped Classical Topology InnerProductSpace ComplexConjugate

private theorem tendsto_zero_of_dense_lipschitz {ι E D : Type*} [PseudoMetricSpace E]
    {F : Filter ι} {d : D → E} (hd : DenseRange d) {b : ι → E → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ i x y, dist (b i x) (b i y) ≤ C * dist x y)
    (h : ∀ j, Tendsto (fun i ↦ b i (d j)) F (𝓝 0)) (x : E) :
    Tendsto (fun i ↦ b i x) F (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := hd.exists_dist_lt x (show 0 < ε / (2 * (C+1)) by positivity)
  filter_upwards [(Metric.tendsto_nhds.1 (h j)) (ε / 2) (by positivity)] with i hi
  have he : C * dist x (d j) < ε / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (C+1))).mp hj
    have hh' := mul_le_mul_of_nonneg_right (show C ≤ C+1 by linarith)
      (show 0 ≤ dist x (d j) from dist_nonneg)
    nlinarith only [hh, hh']
  refine (dist_triangle _ (b i (d j)) _).trans_lt ?_
  have h' := add_lt_add ((hLip i x (d j)).trans_lt he) hi
  linarith only [h']

/-- Under a common operator-norm bound, testing on two dense sets suffices
for convergence of all weak matrix coefficients. -/
private theorem tendsto_inner_zero_of_denseRange_of_opNorm_le {ι D E H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {F : Filter ι}
    {d : D → H} {e : E → H} (hd : DenseRange d) (he : DenseRange e)
    {A : ι → H →L[ℂ] H} {C : ℝ} (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (h : ∀ x y, Tendsto (fun i ↦ ⟪d x, A i (e y)⟫_ℂ) F (𝓝 0)) (x y : H) :
    Tendsto (fun i ↦ ⟪x, A i y⟫_ℂ) F (𝓝 0) := by
  have hLeft (v : E) (u : H) : Tendsto (fun i ↦ ⟪u, A i (e v)⟫_ℂ) F (𝓝 0) := by
    refine tendsto_zero_of_dense_lipschitz hd (b := fun i z ↦ ⟪z, A i (e v)⟫_ℂ)
      (C := C * ‖e v‖) (by positivity) ?_ (fun w ↦ h w v) u
    intro i x y
    rw [dist_eq_norm, dist_eq_norm, ← inner_sub_left]
    calc
      ‖⟪x - y, A i (e v)⟫_ℂ‖ ≤ ‖x - y‖ * ‖A i (e v)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x - y‖ * (C * ‖e v‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
      _ = _ := by ring
  refine tendsto_zero_of_dense_lipschitz he (b := fun i z ↦ ⟪x, A i z⟫_ℂ)
    (C := ‖x‖ * C) (by positivity) ?_ (fun v ↦ hLeft v x) y
  intro i u v
  rw [dist_eq_norm, dist_eq_norm, ← inner_sub_right, ← map_sub]
  calc
    ‖⟪x, A i (u - v)⟫_ℂ‖ ≤ ‖x‖ * ‖A i (u - v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (C * ‖u - v‖) := by
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
    _ = _ := by ring

private theorem test_conj {G : Type*} (a : GaussianTest G) (x : G → ℝ) :
    conj (gaussianCylChar a.times a.frequencies x) =
      gaussianCylChar a.times (fun i ↦ -a.frequencies i) x := by
  simp [gaussianCylChar, ← Complex.exp_conj, Complex.conj_I, Finset.sum_neg_distrib]

variable {G : Type*} [Group G] [Countable G] (φ : G → ℝ) (hφ : RealPositiveDefinite φ)

/-- Vanishing two-sided translates of the covariance give a weak operator limit onto
    constant functions for the Gaussian path system. -/
theorem gaussianPath_koopman_tendsto {J : Type*} (g : J → G) (L : Filter J)
    (hCov : ∀ r s : G, Tendsto (fun z ↦ φ (r * (g z)⁻¹ * s)) L (𝓝 0))
    (x y : Lp ℂ 2 (gaussianPathMeasure φ hφ)) :
    Tendsto (fun z ↦ ⟪x, systemKoopman (gaussianPathSystem φ hφ) (g z)⁻¹ y⟫_ℂ) L
      (𝓝 (⟪x, constantOne (gaussianPathMeasure φ hφ)⟫_ℂ *
         ⟪constantOne (gaussianPathMeasure φ hφ), y⟫_ℂ)) := by
  let S := gaussianPathSystem φ hφ
  let μ := S.measure
  change Lp ℂ 2 μ at x y
  let u := constantOne μ
  let P := rankOne ℂ u u
  let A (z : J) := (systemKoopman S (g z)⁻¹).toLinearIsometry.toContinuousLinearMap - P
  have hAct (z : J) (w : Lp ℂ 2 μ) :
      A z w = systemKoopman S (g z)⁻¹ w - P w := rfl
  have hA (z : J) : ‖A z‖ ≤ 1 + ‖P‖ := by
    exact (norm_sub_le _ _).trans (add_le_add
      (systemKoopman S (g z)⁻¹).toLinearIsometry.norm_toContinuousLinearMap_le le_rfl)
  let V : GaussianTest G → Lp ℂ 2 μ := fun a ↦ a.toVector μ
  have hCoe (a : GaussianTest G) :
      ⟪u, V a⟫_ℂ = ∫ x, gaussianCylChar a.times a.frequencies x ∂μ :=
    (inner_constantOne_left _ _).trans (integral_congr_ae (a.memLp μ).coeFn_toLp)
  have hConj (a : GaussianTest G) :
      ⟪V a, u⟫_ℂ = ∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x ∂μ := by
    rw [← inner_conj_symm, hCoe, ← integral_conj]
    exact integral_congr_ae (.of_forall fun x ↦ test_conj a x)
  have hTest (a b : GaussianTest G) :
      Tendsto (fun z ↦ ⟪V a, A z (V b)⟫_ℂ) L (𝓝 0) := by
    have he (z : J) : ⟪V a, systemKoopman S (g z)⁻¹ (V b)⟫_ℂ =
        ∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x *
          gaussianCylChar b.times b.frequencies (gaussianShift (g z) x) ∂μ := by
      rw [L2.inner_def (μ := S.measure)]
      apply integral_congr_ae
      have hb := (ae_systemKoopman S (g z)⁻¹ (V b)).trans
        ((S.preserves ((g z)⁻¹)⁻¹).quasiMeasurePreserving.ae_eq_comp (b.memLp μ).coeFn_toLp)
      filter_upwards [(a.memLp μ).coeFn_toLp, hb] with x h₁ h₂
      simp only [RCLike.inner_apply', inv_inv] at h₂ ⊢
      rw [show V a x = _ from h₁, h₂, test_conj]
      rfl
    have hlim : Tendsto (fun z ↦ ∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x *
        gaussianCylChar b.times b.frequencies (gaussianShift (g z) x) ∂μ) L
        (𝓝 ((∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x ∂μ) *
          (∫ x, gaussianCylChar b.times b.frequencies x ∂μ))) :=
      gaussianCylChar_mul_shift_tendsto φ hφ a.times (fun i ↦ -a.frequencies i)
        b.times b.frequencies g L hCov
    have hlimit : Tendsto (fun z ↦ ⟪V a, systemKoopman S (g z)⁻¹ (V b)⟫_ℂ) L
        (𝓝 ⟪V a, P (V b)⟫_ℂ) := by
      simpa only [he, P, inner_right_rankOne_apply, hConj, hCoe] using hlim
    simpa only [hAct, inner_sub_right, sub_self] using
      hlimit.sub (tendsto_const_nhds (x := ⟪V a, P (V b)⟫_ℂ))
  let D := Submodule.span ℂ (Set.range V)
  have hD : DenseRange ((↑) : D → Lp ℂ 2 μ) := by
    rw [DenseRange, Subtype.range_coe]
    exact D.dense_iff_topologicalClosure_eq_top.mpr (gaussianTestVectors_dense μ)
  have hRight (a : GaussianTest G) (w : Lp ℂ 2 μ) (hw : w ∈ D) :
      Tendsto (fun z ↦ ⟪V a, A z w⟫_ℂ) L (𝓝 0) := by
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      exact hTest a b
    | zero => simpa only [map_zero, inner_zero_right] using (tendsto_const_nhds (x := (0 : ℂ)))
    | add v w hv hw hv' hw' =>
      simpa only [map_add, inner_add_right, add_zero] using hv'.add hw'
    | smul c w hw hw' =>
      simpa only [map_smul, inner_smul_right, mul_zero] using tendsto_const_nhds.mul hw'
  have hLeft (w v : Lp ℂ 2 μ) (hw : w ∈ D) (hv : v ∈ D) :
      Tendsto (fun z ↦ ⟪w, A z v⟫_ℂ) L (𝓝 0) := by
    induction hw using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨a, rfl⟩ := hw'
      exact hRight a v hv
    | zero => simpa only [inner_zero_left] using (tendsto_const_nhds (x := (0 : ℂ)))
    | add w₁ w₂ h₁ h₂ ht₁ ht₂ =>
      simpa only [inner_add_left, add_zero] using ht₁.add ht₂
    | smul c w' hw' ht =>
      simpa only [inner_smul_left, mul_zero] using tendsto_const_nhds.mul ht
  have ht := tendsto_inner_zero_of_denseRange_of_opNorm_le hD hD
    (by positivity : 0 ≤ 1 + ‖P‖) hA (fun a b ↦ hLeft a b a.property b.property) x y
  have ht' : Tendsto (fun z ↦ ⟪x, A z y⟫_ℂ + ⟪x, P y⟫_ℂ) L (𝓝 (0 + ⟪x, P y⟫_ℂ)) :=
    ht.add tendsto_const_nhds
  have hP : ⟪x, P y⟫_ℂ = ⟪x, u⟫_ℂ * ⟪u, y⟫_ℂ := inner_right_rankOne_apply x u u y
  change Tendsto (fun z ↦ ⟪x, systemKoopman S (g z)⁻¹ y⟫_ℂ) L (𝓝 (⟪x, u⟫_ℂ * ⟪u, y⟫_ℂ))
  simpa only [hAct, inner_sub_right, sub_add_cancel, zero_add, hP] using ht'

/-- Along the same sequence, the Gaussian action is mixing on all measurable events. -/
theorem gaussianPath_measure_inter_tendsto {J : Type*} (g : J → G) (L : Filter J)
    (hCov : ∀ r s : G, Tendsto (fun z ↦ φ (r * (g z)⁻¹ * s)) L (𝓝 0))
    {U V : Set (G → ℝ)} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    Tendsto (fun z ↦ (gaussianPathMeasure φ hφ).real (U ∩ gaussianShift (g z) ⁻¹' V)) L
      (𝓝 ((gaussianPathMeasure φ hφ).real U * (gaussianPathMeasure φ hφ).real V)) := by
  let S := gaussianPathSystem φ hφ
  let μ := S.measure
  let a : Lp ℂ 2 μ := indicatorConstLp 2 hU (measure_ne_top _ _) 1
  let b : Lp ℂ 2 μ := indicatorConstLp 2 hV (measure_ne_top _ _) 1
  have hA : a =ᵐ[μ] U.indicator (fun _ ↦ (1 : ℂ)) := indicatorConstLp_coeFn
  have hB : b =ᵐ[μ] V.indicator (fun _ ↦ (1 : ℂ)) := indicatorConstLp_coeFn
  have hAa : ⟪a, constantOne μ⟫_ℂ = (μ.real U : ℂ) := by
    rw [← inner_conj_symm, inner_constantOne_left, integral_congr_ae hA, integral_indicator_const]
    · simp
    · exact hU
  have hBb : ⟪constantOne μ, b⟫_ℂ = (μ.real V : ℂ) := by
    rw [inner_constantOne_left, integral_congr_ae hB, integral_indicator_const _ hV]
    simp
  have he (z : J) : ⟪a, systemKoopman S (g z)⁻¹ b⟫_ℂ =
      (μ.real (U ∩ gaussianShift (g z) ⁻¹' V) : ℂ) := by
    have hm : MeasurableSet (U ∩ gaussianShift (g z) ⁻¹' V) :=
      hU.inter ((gaussianShift_preserves φ hφ (g z)).measurable hV)
    have hI : (∫ x, (U ∩ gaussianShift (g z) ⁻¹' V).indicator
        (fun _ ↦ (1 : ℂ)) x ∂μ) = (μ.real (U ∩ gaussianShift (g z) ⁻¹' V) : ℂ) := by
      rw [integral_indicator_const _ hm]
      simp
    rw [L2.inner_def (μ := S.measure), ← hI]
    apply integral_congr_ae
    have hb := (ae_systemKoopman S (g z)⁻¹ b).trans
      ((S.preserves ((g z)⁻¹)⁻¹).quasiMeasurePreserving.ae_eq_comp hB)
    filter_upwards [hA, hb] with x ha hb'
    rw [RCLike.inner_apply', ha, hb']
    change conj (U.indicator (fun _ ↦ (1 : ℂ)) x) *
      V.indicator (fun _ ↦ (1 : ℂ)) (gaussianShift ((g z)⁻¹)⁻¹ x) = _
    by_cases h₁ : x ∈ U <;> by_cases h₂ : gaussianShift (g z) x ∈ V <;>
      simp [inv_inv, Set.indicator, h₁, h₂]
  have ht := gaussianPath_koopman_tendsto φ hφ g L hCov a b
  change Tendsto (fun z ↦ ⟪a, systemKoopman S (g z)⁻¹ b⟫_ℂ) L
    (𝓝 (⟪a, constantOne μ⟫_ℂ * ⟪constantOne μ, b⟫_ℂ)) at ht
  rw [hAa, hBb, ← Complex.ofReal_mul] at ht
  change Tendsto (fun z ↦ μ.real (U ∩ gaussianShift (g z) ⁻¹' V)) L
    (𝓝 (μ.real U * μ.real V))
  simpa only [he, Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto ((μ.real U * μ.real V : ℝ) : ℂ)).comp ht

/-- A Gaussian shift with vanishing coefficients along a sequence preserves
    ergodicity when multiplied by any ergodic action of the same group. -/
theorem gaussianPath_prod_isErgodic {X : Type*} [MeasurableSpace X]
    (S : System G X) (hS : S.IsErgodic) (g : ℕ → G)
    (hCov : ∀ r s : G, Tendsto (fun n ↦ φ (r * (g n)⁻¹ * s)) atTop (𝓝 0)) :
    (S.prod (gaussianPathSystem φ hφ)).IsErgodic :=
  prod_isErgodic_of_eventMixing S (gaussianPathSystem φ hφ) hS g
    (fun _ _ hA hB ↦ gaussianPath_measure_inter_tendsto φ hφ g atTop hCov hA hB)

end

end SixProblems.Gaussian
