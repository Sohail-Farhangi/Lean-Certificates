/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.LpConvexity
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Smoothness of the complex Lᵖ norm -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace JdLG

section Lp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The p-th power of the Lᵖ norm has a real derivative along every real affine line.
The derivative can be passed under the integral using a pointwise p-power majorant. -/
theorem differentiableAt_norm_rpow_complexLp_line (hp : 1 < p) (hp_top : p ≠ ∞)
    (f g : Lp ℂ p μ) :
    DifferentiableAt ℝ (fun t : ℝ ↦ ‖f + t • g‖ ^ p.toReal) 0 := by
  let r := p.toReal
  have hr : 1 < r := by
    simpa only [r, ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  have hr₀ : 0 < r := zero_lt_one.trans hr
  have hp₀ : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  let Q (z : ℂ) : ℝ := ‖z‖ ^ r
  let F (t : ℝ) (x : X) : ℝ := Q (f x + t • g x)
  let D (t : ℝ) (x : X) : ℝ := fderiv ℝ Q (f x + t • g x) (g x)
  let B (x : X) : ℝ := (r * (2 : ℝ) ^ (r - 1)) * (‖f x‖ ^ r + ‖g x‖ ^ r)
  have hQ : ContDiff ℝ 1 Q := contDiff_norm_rpow hr
  have hM (t : ℝ) : AEStronglyMeasurable (fun x ↦ f x + t • g x) μ :=
    (Lp.aestronglyMeasurable f).add ((Lp.aestronglyMeasurable g).const_smul t)
  have hF : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    .of_forall fun t ↦ hQ.continuous.comp_aestronglyMeasurable (hM t)
  have hFi : Integrable (F 0) μ := by
    simpa only [F, Q, zero_smul, add_zero] using
      (Lp.memLp f).integrable_norm_rpow hp₀ hp_top
  have hD : AEStronglyMeasurable (D 0) μ :=
    (hQ.continuous_fderiv_apply one_ne_zero).comp_aestronglyMeasurable
      ((hM 0).prodMk (Lp.aestronglyMeasurable g))
  have hBi : Integrable B μ :=
    (((Lp.memLp f).integrable_norm_rpow hp₀ hp_top).add
      ((Lp.memLp g).integrable_norm_rpow hp₀ hp_top)).const_mul _
  have hDiff (x : X) (t : ℝ) : HasDerivAt (F · x) (D t x) t := by
    have hc : HasDerivAt (fun s : ℝ ↦ f x + s • g x) (g x) t := by
      simpa only [one_smul] using
        (((hasDerivAt_id' t).smul_const (g x)).const_add (f x))
    exact ((hQ.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt t hc
  have hDb (x : X) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) : ‖D t x‖ ≤ B x := by
    let a := ‖f x‖ + ‖g x‖
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hg : ‖g x‖ ≤ a := le_add_of_nonneg_left (norm_nonneg _)
    have ht₁ : ‖t‖ ≤ 1 := by
      exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using ht)
    have hab : ‖f x + t • g x‖ ≤ a := by
      apply (norm_add_le _ _).trans
      rw [norm_smul]
      exact add_le_add_right (mul_le_of_le_one_left (norm_nonneg _) ht₁) _
    have hpow : a ^ r ≤ (2 : ℝ) ^ (r - 1) * (‖f x‖ ^ r + ‖g x‖ ^ r) := by
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖f x‖₊ ‖g x‖₊ hr.le
    calc
      ‖D t x‖ ≤ ‖fderiv ℝ Q (f x + t • g x)‖ * ‖g x‖ :=
        (fderiv ℝ Q (f x + t • g x)).le_opNorm _
      _ = r * ‖f x + t • g x‖ ^ (r - 1) * ‖g x‖ := by
        rw [norm_fderiv_norm_id_rpow _ hr]
      _ ≤ r * a ^ (r - 1) * a := by
        have h := Real.rpow_le_rpow (norm_nonneg _) hab (sub_nonneg.mpr hr.le)
        exact mul_le_mul_of_nonneg (mul_le_mul_of_nonneg_left h hr₀.le) hg
          (by positivity) ha
      _ = r * a ^ r := by
        rw [mul_assoc, ← Real.rpow_add_one' ha (by linarith : r - 1 + 1 ≠ 0)]
        ring_nf
      _ ≤ B x := by
        unfold B
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hpow hr₀.le
  have hid := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one) hF hFi hD
    (.of_forall hDb) hBi (.of_forall fun x t _ ↦ hDiff x t)).2
  have hEq (t : ℝ) : ‖f + t • g‖ ^ p.toReal = ∫ x, F t x ∂μ := by
    rw [lp_norm_rpow_eq_integral μ hp₀ hp_top]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f (t • g), Lp.coeFn_smul t g] with x h₁ h₂
    change (f + t • g) x = f x + (t • g) x at h₁
    change (t • g) x = t • g x at h₂
    change ‖(f + t • g) x‖ ^ r = ‖f x + t • g x‖ ^ r
    rw [h₁, h₂]
  rw [show (fun t : ℝ ↦ ‖f + t • g‖ ^ p.toReal) =
    (fun t : ℝ ↦ ∫ x, F t x ∂μ) from funext hEq]
  exact hid.differentiableAt

omit [Fact (1 ≤ p)] in
/-- At a unit vector of complex Lᵖ, the Lᵖ norm is differentiable along every real line. -/
theorem differentiableAt_norm_complexLp_line (hp : 1 < p) (hp_top : p ≠ ∞)
    {f : Lp ℂ p μ} (hf : ‖f‖ = 1) (g : Lp ℂ p μ) :
    DifferentiableAt ℝ (fun t : ℝ ↦ ‖f + t • g‖) 0 := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hr := ENNReal.toReal_pos hp₀ hp_top
  have h := (differentiableAt_norm_rpow_complexLp_line μ hp hp_top f g).hasDerivAt
  have h' := (h.rpow_const (p := p.toReal⁻¹) (.inl (by simp [hf]))).differentiableAt
  have he : (fun t : ℝ ↦ (‖f + t • g‖ ^ p.toReal) ^ p.toReal⁻¹) =
      (fun t : ℝ ↦ ‖f + t • g‖) := by
    funext t
    have ht : 0 ≤ ‖f + t • g‖ := by rw [Lp.norm_def]; exact ENNReal.toReal_nonneg
    exact Real.rpow_rpow_inv ht hr.ne'
  rw [he] at h'
  exact h'

/-- A unit vector in complex Lᵖ has at most one unit norming complex-linear functional. -/
theorem eq_of_norming_complexLp (hp : 1 < p) (hp_top : p ≠ ∞)
    (f : Lp ℂ p μ) (hf : ‖f‖ = 1) {a b : StrongDual ℂ (Lp ℂ p μ)}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (haf : (a f).re = 1) (hbf : (b f).re = 1) :
    a = b := by
  have hreal (g : Lp ℂ p μ) : (a g).re = (b g).re := by
    have h := (differentiableAt_norm_complexLp_line μ hp hp_top hf g).hasDerivAt
    have hnorm (l : StrongDual ℂ (Lp ℂ p μ)) (hl : ‖l‖ = 1) (hlf : (l f).re = 1) :
        (l g).re = deriv (fun t : ℝ ↦ ‖f + t • g‖) 0 := by
      let H (t : ℝ) := ‖f + t • g‖ - (1 + t * (l g).re)
      have h₀ : H 0 = 0 := by simp [H, hf]
      have hpos (t : ℝ) : 0 ≤ H t := by
        have he : (l (f + t • g)).re = 1 + t * (l g).re := by
          rw [map_add, l.map_smul_of_tower, Complex.add_re, hlf, Complex.smul_re, smul_eq_mul]
        apply sub_nonneg.mpr
        rw [← he]
        exact (Complex.re_le_norm _).trans
          (by simpa only [hl, one_mul] using l.le_opNorm (f + t • g))
      have hmin : IsLocalMin H 0 := by
        exact .of_forall fun t ↦ h₀.trans_le (hpos t)
      have hd : HasDerivAt (fun t : ℝ ↦ 1 + t * (l g).re) (l g).re 0 := by
        simpa only [one_mul] using (((hasDerivAt_id' 0).mul_const (l g).re).const_add 1)
      exact (sub_eq_zero.mp (hmin.hasDerivAt_eq_zero (h.sub hd))).symm
    exact (hnorm a ha haf).trans (hnorm b hb hbf).symm
  apply ContinuousLinearMap.ext
  intro g
  apply Complex.ext
  · exact hreal g
  · have hi := hreal (Complex.I • g)
    simpa only [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, neg_inj] using hi

end Lp

end JdLG
