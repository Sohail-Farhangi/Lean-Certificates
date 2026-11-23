/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReflexiveCompactness
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Strict convexity of complex Lᵖ -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace JdLG

private theorem norm_midpoint_le_mean (z w : ℂ) :
    ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w‖ ≤ (1 / 2 : ℝ) * ‖z‖ + (1 / 2 : ℝ) * ‖w‖ := by
  simpa only [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
    norm_add_le ((1 / 2 : ℝ) • z) ((1 / 2 : ℝ) • w)

/-- The p-th power of the complex norm satisfies the midpoint convexity inequality. -/
theorem norm_midpoint_rpow_le {r : ℝ} (hr : 1 < r) (z w : ℂ) :
    ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w‖ ^ r ≤
      (1 / 2 : ℝ) * ‖z‖ ^ r + (1 / 2 : ℝ) * ‖w‖ ^ r := by
  have hc := (convexOn_rpow hr.le).2 (norm_nonneg z) (norm_nonneg w)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  exact (Real.rpow_le_rpow (norm_nonneg _) (norm_midpoint_le_mean z w)
    (by linarith)).trans (by simpa only [smul_eq_mul] using hc)

/-- For p > 1 the midpoint inequality is strict at distinct complex numbers. -/
theorem norm_midpoint_rpow_lt {r : ℝ} (hr : 1 < r) {z w : ℂ} (hne : z ≠ w) :
    ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w‖ ^ r <
      (1 / 2 : ℝ) * ‖z‖ ^ r + (1 / 2 : ℝ) * ‖w‖ ^ r := by
  have hr₀ : 0 < r := by linarith
  by_cases he : ‖z‖ = ‖w‖
  · have hlt : ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w‖ < ‖z‖ :=
      norm_combo_lt_of_ne le_rfl he.ge hne (by norm_num) (by norm_num) (by norm_num)
    have hp := Real.rpow_lt_rpow (norm_nonneg _) hlt hr₀
    rw [← he]
    linarith
  · have hc := (strictConvexOn_rpow hr).2 (norm_nonneg z) (norm_nonneg w) he
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    exact (Real.rpow_le_rpow (norm_nonneg _) (norm_midpoint_le_mean z w)
      hr₀.le).trans_lt (by simpa only [smul_eq_mul] using hc)

section Lp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The p-th power of the Lᵖ norm is the integral of the p-th power of the pointwise norm. -/
theorem lp_norm_rpow_eq_integral (hp : p ≠ 0) (hp_top : p ≠ ∞) (f : Lp ℂ p μ) :
    ‖f‖ ^ p.toReal = ∫ x, ‖f x‖ ^ p.toReal ∂μ := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  have hi : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ := integral_nonneg fun _ ↦ by positivity
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hp hp_top,
    ENNReal.toReal_ofReal (by positivity), ← Real.rpow_mul hi, inv_mul_cancel₀ hr.ne',
    Real.rpow_one]

omit [Fact (1 ≤ p)] in
private theorem lp_integral_norm_rpow_eq_one (hp : 1 < p) (hp_top : p ≠ ∞)
    {f : Lp ℂ p μ} (hf : ‖f‖ = 1) : ∫ x, ‖f x‖ ^ p.toReal ∂μ = 1 := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hr₀ : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp_top
  have hi : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ := integral_nonneg fun _ ↦ by positivity
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hp₀ hp_top,
    ENNReal.toReal_ofReal (by positivity)] at hf
  apply (Real.rpow_left_inj hi zero_le_one (inv_pos.mpr hr₀).ne').1
  simpa only [Real.one_rpow] using hf

/-- For arbitrary measure spaces the norm on complex Lᵖ, with 1 < p < ∞,
is strictly convex. The argument integrates the pointwise scalar strict
convexity of the p-th power of the norm. -/
theorem norm_add_ne_two_complexLp (hp : 1 < p) (hp_top : p ≠ ∞)
    {f g : Lp ℂ p μ} (hf : ‖f‖ = 1) (hg : ‖g‖ = 1) (hfg : f ≠ g) : ‖f + g‖ ≠ 2 := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hr : 1 < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
    simpa only [ENNReal.toReal_one] using h
  intro hadd
  let m : Lp ℂ p μ := (1 / 2 : ℝ) • (f + g)
  have hm : ‖m‖ = 1 := by
    dsimp [m]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), hadd]
    norm_num
  have hpoint : (m : X → ℂ) =ᵐ[μ] fun x ↦ (1 / 2 : ℝ) • f x + (1 / 2 : ℝ) • g x := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (f + g), Lp.coeFn_add f g] with x h₁ h₂
    change m x = (1 / 2 : ℝ) • (f + g) x at h₁
    change (f + g) x = f x + g x at h₂
    rw [h₁, h₂, smul_add]
  let d (x : X) := (1 / 2 : ℝ) * ‖f x‖ ^ p.toReal +
    (1 / 2 : ℝ) * ‖g x‖ ^ p.toReal - ‖m x‖ ^ p.toReal
  have hdi : Integrable d μ := by
    have hfi := (Lp.memLp f).integrable_norm_rpow hp₀ hp_top
    have hgi := (Lp.memLp g).integrable_norm_rpow hp₀ hp_top
    have hmi := (Lp.memLp m).integrable_norm_rpow hp₀ hp_top
    exact ((hfi.const_mul (1 / 2)).add (hgi.const_mul (1 / 2))).sub hmi
  have hda : ∀ᵐ x ∂μ, 0 ≤ d x := by
    filter_upwards [hpoint] with x hx
    dsimp [d]
    rw [hx]
    exact sub_nonneg.mpr (norm_midpoint_rpow_le hr _ _)
  have hdi0 : ∫ x, d x ∂μ = 0 := by
    have hfi := (Lp.memLp f).integrable_norm_rpow hp₀ hp_top
    have hgi := (Lp.memLp g).integrable_norm_rpow hp₀ hp_top
    have hmi := (Lp.memLp m).integrable_norm_rpow hp₀ hp_top
    let F (x : X) := (1 / 2 : ℝ) * ‖f x‖ ^ p.toReal
    let G (x : X) := (1 / 2 : ℝ) * ‖g x‖ ^ p.toReal
    let M (x : X) := ‖m x‖ ^ p.toReal
    have hsub : (∫ x, d x ∂μ) = (∫ x, F x + G x ∂μ) - ∫ x, M x ∂μ :=
      integral_sub ((hfi.const_mul (1 / 2)).add (hgi.const_mul (1 / 2))) hmi
    have hsum : (∫ x, F x + G x ∂μ) = (∫ x, F x ∂μ) + ∫ x, G x ∂μ :=
      integral_add (hfi.const_mul (1 / 2)) (hgi.const_mul (1 / 2))
    rw [hsub, hsum]
    change (∫ x, (1 / 2 : ℝ) * ‖f x‖ ^ p.toReal ∂μ) +
        (∫ x, (1 / 2 : ℝ) * ‖g x‖ ^ p.toReal ∂μ) - (∫ x, ‖m x‖ ^ p.toReal ∂μ) = 0
    rw [integral_const_mul, integral_const_mul, lp_integral_norm_rpow_eq_one μ hp hp_top hf,
      lp_integral_norm_rpow_eq_one μ hp hp_top hg, lp_integral_norm_rpow_eq_one μ hp hp_top hm]
    norm_num
  have hd0 := (integral_eq_zero_iff_of_nonneg_ae hda hdi).1 hdi0
  apply hfg
  apply Lp.ext
  filter_upwards [hd0, hpoint] with x hdx hx
  by_contra hne
  have hlt := norm_midpoint_rpow_lt hr hne
  change d x = 0 at hdx
  dsimp [d] at hdx
  rw [hx] at hdx
  linarith

/-- The norm on complex Lᵖ over an arbitrary measure is strictly convex for 1 < p < ∞. -/
theorem strictConvexSpace_complexLp (hp : 1 < p) (hp_top : p ≠ ∞) :
    StrictConvexSpace ℝ (Lp ℂ p μ) :=
  StrictConvexSpace.of_norm_add_ne_two (fun _ _ ↦ norm_add_ne_two_complexLp μ hp hp_top)

/-- For complex Lᵖ, the reflexive contractive criterion needs only reflexivity
and strict convexity of the dual as additional functional-analytic inputs. -/
theorem admissible_of_complexLp_contractions_of_reflexive_strictConvexDual
    {S : Type*} [Semigroup S] [Nonempty S] (hp : 1 < p) (hp_top : p ≠ ∞)
    [StrictConvexSpace ℝ (StrongDual ℂ (Lp ℂ p μ))]
    (href : Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (Lp ℂ p μ)))
    (π : S →ₙ* (Lp ℂ p μ →L[ℂ] Lp ℂ p μ)) (hπ : ∀ s, ‖π s‖ ≤ 1) :
    IsJdLGAdmissible π := by
  have hstrict :=
    @StrictConvexSpace.of_norm_add_ne_two (Lp ℂ p μ) _
      (NormedSpace.restrictScalars ℝ ℂ (Lp ℂ p μ)) (fun _ _ ↦ norm_add_ne_two_complexLp μ hp hp_top)
  exact @admissible_of_reflexive_strictConvex_contractions (Lp ℂ p μ) _ _ S _ _ _ hstrict _
    href π hπ

end Lp

end JdLG
