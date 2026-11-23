/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReflexiveCompactness
public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.LocallyConvex.Separation

/-! # Reflexivity of uniformly convex complex Banach spaces -/

@[expose] public section

open Filter NormedSpace Set
open scoped Topology

namespace JdLG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem exists_re_dual_gt (f : StrongDual ℂ E) {r : ℝ} (hr : r < ‖f‖) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ r < (f x).re := by
  by_contra! h
  have hr₀ : 0 ≤ r := by simpa using h 0 (by simp)
  apply hr.not_ge
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hr₀
  intro x hx
  by_cases hz : f x = 0
  · simpa only [hz, norm_zero] using hr₀
  let z := f x
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let c : ℂ := (↑‖z‖ : ℂ)⁻¹ * (starRingEnd ℂ) z
  have hc : ‖c‖ = 1 := by
    simp [c, norm_inv, inv_mul_cancel₀ hn]
  have hrot : c * z = (↑‖z‖ : ℂ) := by
    change (↑‖z‖ : ℂ)⁻¹ * (starRingEnd ℂ) z * z = _
    rw [mul_assoc, Complex.conj_mul' z, pow_two, inv_mul_cancel_left₀]
    exact_mod_cast hn
  have hx' : ‖c • x‖ ≤ 1 := by rw [norm_smul, hc, hx, one_mul]
  have hb := h (c • x) hx'
  rw [map_smul, smul_eq_mul] at hb
  change (c * z).re ≤ r at hb
  rw [hrot, Complex.ofReal_re] at hb
  exact hb

local notation "D" => WeakDual ℂ (StrongDual ℂ E)

private noncomputable def weakStarInclusion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    E →L[ℂ] WeakDual ℂ (StrongDual ℂ E) :=
  (inclusionInDoubleDualWeak ℂ E).comp (toWeakSpaceCLM ℂ E)

private theorem weakStarInclusion_apply (x : E) (f : StrongDual ℂ E) :
    weakStarInclusion E x f = f x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Goldstine's theorem for the closed unit ball, in the weak-star bidual. -/
theorem bidual_unitBall_mem_weakStar_closure (y : StrongDual ℂ (StrongDual ℂ E)) (hy : ‖y‖ ≤ 1) :
    StrongDual.toWeakDual y ∈ closure
      ((fun x ↦ StrongDual.toWeakDual (inclusionInDoubleDual ℂ E x)) ''
        Metric.closedBall (0 : E) 1) := by
  let j := weakStarInclusion E
  let B := Metric.closedBall (0 : E) 1
  let s := j '' B
  change StrongDual.toWeakDual y ∈ closure s
  by_contra h
  let : IsScalarTower ℝ ℂ D := inferInstanceAs
    (IsScalarTower ℝ ℂ (StrongDual ℂ (StrongDual ℂ E)))
  let : LocallyConvexSpace ℝ D := by
    exact WeakBilin.locallyConvexSpace (𝕜 := ℂ) (E := StrongDual ℂ (StrongDual ℂ E))
      (F := StrongDual ℂ E) (B := topDualPairing ℂ (StrongDual ℂ E))
  have hc : Convex ℝ s := (convex_closedBall _ _).linear_image (j.toLinearMap.restrictScalars ℝ)
  obtain ⟨L, r, hL, hyL⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    hc.closure isClosed_closure h
  let P := topDualPairing ℂ (StrongDual ℂ E)
  let L' : StrongDual ℂ (WeakBilin P) := L
  obtain ⟨f, hf⟩ := LinearMap.dualEmbedding_surjective (𝕜 := ℂ)
    (E := StrongDual ℂ (StrongDual ℂ E)) (F := StrongDual ℂ E) P L'
  have he (z : D) : L z = z f := by
    change L' z = z f
    rw [← hf]
    rfl
  have hr : r < ‖f‖ := by
    rw [he] at hyL
    exact hyL.trans_le ((RCLike.re_le_norm _).trans
      ((y.le_opNorm f).trans (by simpa using mul_le_mul_of_nonneg_right hy (norm_nonneg f))))
  obtain ⟨x, hx, hxr⟩ := exists_re_dual_gt f hr
  have hx' : j x ∈ closure s := subset_closure ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩
  have hxL := hL (j x) hx'
  rw [he] at hxL
  rw [weakStarInclusion_apply] at hxL
  exact hxr.not_gt hxL

set_option backward.isDefEq.respectTransparency.types false in
/-- Milman–Pettis for complex Banach spaces. Small weak-star slices of the
unit ball have small norm diameter by uniform convexity. -/
theorem surjective_inclusionInDoubleDual_of_uniformConvex [CompleteSpace E]
    [UniformConvexSpace E] : Function.Surjective (inclusionInDoubleDual ℂ E) := by
  have unit (y : StrongDual ℂ (StrongDual ℂ E)) (hy : ‖y‖ = 1) :
      ∃ x : E, inclusionInDoubleDual ℂ E x = y := by
    let j := weakStarInclusion E
    let B := Metric.closedBall (0 : E) 1
    let z : D := StrongDual.toWeakDual y
    let l := comap (fun x : B ↦ j x.val) (𝓝 z)
    let F := map (Subtype.val : B → E) l
    have hyc : z ∈ closure (j '' B) := bidual_unitBall_mem_weakStar_closure y hy.le
    have hl : NeBot l := by
      rw [comap_neBot_iff]
      intro s hs
      obtain ⟨w, hw⟩ := mem_closure_iff_nhds'.mp hyc s hs
      obtain ⟨x, hx, hEq⟩ := w.property
      exact ⟨⟨x, hx⟩, hEq ▸ hw⟩
    have hF : NeBot F := hl.map _
    have hB : B ∈ F := by
      change (Subtype.val : B → E) ⁻¹' B ∈ l
      exact univ_mem' fun x ↦ x.property
    have hT : Tendsto j F (𝓝 z) := by
      change map j (map (Subtype.val : B → E) l) ≤ _
      rw [map_map]
      exact map_comap_le
    have hcauchy : Cauchy F := by
      refine Metric.cauchy_iff.2 ⟨hF, fun ε hε ↦ ?_⟩
      obtain ⟨δ, hδ, hsmall⟩ := exists_forall_closed_ball_dist_add_le_two_sub E hε
      obtain ⟨f, hf, hfre⟩ := exists_re_dual_gt y (show 1 - δ / 2 < ‖y‖ by linarith)
      have hev : Tendsto (fun x ↦ (f x).re) F (𝓝 (y f).re) :=
        (Complex.continuous_re.tendsto _).comp ((WeakDual.eval_continuous f).tendsto z |>.comp hT)
      have hslice : {x | 1 - δ / 2 < (f x).re} ∈ F := hev.eventually (Ioi_mem_nhds hfre)
      refine ⟨B ∩ {x | 1 - δ / 2 < (f x).re}, inter_mem hB hslice, ?_⟩
      intro a ha b hb
      rw [dist_eq_norm]
      by_contra! hfar
      have hab := hsmall (mem_closedBall_zero_iff.1 ha.1) (mem_closedBall_zero_iff.1 hb.1) hfar
      have hn : (f (a + b)).re ≤ ‖a + b‖ := calc
        _ ≤ ‖f (a + b)‖ := RCLike.re_le_norm _
        _ ≤ ‖f‖ * ‖a + b‖ := f.le_opNorm _
        _ ≤ 1 * ‖a + b‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg _)
        _ = ‖a + b‖ := one_mul _
      rw [map_add, Complex.add_re] at hn
      have h₁ : 1 - δ / 2 < (f a).re := ha.2
      have h₂ : 1 - δ / 2 < (f b).re := hb.2
      linarith
    obtain ⟨x, hx⟩ := CompleteSpace.complete hcauchy
    have hlim : j x = z := tendsto_nhds_unique ((j.continuous.tendsto x).mono_left hx) hT
    exact ⟨x, StrongDual.toWeakDual.injective hlim⟩
  intro y
  by_cases hy : y = 0
  · exact ⟨0, by simp [hy]⟩
  let c : ℂ := ↑‖y‖
  have hy₀ : ‖y‖ ≠ 0 := (norm_pos_iff (a := y)).mpr hy |>.ne'
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr hy₀
  have hn : ‖c⁻¹ • y‖ = 1 := by
    have hnorm : ‖c‖ = ‖y‖ := Complex.norm_of_nonneg (norm_nonneg y)
    apply le_antisymm
    · calc
        ‖c⁻¹ • y‖ ≤ ‖c⁻¹‖ * ‖y‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ = 1 := by rw [norm_inv, hnorm, inv_mul_cancel₀ hy₀]
    · have h := ContinuousLinearMap.opNorm_smul_le c (c⁻¹ • y)
      rw [smul_inv_smul₀ hc, hnorm] at h
      apply le_of_not_gt
      intro hlt
      have hh := mul_lt_mul_of_pos_left hlt ((norm_nonneg y).lt_of_ne' hy₀)
      rw [mul_one] at hh
      exact hh.not_ge h
  obtain ⟨x, hx⟩ := unit (c⁻¹ • y) hn
  exact ⟨c • x, by rw [map_smul, hx, smul_inv_smul₀ hc]⟩

/-- Reflexivity and uniqueness of norm-one supporting functionals imply strict
convexity of the complex dual with its underlying real norm. -/
theorem strictConvexSpace_dual_of_reflexive_of_unique_support
    (hrefl : Function.Surjective (inclusionInDoubleDual ℂ E))
    (hunique : ∀ x : E, ‖x‖ = 1 → ∀ {f g : StrongDual ℂ E}, ‖f‖ = 1 → ‖g‖ = 1 →
      (f x).re = 1 → (g x).re = 1 → f = g) :
    StrictConvexSpace ℝ (StrongDual ℂ E) := by
  apply StrictConvexSpace.of_norm_add_ne_two
  intro f g hf hg hfg hnorm
  obtain ⟨z, hz, hzfg⟩ := exists_dual_vector'' ℂ (f + g)
  obtain ⟨x, hx⟩ := hrefl z
  have hxle : ‖x‖ ≤ 1 := by
    have he : ‖x‖ = ‖z‖ := by
      rw [← hx]
      exact ((inclusionInDoubleDualLi (E := E) ℂ).norm_map x).symm
    exact he.le.trans hz
  have hz' : (f x).re + (g x).re = 2 := by
    have h := congrArg Complex.re hzfg
    simp only [← hx, NormedSpace.dual_def, add_apply, Complex.add_re, hnorm] at h
    exact h.trans (Complex.ofReal_re (2 : ℝ))
  have hfx : (f x).re ≤ ‖x‖ := (RCLike.re_le_norm (f x)).trans (by
    simpa only [hf, one_mul] using f.le_opNorm x)
  have hgx : (g x).re ≤ ‖x‖ := (RCLike.re_le_norm (g x)).trans (by
    simpa only [hg, one_mul] using g.le_opNorm x)
  exact hfg (hunique x (by linarith) hf hg (by linarith) (by linarith))

end JdLG

