/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.LpConvexity
public import Mathlib.Analysis.Convex.Uniform

/-! # Uniform convexity of complex Lᵖ -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace JdLG

private theorem scalar_norm_rpow_quantitative_midpoint {r t : ℝ} (hr : 1 < r) (ht : 0 < t) :
    ∃ K > 0, ∀ z w : ℂ, ‖z - w‖ ^ r ≤ t * (‖z‖ ^ r + ‖w‖ ^ r) +
      K * ((‖z‖ ^ r + ‖w‖ ^ r) / 2 - ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w‖ ^ r) := by
  have hr₀ : 0 < r := by linarith
  let A (u : ℂ × ℂ) := ‖u.1‖ ^ r + ‖u.2‖ ^ r
  let B (u : ℂ × ℂ) := ‖u.1 - u.2‖ ^ r
  let D (u : ℂ × ℂ) := A u / 2 - ‖(1 / 2 : ℝ) • u.1 + (1 / 2 : ℝ) • u.2‖ ^ r
  have hD₀ (u : ℂ × ℂ) : 0 ≤ D u := by
    change 0 ≤ (‖u.1‖ ^ r + ‖u.2‖ ^ r) / 2 -
      ‖(1 / 2 : ℝ) • u.1 + (1 / 2 : ℝ) • u.2‖ ^ r
    linarith [norm_midpoint_rpow_le hr u.1 u.2]
  have hDcont : Continuous D := by
    dsimp [D, A]
    fun_prop (disch := positivity)
  let V := Metric.sphere (0 : ℂ × ℂ) 1 ∩ {u | t * A u ≤ B u}
  have hV : IsCompact V :=
    (isCompact_sphere _ _).inter_right (isClosed_le (by
      dsimp [A]
      fun_prop (disch := positivity)) (by
      dsimp [B]
      fun_prop (disch := positivity)))
  have hVpos (u : ℂ × ℂ) (hu : u ∈ V) : 0 < D u := by
    have hne : u.1 ≠ u.2 := by
      intro he
      have hu₁ : ‖u.1‖ = 1 := by
        have h := Metric.mem_sphere.mp hu.1
        rw [dist_zero_right, Prod.norm_def, ← he, max_self] at h
        exact h
      have hh : t * A u ≤ B u := hu.2
      dsimp [A, B] at hh
      rw [← he, hu₁, Real.one_rpow, sub_self, norm_zero, Real.zero_rpow hr₀.ne'] at hh
      linarith
    change 0 < (‖u.1‖ ^ r + ‖u.2‖ ^ r) / 2 -
      ‖(1 / 2 : ℝ) • u.1 + (1 / 2 : ℝ) • u.2‖ ^ r
    linarith [norm_midpoint_rpow_lt hr hne]
  have hex : ∃ δ > 0, ∀ u ∈ V, δ ≤ D u := by
    by_cases hne : V.Nonempty
    · obtain ⟨u, hu, hmin⟩ := hV.exists_isMinOn hne hDcont.continuousOn
      exact ⟨D u, hVpos u hu, fun z hz ↦ hmin hz⟩
    · exact ⟨1, zero_lt_one, fun u hu ↦ (hne ⟨u, hu⟩).elim⟩
  obtain ⟨δ, hδ, hDlb⟩ := hex
  let K := (2 : ℝ) ^ r / δ
  have hK : 0 < K := div_pos (Real.rpow_pos_of_pos (by norm_num) _) hδ
  have hS (u : ℂ × ℂ) (hu : u ∈ Metric.sphere (0 : ℂ × ℂ) 1) :
      B u ≤ t * A u + K * D u := by
    by_cases h : t * A u ≤ B u
    · have hu₁ : ‖u.1‖ ≤ 1 := by
        have hnorm : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
        exact (show ‖u.1‖ ≤ ‖u‖ by rw [Prod.norm_def]; exact le_max_left _ _).trans_eq hnorm
      have hu₂ : ‖u.2‖ ≤ 1 := by
        have hnorm : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hu
        exact (show ‖u.2‖ ≤ ‖u‖ by rw [Prod.norm_def]; exact le_max_right _ _).trans_eq hnorm
      have hB : B u ≤ (2 : ℝ) ^ r :=
        Real.rpow_le_rpow (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) hr₀.le
      have hD : δ ≤ D u := hDlb u ⟨hu, h⟩
      have hlt : (2 : ℝ) ^ r ≤ K * D u := by
        calc
          (2 : ℝ) ^ r = K * δ := by dsimp [K]; field_simp
          _ ≤ K * D u := mul_le_mul_of_nonneg_left hD hK.le
      exact hB.trans (hlt.trans (le_add_of_nonneg_left (mul_nonneg ht.le (by
        dsimp [A]
        positivity))))
    · exact (le_of_not_ge h).trans (le_add_of_nonneg_right (mul_nonneg hK.le (hD₀ u)))
  have hscale (c : ℝ) (hc : 0 ≤ c) (u : ℂ × ℂ) :
      A (c • u) = c ^ r * A u ∧ B (c • u) = c ^ r * B u ∧ D (c • u) = c ^ r * D u := by
    have hm : (1 / 2 : ℝ) • (c • u.1) + (1 / 2 : ℝ) • (c • u.2) =
        c • ((1 / 2 : ℝ) • u.1 + (1 / 2 : ℝ) • u.2) := by
      rw [smul_comm (1 / 2 : ℝ) c u.1, smul_comm (1 / 2 : ℝ) c u.2, smul_add]
    have hA : A (c • u) = c ^ r * A u := by
      dsimp [A]
      change ‖c • u.1‖ ^ r + ‖c • u.2‖ ^ r = _
      simp only [norm_smul, Real.norm_of_nonneg hc, Real.mul_rpow hc (norm_nonneg _),
        mul_add]
    refine ⟨hA, ?_, ?_⟩
    · change ‖c • u.1 - c • u.2‖ ^ r = c ^ r * ‖u.1 - u.2‖ ^ r
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc, Real.mul_rpow hc (norm_nonneg _)]
    · change A (c • u) / 2 - ‖(1 / 2 : ℝ) • (c • u.1) + (1 / 2 : ℝ) • (c • u.2)‖ ^ r =
        c ^ r * (A u / 2 - ‖(1 / 2 : ℝ) • u.1 + (1 / 2 : ℝ) • u.2‖ ^ r)
      rw [hA, hm, norm_smul, Real.norm_of_nonneg hc, Real.mul_rpow hc (norm_nonneg _)]
      ring
  refine ⟨K, hK, fun z w ↦ ?_⟩
  let u : ℂ × ℂ := (z, w)
  change B u ≤ t * A u + K * D u
  by_cases hu : u = 0
  · simp [hu, A, B, D, Real.zero_rpow hr₀.ne']
  let c := ‖u‖⁻¹
  have hc : 0 < c := inv_pos.mpr (norm_pos_iff.mpr hu)
  have hcu : c • u ∈ Metric.sphere (0 : ℂ × ℂ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg hc.le]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)
  have h := hS (c • u) hcu
  obtain ⟨ha, hb, hd⟩ := hscale c hc.le u
  rw [ha, hb, hd] at h
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hc r)).1
  calc
    c ^ r * B u ≤ t * (c ^ r * A u) + K * (c ^ r * D u) := h
    _ = c ^ r * (t * A u + K * D u) := by ring

section Lp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complex Lᵖ is uniformly convex for 1 < p < ∞ on any measure space.
Integrating a quantitative scalar midpoint inequality makes its modulus uniform
over all pairs of vectors in the unit sphere. -/
theorem uniformConvexSpace_complexLp (hp : 1 < p) (hp_top : p ≠ ∞) :
    UniformConvexSpace (Lp ℂ p μ) := by
  let r := p.toReal
  have hr : 1 < r := by
    simpa only [r, ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  have hr₀ : 0 < r := by linarith
  have hp₀ : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  refine ⟨fun ε hε ↦ ?_⟩
  let t := ε ^ r / 4
  have ht : 0 < t := div_pos (Real.rpow_pos_of_pos hε _) (by norm_num)
  obtain ⟨K, hK, hscalar⟩ := scalar_norm_rpow_quantitative_midpoint hr ht
  let b := max 0 (1 - ε ^ r / (2 * K))
  have hb₀ : 0 ≤ b := le_max_left _ _
  have hb₁ : b < 1 := max_lt_iff.2
    ⟨zero_lt_one, sub_lt_self _ (div_pos (Real.rpow_pos_of_pos hε _) (by positivity))⟩
  have hroot : b ^ r⁻¹ < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hb₀ hb₁ (inv_pos.mpr hr₀)
  refine ⟨2 - 2 * b ^ r⁻¹, by linarith, ?_⟩
  intro f hf g hg hfg
  let m : Lp ℂ p μ := (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g
  let F (x : X) := ‖f x‖ ^ r
  let G (x : X) := ‖g x‖ ^ r
  let D (x : X) := (F x + G x) / 2 - ‖m x‖ ^ r
  let B (x : X) := ‖(f - g) x‖ ^ r
  have hm : (m : X → ℂ) =ᵐ[μ] fun x ↦ (1 / 2 : ℝ) • f x + (1 / 2 : ℝ) • g x := by
    filter_upwards [Lp.coeFn_add ((1 / 2 : ℝ) • f) ((1 / 2 : ℝ) • g),
      Lp.coeFn_smul (1 / 2 : ℝ) f, Lp.coeFn_smul (1 / 2 : ℝ) g] with x ha hf₁ hg₁
    change m x = ((1 / 2 : ℝ) • f) x + ((1 / 2 : ℝ) • g) x at ha
    exact ha.trans (congrArg₂ (· + ·) hf₁ hg₁)
  have hpt : ∀ᵐ x ∂μ, B x ≤ t * (F x + G x) + K * D x := by
    filter_upwards [hm, Lp.coeFn_sub f g] with x hx hs
    change (f - g) x = f x - g x at hs
    simpa only [B, F, G, D, hx, hs] using hscalar (f x) (g x)
  have hFi : Integrable F μ := (Lp.memLp f).integrable_norm_rpow hp₀ hp_top
  have hGi : Integrable G μ := (Lp.memLp g).integrable_norm_rpow hp₀ hp_top
  have hMi := (Lp.memLp m).integrable_norm_rpow hp₀ hp_top
  have hBi : Integrable B μ := (Lp.memLp (f - g)).integrable_norm_rpow hp₀ hp_top
  have hDi : Integrable D μ := by
    exact (((hFi.add hGi).div_const 2).sub hMi)
  have hi : (∫ x, B x ∂μ) ≤ (∫ x, t * (F x + G x) + K * D x ∂μ) :=
    integral_mono_ae hBi (((hFi.add hGi).const_mul t).add (hDi.const_mul K)) hpt
  have hF : (∫ x, F x ∂μ) = 1 := by
    change (∫ x, ‖f x‖ ^ p.toReal ∂μ) = 1
    rw [← lp_norm_rpow_eq_integral μ hp₀ hp_top f, hf, Real.one_rpow]
  have hG : (∫ x, G x ∂μ) = 1 := by
    change (∫ x, ‖g x‖ ^ p.toReal ∂μ) = 1
    rw [← lp_norm_rpow_eq_integral μ hp₀ hp_top g, hg, Real.one_rpow]
  have hsum : (∫ x, F x + G x ∂μ) = 2 := by rw [integral_add hFi hGi, hF, hG]; norm_num
  have hD : (∫ x, D x ∂μ) = 1 - ‖m‖ ^ r := by
    calc
      _ = (∫ x, (F x + G x) / 2 ∂μ) - ∫ x, ‖m x‖ ^ r ∂μ :=
        integral_sub ((hFi.add hGi).div_const 2) hMi
      _ = _ := by
        rw [integral_div, hsum, ← lp_norm_rpow_eq_integral μ hp₀ hp_top m, div_self (by norm_num)]
  have hIntSum :
      (∫ x, t * (F x + G x) + K * D x ∂μ) = 2 * t + K * (1 - ‖m‖ ^ r) := by
    calc
      _ = (∫ x, t * (F x + G x) ∂μ) + ∫ x, K * D x ∂μ :=
        integral_add ((hFi.add hGi).const_mul t) (hDi.const_mul K)
      _ = _ := by rw [integral_const_mul, integral_const_mul, hsum, hD, mul_comm t]
  have hB : ‖f - g‖ ^ r = ∫ x, B x ∂μ := lp_norm_rpow_eq_integral μ hp₀ hp_top _
  have hbound := (Real.rpow_le_rpow hε.le hfg hr₀.le).trans
    (hB.trans_le (hi.trans_eq hIntSum))
  have hgap : ε ^ r / (2 * K) ≤ 1 - ‖m‖ ^ r := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * K)).2
    dsimp [t] at hbound
    linarith
  have hmPow : ‖m‖ ^ r ≤ b := (show ‖m‖ ^ r ≤ 1 - ε ^ r / (2 * K) by linarith).trans
    (le_max_right _ _)
  have hmLe : ‖m‖ ≤ b ^ r⁻¹ := by
    calc
      ‖m‖ = (‖m‖ ^ r) ^ r⁻¹ := by
        rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hr₀.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hmPow (inv_nonneg.mpr hr₀.le)
  have hM : ‖m‖ = (1 / 2 : ℝ) * ‖f + g‖ := by
    dsimp [m]
    rw [← smul_add, norm_smul, Real.norm_of_nonneg (by norm_num)]
  rw [hM] at hmLe
  linarith

end Lp

end JdLG
