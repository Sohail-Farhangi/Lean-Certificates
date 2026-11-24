/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconMovingTailTests

/-! # The polynomial error for height multiples with sub-height remainders -/

@[expose] public section

open MeasureTheory Set Filter
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem chacon_move_correlation (a r : ℤ)
    {f g : ChaconOdometer × Bool → ℂ} (hf : Measurable f) (hg : Measurable g) :
    (∫ x, g (chaconTowerSystem.act (Multiplicative.ofAdd (-r)) x) *
        f (chaconTowerSystem.act (Multiplicative.ofAdd a) x) ∂chaconTowerSystem.measure) =
      ∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd (a+r)) x) ∂chaconTowerSystem.measure := by
  let S := chaconTowerSystem
  let H (x : ChaconOdometer × Bool) := g (S.act (Multiplicative.ofAdd (-r)) x) *
    f (S.act (Multiplicative.ofAdd a) x)
  have hH : Measurable H := (hg.comp (S.preserves _).measurable).mul (hf.comp (S.preserves _).measurable)
  have h := integral_map (S.preserves (Multiplicative.ofAdd r)).measurable.aemeasurable
    (μ := S.measure) hH.aestronglyMeasurable
  rw [(S.preserves _).map_eq] at h
  change (∫ x, H x ∂S.measure) = _
  rw [h]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  have hcomp (b : ℤ) :
      S.act (Multiplicative.ofAdd b) (S.act (Multiplicative.ofAdd r) x) =
        S.act (Multiplicative.ofAdd (b+r)) x := by
    change (S.act (Multiplicative.ofAdd b) ∘ S.act (Multiplicative.ofAdd r)) x = _
    rw [← S.act_mul]
    rfl
  simp only [H, hcomp, neg_add_cancel, show Multiplicative.ofAdd (0 : ℤ) = 1 by rfl,
    S.act_one, id_eq]
  rfl

/-- Moving remainder estimate for a fixed finite-prefix test on the first
coordinate of the correlation and an arbitrary bounded observable on the
second coordinate. The hypothesis is `|r_n|/h_n → 0`. -/
theorem tendsto_chaconTower_movingRemainder_error (m N : ℕ) (r : ℕ → ℤ)
    (hr : Tendsto (fun n ↦ ((r n).natAbs : ℝ) / chaconTowerHeight n) atTop (𝓝 0))
    {f g : ChaconOdometer × Bool → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hprefix : ∀ (x : ChaconOdometer) (b : Bool), g (x, b) = g (chaconPrefix N x, b))
    {C D : ℝ} (hD : 0 ≤ D) (hfb : ∀ x, ‖f x‖ ≤ C) (hgb : ∀ x, ‖g x‖ ≤ D) :
    Tendsto (fun n : ℕ ↦ (∫ x, g x *
      f (chaconTowerSystem.act (Multiplicative.ofAdd ((m*chaconTowerHeight n : ℕ) + r n)) x)
        ∂chaconTowerSystem.measure) -
      ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
        ∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ)+r n)) x)
          ∂chaconTowerSystem.measure) atTop (𝓝 0) := by
  let S := chaconTowerSystem
  let μ := chaconOdometerMeasure
  let c := ((1 + μ chaconSpacer)⁻¹).toReal
  let E (n : ℕ) := chaconUnsafePrefix n (r n).natAbs
  let G (n : ℕ) (x : ChaconOdometer × Bool) := g (S.act (Multiplicative.ofAdd (-(r n))) x)
  let B (n : ℕ) (x : ChaconOdometer) := G n (x, false)
  let T (n : ℕ) := chaconSpacer.indicator (fun x : ChaconOdometer ↦ G n (x, true))
  have hG (n : ℕ) : Measurable (G n) := hg.comp (S.preserves _).measurable
  have hB (n : ℕ) : Measurable (B n) := (hG n).comp (measurable_id.prodMk measurable_const)
  have hT (n : ℕ) : Measurable (T n) :=
    ((hG n).comp (measurable_id.prodMk measurable_const)).indicator chaconSpacer_measurable
  have hTb (n : ℕ) (x : ChaconOdometer) : ‖T n x‖ ≤ D := by
    by_cases hx : x ∈ chaconSpacer
    · simpa only [T, indicator_of_mem hx] using hgb _
    · simpa only [T, indicator_of_notMem hx, norm_zero] using hD
  have hE (n : ℕ) : MeasurableSet (E n) := chaconUnsafePrefix_measurable _ _
  have hprob : Tendsto (fun n ↦ μ.real (E n)) atTop (𝓝 0) :=
    tendsto_measureReal_chaconUnsafePrefix _ hr
  have hsafe (n : ℕ) (hn : N ≤ n) (x : ChaconOdometer) (hx : x ∉ E n) (b : Bool) :
      G n (x,b) = G n (chaconPrefix n x,b) := by
    apply chaconTower_safePrefix_test hn g hprefix (-(r n)) x _ b
    simpa only [Int.natAbs_neg] using hx
  have hbp : ∀ᶠ n in atTop, ∀ x ∉ E n, B n x = B n (chaconPrefix n x) :=
    (eventually_ge_atTop N).mono fun n hn x hx ↦ hsafe n hn x hx false
  have htp : ∀ᶠ n in atTop, ∀ x ∉ E n, T n x = T n (chaconPrefix n x) := by
    filter_upwards [eventually_ge_atTop N] with n hn x hx
    let a := chaconPrefixIndex n x
    have ha : a+1 < 3^n := by
      have h : ¬(a < (r n).natAbs ∨ 3^n ≤ a+(r n).natAbs+1) := hx
      omega
    have he : chaconScaleBranch n a (chaconTail n x) = x := chaconScaleBranch_tail n x
    have hsp := chaconSpacer_scaleBranch_iff n a ha (chaconTail n x)
    rw [he] at hsp
    change x ∈ chaconSpacer ↔ chaconPrefix n x ∈ chaconSpacer at hsp
    simp only [T, Set.indicator, ← hsp, hsafe n hn x hx true]
  let M (j : ℤ) (q : ℕ → ChaconOdometer → ℂ) (n : ℕ) (a : ℤ) :=
    ∫ x, q n x * f (S.act (Multiplicative.ofAdd a) (S.act (Multiplicative.ofAdd j) (x,false))) ∂μ
  let a (n : ℕ) : ℤ := m*chaconTowerHeight n
  let J (n : ℕ) (k : ℤ) := ∫ x, G n x * f (S.act (Multiplicative.ofAdd k) x) ∂S.measure
  have hb := tendsto_chaconTowerOffset_moving_error m 0 hf hfb B hB hD
    (fun n x ↦ hgb _) E hE hprob hbp
  have ht := tendsto_chaconTowerOffset_moving_error m 1 hf hfb T hT hD hTb E hE hprob htp
  change Tendsto (fun n ↦ M 0 B n (a n) -
    ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • M 0 B n (-(k : ℤ))) atTop (𝓝 0) at hb
  change Tendsto (fun n ↦ M 1 T n (a n) -
    ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • M 1 T n (-(k : ℤ))) atTop (𝓝 0) at ht
  have hJ (n : ℕ) (k : ℤ) : J n k = c • (M 0 B n k + M 1 T n k) := by
    have hp : Measurable (fun x ↦ G n x * f (S.act (Multiplicative.ofAdd k) x)) :=
      (hG n).mul (hf.comp (S.preserves _).measurable)
    unfold J
    rw [integral_chaconTower_split hp (C := D*C) (fun x ↦
      (norm_mul _ _).le.trans (mul_le_mul (hgb _) (hfb _) (norm_nonneg _) hD))]
    congr 1
    have hBot : M 0 B n k = ∫ x, B n x * f (S.act (Multiplicative.ofAdd k) (x,false)) ∂μ := by
      unfold M
      rw [show Multiplicative.ofAdd (0 : ℤ) = 1 by rfl, S.act_one]
      rfl
    rw [hBot]
    congr 1
    unfold M
    rw [← integral_indicator chaconSpacer_measurable]
    apply integral_congr_ae
    refine ae_of_all _ fun x ↦ ?_
    by_cases h : x ∈ chaconSpacer
    · simp only [indicator_of_mem h, T, S, chaconTower_bottom_step, h, ite_true]
    · simp only [indicator_of_notMem h, T, zero_mul]
  have hsum : Tendsto (fun n ↦ c •
      ((M 0 B n (a n) - ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • M 0 B n (-(k : ℤ))) +
        (M 1 T n (a n) - ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • M 1 T n (-(k : ℤ)))))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
    simpa only [zero_add, smul_zero] using hc.smul (hb.add ht)
  have he (n : ℕ) :
      c • ((M 0 B n (a n) - ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • M 0 B n (-(k : ℤ))) +
        (M 1 T n (a n) - ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • M 1 T n (-(k : ℤ)))) =
      J n (a n) - ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • J n (-(k : ℤ)) := by
    simp only [hJ, smul_add, smul_sub, smul_comm (α := ℂ) _ c, Finset.sum_add_distrib, ← Finset.smul_sum]
    abel
  have hmove (n : ℕ) (k : ℤ) : J n k =
      ∫ x, g x * f (S.act (Multiplicative.ofAdd (k+r n)) x) ∂S.measure :=
    chacon_move_correlation k (r n) hf hg
  change Tendsto (fun n : ℕ ↦ (∫ x, g x * f (S.act (Multiplicative.ofAdd (a n+r n)) x) ∂S.measure) -
    ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
      ∫ x, g x * f (S.act (Multiplicative.ofAdd (-(k : ℤ)+r n)) x) ∂S.measure) atTop (𝓝 0)
  simpa only [hmove] using hsum.congr he

end Mixing
