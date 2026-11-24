/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconTailHaar

/-! # Polynomial limits along the multiples of Chacon's tower heights -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Translations by a fixed multiple of `3^n` converge strongly on odometer L¹. -/
theorem tendsto_integral_norm_chaconTranslate (m : ℕ)
    {F : ChaconOdometer → ℂ} (hF : Integrable F chaconOdometerMeasure) :
    Tendsto (fun n : ℕ ↦ ∫ x, ‖F (x + 3^n*m) - F x‖ ∂chaconOdometerMeasure) atTop (𝓝 0) := by
  let v := (memLp_one_iff_integrable.mpr hF).toLp F
  let a (n : ℕ) : ChaconOdometer := 3^n*m
  let v' (n : ℕ) := Lp.compMeasurePreserving (fun x ↦ x + a n)
    (chaconOdometer_translate_preserving (a n)) v
  have hshift : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_chaconOdometer_pow_three.mul_const (m : ChaconOdometer)
  have hlim : Tendsto v' atTop (𝓝 v) :=
    (tendsto_chaconOdometer_translate_Lp_general (p := 1) (by simp) v).comp hshift
  have hv := (memLp_one_iff_integrable.mpr hF).coeFn_toLp
  have he (n : ℕ) : (∫ x, ‖F (x + a n) - F x‖ ∂chaconOdometerMeasure) = ‖v' n - v‖ := by
    change (∫ x, ‖((F ∘ fun y ↦ y + a n) - F) x‖ ∂chaconOdometerMeasure) = _
    rw [L1.norm_sub_eq_lintegral,
      integral_norm_eq_lintegral_eNorm
        ((((chaconOdometer_translate_preserving (a n)).integrable_comp_of_integrable hF).sub hF).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving v (chaconOdometer_translate_preserving (a n)),
      (chaconOdometer_translate_preserving (a n)).quasiMeasurePreserving.ae_eq_comp hv, hv] with x h₁ h₂ h₃
    change ‖F (x + a n) - F x‖ₑ = ‖v' n x - v x‖ₑ
    rw [h₁, h₃]
    congr 2
    exact h₂.symm
  have hn : Tendsto (fun n ↦ ‖v' n - v‖) atTop (𝓝 0) := by simpa using (hlim.sub_const v).norm
  exact hn.congr fun n ↦ (he n).symm

private theorem tendsto_chaconWeightedTailTranslate (m : ℕ)
    {A : Set ChaconOdometer} (hA : MeasurableSet A)
    {F g : ChaconOdometer → ℂ} (hF : Integrable F chaconOdometerMeasure)
    (hgm : Measurable g) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hgb : ∀ x, ‖g x‖ ≤ C₀) :
    Tendsto (fun n : ℕ ↦ ∫ x in chaconTail n ⁻¹' A, g x * F (x + 3^n*m) ∂chaconOdometerMeasure)
      atTop (𝓝 (chaconOdometerMeasure.real A • ∫ x, g x * F x ∂chaconOdometerMeasure)) := by
  let I (n : ℕ) := ∫ x in chaconTail n ⁻¹' A, g x * F (x + 3^n*m) ∂chaconOdometerMeasure
  let J (n : ℕ) := ∫ x in chaconTail n ⁻¹' A, g x * F x ∂chaconOdometerMeasure
  have hgF (G : ChaconOdometer → ℂ) (hG : Integrable G chaconOdometerMeasure) :
      Integrable (fun x ↦ g x * G x) chaconOdometerMeasure := by
    refine (hG.norm.const_mul C₀).mono' (hgm.aestronglyMeasurable.mul hG.aestronglyMeasurable) ?_
    exact ae_of_all _ fun x ↦ (norm_mul ..).le.trans (mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _))
  have hJ := tendsto_integral_chaconTail_preimage A hA (hgF F hF)
  have hnorm (n : ℕ) : ‖I n - J n‖ ≤
      C₀ * ∫ x, ‖F (x + 3^n*m) - F x‖ ∂chaconOdometerMeasure := by
    let S := chaconTail n ⁻¹' A
    let G (x : ChaconOdometer) := F (x + 3^n*m)
    have hG : Integrable G chaconOdometerMeasure :=
      (chaconOdometer_translate_preserving (3^n*m)).integrable_comp_of_integrable hF
    change ‖(∫ x in S, g x * G x ∂chaconOdometerMeasure) -
      (∫ x in S, g x * F x ∂chaconOdometerMeasure)‖ ≤ _
    rw [← integral_sub (hgF G hG).integrableOn (hgF F hF).integrableOn]
    calc
      _ ≤ ∫ x in S, ‖g x * G x - g x * F x‖ ∂chaconOdometerMeasure :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x in S, C₀ * ‖G x - F x‖ ∂chaconOdometerMeasure := by
        have h₀ : Integrable (fun x ↦ ‖g x * G x - g x * F x‖) chaconOdometerMeasure :=
          ((hgF G hG).sub (hgF F hF)).norm
        have h₁ : Integrable (fun x ↦ C₀ * ‖G x - F x‖) chaconOdometerMeasure :=
          (hG.sub hF).norm.const_mul C₀
        refine integral_mono h₀.integrableOn h₁.integrableOn (fun x ↦ ?_)
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _)
      _ ≤ ∫ x, C₀ * ‖G x - F x‖ ∂chaconOdometerMeasure :=
        integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ ↦ mul_nonneg hC₀ (norm_nonneg _))
          ((hG.sub hF).norm.const_mul C₀)
      _ = _ := integral_const_mul _ _
  have hz : Tendsto (fun n ↦ I n - J n) atTop (𝓝 0) := by
    apply squeeze_zero_norm hnorm
    simpa using (tendsto_integral_norm_chaconTranslate m hF).const_mul C₀
  have he (n : ℕ) : I n - J n + J n = I n := sub_add_cancel _ _
  simpa only [zero_add] using (hz.add hJ).congr he

/-- The tower action formula using the high-digit tail directly, including
after a fixed additional tower offset. -/
theorem chaconTower_act_tail (n m : ℕ) (x : ChaconOdometer) (j : ℤ) :
    chaconTowerSystem.act (Multiplicative.ofAdd (↑(m*chaconTowerHeight n) : ℤ))
        (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false)) =
      chaconTowerSystem.act (Multiplicative.ofAdd (-(chaconSpacerCount m (chaconTail n x) : ℤ)))
        (chaconTowerSystem.act (Multiplicative.ofAdd j) (x + 3^n*m, false)) := by
  let r := PadicInt.toZModPow (p := 3) n x
  have hx := chaconScaleBranch_tail n x
  have he := chaconTower_action_at_height n m r.val (ZMod.val_lt r) (chaconTail n x)
  change (3 : ChaconOdometer)^n * chaconTail n x + (r.val : ChaconOdometer) = x at hx
  have hshift : (3 : ChaconOdometer)^n*(chaconTail n x + m) + (r.val : ChaconOdometer) =
      x + 3^n*m := calc
    _ = ((3 : ChaconOdometer)^n*chaconTail n x + (r.val : ChaconOdometer)) + 3^n*m := by ring
    _ = _ := by rw [hx]
  have hcomm (a b : ℤ) (w : ChaconOdometer × Bool) :
      chaconTowerSystem.act (Multiplicative.ofAdd a) (chaconTowerSystem.act (Multiplicative.ofAdd b) w) =
      chaconTowerSystem.act (Multiplicative.ofAdd b) (chaconTowerSystem.act (Multiplicative.ofAdd a) w) := by
    rw [← Function.comp_apply (f := chaconTowerSystem.act (Multiplicative.ofAdd a)),
      ← chaconTowerSystem.act_mul, mul_comm, chaconTowerSystem.act_mul]
    rfl
  rw [hx, hshift] at he
  rw [hcomm _ j, hcomm _ j, he]

/-- The coefficients of the height-multiple limit, as spacer probabilities. -/
noncomputable def chaconSpacerProbability (m k : ℕ) : ℝ :=
  chaconOdometerMeasure.real {x | chaconSpacerCount m x = k}

private theorem tendsto_chaconTowerOffset (m : ℕ) (j : ℤ)
    {f : ChaconOdometer × Bool → ℂ} {g : ChaconOdometer → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hD : 0 ≤ D)
    (hfb : ∀ x, ‖f x‖ ≤ C) (hgb : ∀ x, ‖g x‖ ≤ D) :
    Tendsto (fun n : ℕ ↦ ∫ x, g x *
      f (chaconTowerSystem.act (Multiplicative.ofAdd (↑(m*chaconTowerHeight n) : ℤ))
        (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false))) ∂chaconOdometerMeasure) atTop
      (𝓝 (∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
        ∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ)))
          (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false))) ∂chaconOdometerMeasure)) := by
  let A (k : ℕ) : Set ChaconOdometer := {x | chaconSpacerCount m x = k}
  let F (k : ℕ) (x : ChaconOdometer) :=
    f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ)))
      (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false)))
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurable_chaconSpacerCount m (measurableSet_singleton _)
  have hF (k : ℕ) : Measurable (F k) :=
    hf.comp ((chaconTowerSystem.preserves _).measurable.comp
      ((chaconTowerSystem.preserves _).measurable.comp (measurable_id.prodMk measurable_const)))
  have hFi (k : ℕ) : Integrable (F k) chaconOdometerMeasure :=
    Integrable.of_bound (hF k).aestronglyMeasurable C (ae_of_all _ fun _ ↦ hfb _)
  have hlim (k : ℕ) := tendsto_chaconWeightedTailTranslate m (hA k) (hFi k) hg hD hgb
  refine (tendsto_finsetSum _ fun k _ ↦ hlim k).congr fun n ↦ ?_
  rw [← Finset.sum_congr rfl (fun k _ ↦ integral_indicator (measurable_chaconTail n (hA k)))]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    refine ae_of_all _ fun x ↦ ?_
    have h := chaconSpacerCount_le m (chaconTail n x)
    simp only [Set.indicator, mem_preimage, A, mem_ofPred_eq, Finset.sum_ite_eq,
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h), ite_true, F, chaconTower_act_tail]
  · intro k _
    apply Integrable.indicator _ (measurable_chaconTail n (hA k))
    have hm : Measurable (fun x : ChaconOdometer ↦ F k (x + 3^n*m)) :=
      (hF k).comp (measurable_id.add measurable_const)
    exact Integrable.of_bound (hg.mul hm).aestronglyMeasurable (D*C) (ae_of_all _ fun x ↦
      (norm_mul _ _).le.trans (mul_le_mul (hgb x) (hfb _) (norm_nonneg _) hD))

/-- Integrating on the tower amounts to integrating on its bottom and its
occupied top, then applying the common normalization. -/
theorem integral_chaconTower_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {H : ChaconOdometer × Bool → E}
    (hH : Measurable H) {C : ℝ} (hC : ∀ x, ‖H x‖ ≤ C) :
    (∫ x, H x ∂chaconTowerSystem.measure) =
      ((1 + chaconOdometerMeasure chaconSpacer)⁻¹).toReal •
        ((∫ x, H (x, false) ∂chaconOdometerMeasure) +
          ∫ x in chaconSpacer, H (x, true) ∂chaconOdometerMeasure) := by
  let μ := chaconOdometerMeasure
  let b : ChaconOdometer → ChaconOdometer × Bool := towerBottom
  let t : ChaconOdometer → ChaconOdometer × Bool := towerTop
  have hb : Measurable b := measurable_id.prodMk measurable_const
  have ht : Measurable t := measurable_id.prodMk measurable_const
  have hbi : Integrable H (μ.map b) := Integrable.of_bound hH.aestronglyMeasurable _ (ae_of_all _ hC)
  have hti : Integrable H ((μ.restrict chaconSpacer).map t) :=
    Integrable.of_bound hH.aestronglyMeasurable _ (ae_of_all _ hC)
  change (∫ x, H x ∂((1 + μ chaconSpacer)⁻¹ • (μ.map b + (μ.restrict chaconSpacer).map t))) = _
  rw [integral_smul_measure, integral_add_measure hbi hti,
    integral_map hb.aemeasurable hbi.aestronglyMeasurable, integral_map ht.aemeasurable hti.aestronglyMeasurable]
  rfl

/-- The correlation version of the polynomial weak limit along `m*h_n`, for
all bounded measurable complex observables, with the sign convention of the
paper's Koopman action. -/
theorem tendsto_chaconTower_polynomial_correlations (m : ℕ)
    {f g : ChaconOdometer × Bool → ℂ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hD : 0 ≤ D)
    (hfb : ∀ x, ‖f x‖ ≤ C) (hgb : ∀ x, ‖g x‖ ≤ D) :
    Tendsto (fun n : ℕ ↦ ∫ x, g x *
      f (chaconTowerSystem.act (Multiplicative.ofAdd (↑(m*chaconTowerHeight n) : ℤ)) x)
          ∂chaconTowerSystem.measure) atTop
      (𝓝 (∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
        ∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ))) x)
          ∂chaconTowerSystem.measure)) := by
  let μ := chaconOdometerMeasure
  let c := ((1 + μ chaconSpacer)⁻¹).toReal
  let b (x : ChaconOdometer) := g (x, false)
  let t := chaconSpacer.indicator (fun x : ChaconOdometer ↦ g (x, true))
  let I (k : ℤ) := ∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd k) x)
    ∂chaconTowerSystem.measure
  let J (j : ℤ) (q : ChaconOdometer → ℂ) (k : ℤ) :=
    ∫ x, q x * f (chaconTowerSystem.act (Multiplicative.ofAdd k)
      (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false))) ∂μ
  have hb : Measurable b := hg.comp (measurable_id.prodMk measurable_const)
  have ht : Measurable t := (hg.comp (measurable_id.prodMk measurable_const)).indicator chaconSpacer_measurable
  have htNorm (x : ChaconOdometer) : ‖t x‖ ≤ D := by
    by_cases h : x ∈ chaconSpacer
    · simpa only [t, indicator_of_mem h] using hgb (x, true)
    · simpa only [t, indicator_of_notMem h, norm_zero] using hD
  have hbot := tendsto_chaconTowerOffset m 0 hf hb hD hfb (fun x ↦ hgb (x, false))
  have htop := tendsto_chaconTowerOffset m 1 hf ht hD hfb htNorm
  have hI (k : ℤ) : I k = c • (J 0 b k + J 1 t k) := by
    have hp : Measurable (fun x ↦ g x * f (chaconTowerSystem.act (Multiplicative.ofAdd k) x)) :=
      hg.mul (hf.comp (chaconTowerSystem.preserves _).measurable)
    change _ = _
    rw [show I k = (∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd k) x)
      ∂chaconTowerSystem.measure) from rfl, integral_chaconTower_split hp (C := D*C) (fun x ↦
      (norm_mul _ _).le.trans (mul_le_mul (hgb x) (hfb _) (norm_nonneg _) hD))]
    congr 1
    have hB : J 0 b k = ∫ x, b x * f (chaconTowerSystem.act (Multiplicative.ofAdd k) (x, false)) ∂μ := by
      unfold J
      rw [show Multiplicative.ofAdd (0 : ℤ) = 1 by rfl, chaconTowerSystem.act_one]
      rfl
    rw [hB]
    congr 1
    unfold J
    rw [← integral_indicator chaconSpacer_measurable]
    apply integral_congr_ae
    refine ae_of_all _ fun x ↦ ?_
    by_cases h : x ∈ chaconSpacer
    · simp only [indicator_of_mem h, t, chaconTower_bottom_step, h, ite_true]
    · simp only [indicator_of_notMem h, t, zero_mul]
  have hfilt : Tendsto (fun n : ℕ ↦ c • (J 0 b (m*chaconTowerHeight n) +
      J 1 t (m*chaconTowerHeight n))) atTop
      (𝓝 (c • ((∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • J 0 b (-(k : ℤ))) +
        (∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • J 1 t (-(k : ℤ)))))) :=
    tendsto_const_nhds.smul (hbot.add htop)
  change Tendsto (fun n : ℕ ↦ I (m * chaconTowerHeight n)) atTop
      (𝓝 (∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • I (-(k : ℤ))))
  simp only [hI, smul_comm (α := ℂ) _ c, smul_add, Finset.sum_add_distrib, ← Finset.smul_sum]
  simpa only [smul_add] using hfilt

end Mixing
