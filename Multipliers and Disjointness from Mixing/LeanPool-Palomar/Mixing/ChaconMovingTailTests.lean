/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconSafePrefixMeasure
public import Mixing.ChaconTowerPolynomialLimits

/-! # Tail independence with a test allowed to move inside a tower -/

@[expose] public section

open MeasureTheory Set Filter
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A bounded moving test remains asymptotically independent of a tail event
after multiplication by any fixed integrable function, provided it agrees
with its prefix evaluation off events of vanishing probability. -/
theorem tendsto_chacon_moving_tail_error {A : Set ChaconOdometer} (hA : MeasurableSet A)
    {F : ChaconOdometer → ℂ} (hF : Integrable F chaconOdometerMeasure)
    (g : ℕ → ChaconOdometer → ℂ) (hgm : ∀ n, Measurable (g n))
    {D : ℝ} (hD : 0 ≤ D) (hgb : ∀ n x, ‖g n x‖ ≤ D)
    (E : ℕ → Set ChaconOdometer) (hE : ∀ n, MeasurableSet (E n))
    (hprob : Tendsto (fun n ↦ chaconOdometerMeasure.real (E n)) atTop (𝓝 0))
    (hprefix : ∀ᶠ n in atTop, ∀ x ∉ E n, g n x = g n (chaconPrefix n x)) :
    Tendsto (fun n ↦
      (∫ x in chaconTail n ⁻¹' A, g n x * F x ∂chaconOdometerMeasure) -
        chaconOdometerMeasure.real A • (∫ x, g n x * F x ∂chaconOdometerMeasure)) atTop (𝓝 0) := by
  let μ := chaconOdometerMeasure
  let c := μ.real A
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c ≤ 1 := measureReal_le_one
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε / (8*(D+1))
  have hη : 0 < η := by unfold η; positivity
  obtain ⟨G, hFG, hG⟩ := hF.exists_boundedContinuous_integral_sub_le hη
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous G.continuous) η hη
  have hp : Tendsto (fun n : ℕ ↦ ((3 : ℝ)⁻¹)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbad : Tendsto (fun n ↦ (2*D*‖G‖) * μ.real (E n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hprob.const_mul (2*D*‖G‖)
  filter_upwards [(tendsto_order.mp hp).2 δ hδ, (tendsto_order.mp hbad).2 (ε/8) (by linarith),
    hprefix] with n hn hsmall hsafe
  let f (x : ChaconOdometer) := g n x * F x
  let J (x : ChaconOdometer) := g n x * G x
  let Q := J ∘ chaconPrefix n
  let W := (E n).indicator (fun _ : ChaconOdometer ↦ (2*D*‖G‖ : ℝ))
  have hfi : Integrable f μ := by
    refine (hF.norm.const_mul D).mono' ((hgm n).aestronglyMeasurable.mul hF.aestronglyMeasurable) ?_
    exact ae_of_all _ (fun x ↦ (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right (hgb n x) (norm_nonneg _)))
  have hQi : Integrable Q μ := by
    refine Integrable.of_bound (((hgm n).mul G.continuous.measurable).comp
      (measurable_chaconPrefix n)).aestronglyMeasurable (D*‖G‖) (ae_of_all _ fun x ↦ ?_)
    exact (norm_mul _ _).le.trans (mul_le_mul (hgb n _) (G.norm_coe_le_norm _) (norm_nonneg _) hD)
  have hWi : Integrable W μ := (integrable_const _).indicator (hE n)
  have hd (x : ChaconOdometer) : ‖G x - G (chaconPrefix n x)‖ ≤ η := by
    have he := hU (dist_chaconPrefix_le n x |>.trans_lt hn)
    simpa only [dist_eq_norm] using he.le
  have hnorm (x : ChaconOdometer) :
      ‖f x - Q x‖ ≤ D * (‖F x - G x‖ + η) + W x := by
    let y := chaconPrefix n x
    calc
      ‖f x - Q x‖ ≤ ‖g n x * F x - g n x * G y‖ + ‖g n x * G y - g n y * G y‖ := by
        change ‖g n x * F x - g n y * G y‖ ≤ _
        have h := dist_triangle (g n x * F x) (g n x * G y) (g n y * G y)
        simpa only [dist_eq_norm] using h
      _ ≤ D * (‖F x - G x‖ + η) + W x := by
        rw [← mul_sub, ← sub_mul, norm_mul, norm_mul]
        refine add_le_add (mul_le_mul (hgb n x) ?_ (norm_nonneg _) hD) ?_
        · have hh := dist_triangle (F x) (G x) (G y)
          simp only [dist_eq_norm] at hh
          exact hh.trans (add_le_add_right (hd x) _)
        · by_cases h : x ∈ E n
          · rw [show W x = 2*D*‖G‖ from indicator_of_mem h _]
            have hGG : ‖g n x - g n y‖ ≤ 2*D := by
              have hh := (norm_sub_le (g n x) (g n y)).trans (add_le_add (hgb n x) (hgb n y))
              linarith
            exact mul_le_mul hGG (G.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
          · rw [show W x = 0 from indicator_of_notMem h _,
              show g n x = g n y from hsafe x h, sub_self, norm_zero, zero_mul]
  have hcost : (∫ x, ‖f x - Q x‖ ∂μ) < 3*ε/8 := by
    let M (x : ChaconOdometer) := ‖F x - G x‖ + η
    have hMi : Integrable M μ := ((hF.sub hG).norm.add (integrable_const _))
    calc
      _ ≤ ∫ x, D * M x + W x ∂μ := integral_mono (hfi.sub hQi).norm
        ((hMi.const_mul D).add hWi) hnorm
      _ = D * ((∫ x, ‖F x - G x‖ ∂μ) + η) + (2*D*‖G‖)*μ.real (E n) := by
        rw [integral_add (hMi.const_mul D) hWi, integral_const_mul, show
          (∫ x, M x ∂μ) = (∫ x, ‖F x - G x‖ ∂μ) + η by
            change (∫ x, ‖(F - ⇑G) x‖ + η ∂μ) = _
            rw [integral_add (hF.sub hG).norm (integrable_const _), integral_const, probReal_univ, one_smul]
            rfl,
          integral_indicator_const _ (hE n), smul_eq_mul, mul_comm (μ.real (E n))]
      _ < 3*ε/8 := by
        have hηbound : D * (η+η) ≤ ε/4 := by
          dsimp [η]
          have hpos : 0 < 8*(D+1) := by positivity
          field_simp
          nlinarith
        have he₁ := mul_le_mul_of_nonneg_left (add_le_add_right hFG η) hD
        linarith only [he₁.trans hηbound, hsmall]
  let S := chaconTail n ⁻¹' A
  have hind : (∫ x in S, Q x ∂μ) = c • ∫ x, Q x ∂μ :=
    integral_chaconPrefix_tail_preimage n A hA J hQi
  have hsub : (∫ x in S, f x ∂μ) - c • (∫ x, f x ∂μ) =
      (∫ x in S, f x - Q x ∂μ) - c • (∫ x, f x - Q x ∂μ) := by
    rw [integral_sub hfi hQi, integral_sub hfi.integrableOn hQi.integrableOn, smul_sub, ← hind]
    abel
  have hL : ‖∫ x in S, f x - Q x ∂μ‖ < 3*ε/8 :=
    (norm_integral_le_integral_norm _).trans_lt
      ((integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ ↦ norm_nonneg _)
        (hfi.sub hQi).norm).trans_lt hcost)
  have hR : ‖c • ∫ x, f x - Q x ∂μ‖ < 3*ε/8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact ((mul_le_of_le_one_left (norm_nonneg _) hc1).trans
      (norm_integral_le_integral_norm _)).trans_lt hcost
  rw [dist_zero_right]
  change ‖(∫ x in S, f x ∂μ) - c • (∫ x, f x ∂μ)‖ < ε
  rw [hsub]
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- A fixed translation by a multiple of the prefix scale contributes
vanishing error even when the other test is moving. -/
theorem tendsto_chacon_moving_translate_error (m : ℕ) (A : Set ChaconOdometer)
    {F : ChaconOdometer → ℂ} (hF : Integrable F chaconOdometerMeasure)
    (g : ℕ → ChaconOdometer → ℂ) (hgm : ∀ n, Measurable (g n))
    {D : ℝ} (hD : 0 ≤ D) (hgb : ∀ n x, ‖g n x‖ ≤ D) :
    Tendsto (fun n ↦
      (∫ x in chaconTail n ⁻¹' A, g n x * F (x + 3^n*m) ∂chaconOdometerMeasure) -
        (∫ x in chaconTail n ⁻¹' A, g n x * F x ∂chaconOdometerMeasure)) atTop (𝓝 0) := by
  have hgI (n : ℕ) (G : ChaconOdometer → ℂ) (hG : Integrable G chaconOdometerMeasure) :
      Integrable (fun x ↦ g n x * G x) chaconOdometerMeasure := by
    refine (hG.norm.const_mul D).mono' ((hgm n).aestronglyMeasurable.mul hG.aestronglyMeasurable) ?_
    exact ae_of_all _ fun x ↦ (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right (hgb n x) (norm_nonneg _))
  have hlim : Tendsto (fun n ↦ D * ∫ x, ‖F (x + 3^n*m) - F x‖ ∂chaconOdometerMeasure)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_integral_norm_chaconTranslate m hF).const_mul D
  refine squeeze_zero_norm (fun n ↦ ?_) hlim
  let μ := chaconOdometerMeasure
  let S := chaconTail n ⁻¹' A
  let G (x : ChaconOdometer) := F (x + 3^n*m)
  have hG : Integrable G μ :=
    (chaconOdometer_translate_preserving (3^n*m)).integrable_comp_of_integrable hF
  change ‖(∫ x in S, g n x * G x ∂μ) - (∫ x in S, g n x * F x ∂μ)‖ ≤ _
  rw [← integral_sub (hgI n G hG).integrableOn (hgI n F hF).integrableOn]
  calc
    _ ≤ ∫ x in S, ‖g n x * G x - g n x * F x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in S, D * ‖G x - F x‖ ∂μ := by
      have h₀ : Integrable (fun x ↦ ‖g n x * G x - g n x * F x‖) μ :=
        ((hgI n G hG).sub (hgI n F hF)).norm
      have h₁ : Integrable (fun x ↦ D * ‖G x - F x‖) μ := (hG.sub hF).norm.const_mul D
      refine integral_mono h₀.integrableOn h₁.integrableOn (fun x ↦ ?_)
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_right (hgb n x) (norm_nonneg _)
    _ ≤ ∫ x, D * ‖G x - F x‖ ∂μ :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ ↦ mul_nonneg hD (norm_nonneg _))
        ((hG.sub hF).norm.const_mul D)
    _ = _ := integral_const_mul _ _

/-- The polynomial error on either tower layer, even against a moving test
that agrees with its prefix evaluation outside a vanishing exceptional set. -/
theorem tendsto_chaconTowerOffset_moving_error (m : ℕ) (j : ℤ)
    {f : ChaconOdometer × Bool → ℂ} (hf : Measurable f) {C : ℝ} (hfb : ∀ x, ‖f x‖ ≤ C)
    (g : ℕ → ChaconOdometer → ℂ) (hgm : ∀ n, Measurable (g n))
    {D : ℝ} (hD : 0 ≤ D) (hgb : ∀ n x, ‖g n x‖ ≤ D)
    (E : ℕ → Set ChaconOdometer) (hE : ∀ n, MeasurableSet (E n))
    (hprob : Tendsto (fun n ↦ chaconOdometerMeasure.real (E n)) atTop (𝓝 0))
    (hprefix : ∀ᶠ n in atTop, ∀ x ∉ E n, g n x = g n (chaconPrefix n x)) :
    Tendsto (fun n : ℕ ↦ (∫ x, g n x *
      f (chaconTowerSystem.act (Multiplicative.ofAdd (↑(m*chaconTowerHeight n) : ℤ))
        (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false))) ∂chaconOdometerMeasure) -
      ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
        ∫ x, g n x * f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ)))
          (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false))) ∂chaconOdometerMeasure)
        atTop (𝓝 0) := by
  let μ := chaconOdometerMeasure
  let A (k : ℕ) : Set ChaconOdometer := {x | chaconSpacerCount m x = k}
  let F (k : ℕ) (x : ChaconOdometer) :=
    f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ)))
      (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false)))
  let I (k n : ℕ) := ∫ x in chaconTail n ⁻¹' A k, g n x * F k (x + 3^n*m) ∂μ
  let J (k n : ℕ) := μ.real (A k) • ∫ x, g n x * F k x ∂μ
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurable_chaconSpacerCount m (measurableSet_singleton _)
  have hF (k : ℕ) : Measurable (F k) :=
    hf.comp ((chaconTowerSystem.preserves _).measurable.comp
      ((chaconTowerSystem.preserves _).measurable.comp (measurable_id.prodMk measurable_const)))
  have hFi (k : ℕ) : Integrable (F k) μ :=
    Integrable.of_bound (hF k).aestronglyMeasurable C (ae_of_all _ fun _ ↦ hfb _)
  have hlim (k : ℕ) : Tendsto (fun n ↦ I k n - J k n) atTop (𝓝 0) := by
    have h₁ := tendsto_chacon_moving_translate_error m (A k) (hFi k) g hgm hD hgb
    have h₂ := tendsto_chacon_moving_tail_error (hA k) (hFi k) g hgm hD hgb E hE hprob hprefix
    have he (n : ℕ) : (I k n - (∫ x in chaconTail n ⁻¹' A k, g n x * F k x ∂μ)) +
        ((∫ x in chaconTail n ⁻¹' A k, g n x * F k x ∂μ) - J k n) = I k n - J k n := by abel
    simpa only [zero_add] using (h₁.add h₂).congr he
  have he (n : ℕ) : ∑ k ∈ Finset.range (m+1), I k n =
      ∫ x, g n x * f (chaconTowerSystem.act (Multiplicative.ofAdd (↑(m*chaconTowerHeight n) : ℤ))
        (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, false))) ∂μ := by
    unfold I
    rw [← Finset.sum_congr rfl (fun k _ ↦ integral_indicator (measurable_chaconTail n (hA k))),
      ← integral_finsetSum]
    · apply integral_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      have h := chaconSpacerCount_le m (chaconTail n x)
      simp only [Set.indicator, mem_preimage, A, mem_ofPred_eq, Finset.sum_ite_eq,
        Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h), ite_true, F, chaconTower_act_tail]
    · intro k _
      apply Integrable.indicator _ (measurable_chaconTail n (hA k))
      have hm : Measurable (fun x : ChaconOdometer ↦ F k (x + 3^n*m)) :=
        (hF k).comp (measurable_id.add measurable_const)
      exact Integrable.of_bound ((hgm n).mul hm).aestronglyMeasurable (D*C) (ae_of_all _ fun x ↦
        (norm_mul _ _).le.trans (mul_le_mul (hgb n x) (hfb _) (norm_nonneg _) hD))
  have h := tendsto_finsetSum (Finset.range (m+1)) (fun k _ ↦ hlim k)
  simpa only [Finset.sum_const_zero, Finset.sum_sub_distrib, he, J, A, F, chaconSpacerProbability] using h

end Mixing
