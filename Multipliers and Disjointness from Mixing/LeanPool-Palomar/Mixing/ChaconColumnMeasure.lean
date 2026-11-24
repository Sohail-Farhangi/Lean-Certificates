/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconColumns

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory Set
open scoped Classical ENNReal Topology

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Each main level receives this mass times the probability of its tail. -/
def chaconColumnWeight (n : ℕ) : ℝ :=
  ((1 + chaconOdometerMeasure chaconSpacer)⁻¹).toReal * (↑(3^n : ℕ) : ℝ)⁻¹

theorem chaconColumnWeight_nonneg (n : ℕ) : 0 ≤ chaconColumnWeight n := by
  unfold chaconColumnWeight
  positivity

theorem tendsto_chaconColumnWeight : Tendsto chaconColumnWeight atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ ((1 + chaconOdometerMeasure chaconSpacer)⁻¹).toReal *
    (↑(3^n : ℕ) : ℝ)⁻¹) atTop (𝓝 0)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, inv_pow, mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul
      ((1 + chaconOdometerMeasure chaconSpacer)⁻¹).toReal

private theorem zmod_finEquiv_val (q : ℕ) [NeZero q] (r : Fin q) :
    (ZMod.finEquiv q r).val = r.val := by
  cases q with
  | zero => exact Fin.elim0 r
  | succ q => rfl

private theorem sum_zmod_eq_sum_range {E : Type*} [AddCommMonoid E]
    (q : ℕ) [NeZero q] (f : ℕ → E) :
    (∑ r : ZMod q, f r.val) = ∑ r ∈ Finset.range q, f r := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine (Equiv.sum_comp (ZMod.finEquiv q).toEquiv (fun r : ZMod q ↦ f r.val)).symm.trans ?_
  exact Finset.sum_congr rfl fun r _ ↦ congrArg f (zmod_finEquiv_val q r)

private theorem chaconColumn_sum_returns {E : Type*} [AddCommMonoid E] (f : ℕ → E) (q : ℕ) :
    (∑ l ∈ Finset.range (chaconReturnSum q 0), f l) =
      ∑ r ∈ Finset.range q, (f (chaconReturnSum r 0) +
        if (r : ChaconOdometer) ∈ chaconSpacer then f (chaconReturnSum r 0 + 1) else 0) := by
  induction q with
  | zero => simp [chaconReturnSum]
  | succ q ih =>
    rw [chaconReturnSum_succ, zero_add, Finset.sum_range_succ _ q]
    by_cases h : (q : ChaconOdometer) ∈ chaconSpacer
    · rw [ite_eq_left h, ite_eq_left h,
        show chaconReturnSum q 0 + 2 = (chaconReturnSum q 0 + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ac_rfl
    · rw [ite_eq_right h, ite_eq_right h, add_zero, Finset.sum_range_succ, ih]

/-- The exact measure formula for the main tower levels and the possible
extra spacer at one level above the column. -/
theorem integral_chaconColumn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {F : ChaconOdometer × Bool → E} (hF : Measurable F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (n : ℕ) :
    (∫ x, F x ∂chaconTowerSystem.measure) =
      chaconColumnWeight n • ((∑ l ∈ Finset.range (chaconTowerHeight n),
        ∫ x, F (chaconColumnPoint n (l : ℤ) x) ∂chaconOdometerMeasure) +
        ∫ x in chaconSpacer, F (chaconColumnPoint n (chaconTowerHeight n : ℤ) x)
          ∂chaconOdometerMeasure) := by
  let μ := chaconOdometerMeasure
  let g (x : ChaconOdometer) := F (x, false)
  let h (x : ChaconOdometer) := chaconSpacer.indicator (fun x ↦ F (x, true)) x
  let f (l : ℕ) := ∫ x, F (chaconColumnPoint n (l : ℤ) x) ∂μ
  let Q := (3 : ℕ)^n
  let top := ∫ x in chaconSpacer, F (chaconColumnPoint n (chaconTowerHeight n : ℤ) x) ∂μ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB (0, false))
  have hg : Integrable g μ := Integrable.of_bound
    (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
    (ae_of_all _ fun x ↦ hB (x, false))
  have hh : Integrable h μ := (Integrable.of_bound
    (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
    (ae_of_all _ fun x ↦ hB (x, true))).indicator chaconSpacer_measurable
  have hIntSp : (∫ x in chaconSpacer, F (x, true) ∂μ) = ∫ x, h x ∂μ :=
    (integral_indicator chaconSpacer_measurable).symm
  rw [integral_chaconTower_split hF hB]
  change ((1 + μ chaconSpacer)⁻¹).toReal •
    ((∫ x, g x ∂μ) + ∫ x in chaconSpacer, F (x, true) ∂μ) = _
  rw [hIntSp, integral_chaconScaleBranch_decomposition n hg,
    integral_chaconScaleBranch_decomposition n hh, ← smul_add, smul_smul]
  change chaconColumnWeight n • _ = chaconColumnWeight n • _
  congr 1
  rw [sum_zmod_eq_sum_range (3^n) (fun r ↦ ∫ x, g (chaconScaleBranch n r x) ∂μ),
    sum_zmod_eq_sum_range (3^n) (fun r ↦ ∫ x, h (chaconScaleBranch n r x) ∂μ),
    ← Finset.sum_add_distrib]
  change (∑ r ∈ Finset.range Q,
    ((∫ x, g (chaconScaleBranch n r x) ∂μ) +
     (∫ x, h (chaconScaleBranch n r x) ∂μ))) =
     (∑ l ∈ Finset.range (chaconTowerHeight n), f l) + top
  have hE : (∑ r ∈ Finset.range Q, if r = Q-1 then top else 0) = top := by
    simp only [Finset.sum_ite_eq', Finset.mem_range, show Q-1 < Q by omega, ite_true]
  rw [← chaconReturnSum_column_height n, chaconColumn_sum_returns, ← hE,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  have hrl : r < 3 ^ n := Finset.mem_range.mp hr
  rw [show (∫ x, g (chaconScaleBranch n r x) ∂μ) = f (chaconReturnSum r 0) by
    simp only [f, g, chaconColumnPoint_returnSum n r hrl]]
  rw [add_assoc]
  congr 1
  by_cases hs : r + 1 < 3 ^ n
  · have hn : r ≠ Q-1 := by omega
    simp only [hn, ite_false, add_zero]
    by_cases hp : (r : ChaconOdometer) ∈ chaconSpacer
    · rw [ite_eq_left hp]
      apply integral_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      have hx := (chaconSpacer_scaleBranch_iff n r hs x).mpr hp
      simp only [h, indicator_of_mem hx]
      rw [Nat.cast_add, Nat.cast_one, chaconColumnPoint_spacer n r hrl x hx]
    · rw [ite_eq_right hp]
      apply integral_eq_zero_of_ae
      exact ae_of_all _ fun x ↦ indicator_of_notMem
        (fun hx ↦ hp ((chaconSpacer_scaleBranch_iff n r hs x).mp hx)) _
  · have hr' : r = Q-1 := by omega
    have hp : (r : ChaconOdometer) ∉ chaconSpacer := by
      intro hsp
      have hbad := (chaconColumn_last_spacer n 0).mp
        (show chaconScaleBranch n (3^n-1) 0 ∈ chaconSpacer by simpa [chaconScaleBranch, hr', Q] using hsp)
      have hz := chaconSpacerBit_three_mul (0 : ChaconOdometer)
      simp [chaconSpacerBit, hbad] at hz
    rw [ite_eq_right hp, ite_eq_left hr', zero_add]
    change _ = ∫ x in chaconSpacer, F (chaconColumnPoint n (chaconTowerHeight n : ℤ) x) ∂μ
    rw [← integral_indicator chaconSpacer_measurable]
    apply integral_congr_ae
    refine ae_of_all _ fun x ↦ ?_
    by_cases hx : x ∈ chaconSpacer
    · rw [indicator_of_mem hx, chaconColumnPoint_top n x hx]
      have hhx := (chaconColumn_last_spacer n x).mpr hx
      change h (chaconScaleBranch n r x) = _
      rw [hr']
      exact indicator_of_mem hhx _
    · rw [indicator_of_notMem hx]
      exact indicator_of_notMem (fun he ↦ hx ((chaconColumn_last_spacer n x).mp (by
        simpa only [hr', Q] using he))) _

end Mixing
