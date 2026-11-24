/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconReturnArithmetic

/-! # Returns to the lower level of the explicit Chacon tower -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal

namespace Mixing

/-- A complete bottom-to-bottom step has return time one or two. -/
theorem chaconTower_return_one (x : ChaconOdometer) :
    chaconTowerSystem.act (Multiplicative.ofAdd (if x ∈ chaconSpacer then (2 : ℤ) else 1))
      (x, false) = (x + 1, false) := by
  by_cases h : x ∈ chaconSpacer
  · rw [ite_eq_left h, show Multiplicative.ofAdd (2 : ℤ) =
      Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 from rfl, chaconTowerSystem.act_mul]
    change chaconTowerSystem.act (Multiplicative.ofAdd 1)
      (chaconTowerSystem.act (Multiplicative.ofAdd 1) (x, false)) = _
    rw [chaconTower_bottom_step, ite_eq_left h, chaconTower_top_step x h]
  · rw [ite_eq_right h, chaconTower_bottom_step, ite_eq_right h]

theorem chaconReturnSum_succ (m : ℕ) (x : ChaconOdometer) :
    chaconReturnSum (m+1) x = chaconReturnSum m x +
      if x + (m : ChaconOdometer) ∈ chaconSpacer then 2 else 1 := by
  simp only [chaconReturnSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  split <;> omega

/-- After the total of the first `m` returns, the lower level is reached at the
odometer point advanced by `m`. -/
theorem chaconTower_return_action (m : ℕ) (x : ChaconOdometer) :
    chaconTowerSystem.act (Multiplicative.ofAdd (chaconReturnSum m x : ℤ))
      (x, false) = (x + (m : ChaconOdometer), false) := by
  induction m with
  | zero =>
    simp only [chaconReturnSum, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Nat.cast_zero]
    change chaconTowerSystem.act 1 (x, false) = (x, false)
    rw [chaconTowerSystem.act_one]
    rfl
  | succ m ih =>
    let k : ℤ := if x + (m : ChaconOdometer) ∈ chaconSpacer then 2 else 1
    have he : (chaconReturnSum (m+1) x : ℤ) = k + (chaconReturnSum m x : ℤ) := by
      rw [chaconReturnSum_succ, Nat.cast_add]
      unfold k
      split <;> omega
    rw [he, show Multiplicative.ofAdd (k + (chaconReturnSum m x : ℤ)) =
      Multiplicative.ofAdd k * Multiplicative.ofAdd (chaconReturnSum m x : ℤ) from rfl,
      chaconTowerSystem.act_mul]
    change chaconTowerSystem.act (Multiplicative.ofAdd
      (if x + (m : ChaconOdometer) ∈ chaconSpacer then (2 : ℤ) else 1))
      (chaconTowerSystem.act (Multiplicative.ofAdd (chaconReturnSum m x : ℤ)) (x, false)) = _
    rw [ih, chaconTower_return_one]
    simp only [Nat.cast_succ, add_assoc]

/-- Removing the tower normalization amounts to multiplying by its total mass. -/
theorem chaconTower_raw_eq_scaled :
    twoLevelTowerRawMeasure chaconOdometerMeasure chaconSpacer =
      (1 + chaconOdometerMeasure chaconSpacer) • chaconTowerSystem.measure := by
  change _ = (1 + chaconOdometerMeasure chaconSpacer) •
    twoLevelTowerMeasure chaconOdometerMeasure chaconSpacer
  rw [twoLevelTowerMeasure, smul_smul, ENNReal.mul_inv_cancel (by simp)
    (ENNReal.add_ne_top.mpr ⟨by simp, measure_ne_top _ _⟩), one_smul]

theorem chaconTower_bottom_dominated : chaconOdometerMeasure.map towerBottom ≤
    (1 + chaconOdometerMeasure chaconSpacer) • chaconTowerSystem.measure := by
  rw [← chaconTower_raw_eq_scaled]
  apply Measure.le_iff'.mpr
  intro A
  change chaconOdometerMeasure.map towerBottom A ≤
    (chaconOdometerMeasure.map towerBottom +
      (chaconOdometerMeasure.restrict chaconSpacer).map towerTop) A
  rw [add_apply]
  exact le_self_add

/-- Almost-everywhere properties on the tower restrict to the bottom level
with the odometer probability measure. -/
theorem ae_chaconTower_bottom {P : ChaconOdometer × Bool → Prop}
    (hP : MeasurableSet {x | P x}) (h : ∀ᵐ x ∂chaconTowerSystem.measure, P x) :
    ∀ᵐ x ∂chaconOdometerMeasure, P (x, false) := by
  have hm : Measurable (towerBottom : ChaconOdometer → ChaconOdometer × Bool) :=
    measurable_id.prodMk measurable_const
  exact (ae_map_iff hm.aemeasurable hP).mp
    ((Measure.absolutelyContinuous_of_le_smul chaconTower_bottom_dominated).ae_le h)

/-- L² functions on the tower restrict to L² functions on the bottom level. -/
theorem memLp_chaconTower_bottom {f : ChaconOdometer × Bool → ℂ}
    (h : MemLp f 2 chaconTowerSystem.measure) :
    MemLp (fun x ↦ f (x, false)) 2 chaconOdometerMeasure := by
  have hm : Measurable (towerBottom : ChaconOdometer → ChaconOdometer × Bool) :=
    measurable_id.prodMk measurable_const
  exact (h.of_measure_le_smul (ENNReal.add_ne_top.mpr ⟨by simp, measure_ne_top _ _⟩)
    chaconTower_bottom_dominated).comp_of_map hm.aemeasurable

/-- A property true almost everywhere on the bottom and on the occupied top is
true almost everywhere on the entire tower. -/
theorem ae_chaconTower_of_bottom_and_top {P : ChaconOdometer × Bool → Prop}
    (hP : MeasurableSet {x | P x})
    (h₀ : ∀ᵐ x ∂chaconOdometerMeasure, P (x, false))
    (h₁ : ∀ᵐ x ∂chaconOdometerMeasure.restrict chaconSpacer, P (x, true)) :
    ∀ᵐ x ∂chaconTowerSystem.measure, P x := by
  have hm₀ : Measurable (towerBottom : ChaconOdometer → ChaconOdometer × Bool) :=
    measurable_id.prodMk measurable_const
  have hm₁ : Measurable (towerTop : ChaconOdometer → ChaconOdometer × Bool) :=
    measurable_id.prodMk measurable_const
  change ∀ᵐ x ∂twoLevelTowerMeasure chaconOdometerMeasure chaconSpacer, P x
  unfold twoLevelTowerMeasure twoLevelTowerRawMeasure
  apply Measure.ae_smul_measure
  rw [ae_add_measure_iff]
  exact ⟨(ae_map_iff hm₀.aemeasurable hP).mpr h₀, (ae_map_iff hm₁.aemeasurable hP).mpr h₁⟩

end Mixing
