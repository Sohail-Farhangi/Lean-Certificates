/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconReturnArithmetic

/-! # The positive-size critical residues of the Chacon odometer -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A cylinder of fixed residue has measurable preimage in the odometer. -/
theorem measurableSet_chaconSuccessorResidue_eq (n : ℕ) (r : ZMod (3^n)) :
    MeasurableSet {x | chaconSuccessorResidue n x = r} := by
  have he : {x | chaconSuccessorResidue n x = r} =
      {x : ChaconOdometer | ‖x + 1 - (r.val : ChaconOdometer)‖ ≤ ((3 : ℕ) : ℝ) ^ (-(n : ℕ) : ℤ)} := by
    ext x
    simp only [mem_ofPred_eq, chaconSuccessorResidue]
    rw [PadicInt.norm_le_pow_iff_mem_span_pow (p := 3) _ n,
      ← PadicInt.ker_toZModPow (p := 3) n, RingHom.mem_ker, map_sub, map_natCast,
      ZMod.natCast_zmod_val, sub_eq_zero]
  rw [he]
  exact measurableSet_le (by fun_prop) measurable_const

noncomputable def criticalEvent (n r : ℕ) : Set ChaconOdometer :=
  {x | chaconCriticalResidue n x = ((r * 3^n : ℕ) : ZMod (3^(n+1)))}

private theorem criticalEvent_measurable (n r : ℕ) : MeasurableSet (criticalEvent n r) := by
  have he : criticalEvent n r =
      ⋃ j : Fin (3^n), {x | chaconSuccessorResidue (n+1) (x + (j.val : ChaconOdometer)) =
        ((r * 3^n : ℕ) : ZMod (3^(n+1)))} := by
    ext x
    simp only [criticalEvent, mem_ofPred_eq, mem_iUnion]
    constructor
    · exact fun hx ↦ ⟨chaconCriticalIndex n x, hx⟩
    · rintro ⟨j, hj⟩
      have hj₀ : chaconSuccessorResidue n (x + (j.val : ChaconOdometer)) = 0 := by
        have hs := PadicInt.cast_toZModPow n (n+1) (Nat.le_succ n)
          (x + (j.val : ChaconOdometer) + 1)
        change ZMod.cast (chaconSuccessorResidue (n+1) (x + (j.val : ChaconOdometer))) =
          chaconSuccessorResidue n (x + (j.val : ChaconOdometer)) at hs
        rw [hj, ZMod.cast_natCast (pow_dvd_pow 3 (Nat.le_succ n))] at hs
        rw [← hs]
        exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_left _ _)
      rw [chaconCriticalIndex_unique n x j hj₀] at hj
      exact hj
  rw [he]
  apply MeasurableSet.iUnion
  intro j
  exact (measurable_id.add measurable_const)
    (measurableSet_chaconSuccessorResidue_eq (n+1) _)

private theorem criticalEvent_cover (n : ℕ) :
    (⋃ r : Fin 3, criticalEvent n r.val) = univ := by
  ext x
  simp only [mem_univ, iff_true, mem_iUnion]
  let v := chaconCriticalResidue n x
  have h₀ : (ZMod.cast v : ZMod (3^n)) = 0 := by
    unfold v chaconCriticalResidue
    exact (PadicInt.cast_toZModPow n (n+1) (Nat.le_succ n) _).trans (chaconCriticalIndex_spec n x)
  have hDvd : 3^n ∣ v.val := by
    rw [← ZMod.natCast_zmod_val v, ZMod.cast_natCast (pow_dvd_pow 3 (Nat.le_succ n))] at h₀
    exact (ZMod.natCast_eq_zero_iff _ _).mp h₀
  obtain ⟨r, hr⟩ := hDvd
  have hrbound : r < 3 := by
    have h := ZMod.val_lt v
    rw [hr, pow_succ] at h
    exact Nat.lt_of_mul_lt_mul_left h
  refine ⟨⟨r, hrbound⟩, ?_⟩
  change v = ((r * 3^n : ℕ) : ZMod (3^(n+1)))
  rw [mul_comm r, ← hr, ZMod.natCast_zmod_val]

private theorem criticalEvent_disjoint (n : ℕ) :
    Pairwise (fun a b : Fin 3 ↦ _root_.Disjoint (criticalEvent n a.val) (criticalEvent n b.val)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x ha hb
  change chaconCriticalResidue n x = ((a.val * 3^n : ℕ) : ZMod (3^(n+1))) at ha
  change chaconCriticalResidue n x = ((b.val * 3^n : ℕ) : ZMod (3^(n+1))) at hb
  have hq : 0 < (3 : ℕ)^n := pow_pos (by decide) _
  have hlt (r : Fin 3) : r.val * 3^n < 3^(n+1) := by
    rw [pow_succ, mul_comm (3^n) 3]
    exact Nat.mul_lt_mul_of_pos_right r.isLt hq
  have h := congrArg ZMod.val (ha.symm.trans hb)
  rw [ZMod.val_natCast_of_lt (hlt a), ZMod.val_natCast_of_lt (hlt b)] at h
  exact hab (Fin.ext (Nat.eq_of_mul_eq_mul_right hq h))

private theorem criticalEvent_measure_succ (n r : ℕ) :
    chaconOdometerMeasure (criticalEvent n (r+1)) = chaconOdometerMeasure (criticalEvent n r) := by
  have hpre : (fun x : ChaconOdometer ↦ x + ((3^n : ℕ) : ChaconOdometer)) ⁻¹'
      criticalEvent n (r+1) = criticalEvent n r := by
    ext x
    change chaconCriticalResidue n (x + ((3^n : ℕ) : ChaconOdometer)) =
      (((r+1) * 3^n : ℕ) : ZMod (3^(n+1))) ↔
      chaconCriticalResidue n x = ((r * 3^n : ℕ) : ZMod (3^(n+1)))
    rw [chaconCriticalResidue_shift_pow, Nat.add_mul, one_mul, Nat.cast_add, add_right_cancel_iff]
  conv_rhs => rw [← hpre]
  exact ((chaconOdometer_translate_preserving ((3^n : ℕ) : ChaconOdometer)).measure_preimage
    (criticalEvent_measurable n (r+1)).nullMeasurableSet).symm

/-- On this cylinder union the second complete cycle crosses exactly one
more spacer than the first complete cycle. -/
noncomputable def chaconCycleGood (n : ℕ) : Set ChaconOdometer := criticalEvent n 1

theorem chaconCycleGood_measurable (n : ℕ) : MeasurableSet (chaconCycleGood n) :=
  criticalEvent_measurable n 1

/-- Each of the three critical residues has probability one third. -/
theorem chaconCycleGood_measure_real (n : ℕ) : chaconOdometerMeasure.real (chaconCycleGood n) = 1 / 3 := by
  have hTotal : chaconOdometerMeasure (criticalEvent n 0) +
      chaconOdometerMeasure (criticalEvent n 1) + chaconOdometerMeasure (criticalEvent n 2) = 1 := by
    have hsum := measure_iUnion (μ := chaconOdometerMeasure) (criticalEvent_disjoint n)
      (fun (r : Fin 3) ↦ criticalEvent_measurable n r.val)
    rw [criticalEvent_cover n, measure_univ, tsum_fintype, Fin.sum_univ_three] at hsum
    exact hsum.symm
  rw [← criticalEvent_measure_succ n 0, criticalEvent_measure_succ n 1] at hTotal
  have hr := congrArg ENNReal.toReal hTotal
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    (measure_ne_top _ _), ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_one] at hr
  change (chaconOdometerMeasure (criticalEvent n 1)).toReal = 1 / 3
  linarith only [hr]

theorem chaconReturnSum_shift_pow_on_good (n : ℕ) {x : ChaconOdometer}
    (hx : x ∈ chaconCycleGood n) :
    chaconReturnSum (3^n) (x + ((3^n : ℕ) : ChaconOdometer)) =
      chaconReturnSum (3^n) x + 1 :=
  chaconReturnSum_shift_pow_of_critical_one n x (by simpa only [chaconCycleGood, criticalEvent,
    mem_ofPred_eq, one_mul] using hx)

end Mixing
