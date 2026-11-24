/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconOdometerErgodic

/-! # Spacer arithmetic for a complete ternary odometer cycle -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The residue of the odometer successor modulo a power of three. -/
noncomputable def chaconSuccessorResidue (n : ℕ) (x : ChaconOdometer) : ZMod (3^n) :=
  PadicInt.toZModPow n (x + 1)

private theorem chaconSuccessorResidue_reduce {m n : ℕ} (h : m ≤ n) (x : ChaconOdometer) :
    ZMod.cast (chaconSuccessorResidue n x) = chaconSuccessorResidue m x :=
  PadicInt.cast_toZModPow m n h (x + 1)

private theorem chaconSuccessorResidue_add_nat (n j : ℕ) (x : ChaconOdometer) :
    chaconSuccessorResidue n (x + j) = chaconSuccessorResidue n x + j := by
  unfold chaconSuccessorResidue
  rw [show x + (j : ChaconOdometer) + 1 = x + 1 + j by ring, map_add, map_natCast]

private theorem powThree_dvd_mul_powThree {m k r : ℕ} (hm : m ≤ k) :
    3^m ∣ r * 3^k :=
  (pow_dvd_pow 3 hm).trans (dvd_mul_left _ _)

private theorem chaconResidue_reduce_peak {m k r : ℕ} (hm : m ≤ k)
    {x : ChaconOdometer} (hx : chaconSuccessorResidue (k+1) x = (r * 3^k : ℕ)) :
    chaconSuccessorResidue m x = 0 := by
  have hm' : m ≤ k + 1 := hm.trans (Nat.le_succ k)
  rw [← chaconSuccessorResidue_reduce hm' x, hx, ZMod.cast_natCast (pow_dvd_pow 3 hm')]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (powThree_dvd_mul_powThree hm)

private theorem chaconPeak_nonzero (n r : ℕ) (hr : 0 < r) (hr' : r < 3) :
    ((r * 3^n : ℕ) : ZMod (3^(n+1))) ≠ 0 := by
  have hq : 0 < (3 : ℕ)^n := pow_pos (by decide) _
  have hlt : r * 3^n < 3^(n+1) := by
    rw [pow_succ, mul_comm (3^n) 3]
    exact Nat.mul_lt_mul_of_pos_right hr' hq
  intro h
  have hv := ZMod.val_natCast_of_lt hlt
  rw [h, ZMod.val_zero] at hv
  exact (Nat.ne_of_gt (Nat.mul_pos hr hq)) hv.symm

private theorem chaconSpacer_iff_peak (x : ChaconOdometer) :
    x ∈ chaconSpacer ↔ ∃ n : ℕ, chaconSuccessorResidue (n+1) x = (2 * 3^n : ℕ) := by
  rw [mem_chaconSpacer_iff_modular]
  simp only [chaconSuccessorResidue, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]

private theorem chaconPeak_order_unique {i j r s : ℕ} {x : ChaconOdometer}
    (hr : 0 < r) (hr' : r < 3) (hs : 0 < s) (hs' : s < 3)
    (hi : chaconSuccessorResidue (i+1) x = (r * 3^i : ℕ))
    (hj : chaconSuccessorResidue (j+1) x = (s * 3^j : ℕ)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (chaconPeak_nonzero i r hr hr' (hi.symm.trans (chaconResidue_reduce_peak h hj)))
  · exact h
  · exact False.elim (chaconPeak_nonzero j s hs hs' (hj.symm.trans (chaconResidue_reduce_peak h hi)))

private theorem chaconSpacer_of_peak_two {n : ℕ} {x : ChaconOdometer}
    (hx : chaconSuccessorResidue (n+1) x = (2 * 3^n : ℕ)) : x ∈ chaconSpacer :=
  (chaconSpacer_iff_peak x).mpr ⟨n, hx⟩

private theorem chaconSpacer_not_of_peak_one {n : ℕ} {x : ChaconOdometer}
    (hx : chaconSuccessorResidue (n+1) x = ((3^n : ℕ) : ZMod (3^(n+1)))) : x ∉ chaconSpacer := by
  intro hi
  have hx' : chaconSuccessorResidue (n+1) x = (1 * 3^n : ℕ) := by simpa only [one_mul] using hx
  obtain ⟨i, hi⟩ := (chaconSpacer_iff_peak x).mp hi
  have he := chaconPeak_order_unique (by decide : 0 < 1) (by decide : 1 < 3)
    (by decide : 0 < 2) (by decide : 2 < 3) hx' hi
  subst i
  have hq : 0 < (3 : ℕ)^n := pow_pos (by decide) _
  have hn₁ : 3^n < 3^(n+1) := by rw [pow_succ]; omega
  have hn₂ : 2 * 3^n < 3^(n+1) := by rw [pow_succ]; omega
  have heq := congrArg ZMod.val (hx.symm.trans hi)
  rw [ZMod.val_natCast_of_lt hn₁, ZMod.val_natCast_of_lt hn₂] at heq
  omega

private theorem chaconSpacer_shift_pow_iff {n : ℕ} {x : ChaconOdometer}
    (hx : chaconSuccessorResidue n x ≠ 0) :
    x + ((3^n : ℕ) : ChaconOdometer) ∈ chaconSpacer ↔ x ∈ chaconSpacer := by
  have hr (m : ℕ) (hm : m ≤ n) :
      chaconSuccessorResidue m (x + ((3^n : ℕ) : ChaconOdometer)) = chaconSuccessorResidue m x := by
    rw [chaconSuccessorResidue_add_nat]
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow 3 hm), add_zero]
  have hx' := hx
  rw [← hr n le_rfl] at hx'
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (chaconSpacer_iff_peak _).mp h
    have hk' : k < n := by
      by_contra! hkn
      exact hx' (chaconResidue_reduce_peak hkn hk)
    exact chaconSpacer_of_peak_two ((hr (k+1) hk').symm.trans hk)
  · intro h
    obtain ⟨k, hk⟩ := (chaconSpacer_iff_peak _).mp h
    have hk' : k < n := by
      by_contra! hkn
      exact hx (chaconResidue_reduce_peak hkn hk)
    exact chaconSpacer_of_peak_two ((hr (k+1) hk').trans hk)

/-- Among `3^n` consecutive successors, this is the position of the one
congruent to zero modulo `3^n`. -/
noncomputable def chaconCriticalIndex (n : ℕ) (x : ChaconOdometer) : Fin (3^n) :=
  ⟨(-chaconSuccessorResidue n x).val, ZMod.val_lt _⟩

theorem chaconCriticalIndex_spec (n : ℕ) (x : ChaconOdometer) :
    chaconSuccessorResidue n (x + ((chaconCriticalIndex n x).val : ChaconOdometer)) = 0 := by
  rw [chaconSuccessorResidue_add_nat]
  change chaconSuccessorResidue n x + (((-chaconSuccessorResidue n x).val : ℕ) : ZMod (3^n)) = 0
  rw [ZMod.natCast_zmod_val, add_neg_cancel]

theorem chaconCriticalIndex_unique (n : ℕ) (x : ChaconOdometer) (j : Fin (3^n))
    (hj : chaconSuccessorResidue n (x + (j.val : ChaconOdometer)) = 0) : j = chaconCriticalIndex n x := by
  have h := chaconCriticalIndex_spec n x
  rw [chaconSuccessorResidue_add_nat] at h hj
  have he := congrArg ZMod.val (add_left_cancel (hj.trans h.symm))
  rw [ZMod.val_natCast_of_lt j.isLt, ZMod.val_natCast_of_lt (chaconCriticalIndex n x).isLt] at he
  exact Fin.ext he

private theorem chaconCriticalIndex_shift_pow (n : ℕ) (x : ChaconOdometer) :
    chaconCriticalIndex n (x + ((3^n : ℕ) : ChaconOdometer)) = chaconCriticalIndex n x := by
  have h : chaconSuccessorResidue n (x + ((3^n : ℕ) : ChaconOdometer)) =
      chaconSuccessorResidue n x := by
    rw [chaconSuccessorResidue_add_nat, ZMod.natCast_self, add_zero]
  apply Fin.ext
  change (-chaconSuccessorResidue n (x + ((3^n : ℕ) : ChaconOdometer))).val =
    (-chaconSuccessorResidue n x).val
  rw [h]

/-- The residue modulo one further power of three at the critical position. -/
noncomputable def chaconCriticalResidue (n : ℕ) (x : ChaconOdometer) : ZMod (3^(n+1)) :=
  chaconSuccessorResidue (n+1) (x + ((chaconCriticalIndex n x).val : ChaconOdometer))

theorem chaconCriticalResidue_shift_pow (n : ℕ) (x : ChaconOdometer) :
    chaconCriticalResidue n (x + ((3^n : ℕ) : ChaconOdometer)) =
      chaconCriticalResidue n x + (3^n : ℕ) := by
  unfold chaconCriticalResidue
  rw [chaconCriticalIndex_shift_pow]
  rw [show x + ((3^n : ℕ) : ChaconOdometer) + (chaconCriticalIndex n x).val =
    x + (chaconCriticalIndex n x).val + ((3^n : ℕ) : ChaconOdometer) by ring,
    chaconSuccessorResidue_add_nat]

/-- The total return time of the tower over the first `m` odometer steps. -/
noncomputable def chaconReturnSum (m : ℕ) (x : ChaconOdometer) : ℕ :=
  m + ∑ j : Fin m, if x + (j.val : ChaconOdometer) ∈ chaconSpacer then 1 else 0

/-- On the first nonzero critical residue, shifting the base by `3^n`
increases the complete-cycle return time by one. -/
theorem chaconReturnSum_shift_pow_of_critical_one (n : ℕ) (x : ChaconOdometer)
    (hx : chaconCriticalResidue n x = (3^n : ℕ)) :
    chaconReturnSum (3^n) (x + ((3^n : ℕ) : ChaconOdometer)) =
      chaconReturnSum (3^n) x + 1 := by
  let c := chaconCriticalIndex n x
  have hBefore : x + (c.val : ChaconOdometer) ∉ chaconSpacer :=
    chaconSpacer_not_of_peak_one hx
  have hAfter : x + ((3^n : ℕ) : ChaconOdometer) + (c.val : ChaconOdometer) ∈ chaconSpacer := by
    apply chaconSpacer_of_peak_two (n := n)
    have h := chaconCriticalResidue_shift_pow n x
    rw [hx, chaconCriticalResidue, chaconCriticalIndex_shift_pow] at h
    change chaconSuccessorResidue (n+1)
      (x + ((3^n : ℕ) : ChaconOdometer) + (c.val : ChaconOdometer)) =
        ((2 * 3^n : ℕ) : ZMod (3^(n+1)))
    simpa only [← Nat.cast_add, two_mul] using h
  have hOther (j : Fin (3^n)) (hj : j ≠ c) :
      x + ((3^n : ℕ) : ChaconOdometer) + (j.val : ChaconOdometer) ∈ chaconSpacer ↔
        x + (j.val : ChaconOdometer) ∈ chaconSpacer := by
    rw [show x + ((3^n : ℕ) : ChaconOdometer) + (j.val : ChaconOdometer) =
      x + j.val + ((3^n : ℕ) : ChaconOdometer) by ring]
    apply chaconSpacer_shift_pow_iff
    exact fun hz ↦ hj (chaconCriticalIndex_unique n x j hz)
  let w (y : ChaconOdometer) (j : Fin (3^n)) : ℕ :=
    if y + (j.val : ChaconOdometer) ∈ chaconSpacer then 1 else 0
  have heq (j : Fin (3^n)) :
      w (x + ((3^n : ℕ) : ChaconOdometer)) j = w x j + if j = c then 1 else 0 := by
    by_cases hj : j = c
    · subst j
      simp only [w, hBefore, hAfter, ite_true, ite_false, zero_add]
    · simp only [w, hj, hOther j hj, ite_false, add_zero]
  change 3^n + (∑ j, w (x + ((3^n : ℕ) : ChaconOdometer)) j) = 3^n + (∑ j, w x j) + 1
  simp_rw [heq, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_assoc]

end Mixing
