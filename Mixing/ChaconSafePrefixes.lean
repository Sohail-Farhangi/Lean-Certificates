/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconTailHaar

/-! # Chacon trajectories inside a ternary prefix before crossing its boundary -/

@[expose] public section

open scoped Classical

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Unless the entire prefix consists of twos, the spacer bit is determined
before looking at the higher digits. -/
theorem chaconSpacerBit_scaleBranch (n r : ℕ) (hr : r+1 < 3^n) (x : ChaconOdometer) :
    chaconSpacerBit (chaconScaleBranch n r x) = chaconSpacerBit (r : ChaconOdometer) := by
  induction n generalizing r with
  | zero => simp only [pow_zero] at hr; omega
  | succ n ih =>
    let d := r%3
    let q := r/3
    have hrq : r = 3*q+d := (Nat.div_add_mod r 3).symm
    have h₀ : chaconScaleBranch (n+1) r x = 3 * chaconScaleBranch n q x + (d : ChaconOdometer) := by
      unfold chaconScaleBranch
      rw [pow_succ' (3 : ChaconOdometer)]
      nth_rw 1 [hrq]
      push_cast
      ring
    have h₁ : (r : ChaconOdometer) = 3*(q : ChaconOdometer)+(d : ChaconOdometer) := by exact_mod_cast hrq
    have hd : d < 3 := Nat.mod_lt r (by decide)
    rw [h₀, h₁]
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with h | h | h
    · simp only [h, Nat.cast_zero, add_zero, chaconSpacerBit_three_mul]
    · simp only [h, Nat.cast_one, chaconSpacerBit_three_mul_add_one]
    · simp only [h, Nat.cast_ofNat, chaconSpacerBit_three_mul_add_two]
      apply ih
      rw [pow_succ' (3 : ℕ) n] at hr
      omega

theorem chaconSpacer_scaleBranch_iff (n r : ℕ) (hr : r+1 < 3^n) (x : ChaconOdometer) :
    chaconScaleBranch n r x ∈ chaconSpacer ↔ (r : ChaconOdometer) ∈ chaconSpacer := by
  have hb := chaconSpacerBit_scaleBranch n r hr x
  unfold chaconSpacerBit at hb
  split_ifs at hb <;> simp_all

private theorem chaconTower_step_scaleBranch (n r : ℕ) (hr : r+1 < 3^n) (b : Bool) :
    ∃ (s : ℕ) (c : Bool), r ≤ s ∧ s ≤ r+1 ∧ ∀ x : ChaconOdometer,
      chaconTowerSystem.act (Multiplicative.ofAdd 1) (chaconScaleBranch n r x, b) =
        (chaconScaleBranch n s x, c) := by
  have hAct (x : ChaconOdometer) :
      chaconTowerSystem.act (Multiplicative.ofAdd 1) (chaconScaleBranch n r x, b) =
        towerNext chaconOdometerStep chaconSpacer (chaconScaleBranch n r x, b) := by
    change ((twoLevelTowerEquiv chaconOdometerStep chaconSpacer chaconSpacer_measurable).toEquiv ^
        (1 : ℤ)) _ = _
    rw [zpow_one]
    rfl
  have he (x : ChaconOdometer) :
      chaconOdometerStep (chaconScaleBranch n r x) = chaconScaleBranch n (r+1) x := by
    change (3 : ChaconOdometer)^n*x+r+1 = 3^n*x+((r+1 : ℕ) : ChaconOdometer)
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
  cases b
  · by_cases hx : (r : ChaconOdometer) ∈ chaconSpacer
    · refine ⟨r, true, le_rfl, Nat.le_succ r, fun x ↦ ?_⟩
      simp only [hAct, towerNext, Bool.false_eq_true, ite_false, chaconSpacer_scaleBranch_iff n r hr,
        hx, ite_true, towerTop]
    · refine ⟨r+1, false, Nat.le_succ r, le_rfl, fun x ↦ ?_⟩
      simp only [hAct, towerNext, Bool.false_eq_true, ite_false, chaconSpacer_scaleBranch_iff n r hr,
        hx, he, towerBottom]
  · by_cases hx : (r : ChaconOdometer) ∈ chaconSpacer
    · refine ⟨r+1, false, Nat.le_succ r, le_rfl, fun x ↦ ?_⟩
      simp only [hAct, towerNext, ite_true, chaconSpacer_scaleBranch_iff n r hr, hx, he, towerBottom]
    · refine ⟨r, true, le_rfl, Nat.le_succ r, fun x ↦ ?_⟩
      simp only [hAct, towerNext, ite_true, chaconSpacer_scaleBranch_iff n r hr, hx, ite_false]

/-- Forward trajectories of length `t` starting at the same safe prefix
have identical changing low prefixes and tower levels, for every high tail. -/
theorem chaconTower_act_safePrefix_forward (n r t : ℕ) (hr : r+t < 3^n) (b : Bool) :
    ∃ (s : ℕ) (c : Bool), r ≤ s ∧ s ≤ r+t ∧ ∀ x : ChaconOdometer,
      chaconTowerSystem.act (Multiplicative.ofAdd (t : ℤ)) (chaconScaleBranch n r x, b) =
        (chaconScaleBranch n s x, c) := by
  induction t with
  | zero =>
    refine ⟨r, b, le_rfl, Nat.le_add_right _ _, fun x ↦ ?_⟩
    change chaconTowerSystem.act 1 _ = _
    rw [chaconTowerSystem.act_one]
    rfl
  | succ t ih =>
    obtain ⟨s, c, hrs, hst, hAct⟩ := ih (by omega)
    obtain ⟨s', c', hss, hss', hAct'⟩ := chaconTower_step_scaleBranch n s (by omega) c
    refine ⟨s', c', by omega, by omega, fun x ↦ ?_⟩
    have hsum : Multiplicative.ofAdd ((↑(t+1) : ℤ)) =
        Multiplicative.ofAdd (1 : ℤ) * Multiplicative.ofAdd (t : ℤ) := by
      change (↑(t+1) : ℤ) = 1 + t
      push_cast
      omega
    rw [hsum, chaconTowerSystem.act_mul, Function.comp_apply, hAct, hAct']

private theorem chaconTower_stepBack_scaleBranch (n r : ℕ) (hr : r+1 < 3^n) (hr₀ : 0 < r)
    (b : Bool) :
    ∃ (s : ℕ) (c : Bool), s ≤ r ∧ r ≤ s+1 ∧ ∀ x : ChaconOdometer,
      chaconTowerSystem.act (Multiplicative.ofAdd (-1)) (chaconScaleBranch n r x, b) =
        (chaconScaleBranch n s x, c) := by
  have hAct (x : ChaconOdometer) :
      chaconTowerSystem.act (Multiplicative.ofAdd (-1)) (chaconScaleBranch n r x, b) =
        towerPrevious chaconOdometerStep chaconSpacer (chaconScaleBranch n r x, b) := by
    change ((twoLevelTowerEquiv chaconOdometerStep chaconSpacer chaconSpacer_measurable).toEquiv ^
        (- (1 : ℤ))) _ = _
    rw [zpow_neg, zpow_one]
    rfl
  have he (x : ChaconOdometer) :
      chaconOdometerStep.symm (chaconScaleBranch n r x) = chaconScaleBranch n (r-1) x := by
    change (3 : ChaconOdometer)^n*x+r + -1 = 3^n*x+((r-1 : ℕ) : ChaconOdometer)
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  cases b
  · by_cases hx : ((r-1 : ℕ) : ChaconOdometer) ∈ chaconSpacer
    · refine ⟨r-1, true, by omega, by omega, fun x ↦ ?_⟩
      simp only [hAct, towerPrevious, Bool.false_eq_true, ite_false, he,
        chaconSpacer_scaleBranch_iff n (r-1) (by omega), hx, ite_true, towerTop]
    · refine ⟨r-1, false, by omega, by omega, fun x ↦ ?_⟩
      simp only [hAct, towerPrevious, Bool.false_eq_true, ite_false, he,
        chaconSpacer_scaleBranch_iff n (r-1) (by omega), hx, towerBottom]
  · by_cases hx : (r : ChaconOdometer) ∈ chaconSpacer
    · refine ⟨r, false, le_rfl, Nat.le_succ r, fun x ↦ ?_⟩
      simp only [hAct, towerPrevious, ite_true, chaconSpacer_scaleBranch_iff n r hr, hx, towerBottom]
    · refine ⟨r, true, le_rfl, Nat.le_succ r, fun x ↦ ?_⟩
      simp only [hAct, towerPrevious, ite_true, chaconSpacer_scaleBranch_iff n r hr, hx, ite_false]

/-- A backward trajectory also depends only on the low prefix and tower
level, provided the prefix stays clear of the boundary. -/
theorem chaconTower_act_safePrefix_backward (n r t : ℕ) (hr : r+1 < 3^n) (ht : t ≤ r) (b : Bool) :
    ∃ (s : ℕ) (c : Bool), s ≤ r ∧ r ≤ s+t ∧ ∀ x : ChaconOdometer,
      chaconTowerSystem.act (Multiplicative.ofAdd (-(t : ℤ))) (chaconScaleBranch n r x, b) =
        (chaconScaleBranch n s x, c) := by
  induction t with
  | zero =>
    refine ⟨r, b, le_rfl, Nat.le_add_right _ _, fun x ↦ ?_⟩
    change chaconTowerSystem.act 1 _ = _
    rw [chaconTowerSystem.act_one]
    rfl
  | succ t ih =>
    obtain ⟨s, c, hrs, hst, hAct⟩ := ih (by omega)
    obtain ⟨s', c', hss, hss', hAct'⟩ := chaconTower_stepBack_scaleBranch n s
      (by omega) (by omega) c
    refine ⟨s', c', by omega, by omega, fun x ↦ ?_⟩
    have hsum : Multiplicative.ofAdd (-(↑(t+1) : ℤ)) =
        Multiplicative.ofAdd (-1 : ℤ) * Multiplicative.ofAdd (-(t : ℤ)) := by
      change -(↑(t+1) : ℤ) = -1 + -(t : ℤ)
      push_cast
      omega
    rw [hsum, chaconTowerSystem.act_mul, Function.comp_apply, hAct, hAct']

end Mixing
