/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconSafePrefixMeasure
public import Mixing.ChaconTowerPolynomialLimits

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory Set
open scoped Classical ENNReal Topology

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The point on level `l` over the tail `x` at the `n`th tower scale. -/
def chaconColumnPoint (n : ℕ) (l : ℤ) (x : ChaconOdometer) :
    ChaconOdometer × Bool :=
  chaconTowerSystem.act (Multiplicative.ofAdd l) (chaconScaleBranch n 0 x, false)

theorem measurable_chaconColumnPoint (n : ℕ) (l : ℤ) :
    Measurable (chaconColumnPoint n l) :=
  (chaconTowerSystem.preserves _).measurable.comp
    ((measurable_chaconScaleBranch n 0).prodMk measurable_const)

theorem chaconColumnPoint_shift (n : ℕ) (l s : ℤ) (x : ChaconOdometer) :
    chaconTowerSystem.act (Multiplicative.ofAdd s) (chaconColumnPoint n l x) =
      chaconColumnPoint n (s + l) x := by
  unfold chaconColumnPoint
  exact (congrFun (chaconTowerSystem.act_mul (Multiplicative.ofAdd s)
    (Multiplicative.ofAdd l)) _).symm

/-- Main-column return times depend only on the finite residue. -/
theorem chaconReturnSum_column (n r : ℕ) (hr : r < 3 ^ n) (x : ChaconOdometer) :
    chaconReturnSum r (chaconScaleBranch n 0 x) = chaconReturnSum r 0 := by
  induction r with
  | zero => simp [chaconReturnSum]
  | succ r ih =>
    have h : chaconScaleBranch n 0 x + (r : ChaconOdometer) = chaconScaleBranch n r x := by
      simp [chaconScaleBranch]
    rw [chaconReturnSum_succ, chaconReturnSum_succ, ih (by omega), h, zero_add,
      chaconSpacer_scaleBranch_iff n r hr x]

theorem chaconReturnSum_zero_strictMono : StrictMono (fun r ↦ chaconReturnSum r 0) := by
  apply strictMono_nat_of_lt_succ
  intro r
  rw [chaconReturnSum_succ]
  split <;> omega

private theorem chaconSpacerBit_last_prefix (n : ℕ) (x : ChaconOdometer) :
    chaconSpacerBit (chaconScaleBranch n (3 ^ n - 1) x) = chaconSpacerBit x := by
  induction n with
  | zero => simp [chaconScaleBranch]
  | succ n ih =>
    have h : chaconScaleBranch (n+1) (3^(n+1)-1) x =
        3 * chaconScaleBranch n (3^n-1) x + 2 := by
      unfold chaconScaleBranch
      have hpos : 0 < (3 : ℕ)^n := by positivity
      have he : 3^(n+1)-1 = 3*(3^n-1)+2 := by rw [pow_succ]; omega
      rw [he, pow_succ']
      push_cast
      ring
    rw [h, chaconSpacerBit_three_mul_add_two, ih]

theorem chaconColumn_last_spacer (n : ℕ) (x : ChaconOdometer) :
    chaconScaleBranch n (3 ^ n - 1) x ∈ chaconSpacer ↔ x ∈ chaconSpacer := by
  have h := chaconSpacerBit_last_prefix n x
  unfold chaconSpacerBit at h
  split_ifs at h <;> simp_all

private theorem chaconZero_not_mem_spacer : (0 : ChaconOdometer) ∉ chaconSpacer := by
  have h := chaconSpacerBit_three_mul (0 : ChaconOdometer)
  simp only [mul_zero] at h
  intro h₀
  simp [chaconSpacerBit, h₀] at h

theorem chaconReturnSum_column_height (n : ℕ) :
    chaconReturnSum (3 ^ n) 0 = chaconTowerHeight n := by
  have h := chaconReturnSum_at_height n 1 0 (by positivity) (0 : ChaconOdometer)
  simpa [chaconSpacerCount, chaconSpacerBit, chaconZero_not_mem_spacer] using h

theorem chaconColumnPoint_returnSum (n r : ℕ) (hr : r < 3 ^ n) (x : ChaconOdometer) :
    chaconColumnPoint n (chaconReturnSum r 0 : ℤ) x = (chaconScaleBranch n r x, false) := by
  rw [← chaconReturnSum_column n r hr x]
  exact (chaconTower_return_action r (chaconScaleBranch n 0 x)).trans (by simp [chaconScaleBranch])

theorem chaconColumnPoint_spacer (n r : ℕ) (hr : r < 3 ^ n) (x : ChaconOdometer)
    (hx : chaconScaleBranch n r x ∈ chaconSpacer) :
    chaconColumnPoint n ((chaconReturnSum r 0 : ℤ) + 1) x =
      (chaconScaleBranch n r x, true) := by
  rw [add_comm, ← chaconColumnPoint_shift, chaconColumnPoint_returnSum n r hr,
    chaconTower_bottom_step, ite_eq_left hx]

theorem chaconColumnPoint_top (n : ℕ) (x : ChaconOdometer) (hx : x ∈ chaconSpacer) :
    chaconColumnPoint n (chaconTowerHeight n : ℤ) x =
      (chaconScaleBranch n (3 ^ n - 1) x, true) := by
  have hpos : 0 < (3 : ℕ)^n := by positivity
  have hr : 3 ^ n - 1 < (3 : ℕ) ^ n := by omega
  have hs : 3 ^ n - 1 + 1 = (3 : ℕ)^n := by omega
  have h0 : ((3 ^ n - 1 : ℕ) : ChaconOdometer) ∉ chaconSpacer := by
    simpa only [chaconScaleBranch, mul_zero, zero_add] using
      (chaconColumn_last_spacer n 0).not.mpr chaconZero_not_mem_spacer
  have he := chaconReturnSum_succ (3 ^ n - 1) (0 : ChaconOdometer)
  rw [hs, chaconReturnSum_column_height, zero_add, ite_eq_right h0] at he
  rw [he, Nat.cast_add, Nat.cast_one]
  exact chaconColumnPoint_spacer n _ hr x ((chaconColumn_last_spacer n x).mpr hx)

/-- A level below the height lies in a residue and layer independent of the tail. -/
theorem chaconColumnPoint_core (n l : ℕ) (hl : l < chaconTowerHeight n) :
    ∃ (r : ℕ) (b : Bool), r < 3 ^ n ∧ ∀ x : ChaconOdometer,
      chaconColumnPoint n (l : ℤ) x = (chaconScaleBranch n r x, b) := by
  have he : ∃ r, l < chaconReturnSum r 0 := ⟨3 ^ n, chaconReturnSum_column_height n ▸ hl⟩
  let k := Nat.find he
  have hk := Nat.find_spec he
  have hkle := Nat.find_min' he (show l < chaconReturnSum (3 ^ n) 0 by
    rw [chaconReturnSum_column_height]; exact hl)
  change l < chaconReturnSum k 0 at hk
  change k ≤ 3 ^ n at hkle
  cases h : k with
  | zero => simp [h, chaconReturnSum] at hk
  | succ r =>
    have hr : r < (3 : ℕ)^n := by omega
    have hrl : chaconReturnSum r 0 ≤ l :=
      Nat.le_of_not_gt (Nat.find_min he (show r < Nat.find he by change r < k; omega))
    rw [h, chaconReturnSum_succ, zero_add] at hk
    rcases eq_or_ne l (chaconReturnSum r 0) with rfl | hn
    · exact ⟨r, false, hr, chaconColumnPoint_returnSum n r hr⟩
    · have hs : (r : ChaconOdometer) ∈ chaconSpacer := by
        by_contra h'
        rw [ite_eq_right h'] at hk
        omega
      rw [ite_eq_left hs] at hk
      have hlt : r + 1 < (3 : ℕ)^n := by
        by_contra! h'
        have hr' : r = 3 ^ n - 1 := by omega
        exact chaconZero_not_mem_spacer ((chaconColumn_last_spacer n 0).mp
          (by simpa [chaconScaleBranch, hr'] using hs))
      have h' : l = chaconReturnSum r 0 + 1 := by omega
      subst l
      exact ⟨r, true, hr, fun x ↦ by
        push_cast
        exact chaconColumnPoint_spacer n r hr x ((chaconSpacer_scaleBranch_iff n r hlt x).mpr hs)⟩

/-- The return to the origin of the column after advancing by `m` tails. -/
theorem chaconColumnPoint_advance (n m : ℕ) (l q : ℤ) (x : ChaconOdometer) :
    chaconColumnPoint n ((m * chaconTowerHeight n : ℕ) + q + l) x =
      chaconColumnPoint n (q + l - (chaconSpacerCount m x : ℤ)) (x + m) := by
  have h := chaconTower_action_at_height n m 0 (by positivity) x
  change chaconColumnPoint n (m * chaconTowerHeight n : ℕ) x =
    chaconColumnPoint n (-(chaconSpacerCount m x : ℤ)) (x + m) at h
  rw [show (↑(m * chaconTowerHeight n) : ℤ) + q + l = q + l + ↑(m * chaconTowerHeight n) by ring,
    ← chaconColumnPoint_shift, h, chaconColumnPoint_shift, sub_eq_add_neg]

end Mixing
