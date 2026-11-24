/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconWeakLimitRecursion

/-! # Return times at every cutting-and-stacking scale of Chacon's tower -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped Classical ENNReal

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The height after `n` cuts into three and one additional middle spacer. -/
def chaconTowerHeight : ℕ → ℕ
  | 0 => 1
  | n+1 => 3 * chaconTowerHeight n + 1

theorem chaconTowerHeight_twice_add_one (n : ℕ) :
    2 * chaconTowerHeight n + 1 = 3^(n+1) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [chaconTowerHeight, pow_succ (3 : ℕ) (n+1), ← hn]
    omega

/-- Number of steps to advance `3^n*m` odometer positions from a specified
low-digit cylinder. The excess over `m` copies of the nominal tower height
is the same spacer cocycle on the high-digit tail. -/
theorem chaconReturnSum_at_height (n m r : ℕ) (hr : r < 3^n) (x : ChaconOdometer) :
    chaconReturnSum (3^n*m) (3^n*x+r) =
      m * chaconTowerHeight n + chaconSpacerCount m x := by
  induction n generalizing r x with
  | zero =>
    have hr' : r = 0 := by simpa using hr
    subst r
    simp [chaconTowerHeight, chaconReturnSum_eq_add_spacerCount]
  | succ n hn =>
    let d : Fin 3 := ⟨r % 3, Nat.mod_lt _ (by decide)⟩
    have hq : r / 3 < 3^n :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr (by simpa only [pow_succ] using hr)
    have hrq : (3^ (n+1)*x+(r : ChaconOdometer)) =
        3*(3^n*x+((r/3 : ℕ) : ChaconOdometer))+(d.val : ChaconOdometer) := by
      have h : ((r : ℕ) : ChaconOdometer) = 3*((r/3 : ℕ) : ChaconOdometer) + ((r%3 : ℕ) : ChaconOdometer) := by
        exact_mod_cast (Nat.div_add_mod r 3).symm
      rw [pow_succ' (3 : ChaconOdometer), h]
      change _ = 3*(3^n*x+((r/3 : ℕ) : ChaconOdometer))+((r%3 : ℕ) : ChaconOdometer)
      ring
    have hi := hn (r/3) hq x
    rw [chaconReturnSum_eq_add_spacerCount] at hi ⊢
    have ht := congrArg (fun t : ℕ ↦ t*m) (chaconTowerHeight_twice_add_one n)
    rw [pow_succ' (3 : ℕ) n, add_mul, mul_assoc, one_mul, mul_assoc] at ht
    rw [pow_succ' (3 : ℕ) n, mul_assoc, hrq, chaconSpacerCount_three, chaconTowerHeight]
    rw [show m * (3 * chaconTowerHeight n + 1) = 3 * (chaconTowerHeight n * m) + m by ring]
    rw [Nat.mul_comm m (chaconTowerHeight n)] at hi
    omega

/-- The actual tower transformation at a multiple of a tower height. -/
theorem chaconTower_action_at_height (n m r : ℕ) (hr : r < 3^n) (x : ChaconOdometer) :
    chaconTowerSystem.act (Multiplicative.ofAdd (m*chaconTowerHeight n : ℕ)) (3^n*x+r, false) =
      chaconTowerSystem.act (Multiplicative.ofAdd (-(chaconSpacerCount m x : ℤ)))
        (3^n*(x+m)+r, false) := by
  have ha := chaconTower_return_action (3^n*m) (3^n*x+r)
  rw [chaconReturnSum_at_height n m r hr x] at ha
  have hsum : Multiplicative.ofAdd (((m * chaconTowerHeight n + chaconSpacerCount m x : ℕ)) : ℤ) =
      Multiplicative.ofAdd (chaconSpacerCount m x : ℤ) *
        Multiplicative.ofAdd (↑(m * chaconTowerHeight n) : ℤ) := by
    change (↑(m * chaconTowerHeight n + chaconSpacerCount m x) : ℤ) =
      ↑(chaconSpacerCount m x) + ↑(m * chaconTowerHeight n)
    push_cast
    ring
  rw [hsum, chaconTowerSystem.act_mul] at ha
  have h := congrArg (chaconTowerSystem.act (Multiplicative.ofAdd (-(chaconSpacerCount m x : ℤ)))) ha
  change (chaconTowerSystem.act (Multiplicative.ofAdd (-(chaconSpacerCount m x : ℤ))) ∘
    chaconTowerSystem.act (Multiplicative.ofAdd (chaconSpacerCount m x : ℤ))) _ =
      chaconTowerSystem.act _ _ at h
  rw [← chaconTowerSystem.act_mul] at h
  have hid : Multiplicative.ofAdd (-(chaconSpacerCount m x : ℤ)) *
      Multiplicative.ofAdd (chaconSpacerCount m x : ℤ) = 1 := by
    change -(chaconSpacerCount m x : ℤ) + chaconSpacerCount m x = 0
    omega
  rw [hid, chaconTowerSystem.act_one, id_eq] at h
  have hx : (3^n*x+(r : ChaconOdometer) + ((3^n*m : ℕ) : ChaconOdometer)) =
      3^n*(x+m)+r := by
    push_cast
    ring
  rwa [hx] at h

end Mixing
