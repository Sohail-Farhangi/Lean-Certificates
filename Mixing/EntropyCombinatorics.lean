/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section

namespace Mixing

open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Shannon entropy with the convention that a zero weight contributes zero. -/
def shannonEntropy (p : A → ℝ) : ℝ := -(∑ a, p a * Real.log (p a))

/-- Gibbs's inequality, written as a comparison with cross entropy.
Each positive weight of p must also have a positive weight under q. -/
theorem shannonEntropy_le_crossEntropy (p q : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hq₀ : ∀ a, 0 ≤ q a)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1)
    (hsupport : ∀ a, 0 < p a → 0 < q a) :
    shannonEntropy p ≤ -(∑ a, p a * Real.log (q a)) := by
  have hpoint (a : A) : p a * (Real.log (q a) - Real.log (p a)) ≤ q a - p a := by
    obtain ha | ha := (hp₀ a).eq_or_lt
    · rw [← ha, zero_mul, sub_zero]
      exact hq₀ a
    have hb := hsupport a ha
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha)) ha.le
    rw [Real.log_div hb.ne' ha.ne'] at h
    calc
      _ ≤ p a * (q a / p a - 1) := h
      _ = q a - p a := by rw [mul_sub, mul_comm (p a) (q a / p a), div_mul_cancel₀ _ ha.ne', mul_one]
  have h : (∑ a, p a * (Real.log (q a) - Real.log (p a))) ≤ ∑ a, (q a - p a) :=
    Finset.sum_le_sum (fun a _ ↦ hpoint a)
  simp_rw [mul_sub] at h
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hq, hp] at h
  unfold shannonEntropy
  linarith

/-- Entropy of a joint distribution is bounded by the sum of the two
marginal entropies. -/
theorem shannonEntropy_joint_le (w : A × B → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hprob : ∑ z, w z = 1) :
    shannonEntropy w ≤
      shannonEntropy (fun a ↦ ∑ b, w (a, b)) +
      shannonEntropy (fun b ↦ ∑ a, w (a, b)) := by
  let p (a : A) := ∑ b, w (a, b)
  let q (b : B) := ∑ a, w (a, b)
  have hp : ∑ a, p a = 1 := by
    simpa only [Fintype.sum_prod_type, p] using hprob
  have hq : ∑ b, q b = 1 := by
    rw [show ∑ b, q b = ∑ a, p a from Finset.sum_comm, hp]
  have hp₀ (a : A) : 0 ≤ p a := Finset.sum_nonneg (fun b _ ↦ hw (a, b))
  have hq₀ (b : B) : 0 ≤ q b := Finset.sum_nonneg (fun a _ ↦ hw (a, b))
  have hwp (a : A) (b : B) : w (a, b) ≤ p a :=
    Finset.single_le_sum (fun j _ ↦ hw (a, j)) (Finset.mem_univ b)
  have hwq (a : A) (b : B) : w (a, b) ≤ q b :=
    Finset.single_le_sum (fun i _ ↦ hw (i, b)) (Finset.mem_univ a)
  let t (z : A × B) := p z.1 * q z.2
  have ht : ∑ z, t z = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [t, ← Finset.mul_sum, hq, mul_one, hp]
  have hle := shannonEntropy_le_crossEntropy w t hw
    (fun z ↦ mul_nonneg (hp₀ z.1) (hq₀ z.2)) hprob ht
    (fun z hz ↦ mul_pos (hz.trans_le (hwp z.1 z.2)) (hz.trans_le (hwq z.1 z.2)))
  have hlog (z : A × B) :
      w z * Real.log (t z) =
        w z * Real.log (p z.1) + w z * Real.log (q z.2) := by
    obtain h | h := (hw z).eq_or_lt
    · simp [← h]
    rw [show t z = p z.1 * q z.2 from rfl, Real.log_mul (h.trans_le (hwp z.1 z.2)).ne'
      (h.trans_le (hwq z.1 z.2)).ne', mul_add]
  refine hle.trans_eq ?_
  simp_rw [hlog, Finset.sum_add_distrib]
  have hL : ∑ z : A × B, w z * Real.log (p z.1) = ∑ a, p a * Real.log (p a) := by
    rw [Fintype.sum_prod_type]
    simp only [p, Finset.sum_mul]
  have hR : ∑ z : A × B, w z * Real.log (q z.2) = ∑ b, q b * Real.log (q b) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [q, Finset.sum_mul]
  rw [hL, hR, neg_add]
  rfl

/-- Pushing a distribution forward through a deterministic function cannot
increase its entropy. -/
theorem shannonEntropy_coarsen_le (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (f : A → B)
    [DecidableEq B] :
    shannonEntropy (fun b ↦ ∑ a, if f a = b then w a else 0) ≤ shannonEntropy w := by
  let q (b : B) := ∑ a, if f a = b then w a else 0
  have hQ (a : A) : w a ≤ q (f a) := by
    simpa only [ite_true] using
      Finset.single_le_sum (f := fun i ↦ if f i = f a then w i else 0)
        (fun i _ ↦ by split_ifs <;> simp [hw]) (Finset.mem_univ a)
  have hE : ∑ b, q b * Real.log (q b) = ∑ a, w a * Real.log (q (f a)) := by
    calc
      _ = ∑ b : B, ∑ a : A, if f a = b then w a * Real.log (q b) else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        change (∑ a, if f a = b then w a else 0) * Real.log (q b) = _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp
      _ = _ := by rw [Finset.sum_comm]; simp
  unfold shannonEntropy
  change -(∑ b, q b * Real.log (q b)) ≤ _
  rw [hE, neg_le_neg_iff]
  apply Finset.sum_le_sum
  intro a _
  obtain h | h := (hw a).eq_or_lt
  · simp [← h]
  exact mul_le_mul_of_nonneg_left (Real.log_le_log h (hQ a)) h.le

end Mixing
