/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EntropyCombinatorics

@[expose] public section
noncomputable section

namespace Mixing

open scoped BigOperators

/-- The information needed to specify an error of probability d and,
if an error occurred, a value among m possible alternatives. -/
def entropyErrorBound (m : ℕ) (d : ℝ) : ℝ :=
  -((1 - d) * Real.log (1 - d)) - d * Real.log d + d * Real.log m

theorem continuous_entropyErrorBound (m : ℕ) : Continuous (entropyErrorBound m) := by
  exact ((Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).neg.sub
    Real.continuous_mul_log).add (continuous_id.mul continuous_const)

@[simp] theorem entropyErrorBound_zero (m : ℕ) : entropyErrorBound m 0 = 0 := by
  simp [entropyErrorBound]

/-- Entropy of an optional label, with a total mass d on the labels that
are present, is bounded by the error-information expression. -/
theorem shannonEntropy_option_le {A : Type*} [Fintype A] [Nonempty A]
    (w : Option A → ℝ) (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∑ i, w i = 1) :
    shannonEntropy w ≤ entropyErrorBound (Fintype.card A) (∑ a : A, w (some a)) := by
  let d : ℝ := ∑ a : A, w (some a)
  let m : ℝ := Fintype.card A
  have hm : 0 < m := by
    change 0 < (Fintype.card A : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hd : 0 ≤ d := Finset.sum_nonneg fun i _ ↦ h₀ (some i)
  have hn : w none = 1 - d := by
    rw [Fintype.sum_option] at h₁
    linarith only [h₁]
  by_cases hz : d = 0
  · have hsome (a : A) : w (some a) = 0 := by
      have hl : w (some a) ≤ d :=
        Finset.single_le_sum (fun i _ ↦ h₀ (some i)) (Finset.mem_univ a)
      exact le_antisymm (hz ▸ hl) (h₀ _)
    have hone : w none = 1 := by rwa [hz, sub_zero] at hn
    simp [shannonEntropy, Fintype.sum_option, hone, hsome]
  have hdpos : 0 < d := hd.lt_of_ne (Ne.symm hz)
  let v : Option A → ℝ := fun i ↦ i.elim (1 - d) (fun _ ↦ d / m)
  have hprob : ∑ i, v i = 1 := by
    rw [Fintype.sum_option]
    simp only [v, Option.elim_none, Option.elim_some, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change 1 - d + m * (d / m) = 1
    rw [mul_comm m, div_mul_cancel₀ _ hm.ne']
    linarith
  have hv (i : Option A) : 0 ≤ v i := by
    cases i
    · change 0 ≤ 1 - d
      rw [← hn]
      exact h₀ none
    · exact div_nonneg hd hm.le
  have hs (i : Option A) (hi : 0 < w i) : 0 < v i := by
    cases i
    · change 0 < 1 - d
      rw [← hn]
      exact hi
    · exact div_pos hdpos hm
  refine (shannonEntropy_le_crossEntropy w v h₀ hv h₁ hprob hs).trans_eq ?_
  rw [Fintype.sum_option]
  simp only [v, Option.elim_none, Option.elim_some, ← Finset.sum_mul, hn, Real.log_div hdpos.ne' hm.ne']
  change -( (1 - d) * Real.log (1 - d) + d * (Real.log d - Real.log m)) =
    entropyErrorBound (Fintype.card A) d
  unfold entropyErrorBound
  ring

end Mixing
