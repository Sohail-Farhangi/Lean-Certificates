/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroSubshift

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory
open scoped BigOperators Classical ComplexConjugate InnerProductSpace Topology

/-- A product of neighbouring signs in the generating word. -/
private def neighbourSign (j : ℕ) : ℝ := rudinShapiro j * rudinShapiro (j + 1)

private theorem neighbourSign_even (j : ℕ) : neighbourSign (2 * j) = (-1 : ℝ) ^ j := by
  rw [neighbourSign, rudinShapiro_even, rudinShapiro_odd]
  calc
    _ = (-1 : ℝ) ^ j * rudinShapiro j ^ 2 := by ring
    _ = _ := by rw [rudinShapiro_sq, mul_one]

private theorem neighbourSign_four_mul_add_one (j : ℕ) :
    neighbourSign (4 * j + 1) = (-1 : ℝ) ^ j := by
  have h₁ : 4 * j + 1 = 2 * (2 * j) + 1 := by omega
  have h₂ : 2 * (2 * j) + 1 + 1 = 2 * (2 * j + 1) := by omega
  have h₃ : (-1 : ℝ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  rw [h₁, neighbourSign, h₂, rudinShapiro_odd, rudinShapiro_even (2 * j + 1), h₃, one_mul]
  exact neighbourSign_even j

private theorem neighbourSign_even_period (j : ℕ) :
    neighbourSign (2 * j + 4) = neighbourSign (2 * j) := by
  rw [show 2 * j + 4 = 2 * (j + 2) by omega, neighbourSign_even, neighbourSign_even, pow_add]
  norm_num

private theorem neighbourSign_odd_change (j : ℕ) :
    neighbourSign (4 * j + 1 + 4) ≠ neighbourSign (4 * j + 1) := by
  rw [show 4 * j + 1 + 4 = 4 * (j + 1) + 1 by omega,
    neighbourSign_four_mul_add_one, neighbourSign_four_mul_add_one, pow_succ]
  have hn : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  intro h
  apply hn
  linarith

def rudinShapiroParityTest (u : Fin 8 → Bool) : ℝ :=
  if signValue (u 0) * signValue (u 1) = signValue (u 4) * signValue (u 5) ∧
    signValue (u 2) * signValue (u 3) = signValue (u 6) * signValue (u 7) then 1 else -1

/-- The parity of the centre is recoverable from eight consecutive signs
of the Rudin–Shapiro word. -/
def rudinShapiroParity : C(SignWords, ℝ) where
  toFun w := rudinShapiroParityTest (fun i ↦ w (i.val : ℤ))
  continuous_toFun := (continuous_of_discreteTopology (f := rudinShapiroParityTest)).comp
    (continuous_pi fun i : Fin 8 ↦ continuous_apply (i.val : ℤ))

theorem rudinShapiroParity_sq (w : SignWords) : (rudinShapiroParity w) ^ 2 = 1 := by
  change (rudinShapiroParityTest (fun i ↦ w (i.val : ℤ))) ^ 2 = 1
  unfold rudinShapiroParityTest
  split_ifs <;> norm_num

private theorem neighbourSign_shifted (j s : ℕ) :
    signValue (signWordShift j rudinShapiroWord s) *
      signValue (signWordShift j rudinShapiroWord (s + 1 : ℤ)) = neighbourSign (j + s) := by
  change signValue (rudinShapiroWord ((s : ℤ) + j)) *
    signValue (rudinShapiroWord ((s : ℤ) + 1 + j)) = _
  rw [signValue_rudinShapiroWord, signValue_rudinShapiroWord, neighbourSign,
    show ((s : ℤ) + j).toNat = j + s by omega,
    show ((s : ℤ) + 1 + j).toNat = j + s + 1 by omega]

theorem rudinShapiroParity_on_sample (j : ℕ) :
    rudinShapiroParity (signWordShift j rudinShapiroWord) = (-1 : ℝ) ^ j := by
  change (if signValue (signWordShift j rudinShapiroWord 0) *
    signValue (signWordShift j rudinShapiroWord 1) =
      signValue (signWordShift j rudinShapiroWord 4) * signValue (signWordShift j rudinShapiroWord 5) ∧
      signValue (signWordShift j rudinShapiroWord 2) * signValue (signWordShift j rudinShapiroWord 3) =
      signValue (signWordShift j rudinShapiroWord 6) * signValue (signWordShift j rudinShapiroWord 7)
    then 1 else -1) = _
  have h₀ := neighbourSign_shifted j 0
  have h₂ := neighbourSign_shifted j 2
  have h₄ := neighbourSign_shifted j 4
  have h₆ := neighbourSign_shifted j 6
  norm_num at h₀ h₂ h₄ h₆
  rw [h₀, h₂, h₄, h₆]
  by_cases hj : j % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = 2 * m := ⟨j / 2, by omega⟩
    have h : neighbourSign (2 * m + 2) = neighbourSign (2 * m + 6) := by
      simpa only [show 2 * (m + 1) = 2 * m + 2 by omega,
        show 2 * m + 2 + 4 = 2 * m + 6 by omega] using (neighbourSign_even_period (m + 1)).symm
    rw [ite_eq_left ⟨(neighbourSign_even_period m).symm, h⟩, pow_mul]
    norm_num
  · have h : ¬ (neighbourSign j = neighbourSign (j + 4) ∧
      neighbourSign (j + 2) = neighbourSign (j + 6)) := by
      intro he
      by_cases h₁ : j % 4 = 1
      · have heq : j = 4 * (j / 4) + 1 := by omega
        exact neighbourSign_odd_change (j / 4) (by simpa only [← heq] using he.1.symm)
      · have heq : j + 2 = 4 * ((j + 2) / 4) + 1 := by omega
        exact neighbourSign_odd_change ((j + 2) / 4) (by
          rw [← heq, show j + 2 + 4 = j + 6 by omega]
          exact he.2.symm)
    rw [ite_eq_right h, show j = 2 * (j / 2) + 1 by omega, pow_succ, pow_mul]
    norm_num

/-- The dyadic phase is an eigenfunction on the Rudin–Shapiro subshift. -/
theorem rudinShapiroParity_shift_of_mem {w : SignWords} (hw : w ∈ rudinShapiroSubshift) (k : ℤ) :
    rudinShapiroParity (signWordShift k w) = (-1 : ℝ) ^ k * rudinShapiroParity w := by
  let I := (Finset.range 8).image (fun i : ℕ ↦ (i : ℤ) + k)
  let J := (Finset.range 8).image (fun i : ℕ ↦ (i : ℤ))
  refine rudinShapiro_local_property (P := fun w ↦
    rudinShapiroParity (signWordShift k w) = (-1 : ℝ) ^ k * rudinShapiroParity w)
    (I ∪ J) ?_ k.natAbs ?_ hw
  · intro u v h hh
    have h₁ : (fun i : Fin 8 ↦ signWordShift k u (i.val : ℤ)) =
        fun i : Fin 8 ↦ signWordShift k v (i.val : ℤ) := by
      funext i
      exact h _ (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩))
    have h₂ : (fun i : Fin 8 ↦ u (i.val : ℤ)) = fun i : Fin 8 ↦ v (i.val : ℤ) := by
      funext i
      exact h _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩))
    change rudinShapiroParityTest (fun i ↦ signWordShift k u (i.val : ℤ)) =
      (-1 : ℝ) ^ k * rudinShapiroParityTest (fun i ↦ u (i.val : ℤ)) at hh
    change rudinShapiroParityTest (fun i ↦ signWordShift k v (i.val : ℤ)) =
      (-1 : ℝ) ^ k * rudinShapiroParityTest (fun i ↦ v (i.val : ℤ))
    rwa [h₁, h₂] at hh
  · intro j hj
    have hneg : -k ≤ (k.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -k))
    have hNat : 0 ≤ k + (j : ℤ) := by omega
    have heq : ((k + (j : ℤ)).toNat : ℤ) = k + (j : ℤ) := Int.toNat_of_nonneg hNat
    change rudinShapiroParity ((signWordShift k ∘ signWordShift (j : ℤ)) rudinShapiroWord) =
      (-1 : ℝ) ^ k * rudinShapiroParity (signWordShift j rudinShapiroWord)
    rw [← signWordShift_add, ← heq, rudinShapiroParity_on_sample, rudinShapiroParity_on_sample,
      ← zpow_natCast, heq, zpow_add₀ (by norm_num), zpow_natCast]

private def rudinShapiroSignedPair (k : ℕ) : C(SignWords, ℝ) where
  toFun w := rudinShapiroParity w * (signValue (w 0) * signValue (w k))
  continuous_toFun :=
    let hc : Continuous signValue := continuous_of_discreteTopology
    rudinShapiroParity.continuous.mul ((hc.comp (continuous_apply 0)).mul
      (hc.comp (continuous_apply (k : ℤ))))

/-- Inserting the recovered sign of the centre parity makes every
nonnegative-lag correlation vanish, including lag zero. -/
theorem integral_rudinShapiro_signedPair (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (k : ℕ) : (∫ w, rudinShapiroParity w * (signValue (w 0) * signValue (w k))
      ∂(rudinShapiroOrbitLaw p : Measure SignWords)) = 0 := by
  have h := tendsto_integral_dyadicOrbitLaw (signWordShift 1) rudinShapiroWord p
    (rudinShapiroSignedPair k)
  have he (n : ℕ) : (∑ j ∈ Finset.range (2 ^ n),
      rudinShapiroSignedPair k ((signWordShift 1)^[j] rudinShapiroWord)) / (2 : ℝ) ^ n =
        rudinShapiroSignedCorrelation n k := by
    unfold rudinShapiroSignedCorrelation
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [signWordShift_iterate]
    change rudinShapiroParity (signWordShift j rudinShapiroWord) *
      (signValue (rudinShapiroWord (0 + j)) * signValue (rudinShapiroWord ((k : ℤ) + j))) = _
    rw [rudinShapiroParity_on_sample, zero_add, signValue_rudinShapiroWord,
      signValue_rudinShapiroWord, Int.toNat_natCast, show ((k : ℤ) + (j : ℤ)).toNat = j + k by omega]
  simp_rw [he] at h
  exact tendsto_nhds_unique h ((rudinShapiro_dyadic_correlations k).2.mono_left hp)

end Mixing
