/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconSafePrefixes

/-! # Haar mass of the exceptional prefixes for short movements of the tower -/

@[expose] public section

open MeasureTheory Set Filter
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The discarded low-digit prefix as an ordinary natural number. -/
noncomputable def chaconPrefixIndex (n : ℕ) (x : ChaconOdometer) : ℕ :=
  (PadicInt.toZModPow (p := 3) n x).val

theorem measurable_chaconPrefixIndex (n : ℕ) : Measurable (chaconPrefixIndex n) := by
  refine measurable_to_countable' (f := chaconPrefixIndex n) fun r ↦ ?_
  have he : chaconPrefixIndex n ⁻¹' {r} = chaconPrefix n ⁻¹' {(r : ChaconOdometer)} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, chaconPrefixIndex, chaconPrefix, Nat.cast_inj]
  rw [he]
  exact measurable_chaconPrefix n (measurableSet_singleton _)

theorem chaconPrefixIndex_scaleBranch (n : ℕ) (r : ZMod (3^n)) (x : ChaconOdometer) :
    chaconPrefixIndex n (chaconScaleBranch n r.val x) = r.val := by
  rw [chaconPrefixIndex, chaconScaleBranch_residue]

theorem chaconPrefixIndex_lt (n : ℕ) (x : ChaconOdometer) : chaconPrefixIndex n x < 3^n :=
  ZMod.val_lt _

/-- Each prefix cylinder has mass `3⁻ⁿ` if the residue is in range and zero
otherwise. In particular its mass is at most `3⁻ⁿ`. -/
theorem measureReal_chaconPrefixIndex_eq_le (n r : ℕ) :
    chaconOdometerMeasure.real {x | chaconPrefixIndex n x = r} ≤ (↑(3^n : ℕ) : ℝ)⁻¹ := by
  let A := {x | chaconPrefixIndex n x = r}
  have hA : MeasurableSet A := measurable_chaconPrefixIndex n (measurableSet_singleton r)
  have he := integral_chaconScaleBranch_decomposition n ((integrable_const (1 : ℝ)).indicator hA)
  rw [integral_indicator_const _ hA, smul_eq_mul, mul_one] at he
  have hf (s : ZMod (3^n)) (x : ChaconOdometer) :
      A.indicator (fun _ ↦ (1 : ℝ)) (chaconScaleBranch n s.val x) =
        if s.val = r then 1 else 0 := by
    simp only [A, Set.indicator, mem_ofPred_eq, chaconPrefixIndex_scaleBranch]
  simp only [hf, integral_const, probReal_univ, smul_eq_mul, one_mul] at he
  rw [he]
  refine mul_le_of_le_one_right (by positivity) ?_
  by_cases hr : r < 3^n
  · let s : ZMod (3^n) := r
    have hs : s.val = r := ZMod.val_natCast_of_lt hr
    have hi (x : ZMod (3^n)) : x.val = r ↔ x = s :=
      ⟨fun h ↦ ZMod.val_injective (3^n) (h.trans hs.symm), fun h ↦ h ▸ hs⟩
    simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, ite_true, le_refl]
  · have hs (x : ZMod (3^n)) : x.val ≠ r := fun h ↦ hr (h ▸ ZMod.val_lt x)
    simp only [hs, ite_false, Finset.sum_const_zero, zero_le_one]

/-- Prefixes too close to a boundary for the safe-prefix estimate at distance `t`. -/
noncomputable def chaconUnsafePrefix (n t : ℕ) : Set ChaconOdometer :=
  {x | chaconPrefixIndex n x < t ∨ 3^n ≤ chaconPrefixIndex n x + t + 1}

theorem chaconUnsafePrefix_measurable (n t : ℕ) : MeasurableSet (chaconUnsafePrefix n t) := by
  change MeasurableSet (chaconPrefixIndex n ⁻¹' {r | r < t ∨ 3^n ≤ r + t + 1})
  exact (measurable_chaconPrefixIndex n) MeasurableSet.of_discrete

/-- At most `2*t+1` of the equally weighted prefix cylinders can be unsafe for
an orbit movement of length `t`. -/
theorem measureReal_chaconUnsafePrefix_le (n t : ℕ) :
    chaconOdometerMeasure.real (chaconUnsafePrefix n t) ≤
      ((2*t+1 : ℕ) : ℝ) * (↑(3^n : ℕ) : ℝ)⁻¹ := by
  let A (r : ℕ) : Set ChaconOdometer := {x | chaconPrefixIndex n x = r}
  let L := ⋃ r ∈ Finset.range t, A r
  let R := ⋃ r ∈ Finset.range (t+1), A (3^n - 1 - r)
  have hsub : chaconUnsafePrefix n t ⊆ L ∪ R := by
    intro x hx
    have hq := chaconPrefixIndex_lt n x
    rcases hx with hx | hx
    · exact Or.inl (mem_iUnion.mpr ⟨chaconPrefixIndex n x, mem_iUnion.mpr
        ⟨Finset.mem_range.mpr hx, rfl⟩⟩)
    · let d := 3^n - 1 - chaconPrefixIndex n x
      have hd : d < t+1 := by dsimp [d]; omega
      have he : chaconPrefixIndex n x = 3^n - 1 - d := by dsimp [d]; omega
      exact Or.inr (mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨Finset.mem_range.mpr hd, he⟩⟩)
  calc
    _ ≤ chaconOdometerMeasure.real (L ∪ R) := measureReal_mono hsub
    _ ≤ chaconOdometerMeasure.real L + chaconOdometerMeasure.real R :=
      measureReal_union_le _ _
    _ ≤ (∑ _ ∈ Finset.range t, (↑(3^n : ℕ) : ℝ)⁻¹) +
        (∑ _ ∈ Finset.range (t+1), (↑(3^n : ℕ) : ℝ)⁻¹) := by
      refine add_le_add ((measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_))
        ((measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun r _ ↦ ?_))
      · exact measureReal_chaconPrefixIndex_eq_le n r
      · exact measureReal_chaconPrefixIndex_eq_le n (3^n - 1 - r)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]; ring

/-- The exceptional prefix mass goes to zero for moves of sub-height length. -/
theorem tendsto_measureReal_chaconUnsafePrefix (t : ℕ → ℕ)
    (ht : Tendsto (fun n ↦ (t n : ℝ) / chaconTowerHeight n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ chaconOdometerMeasure.real (chaconUnsafePrefix n (t n))) atTop (𝓝 0) := by
  have hq : Tendsto (fun n : ℕ ↦ (((3^n : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, ← inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ ((3 : ℝ)⁻¹)) (by norm_num))
  apply squeeze_zero (fun _ ↦ MeasureTheory.measureReal_nonneg)
    (g := fun n ↦ 4 * ((t n : ℝ) / chaconTowerHeight n) + (((3^n : ℕ) : ℝ)⁻¹))
  · intro n
    refine (measureReal_chaconUnsafePrefix_le n (t n)).trans ?_
    have hn := chaconTowerHeight_twice_add_one n
    rw [pow_succ] at hn
    have hN : chaconTowerHeight n ≤ 2*(3^n) := by omega
    have hR : (chaconTowerHeight n : ℝ) ≤ 2*((3^n : ℕ) : ℝ) := by exact_mod_cast hN
    have hH : 0 < chaconTowerHeight n := by cases n <;> simp [chaconTowerHeight]
    have hb : (t n : ℝ) / ((3^n : ℕ) : ℝ) ≤ 2*((t n : ℝ) / chaconTowerHeight n) := by
      have hH' : 0 < (chaconTowerHeight n : ℝ) := by exact_mod_cast hH
      have hq' : 0 < ((3^n : ℕ) : ℝ) := by positivity
      rw [← mul_div_assoc, div_le_div_iff₀ hq' hH']
      nlinarith only [mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg (t n))]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← div_eq_mul_inv]
    rw [add_div, mul_div_assoc, one_div]
    linarith only [hb]
  · simpa only [mul_zero, zero_add] using ((ht.const_mul (4 : ℝ)).add hq)

private theorem chaconPrefix_coarse_scaleBranch {N n s : ℕ} (hN : N ≤ n) (hs : s < 3^n)
    (x : ChaconOdometer) :
    chaconPrefix N (chaconScaleBranch n s x) = chaconPrefix N (chaconScaleBranch n s 0) := by
  have hval : ((s : ZMod (3^n))).val = s := ZMod.val_natCast_of_lt hs
  have h₁ := chaconScaleBranch_residue n (s : ZMod (3^n)) x
  have h₂ := chaconScaleBranch_residue n (s : ZMod (3^n)) 0
  rw [hval] at h₁ h₂
  unfold chaconPrefix
  rw [← PadicInt.cast_toZModPow N n hN, ← PadicInt.cast_toZModPow N n hN, h₁, h₂]

/-- A low-prefix test evaluated after an arbitrary signed short move is
insensitive to the high tail on each safe prefix. -/
theorem chaconTower_safePrefix_test {N n : ℕ} (hN : N ≤ n)
    {E : Type*} (f : ChaconOdometer × Bool → E)
    (hf : ∀ (x : ChaconOdometer) (b : Bool), f (x, b) = f (chaconPrefix N x, b))
    (j : ℤ) (x : ChaconOdometer) (hx : x ∉ chaconUnsafePrefix n j.natAbs) (b : Bool) :
    f (chaconTowerSystem.act (Multiplicative.ofAdd j) (x, b)) =
      f (chaconTowerSystem.act (Multiplicative.ofAdd j) (chaconPrefix n x, b)) := by
  let r := chaconPrefixIndex n x
  have hr : ¬(r < j.natAbs ∨ 3^n ≤ r + j.natAbs + 1) := hx
  have hr₁ : j.natAbs ≤ r := by omega
  have hr₂ : r + j.natAbs + 1 < 3^n := by omega
  have h₁ : chaconScaleBranch n r (chaconTail n x) = x := chaconScaleBranch_tail n x
  have h₂ : chaconScaleBranch n r 0 = chaconPrefix n x := by
    simp only [chaconScaleBranch, mul_zero, zero_add]
    rfl
  have hs : ∃ (s : ℕ) (c : Bool), s < 3^n ∧ ∀ y : ChaconOdometer,
      chaconTowerSystem.act (Multiplicative.ofAdd j) (chaconScaleBranch n r y, b) =
        (chaconScaleBranch n s y, c) := by
    by_cases h : 0 ≤ j
    · have hj : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg h
      obtain ⟨s, c, _, hs, he⟩ := chaconTower_act_safePrefix_forward n r j.natAbs (by omega) b
      exact ⟨s, c, by omega, hj ▸ he⟩
    · have hj : -(j.natAbs : ℤ) = j := by omega
      obtain ⟨s, c, hs, _, he⟩ := chaconTower_act_safePrefix_backward n r j.natAbs (by omega) hr₁ b
      exact ⟨s, c, by omega, hj ▸ he⟩
  obtain ⟨s, c, hs, he⟩ := hs
  nth_rw 1 [← h₁]
  rw [he, ← h₂, he, hf (chaconScaleBranch n s (chaconTail n x)) c,
    hf (chaconScaleBranch n s 0) c, chaconPrefix_coarse_scaleBranch hN hs]

end Mixing
