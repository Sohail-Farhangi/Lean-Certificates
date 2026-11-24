/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroResidues

@[expose] public section
noncomputable section

namespace Mixing

open scoped Classical

/-- The centre sign restricted to the zero class at dyadic level k. -/
def rudinShapiroZeroCutoff (k : ℕ) (w : SignWords) : ℝ :=
  if rudinShapiroZeroPhase k w then signValue (w 0) else 0

/-- The same cutoff with the sign of the next binary digit included. -/
def rudinShapiroSignedZeroCutoff (k : ℕ) (w : SignWords) : ℝ :=
  if rudinShapiroZeroPhase (k + 1) w then rudinShapiroZeroCutoff k w
  else -rudinShapiroZeroCutoff k w

private theorem rudinShapiro_pow_mul_two (k q : ℕ) : rudinShapiro (2 ^ k * q) = rudinShapiro q := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, rudinShapiro_even, ih]

private theorem zeroCutoff_on_sample (k j : ℕ) :
    rudinShapiroZeroCutoff k (signWordShift j rudinShapiroWord) =
      if j % (2 ^ k) = 0 then rudinShapiro (j / 2 ^ k) else 0 := by
  unfold rudinShapiroZeroCutoff
  rw [if_congr (rudinShapiroZeroPhase_on_sample k j) rfl rfl]
  by_cases hj : j % (2 ^ k) = 0
  · simp only [hj, ite_true]
    change signValue (rudinShapiroWord (0 + j)) = _
    rw [zero_add, signValue_rudinShapiroWord, Int.toNat_natCast,
      ← rudinShapiro_pow_mul_two k (j / 2 ^ k)]
    congr 1
    simpa only [hj, zero_add] using (Nat.mod_add_div j (2 ^ k)).symm
  · simp only [hj, ite_false]

private theorem signedZeroCutoff_on_sample (k j : ℕ) :
    rudinShapiroSignedZeroCutoff k (signWordShift j rudinShapiroWord) =
      if j % (2 ^ k) = 0 then (-1 : ℝ) ^ (j / 2 ^ k) * rudinShapiro (j / 2 ^ k)
      else 0 := by
  unfold rudinShapiroSignedZeroCutoff
  rw [if_congr (rudinShapiroZeroPhase_on_sample (k + 1) j) rfl rfl, zeroCutoff_on_sample]
  by_cases h : j % (2 ^ k) = 0
  · simp only [h, ite_true]
    rw [neg_one_pow_mod_two (j / 2 ^ k)]
    have he : j = 2 ^ k * (j / 2 ^ k) := by
      simpa only [h, zero_add] using (Nat.mod_add_div j (2 ^ k)).symm
    have hm : j % (2 ^ (k + 1)) = 0 ↔ (j / 2 ^ k) % 2 = 0 := by
      conv_lhs => rw [he, pow_succ, Nat.mul_mod_mul_left,
        Nat.mul_eq_zero, or_iff_right (by positivity : (2 : ℕ) ^ k ≠ 0)]
    rw [if_congr hm rfl rfl]
    rcases Nat.mod_two_eq_zero_or_one (j / 2 ^ k) with hq | hq <;> simp [hq]
  · simp [h]

private theorem shiftedSample_eq (j t : ℕ) :
    signWordShift t (signWordShift j rudinShapiroWord) =
      signWordShift (j + t : ℕ) rudinShapiroWord := by
  rw [Nat.cast_add, add_comm, signWordShift_add]
  rfl

private theorem signedCutoff_recursion_sample (k j : ℕ) :
    let w := signWordShift j rudinShapiroWord
    2 * rudinShapiroSignedZeroCutoff (k + 1) w =
      rudinShapiroZeroCutoff k (signWordShift ((2 : ℕ) ^ k : ℕ) w) -
      rudinShapiroSignedZeroCutoff k (signWordShift ((2 : ℕ) ^ k : ℕ) w) := by
  dsimp only
  rw [shiftedSample_eq, zeroCutoff_on_sample, signedZeroCutoff_on_sample, signedZeroCutoff_on_sample]
  let B := (2 : ℕ) ^ k
  let q := j / B
  have hp : 0 < B := by dsimp [B]; positivity
  have hm : (j + B) % B = j % B := Nat.add_mod_right j B
  have hdiv : (j + B) / B = q + 1 := by
    simpa only [mul_one] using (Nat.add_mul_div_left j 1 hp)
  rw [hm, hdiv]
  by_cases h : j % B = 0
  · have he : j = B * q := by simpa only [h, zero_add] using (Nat.mod_add_div j B).symm
    have hMod : j % (2 ^ (k + 1)) = 0 ↔ q % 2 = 0 := by
      conv_lhs => rw [he, pow_succ, Nat.mul_mod_mul_left, Nat.mul_eq_zero, or_iff_right hp.ne']
    simp only [h, ite_true, hMod]
    by_cases hq : q % 2 = 0
    · have hJ : j / 2 ^ (k + 1) = q / 2 := by
        rw [he, pow_succ, Nat.mul_div_mul_left _ _ hp]
      rw [ite_eq_left hq, hJ, show q + 1 = 2 * (q / 2) + 1 by omega,
        rudinShapiro_odd, pow_succ, pow_mul]
      norm_num
      ring
    · have hEven : (q + 1) % 2 = 0 := by omega
      rw [ite_eq_right hq, neg_one_pow_mod_two, hEven, pow_zero, one_mul, sub_self, mul_zero]
  · have hbad : j % (2 ^ (k + 1)) ≠ 0 := by
      intro hz
      apply h
      rw [← Nat.mod_mod_of_dvd j (show B ∣ 2 ^ (k + 1) by rw [pow_succ]; exact dvd_mul_right _ _),
        hz, Nat.zero_mod]
    simp [h, hbad]

theorem rudinShapiroZeroCutoff_succ (k : ℕ) (w : SignWords) :
    2 * rudinShapiroZeroCutoff (k + 1) w =
      rudinShapiroZeroCutoff k w + rudinShapiroSignedZeroCutoff k w := by
  by_cases h : rudinShapiroZeroPhase (k + 1) w
  · have h' : rudinShapiroZeroPhase k w := by
      cases k with
      | zero => trivial
      | succ k => exact h.1
    simp [rudinShapiroZeroCutoff, rudinShapiroSignedZeroCutoff, h, h', two_mul]
  · simp [rudinShapiroZeroCutoff, rudinShapiroSignedZeroCutoff, h]

/-- The paired cutoffs at the next scale come from addition and a shifted
difference of the previous pair. -/
theorem rudinShapiroSignedZeroCutoff_succ {w : SignWords}
    (hw : w ∈ rudinShapiroSubshift) (k : ℕ) :
    2 * rudinShapiroSignedZeroCutoff (k + 1) w =
      rudinShapiroZeroCutoff k (signWordShift ((2 : ℕ) ^ k : ℕ) w) -
      rudinShapiroSignedZeroCutoff k (signWordShift ((2 : ℕ) ^ k : ℕ) w) := by
  let t := ((2 : ℕ) ^ k : ℕ)
  let W (j : ℕ) := insert (0 : ℤ) (rudinShapiroZeroPhaseWindow j)
  let I := W (k + 1) ∪ W (k + 2)
  let J := (W k ∪ W (k + 1)).image fun i ↦ i + (t : ℤ)
  refine rudinShapiro_local_property (P := fun w ↦
    2 * rudinShapiroSignedZeroCutoff (k + 1) w =
      rudinShapiroZeroCutoff k (signWordShift t w) -
      rudinShapiroSignedZeroCutoff k (signWordShift t w)) (I ∪ J) ?_ 0 ?_ hw
  · intro u v h hEq
    have hLocal (j : ℕ) (x y : SignWords) (he : ∀ i ∈ W j, x i = y i) :
        rudinShapiroZeroCutoff j x = rudinShapiroZeroCutoff j y :=
      if_congr (rudinShapiroZeroPhase_iff_of_agree j x y
        (fun _ hi ↦ he _ (Finset.mem_insert_of_mem hi)))
        (congrArg signValue (he 0 (Finset.mem_insert_self _ _))) rfl
    have h₀ : rudinShapiroZeroCutoff (k + 1) u = rudinShapiroZeroCutoff (k + 1) v :=
      hLocal _ _ _ (fun _ hi ↦ h _ (Finset.mem_union_left _ (Finset.mem_union_left _ hi)))
    have h₁ : rudinShapiroZeroPhase (k + 2) u ↔ rudinShapiroZeroPhase (k + 2) v :=
      rudinShapiroZeroPhase_iff_of_agree _ _ _ (fun _ hi ↦ h _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_insert_of_mem hi))))
    have h₂ : rudinShapiroZeroCutoff k (signWordShift t u) =
        rudinShapiroZeroCutoff k (signWordShift t v) :=
      hLocal _ _ _ (fun i hi ↦ h _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_union_left _ hi, rfl⟩)))
    have h₃ : rudinShapiroZeroPhase (k + 1) (signWordShift t u) ↔
        rudinShapiroZeroPhase (k + 1) (signWordShift t v) :=
      rudinShapiroZeroPhase_iff_of_agree _ _ _ (fun i hi ↦ h _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_union_right _ (Finset.mem_insert_of_mem hi), rfl⟩)))
    unfold rudinShapiroSignedZeroCutoff at hEq ⊢
    rwa [if_congr h₁ h₀ (congrArg Neg.neg h₀), h₂,
      if_congr h₃ rfl rfl] at hEq
  · intro j _
    exact signedCutoff_recursion_sample k j

/-- The centre sign restricted to an arbitrary dyadic class. -/
def rudinShapiroResidueCutoff (k a : ℕ) (w : SignWords) : ℝ :=
  if rudinShapiroResidue k a w then signValue (w 0) else 0

private theorem residueCutoff_sample (k a j : ℕ) (ha : a < 2 ^ (k + 1)) (hj : a ≤ j) :
    rudinShapiroResidueCutoff (k + 1) a (signWordShift j rudinShapiroWord) =
      rudinShapiro a * (if a / 2 ^ k = 0 then
        rudinShapiroZeroCutoff (k + 1) (signWordShift (-(a : ℤ)) (signWordShift j rudinShapiroWord))
      else rudinShapiroSignedZeroCutoff (k + 1)
        (signWordShift (-(a : ℤ)) (signWordShift j rudinShapiroWord))) := by
  let B := (2 : ℕ) ^ (k + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hShift : signWordShift (-(a : ℤ)) (signWordShift j rudinShapiroWord) =
      signWordShift ((j - a : ℕ) : ℤ) rudinShapiroWord := by
    change (signWordShift (-(a : ℤ)) ∘ signWordShift j) rudinShapiroWord = _
    rw [← signWordShift_add, Nat.cast_sub hj]
    ring_nf
  unfold rudinShapiroResidueCutoff
  rw [if_congr (rudinShapiroResidue_on_sample (k + 1) a j ha) rfl rfl,
    hShift, zeroCutoff_on_sample, signedZeroCutoff_on_sample]
  have hm : (j - a) % B = 0 ↔ j % B = a := by
    constructor
    · intro h
      rw [← Nat.sub_add_cancel hj, Nat.add_mod, h, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt ha]
    · intro hh
      have he : j = B * (j / B) + a := by
        simpa only [hh, add_comm] using (Nat.mod_add_div j B).symm
      have hDiff : j - a = B * (j / B) := by omega
      rw [hDiff, Nat.mul_mod_right]
  dsimp only [B] at hm
  simp only [hm]
  by_cases h : j % B = a
  · have he : j = B * (j / B) + a := by
      simpa only [h, add_comm] using (Nat.mod_add_div j B).symm
    have hdiv : (j - a) / B = j / B := by
      rw [show j - a = B * (j / B) by omega, Nat.mul_div_cancel_left _ hB]
    have hTop : a / 2 ^ k < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).2
      rwa [mul_comm, ← pow_succ]
    dsimp only [B] at h hdiv
    simp only [h, ite_true, hdiv]
    change signValue (rudinShapiroWord (0 + j)) = _
    rw [zero_add, signValue_rudinShapiroWord, Int.toNat_natCast]
    conv_lhs => rw [he, rudinShapiro_binary_block k (j / B) a ha]
    change rudinShapiro (j / B) * rudinShapiro a * (-1 : ℝ) ^ ((j / B % 2) * (a / 2 ^ k)) =
      rudinShapiro a * (if a / 2 ^ k = 0 then rudinShapiro (j / B)
        else (-1 : ℝ) ^ (j / B) * rudinShapiro (j / B))
    obtain h₀ | h₁ := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hTop)
    · simp [h₀, mul_comm]
    · simp only [h₁, one_ne_zero, ite_false, mul_one]
      rw [neg_one_pow_mod_two (j / B)]
      ring
  · dsimp only [B] at h
    simp [h]

/-- Each sign times a residue indicator is a scalar multiple of a translate
of one of the paired zero-class cutoffs. -/
theorem rudinShapiroResidueCutoff_eq_translate {w : SignWords} (hw : w ∈ rudinShapiroSubshift)
    (k a : ℕ) (ha : a < 2 ^ (k + 1)) :
    rudinShapiroResidueCutoff (k + 1) a w =
      rudinShapiro a * (if a / 2 ^ k = 0 then rudinShapiroZeroCutoff (k + 1) (signWordShift (-(a : ℤ)) w)
        else rudinShapiroSignedZeroCutoff (k + 1) (signWordShift (-(a : ℤ)) w)) := by
  let t := -(a : ℤ)
  let I := insert (0 : ℤ) (rudinShapiroResidueWindow (k + 1) a)
  let J := (insert (0 : ℤ) (rudinShapiroZeroPhaseWindow (k + 1) ∪
    rudinShapiroZeroPhaseWindow (k + 2))).image fun i ↦ i + t
  refine rudinShapiro_local_property (P := fun w ↦ rudinShapiroResidueCutoff (k + 1) a w =
    rudinShapiro a * (if a / 2 ^ k = 0 then rudinShapiroZeroCutoff (k + 1) (signWordShift t w)
      else rudinShapiroSignedZeroCutoff (k + 1) (signWordShift t w))) (I ∪ J) ?_ a ?_ hw
  · intro u v h he
    have hI : rudinShapiroResidueCutoff (k + 1) a u = rudinShapiroResidueCutoff (k + 1) a v :=
      if_congr (rudinShapiroResidue_iff_of_agree _ _ _ _ fun _ hi ↦
        h _ (Finset.mem_union_left _ (Finset.mem_insert_of_mem hi)))
        (congrArg signValue (h 0 (Finset.mem_union_left _ (Finset.mem_insert_self _ _)))) rfl
    have hJ (i : ℤ) (hi : i ∈ insert (0 : ℤ) (rudinShapiroZeroPhaseWindow (k + 1) ∪
        rudinShapiroZeroPhaseWindow (k + 2))) : signWordShift t u i = signWordShift t v i :=
      h _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    have h₁ : rudinShapiroZeroCutoff (k + 1) (signWordShift t u) =
        rudinShapiroZeroCutoff (k + 1) (signWordShift t v) :=
      if_congr (rudinShapiroZeroPhase_iff_of_agree _ _ _ fun _ hi ↦
        hJ _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)))
        (congrArg signValue (hJ _ (Finset.mem_insert_self _ _))) rfl
    have h₂ : rudinShapiroSignedZeroCutoff (k + 1) (signWordShift t u) =
        rudinShapiroSignedZeroCutoff (k + 1) (signWordShift t v) :=
      if_congr (rudinShapiroZeroPhase_iff_of_agree _ _ _ fun _ hi ↦
        hJ _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hi))) h₁ (congrArg Neg.neg h₁)
    rwa [hI, h₁, h₂] at he
  · intro j hj
    exact residueCutoff_sample k a j ha hj

end Mixing
