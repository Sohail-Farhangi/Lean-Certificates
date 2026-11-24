/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroParity
public import Mixing.RudinShapiroBlocks

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped Classical

/-- Test whether the dyadic phase is zero modulo a power of two.
At each step the product across half a block reads the next digit. -/
def rudinShapiroZeroPhase (k : ℕ) (w : SignWords) : Prop :=
  match k with
  | 0 => True
  | 1 => rudinShapiroParity w = 1
  | k + 2 => rudinShapiroZeroPhase (k + 1) w ∧
      signValue (w 0) * signValue (w (2 ^ k)) = 1

/-- A finite coordinate window which determines the zero-phase test. -/
def rudinShapiroZeroPhaseWindow : ℕ → Finset ℤ
  | 0 => ∅
  | 1 => (Finset.range 8).image (fun j : ℕ ↦ (j : ℤ))
  | k + 2 => insert 0 (insert (2 ^ k) (rudinShapiroZeroPhaseWindow (k + 1)))

theorem rudinShapiroZeroPhase_iff_of_agree (k : ℕ) (u v : SignWords)
    (h : ∀ i ∈ rudinShapiroZeroPhaseWindow k, u i = v i) :
    rudinShapiroZeroPhase k u ↔ rudinShapiroZeroPhase k v := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    have he : (fun i : Fin 8 ↦ u (i.val : ℤ)) = fun i : Fin 8 ↦ v (i.val : ℤ) := by
      funext i
      exact h _ (Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, rfl⟩)
    change rudinShapiroParityTest (fun i : Fin 8 ↦ u (i.val : ℤ)) = 1 ↔
      rudinShapiroParityTest (fun i : Fin 8 ↦ v (i.val : ℤ)) = 1
    rw [he]
  | more k _ ih =>
    have h₀ : u 0 = v 0 := h _ (Finset.mem_insert_self _ _)
    have h₁ : u (2 ^ k) = v (2 ^ k) :=
      h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hi := ih (fun i hi ↦ h i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)))
    simp only [rudinShapiroZeroPhase, hi, h₀, h₁]

theorem measurableSet_rudinShapiroZeroPhase (k : ℕ) :
    MeasurableSet {w : SignWords | rudinShapiroZeroPhase k w} := by
  induction k using Nat.twoStepInduction with
  | zero => simp [rudinShapiroZeroPhase]
  | one => exact rudinShapiroParity.continuous.measurable (measurableSet_singleton 1)
  | more k _ ih =>
    let f (w : SignWords) := signValue (w 0) * signValue (w (2 ^ k))
    have hf : Continuous f := by
      have hc : Continuous signValue := continuous_of_discreteTopology
      exact (hc.comp (continuous_apply 0)).mul (hc.comp (continuous_apply (2 ^ k)))
    exact ih.inter (hf.measurable (measurableSet_singleton 1))

private theorem rudinShapiro_pow_two (k : ℕ) : rudinShapiro (2 ^ k) = 1 := by
  induction k with
  | zero => simpa using rudinShapiro_odd 0
  | succ k ih => rw [pow_succ', rudinShapiro_even, ih]

private theorem rudinShapiro_zeroPhase_pair (k q : ℕ) :
    rudinShapiro (2 ^ (k + 1) * q) * rudinShapiro (2 ^ (k + 1) * q + 2 ^ k) =
      (-1 : ℝ) ^ (q % 2) := by
  have hlt : 2 ^ k < (2 : ℕ) ^ (k + 1) := by
    rw [pow_succ]
    have hpos : 0 < (2 : ℕ) ^ k := by positivity
    omega
  have h₀ := rudinShapiro_binary_block k q 0 (by positivity)
  have h₁ := rudinShapiro_binary_block k q (2 ^ k) hlt
  simp only [add_zero, rudinShapiro_zero, Nat.zero_div, mul_zero, pow_zero, mul_one] at h₀
  rw [Nat.div_self (by positivity), mul_one, rudinShapiro_pow_two, mul_one] at h₁
  rw [h₀, h₁, ← mul_assoc, ← pow_two, rudinShapiro_sq, one_mul]

private theorem neg_one_pow_eq_one_iff_mod (j : ℕ) : (-1 : ℝ) ^ j = 1 ↔ j % 2 = 0 := by
  rw [neg_one_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> norm_num [h]

theorem rudinShapiroZeroPhase_on_sample (k j : ℕ) :
    rudinShapiroZeroPhase k (signWordShift j rudinShapiroWord) ↔ j % (2 ^ k) = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [rudinShapiroZeroPhase, Nat.mod_one]
  | one =>
    simpa only [rudinShapiroZeroPhase, rudinShapiroParity_on_sample, pow_one]
      using neg_one_pow_eq_one_iff_mod j
  | more k _ ih =>
    let B := (2 : ℕ) ^ (k + 1)
    let q := j / B
    have hB : (2 : ℕ) ^ (k + 2) = B * 2 := pow_succ _ _
    have hpos : 0 < B := by dsimp [B]; positivity
    have hdiv : B ∣ B * 2 := dvd_mul_right B 2
    change (rudinShapiroZeroPhase (k + 1) (signWordShift j rudinShapiroWord) ∧ _) ↔ _
    rw [ih, hB]
    by_cases hmod : j % B = 0
    · have hq : j = B * q := by
        simpa only [hmod, zero_add] using (Nat.mod_add_div j B).symm
      have he : signValue (signWordShift j rudinShapiroWord 0) *
          signValue (signWordShift j rudinShapiroWord (2 ^ k)) = (-1 : ℝ) ^ (q % 2) := by
        change signValue (rudinShapiroWord (0 + j)) *
          signValue (rudinShapiroWord ((2 : ℤ) ^ k + j)) = _
        rw [zero_add, signValue_rudinShapiroWord, signValue_rudinShapiroWord, Int.toNat_natCast]
        have ht : ((2 : ℤ) ^ k + j).toNat = j + 2 ^ k := by
          have heq : (2 : ℤ) ^ k + (j : ℤ) = ((j + 2 ^ k : ℕ) : ℤ) := by
            push_cast
            ring
          rw [heq, Int.toNat_natCast]
        rw [ht, hq]
        exact rudinShapiro_zeroPhase_pair k q
      change (j % B = 0 ∧ _) ↔ j % (B * 2) = 0
      simp only [he, hmod, true_and]
      rw [hq, Nat.mul_mod_mul_left, Nat.mul_eq_zero, or_iff_right hpos.ne']
      rcases Nat.mod_two_eq_zero_or_one q with h | h <;> norm_num [h]
    · change (j % B = 0 ∧ _) ↔ j % (B * 2) = 0
      simp only [hmod, false_and, false_iff]
      intro hn
      apply hmod
      rw [← Nat.mod_mod_of_dvd j hdiv, hn, Nat.zero_mod]

/-- The dyadic residue classes of the measured Rudin–Shapiro shift. -/
def rudinShapiroResidue (k a : ℕ) (w : SignWords) : Prop :=
  rudinShapiroZeroPhase k (signWordShift ((2 ^ k - a : ℕ) : ℤ) w)

/-- A finite coordinate window which determines the indicated residue test. -/
def rudinShapiroResidueWindow (k a : ℕ) : Finset ℤ :=
  (rudinShapiroZeroPhaseWindow k).image fun i ↦ i + ((2 ^ k - a : ℕ) : ℤ)

theorem rudinShapiroResidue_iff_of_agree (k a : ℕ) (u v : SignWords)
    (h : ∀ i ∈ rudinShapiroResidueWindow k a, u i = v i) :
    rudinShapiroResidue k a u ↔ rudinShapiroResidue k a v :=
  rudinShapiroZeroPhase_iff_of_agree k _ _ fun i hi ↦ h _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem measurableSet_rudinShapiroResidue (k a : ℕ) :
    MeasurableSet {w : SignWords | rudinShapiroResidue k a w} :=
  (signWordShift_continuous _).measurable (measurableSet_rudinShapiroZeroPhase k)

private theorem zeroPhase_shifted_on_sample (k j t : ℕ) :
    rudinShapiroZeroPhase k (signWordShift t (signWordShift j rudinShapiroWord)) ↔
      (j + t) % (2 ^ k) = 0 := by
  change rudinShapiroZeroPhase k ((signWordShift t ∘ signWordShift j) rudinShapiroWord) ↔ _
  rw [← signWordShift_add, ← Nat.cast_add]
  simpa only [add_comm] using rudinShapiroZeroPhase_on_sample k (j + t)

theorem rudinShapiroResidue_on_sample (k a j : ℕ) (ha : a < 2 ^ k) :
    rudinShapiroResidue k a (signWordShift j rudinShapiroWord) ↔ j % (2 ^ k) = a := by
  unfold rudinShapiroResidue
  rw [zeroPhase_shifted_on_sample, Nat.add_mod j]
  let B := (2 : ℕ) ^ k
  have hB : 0 < B := by dsimp [B]; positivity
  have hj : j % B < B := Nat.mod_lt _ hB
  change ((j % B + (B - a) % B) % B = 0) ↔ j % B = a
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp
  · rw [Nat.mod_eq_of_lt (show B - a < B by omega)]
    constructor
    · intro hh
      have hd := Nat.mod_add_div (j % B + (B - a)) B
      have hlt : (j % B + (B - a)) / B < 2 := (Nat.div_lt_iff_lt_mul hB).2 (by omega)
      have hne : (j % B + (B - a)) / B ≠ 0 := by
        intro he
        rw [he, hh, mul_zero, add_zero] at hd
        omega
      have he : (j % B + (B - a)) / B = 1 :=
        le_antisymm (Nat.le_of_lt_succ hlt) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne))
      rw [he, hh, mul_one, zero_add] at hd
      omega
    · intro hh
      rw [hh, show a + (B - a) = B by omega, Nat.mod_self]

private def allResidueWindows (k : ℕ) : Finset ℤ :=
  (Finset.range (2 ^ k)).biUnion (rudinShapiroResidueWindow k)

private theorem agrees_on_residue_window {k : ℕ} {a : Fin (2 ^ k)} {u v : SignWords}
    (h : ∀ i ∈ allResidueWindows k, u i = v i) :
    rudinShapiroResidue k a u ↔ rudinShapiroResidue k a v :=
  rudinShapiroResidue_iff_of_agree k a u v fun i hi ↦
    h i (Finset.mem_biUnion.mpr ⟨a, Finset.mem_range.mpr a.isLt, hi⟩)

/-- Every word in the subshift has a unique phase modulo each power of two. -/
theorem rudinShapiroResidue_existsUnique_of_mem {w : SignWords}
    (hw : w ∈ rudinShapiroSubshift) (k : ℕ) :
    ∃! a : Fin (2 ^ k), rudinShapiroResidue k a w := by
  refine rudinShapiro_local_property (P := fun w ↦
    ∃! a : Fin (2 ^ k), rudinShapiroResidue k a w)
    (allResidueWindows k) ?_ 0 ?_ hw
  · intro u v h huv
    obtain ⟨a, ha, hu⟩ := huv
    exact ⟨a, (agrees_on_residue_window h).mp ha,
      fun b hb ↦ hu b ((agrees_on_residue_window h).mpr hb)⟩
  · intro j _
    let a : Fin (2 ^ k) := ⟨j % (2 ^ k), Nat.mod_lt _ (by positivity)⟩
    refine ⟨a, (rudinShapiroResidue_on_sample k a j a.isLt).mpr rfl, ?_⟩
    intro b hb
    exact Fin.ext ((rudinShapiroResidue_on_sample k b j b.isLt).mp hb).symm

/-- Consecutive dyadic phases are compatible under reduction. -/
theorem rudinShapiroResidue_succ_coherence_of_mem {w : SignWords}
    (hw : w ∈ rudinShapiroSubshift) (k : ℕ) (a : Fin (2 ^ (k + 1)))
    (b : Fin (2 ^ k)) (ha : rudinShapiroResidue (k + 1) a w)
    (hb : rudinShapiroResidue k b w) : a.val % (2 ^ k) = b.val := by
  refine rudinShapiro_local_property (P := fun w ↦ rudinShapiroResidue (k + 1) a w →
    rudinShapiroResidue k b w → a.val % (2 ^ k) = b.val)
      (allResidueWindows (k + 1) ∪ allResidueWindows k) ?_ 0 ?_ hw ha hb
  · intro u v h huv hav hbv
    exact huv
      ((agrees_on_residue_window (fun i hi ↦ h i (Finset.mem_union_left _ hi))).mpr hav)
      ((agrees_on_residue_window (fun i hi ↦ h i (Finset.mem_union_right _ hi))).mpr hbv)
  · intro j _ haj hbj
    rw [← (rudinShapiroResidue_on_sample (k + 1) a j a.isLt).mp haj,
      Nat.mod_mod_of_dvd _ (by rw [pow_succ]; exact dvd_mul_right _ _)]
    exact (rudinShapiroResidue_on_sample k b j b.isLt).mp hbj

/-- Shifting an integer number of places translates the dyadic phase. -/
theorem rudinShapiroResidue_shift_of_mem {w : SignWords} (hw : w ∈ rudinShapiroSubshift)
    (k : ℕ) (t : ℤ) (a b : Fin (2 ^ k)) (ha : rudinShapiroResidue k a w)
    (hb : rudinShapiroResidue k b (signWordShift t w)) :
    (b.val : ℤ) = ((a.val : ℤ) + t) % (2 ^ k) := by
  let J := (allResidueWindows k).image fun i ↦ i + t
  refine rudinShapiro_local_property (P := fun w ↦ rudinShapiroResidue k a w →
    rudinShapiroResidue k b (signWordShift t w) →
      (b.val : ℤ) = ((a.val : ℤ) + t) % (2 ^ k))
    (allResidueWindows k ∪ J) ?_ t.natAbs ?_ hw ha hb
  · intro u v h huv hav hbv
    apply huv
    · exact (agrees_on_residue_window (fun i hi ↦ h i (Finset.mem_union_left _ hi))).mpr hav
    · exact (agrees_on_residue_window (fun i hi ↦ h _
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))).mpr hbv
  · intro j hj haj hbj
    have ht : -t ≤ (t.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -t))
    have hNonneg : 0 ≤ t + (j : ℤ) := by omega
    let j' := (t + (j : ℤ)).toNat
    have hj' : (j' : ℤ) = t + (j : ℤ) := Int.toNat_of_nonneg hNonneg
    change rudinShapiroResidue k b ((signWordShift t ∘ signWordShift (j : ℤ)) rudinShapiroWord) at hbj
    rw [← signWordShift_add, ← hj'] at hbj
    have hAj := (rudinShapiroResidue_on_sample k a j a.isLt).mp haj
    have hBj := (rudinShapiroResidue_on_sample k b j' b.isLt).mp hbj
    have hAj' : (j : ℤ) % (2 ^ k) = a.val := by exact_mod_cast hAj
    have hBj' : (j' : ℤ) % (2 ^ k) = b.val := by exact_mod_cast hBj
    have hAmod : (a.val : ℤ) % (2 ^ k) = a.val := by
      rw [← hAj', Int.emod_emod]
    calc
      (b.val : ℤ) = (j' : ℤ) % (2 ^ k) := hBj'.symm
      _ = ((j : ℤ) + t) % (2 ^ k) := by rw [hj', add_comm]
      _ = ((a.val : ℤ) + t) % (2 ^ k) := by
        rw [Int.add_emod (j : ℤ) t, Int.add_emod (a.val : ℤ) t, hAj', hAmod]

end Mixing
