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

open Filter MeasureTheory Set
open scoped BigOperators Classical ENNReal Topology

private theorem sum_range_residue (B N a : ℕ) (ha : a < B) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (B * N), if j % B = a then f j else 0) =
      ∑ q ∈ Finset.range N, f (B * q + a) := by
  have hB : 0 < B := Nat.zero_le a |>.trans_lt ha
  have hdiv (q : ℕ) : (B * q + a) / B = q := by
    rw [Nat.mul_add_div hB, Nat.div_eq_of_lt ha, add_zero]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij' (fun q _ ↦ B * q + a) (fun j _ ↦ j / B) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      rw [Nat.mul_comm B N, ← Nat.div_lt_iff_lt_mul hB, hdiv]
      exact Finset.mem_range.mp hq
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha]
  · intro j hj
    apply Finset.mem_range.mpr
    rw [Nat.div_lt_iff_lt_mul hB, Nat.mul_comm]
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  · intro q _
    exact hdiv q
  · intro j hj
    have h := (Finset.mem_filter.mp hj).2
    rw [add_comm, ← h, Nat.mod_add_div]
  · intros
    rfl

private def residueSignTest (k a : ℕ) (b : Bool) : C(SignWords, ℝ) where
  toFun w := if rudinShapiroResidue k a w ∧ w 0 = b then 1 else 0
  continuous_toFun := by
    let I := insert 0 (rudinShapiroResidueWindow k a)
    let ext (u : I → Bool) (i : ℤ) := if hi : i ∈ I then u ⟨i, hi⟩ else false
    let f (u : I → Bool) : ℝ :=
      if rudinShapiroResidue k a (ext u) ∧ ext u 0 = b then 1 else 0
    have he (w : SignWords) (i : ℤ) (hi : i ∈ I) : ext (fun j ↦ w j) i = w i := by
      simp [ext, hi]
    have hcomp : (fun w : SignWords ↦ if rudinShapiroResidue k a w ∧ w 0 = b then (1 : ℝ) else 0) =
        fun w ↦ f (fun j : I ↦ w j) := by
      funext w
      have hr := rudinShapiroResidue_iff_of_agree k a (ext (fun j ↦ w j)) w
        (fun i hi ↦ he w i (Finset.mem_insert_of_mem hi))
      change _ = if rudinShapiroResidue k a (ext (fun j ↦ w j)) ∧
        ext (fun j ↦ w j) 0 = b then 1 else 0
      rw [hr, he w 0 (Finset.mem_insert_self _ _)]
    rw [hcomp]
    have hc : Continuous (fun w : SignWords ↦ fun i : I ↦ w i) :=
      continuous_pi fun i : I ↦ continuous_apply (i : ℤ)
    exact (continuous_of_discreteTopology (f := f)).comp hc

private theorem tendsto_rudinShapiro_progression_mean (k a : ℕ) (ha : a < 2 ^ k) :
    Tendsto (fun n : ℕ ↦
      (∑ q ∈ Finset.range (2 ^ n), rudinShapiro (2 ^ k * q + a)) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  cases k with
  | zero =>
    have h : a = 0 := by simp only [pow_zero] at ha; omega
    subst a
    simp only [pow_zero, one_mul, add_zero]
    exact rudinShapiro_dyadic_means.1
  | succ k =>
    have hbound : a / 2 ^ k < 2 :=
      (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa only [pow_succ'] using ha)
    have hsplit : a / 2 ^ k = 0 ∨ a / 2 ^ k = 1 := by
      generalize a / 2 ^ k = d at hbound ⊢
      omega
    rcases hsplit with ht | ht
    · have h (q : ℕ) : rudinShapiro (2 ^ (k + 1) * q + a) = rudinShapiro a * rudinShapiro q := by
        rw [rudinShapiro_binary_block k q a ha, ht, mul_zero, pow_zero, mul_one, mul_comm]
      simp_rw [h, ← Finset.mul_sum, mul_div_assoc]
      change Tendsto (fun n ↦ rudinShapiro a * rudinShapiroMean n) atTop (𝓝 0)
      simpa only [mul_zero] using rudinShapiro_dyadic_means.1.const_mul (rudinShapiro a)
    · have h (q : ℕ) : rudinShapiro (2 ^ (k + 1) * q + a) =
          rudinShapiro a * ((-1 : ℝ) ^ q * rudinShapiro q) := by
        rw [rudinShapiro_binary_block k q a ha, ht, mul_one, ← neg_one_pow_mod_two]
        ring
      simp_rw [h, ← Finset.mul_sum, mul_div_assoc]
      change Tendsto (fun n ↦ rudinShapiro a * rudinShapiroSignedMean n) atTop (𝓝 0)
      simpa only [mul_zero] using rudinShapiro_dyadic_means.2.const_mul (rudinShapiro a)

private theorem rudinShapiro_bool_eq_indicator (j : ℕ) (b : Bool) :
    (if rudinShapiroWord (j : ℤ) = b then (1 : ℝ) else 0) =
      (1 + signValue b * rudinShapiro j) / 2 := by
  have h : signValue (rudinShapiroWord (j : ℤ)) = rudinShapiro j := by
    rw [signValue_rudinShapiroWord, Int.toNat_natCast]
  rw [← h]
  cases rudinShapiroWord (j : ℤ) <;> cases b <;> norm_num [signValue]

private theorem tendsto_rudinShapiro_residueSign (k a : ℕ) (b : Bool) (ha : a < 2 ^ k) :
    Tendsto (fun n : ℕ ↦
      (∑ j ∈ Finset.range (2 ^ n),
        residueSignTest k a b ((signWordShift 1)^[j] rudinShapiroWord)) / (2 : ℝ) ^ n)
      atTop (𝓝 ((1 / 2) / (2 : ℝ) ^ k)) := by
  apply (tendsto_add_atTop_iff_nat k).1
  have hsum (n : ℕ) :
      (∑ q ∈ Finset.range (2 ^ n),
        (if rudinShapiroWord ((2 ^ k * q + a : ℕ) : ℤ) = b then (1 : ℝ) else 0)) / (2 : ℝ) ^ n =
      (1 + signValue b *
        ((∑ q ∈ Finset.range (2 ^ n), rudinShapiro (2 ^ k * q + a)) / (2 : ℝ) ^ n)) / 2 := by
    simp_rw [rudinShapiro_bool_eq_indicator, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat, mul_one]
    field_simp
  have he (n : ℕ) :
      (∑ j ∈ Finset.range (2 ^ (n + k)),
        residueSignTest k a b ((signWordShift 1)^[j] rudinShapiroWord)) / (2 : ℝ) ^ (n + k) =
      ((1 + signValue b *
        ((∑ q ∈ Finset.range (2 ^ n), rudinShapiro (2 ^ k * q + a)) / (2 : ℝ) ^ n)) / 2) /
          (2 : ℝ) ^ k := by
    have hf (j : ℕ) : residueSignTest k a b ((signWordShift 1)^[j] rudinShapiroWord) =
        if j % (2 ^ k) = a then
          (if rudinShapiroWord (j : ℤ) = b then (1 : ℝ) else 0) else 0 := by
      rw [signWordShift_iterate]
      change (if rudinShapiroResidue k a (signWordShift j rudinShapiroWord) ∧
        rudinShapiroWord (0 + j) = b then (1 : ℝ) else 0) = _
      rw [zero_add, rudinShapiroResidue_on_sample k a j ha]
      split_ifs <;> simp_all
    simp_rw [hf]
    rw [pow_add (2 : ℕ), mul_comm (2 ^ n) (2 ^ k), sum_range_residue _ _ _ ha,
      pow_add (2 : ℝ), ← div_div, hsum]
  simp_rw [he]
  have h := (((tendsto_rudinShapiro_progression_mean k a ha).const_mul (signValue b)).const_add 1
      |>.div_const 2).div_const ((2 : ℝ) ^ k)
  simpa only [mul_zero, add_zero] using h

/-- Under the measured Rudin–Shapiro orbit law, the central sign is uniform
and independent of the residue modulo each power of two. -/
theorem measure_rudinShapiro_residueSign (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (k a : ℕ) (b : Bool) (ha : a < 2 ^ k) :
    (rudinShapiroOrbitLaw p : Measure SignWords) {w | rudinShapiroResidue k a w ∧ w 0 = b} =
      ENNReal.ofReal ((1 / 2) / (2 : ℝ) ^ k) := by
  let L := (rudinShapiroOrbitLaw p : Measure SignWords)
  let D := {w : SignWords | rudinShapiroResidue k a w ∧ w 0 = b}
  let f := residueSignTest k a b
  have hD : MeasurableSet D := (measurableSet_rudinShapiroResidue k a).inter
    (measurable_pi_apply 0 (measurableSet_singleton b))
  have he : (f : SignWords → ℝ) = D.indicator (fun _ ↦ 1) := by
    funext w
    change (if w ∈ D then (1 : ℝ) else 0) = D.indicator (fun _ ↦ 1) w
    rw [Set.indicator_apply]
  have hInt : (∫ w, f w ∂L) = (1 / 2) / (2 : ℝ) ^ k :=
    tendsto_nhds_unique (tendsto_integral_dyadicOrbitLaw (signWordShift 1) rudinShapiroWord p f)
      ((tendsto_rudinShapiro_residueSign k a b ha).mono_left hp)
  rw [he, integral_indicator_const _ hD, smul_eq_mul, mul_one] at hInt
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top L D)] using
    congrArg ENNReal.ofReal hInt

/-- Every residue class modulo a power of two has the same probability. -/
theorem measure_rudinShapiro_residue (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (k : ℕ) (a : Fin (2 ^ k)) :
    (rudinShapiroOrbitLaw p : Measure SignWords) {w | rudinShapiroResidue k a w} =
      ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  let D (b : Bool) := {w : SignWords | rudinShapiroResidue k a w ∧ w 0 = b}
  have hd : _root_.Disjoint (D true) (D false) := Set.disjoint_left.mpr fun w h₁ h₂ ↦ by
    have ha : w 0 = true := h₁.2
    have hb : w 0 = false := h₂.2
    exact Bool.noConfusion (ha.symm.trans hb)
  have hD : MeasurableSet (D false) := (measurableSet_rudinShapiroResidue k a).inter
    (measurable_pi_apply 0 (measurableSet_singleton false))
  have he : {w | rudinShapiroResidue k a w} = D true ∪ D false := by
    ext w
    change rudinShapiroResidue k a w ↔
      (rudinShapiroResidue k a w ∧ w 0 = true) ∨ (rudinShapiroResidue k a w ∧ w 0 = false)
    cases w 0 <;> simp
  rw [he, measure_union hd hD]
  change (rudinShapiroOrbitLaw p : Measure SignWords)
    {w | rudinShapiroResidue k a w ∧ w 0 = true} +
    (rudinShapiroOrbitLaw p : Measure SignWords)
    {w | rudinShapiroResidue k a w ∧ w 0 = false} = _
  rw [measure_rudinShapiro_residueSign p hp k a true a.isLt,
    measure_rudinShapiro_residueSign p hp k a false a.isLt, ← ENNReal.ofReal_add (by positivity)
      (by positivity), ← add_div, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num

end Mixing
