/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroSpectral

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped BigOperators Classical ENNReal Topology

/-- A finite pattern occurring after the given index in the one-sided
Rudin–Shapiro word. All positions in the occurrence are nonnegative. -/
def RudinShapiroPattern (I : Finset ℤ) (N : ℕ) (u : I → Bool) : Prop :=
  ∃ j : ℕ, N ≤ j ∧ ∀ i : I, 0 ≤ (j : ℤ) + i ∧ u i = rudinShapiroWord ((j : ℤ) + i)

/-- Two-sided Rudin–Shapiro words described by finite patterns seen
arbitrarily far along the generating word. -/
def rudinShapiroSubshift : Set SignWords :=
  {w | ∀ (I : Finset ℤ) (N : ℕ), RudinShapiroPattern I N (fun i ↦ w i)}

/-- A property determined by a single finite window passes from eventual
samples of the generating word to every point of its subshift. -/
theorem rudinShapiro_local_property {P : SignWords → Prop} (I : Finset ℤ)
    (hLocal : ∀ u v : SignWords, (∀ i ∈ I, u i = v i) → P u → P v)
    (N : ℕ) (hSamples : ∀ j : ℕ, N ≤ j → P (signWordShift j rudinShapiroWord))
    {w : SignWords} (hw : w ∈ rudinShapiroSubshift) : P w := by
  obtain ⟨j, hj, hPat⟩ := hw I N
  apply hLocal (signWordShift j rudinShapiroWord) w _ (hSamples j hj)
  intro i hi
  have h := (hPat ⟨i, hi⟩).2.symm
  simpa only [signWordShift, add_comm] using h

private def rudinShapiroBadPattern (I : Finset ℤ) (N : ℕ) : C(SignWords, ℝ) where
  toFun w := if RudinShapiroPattern I N (fun i ↦ w i) then 0 else 1
  continuous_toFun := by
    let h (u : I → Bool) : ℝ := if RudinShapiroPattern I N u then 0 else 1
    exact (continuous_of_discreteTopology (f := h)).comp
      (continuous_pi fun i : I ↦ continuous_apply (i : ℤ))

private theorem sample_badPattern_tendsto_zero (I : Finset ℤ) (N : ℕ) :
    Tendsto (fun n : ℕ ↦ (∑ j ∈ Finset.range (2 ^ n),
      rudinShapiroBadPattern I N ((signWordShift 1)^[j] rudinShapiroWord)) / (2 ^ n : ℝ))
      atTop (𝓝 0) := by
  let M := N + I.sup Int.natAbs
  let f (j : ℕ) := rudinShapiroBadPattern I N ((signWordShift 1)^[j] rudinShapiroWord)
  have hf₀ (j : ℕ) : 0 ≤ f j := by
    change 0 ≤ if RudinShapiroPattern I N _ then 0 else 1
    split_ifs <;> norm_num
  have hf₁ (j : ℕ) : f j ≤ 1 := by
    change (if RudinShapiroPattern I N _ then 0 else 1) ≤ 1
    split_ifs <;> norm_num
  have hZero (j : ℕ) (hj : M ≤ j) : f j = 0 := by
    classical
    change (if RudinShapiroPattern I N
      (fun i ↦ ((signWordShift 1)^[j] rudinShapiroWord) i) then 0 else 1) = 0
    rw [ite_eq_left]
    refine ⟨j, (Nat.le_add_right _ _).trans hj, fun i ↦ ⟨?_, ?_⟩⟩
    · have hl : i.val.natAbs ≤ I.sup Int.natAbs := Finset.le_sup i.property
      have hAbs : -i.val ≤ (i.val.natAbs : ℤ) := by
        simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -i.val))
      omega
    · rw [signWordShift_iterate]
      change rudinShapiroWord (i.val + j) = rudinShapiroWord ((j : ℤ) + i.val)
      rw [add_comm]
  have hBound (n : ℕ) : (∑ j ∈ Finset.range (2 ^ n), f j) ≤ M := by
    classical
    calc
      _ ≤ ∑ j ∈ Finset.range (2 ^ n), if j < M then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j < M
        · simpa only [ite_eq_left hj] using hf₁ j
        · rw [ite_eq_right hj, hZero j (le_of_not_gt hj)]
      _ = ((Finset.range (2 ^ n)).filter (· < M)).card := by
        rw [← Finset.sum_filter]
        simp
      _ ≤ M := by
        exact_mod_cast (Finset.card_le_card (s := (Finset.range (2 ^ n)).filter (· < M))
          (t := Finset.range M) (by
            intro j hj
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)).trans_eq (Finset.card_range M)
  have hUpper : Tendsto (fun n : ℕ ↦ (M : ℝ) / (2 ^ n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)).const_mul (M : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun n ↦ div_nonneg (Finset.sum_nonneg (fun j _ ↦ hf₀ j)) (by positivity))
    (fun n ↦ div_le_div_of_nonneg_right (hBound n) (by positivity))

/-- The invariant orbit law is carried by the Rudin–Shapiro subshift. -/
theorem ae_mem_rudinShapiroSubshift (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    ∀ᵐ w ∂(rudinShapiroOrbitLaw p : Measure SignWords), w ∈ rudinShapiroSubshift := by
  change ∀ᵐ w ∂(rudinShapiroOrbitLaw p : Measure SignWords),
    ∀ I : Finset ℤ, ∀ N : ℕ, RudinShapiroPattern I N (fun i ↦ w i)
  refine ae_all_iff.2 fun I ↦ ae_all_iff.2 fun N ↦ ?_
  let L := (rudinShapiroOrbitLaw p : Measure SignWords)
  let D := {w : SignWords | ¬ RudinShapiroPattern I N (fun i ↦ w i)}
  let f := rudinShapiroBadPattern I N
  have hD : MeasurableSet D := by
    have he : D = f ⁻¹' {1} := by
      ext w
      change ¬ RudinShapiroPattern I N _ ↔ (if RudinShapiroPattern I N _ then 0 else 1) = 1
      split_ifs <;> simp_all
    exact he ▸ f.continuous.measurable (measurableSet_singleton 1)
  have he : (f : SignWords → ℝ) = D.indicator (fun _ ↦ 1) := by
    funext w
    by_cases hw : RudinShapiroPattern I N (fun i ↦ w i) <;>
      simp [f, rudinShapiroBadPattern, D, hw]
  have hInt : (∫ w, f w ∂L) = 0 :=
    tendsto_nhds_unique (tendsto_integral_dyadicOrbitLaw (signWordShift 1) rudinShapiroWord p f)
      ((sample_badPattern_tendsto_zero I N).mono_left hp)
  rw [he, integral_indicator_const _ hD, smul_eq_mul, mul_one] at hInt
  have hNull : L D = 0 := by
    have h := congrArg ENNReal.ofReal hInt
    simpa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h
  exact ae_iff.mpr (by simpa [D] using hNull)

end Mixing
