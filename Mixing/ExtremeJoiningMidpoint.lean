/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.JoiningExtreme

@[expose] public section
noncomputable section

namespace Mixing

open MeasureTheory Set
open scoped ENNReal

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable {S : System G X} {T : System G Y}

private theorem affine_preserves {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]
    {f : W → V} {μ₁ μ₂ : Measure W} {ν₁ ν₂ : Measure V}
    (h₁ : MeasurePreserving f μ₁ ν₁) (h₂ : MeasurePreserving f μ₂ ν₂) (a b : ℝ≥0∞) :
    MeasurePreserving f (a • μ₁ + b • μ₂) (a • ν₁ + b • ν₂) := by
  refine ⟨h₁.measurable, ?_⟩
  rw [Measure.map_add _ _ h₁.measurable, Measure.map_smul a h₁.aemeasurable,
    Measure.map_smul b h₂.aemeasurable, h₁.map_eq, h₂.map_eq]

/-- Joinings with fixed marginal systems are closed under convex combinations. -/
theorem IsJoining.affineCombination {μ₁ μ₂ : Measure (X × Y)}
    (h₁ : IsJoining S T μ₁) (h₂ : IsJoining S T μ₂) {a b : ℝ≥0∞} (hab : a + b = 1) :
    IsJoining S T (a • μ₁ + b • μ₂) := by
  let := h₁.probability
  let := h₂.probability
  refine ⟨⟨?_⟩, ?_, ?_, fun g => affine_preserves (h₁.invariant g) (h₂.invariant g) a b⟩
  · simp only [add_apply, smul_apply, smul_eq_mul, measure_univ, mul_one, hab]
  · simpa only [← add_smul, hab, one_smul] using affine_preserves h₁.fst h₂.fst a b
  · simpa only [← add_smul, hab, one_smul] using affine_preserves h₁.snd h₂.snd a b

private theorem eq_of_nonzero_affine_eq_right {W : Type*} [MeasurableSpace W]
    {μ ν : Measure W} [IsFiniteMeasure ν] {a b : ℝ≥0∞}
    (ha : 0 < a) (hab : a + b = 1) (h : a • μ + b • ν = ν) : μ = ν := by
  have haTop : a ≠ ∞ := ne_of_lt ((show a ≤ 1 from hab ▸ le_self_add).trans_lt ENNReal.one_lt_top)
  have hbTop : b ≠ ∞ := ne_of_lt ((show b ≤ 1 from hab ▸ le_add_self).trans_lt ENNReal.one_lt_top)
  apply Measure.ext
  intro E _
  have he := congrArg (fun m : Measure W => m E) h
  simp only [add_apply, smul_apply, smul_eq_mul] at he
  have hsplit : ν E = a * ν E + b * ν E := by rw [← add_mul, hab, one_mul]
  exact (ENNReal.mul_right_inj ha.ne' haTop).1
    ((ENNReal.add_left_inj (ENNReal.mul_ne_top hbTop (measure_ne_top _ _))).1 (he.trans hsplit))

private theorem half_add_half : (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) = 1 := by
  rw [← two_mul, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

private theorem one_sub_half : 1 - (1 / 2 : ℝ≥0∞) = 1 / 2 :=
  (ENNReal.add_left_inj (show (1 / 2 : ℝ≥0∞) ≠ ∞ by norm_num)).1
    ((tsub_add_cancel_of_le (by norm_num : (1 / 2 : ℝ≥0∞) ≤ 1)).trans half_add_half.symm)

private theorem eq_of_small_affine_split {μ μ₁ μ₂ : Measure (X × Y)}
    (h₁ : IsJoining S T μ₁) (h₂ : IsJoining S T μ₂)
    (hMid : ∀ τ, IsJoining S T τ → (1 / 2 : ℝ≥0∞) • τ + (1 / 2 : ℝ≥0∞) • μ₂ = μ → τ = μ₂)
    {a b : ℝ≥0∞} (ha : 0 < a) (haHalf : a ≤ 1 / 2) (hab : a + b = 1)
    (he : a • μ₁ + b • μ₂ = μ) : μ₁ = μ₂ := by
  let c := a + a
  let τ := c • μ₁ + (1 - c) • μ₂
  have hc : c ≤ 1 := (add_le_add haHalf haHalf).trans_eq half_add_half
  have hSplit : (1 - c) + c = 1 := tsub_add_cancel_of_le hc
  have hτ : IsJoining S T τ := h₁.affineCombination h₂ (by rw [add_comm, hSplit])
  have hLeft : (1 / 2 : ℝ≥0∞) * c = a := by
    change (1 / 2 : ℝ≥0∞) * (a + a) = _
    rw [mul_add, ← add_mul, half_add_half, one_mul]
  have hRight : (1 / 2 : ℝ≥0∞) * (1 - c) + 1 / 2 = b := by
    have h := congrArg (fun x : ℝ≥0∞ => (1 / 2 : ℝ≥0∞) * x) hSplit
    simp only [mul_add, hLeft, mul_one] at h
    have hs : (1 / 2 : ℝ≥0∞) * (1 - c) + 1 / 2 + a = b + a := by
      rw [add_right_comm, h, half_add_half, add_comm b a, hab]
    exact (ENNReal.add_left_inj (ne_of_lt (haHalf.trans_lt (by norm_num)))).1 hs
  have hm : (1 / 2 : ℝ≥0∞) • τ + (1 / 2 : ℝ≥0∞) • μ₂ = μ := by
    change (1 / 2 : ℝ≥0∞) • (c • μ₁ + (1 - c) • μ₂) + (1 / 2 : ℝ≥0∞) • μ₂ = μ
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, hLeft, hRight, he]
  let := h₂.probability
  exact eq_of_nonzero_affine_eq_right (ha.trans_le le_self_add)
    (by rw [add_comm, hSplit]) (hMid τ hτ hm)

/-- Extremality among the joinings can be tested using only midpoint decompositions. -/
theorem isExtremeJoining_iff_midpoint {μ : Measure (X × Y)} :
    IsExtremeJoining S T μ ↔ IsJoining S T μ ∧
      ∀ μ₁ μ₂, IsJoining S T μ₁ → IsJoining S T μ₂ →
        (1 / 2 : ℝ≥0∞) • μ₁ + (1 / 2 : ℝ≥0∞) • μ₂ = μ → μ₁ = μ₂ := by
  constructor
  · rintro ⟨hμ, hx⟩
    refine ⟨hμ, fun μ₁ μ₂ h₁ h₂ hmid => ?_⟩
    obtain ⟨h₁μ, h₂μ⟩ := hx μ₁ μ₂ h₁ h₂ (1 / 2) (by norm_num) (by norm_num) (by rwa [one_sub_half])
    exact h₁μ.trans h₂μ.symm
  · rintro ⟨hμ, hMid⟩
    refine ⟨hμ, fun μ₁ μ₂ h₁ h₂ a ha₀ ha₁ hEq => ?_⟩
    have hab : a + (1 - a) = 1 := add_tsub_cancel_of_le ha₁.le
    have h₁₂ : μ₁ = μ₂ := by
      by_cases ha : a ≤ 1 / 2
      · exact eq_of_small_affine_split h₁ h₂ (fun τ hτ he => hMid τ μ₂ hτ h₂ he) ha₀ ha hab hEq
      · have hbf : 1 - a ≤ 1 / 2 :=
          (tsub_le_tsub_left (le_of_not_ge ha) 1).trans_eq one_sub_half
        symm
        apply eq_of_small_affine_split h₂ h₁ (fun τ hτ he => hMid τ μ₁ hτ h₁ he)
          (tsub_pos_of_lt ha₁) hbf
        · rwa [add_comm]
        · rwa [add_comm]
    rw [h₁₂, ← add_smul, hab, one_smul] at hEq
    exact ⟨h₁₂.trans hEq, hEq⟩

end Mixing
