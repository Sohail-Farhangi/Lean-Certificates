/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Dynamics.Ergodic.EmpiricalMeasure

@[expose] public section
noncomputable section

namespace SixProblems

open Filter MeasureTheory
open scoped Topology symmDiff ENNReal

/-- An average over a finite set, with the conventional value zero at the empty set. -/
def finiteAverage {ι E : Type*} [AddCommMonoid E] [Module ℝ E] (A : Finset ι) (f : ι → E) : E :=
  (A.card : ℝ)⁻¹ • ∑ i ∈ A, f i

/-- A left Følner sequence of nonempty finite subsets of a group. -/
structure LeftFolnerSequence (G : Type*) [Group G] [DecidableEq G] where
  blocks : ℕ → Finset G
  nonempty : ∀ n, (blocks n).Nonempty
  tendsto_defect (a : G) :
    Tendsto (fun n ↦ ((blocks n).image (a * ·) ∆ blocks n).card / ((blocks n).card : ℝ))
      atTop (𝓝 0)

private theorem norm_sum_sub_sum_bound {ι : Type*} [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] (A B : Finset ι) (f : ι → E)
    {C : ℝ} (hC : ∀ i, ‖f i‖ ≤ C) :
    ‖(∑ i ∈ A, f i) - ∑ i ∈ B, f i‖ ≤ ((A ∆ B).card : ℝ) * C := by
  have hA := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : A ∩ B ⊆ A)
  have hB := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : A ∩ B ⊆ B)
  have hdiffA : A \ (A ∩ B) = A \ B := by ext; simp
  have hdiffB : B \ (A ∩ B) = B \ A := by ext; simp
  rw [hdiffA] at hA
  rw [hdiffB] at hB
  rw [← hA, ← hB, add_sub_add_right_eq_sub]
  calc
    _ ≤ ‖∑ i ∈ A \ B, f i‖ + ‖∑ i ∈ B \ A, f i‖ := norm_sub_le _ _
    _ ≤ (∑ i ∈ A \ B, C) + ∑ i ∈ B \ A, C :=
      add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hC i))
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hC i))
    _ = _ := by
      rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
      · simp [add_mul]
      · rw [Finset.disjoint_left]
        intro i hi hj
        exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

/-- Left shifts do not affect a limit of bounded Følner averages. -/
theorem LeftFolnerSequence.tendsto_average_sub_translate {G : Type*} [Group G] [DecidableEq G]
    (F : LeftFolnerSequence G) (a : G) (f : G → ℝ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C) :
    Tendsto (fun n ↦ finiteAverage (F.blocks n) (fun g ↦ f (a * g)) -
      finiteAverage (F.blocks n) f) atTop (𝓝 0) := by
  have h := (F.tendsto_defect a).mul_const C
  rw [zero_mul] at h
  apply squeeze_zero_norm _ h
  intro n
  let A := F.blocks n
  have hinj : Function.Injective (a * ·) := fun _ _ h ↦ mul_left_cancel h
  have hs := Finset.sum_image (f := f) (s := A) (g := (a * ·))
    (fun _ _ _ _ he ↦ hinj he)
  simp only [finiteAverage, smul_eq_mul, ← mul_sub, norm_mul]
  rw [← hs, Real.norm_of_nonneg (by positivity)]
  convert mul_le_mul_of_nonneg_left (norm_sum_sub_sum_bound (A.image (a * ·)) A f hC)
    (inv_nonneg.mpr (Nat.cast_nonneg A.card)) using 1
  rw [div_eq_mul_inv]
  ring

/-- The probability law of a map on a uniformly distributed finite index set. -/
def finiteEmpiricalLaw {ι E : Type*} [MeasurableSpace E] (A : Finset ι) (hA : A.Nonempty)
    (f : ι → E) : ProbabilityMeasure E :=
  ⟨(A.card : ℝ≥0∞)⁻¹ • ∑ i ∈ A, Measure.dirac (f i), ⟨by
    simp [ENNReal.inv_mul_cancel, Finset.Nonempty.card_ne_zero hA]⟩⟩

theorem integral_finiteEmpiricalLaw {ι E B : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] (A : Finset ι) (hA : A.Nonempty) (f : ι → E) (k : E → B) :
    ∫ x, k x ∂(finiteEmpiricalLaw A hA f : Measure E) = finiteAverage A (k ∘ f) := by
  change ∫ x, k x ∂((A.card : ℝ≥0∞)⁻¹ • ∑ i ∈ A, Measure.dirac (f i)) = _
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [finiteAverage]
  · exact fun i _ ↦ integrable_dirac (f := k) (by simp)

end SixProblems
