/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.RectangleFourier
public import VdC.Rectangles

/-! # Rectangle Transfer -/

@[expose] public section

open Finset MeasureTheory Set
open scoped BigOperators

namespace VdC

noncomputable section

/-- The manuscript's finite Fourier estimate in terms of its closed-rectangle discrepancy. -/
theorem finite_fourier_rectangle_bound {d : ℕ} (m : Fin d → ℤ) (hm : m ≠ 0)
    (u : ℕ → Fin d → UnitInterval) (N : ℕ) :
    ‖cesaro (fun n ↦ torusCharacter m (fun i ↦ ((u n i : ℝ) : UnitAddCircle))) N‖ ≤
      fourierDiscrepancyConstant m * rectangleDiscrepancy u N := by
  classical
  have h := finite_fourier_bound_of_upper_rectangles m hm u N
    (rectangleDiscrepancy u N) (rectangleDiscrepancy_mem_Icc u N).1
  apply h
  intro s t
  let a : Fin d → UnitInterval := fun _ ↦ ⟨0, by simp⟩
  let b : Fin d → UnitInterval := fun i ↦ if i ∈ s then t i else ⟨1, by simp⟩
  have hf (n : ℕ) : (∀ i, (a i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ b i) ↔
      ∀ i ∈ s, (u n i : ℝ) ≤ t i := by
    refine ⟨fun H i hi ↦ ?_, fun H i ↦ ⟨(u n i).property.1, ?_⟩⟩
    · simpa [b, hi] using (H i).2
    by_cases hi : i ∈ s
    · simpa [b, hi] using H i hi
    · simpa [b, hi] using (u n i).property.2
  have hfreq : rectangleFrequency u N a b =
      (((range N).filter fun n ↦ ∀ i ∈ s, (u n i : ℝ) ≤ t i).card : ℝ) / N := by
    unfold rectangleFrequency
    exact congrArg (fun T : Finset ℕ ↦ (T.card : ℝ) / N) (Finset.filter_congr (fun n _ ↦ hf n))
  have hvol : rectangleVolume a b = ∏ i ∈ s, (t i : ℝ) := by
    unfold rectangleVolume
    simp only [a, sub_zero, max_eq_right (b _).property.1]
    simp only [b, apply_ite Subtype.val, Finset.prod_ite_mem, Finset.univ_inter]
  rw [← hfreq, ← hvol]
  exact rectangle_deviation_le_discrepancy u N a b

/-- The finite rectangle estimate for the differences of an arbitrary torus sequence. -/
theorem characterRectangleEstimate_all {d : ℕ} (x : ℕ → Torus d) : CharacterRectangleEstimate x := by
  intro m hm
  refine ⟨fourierDiscrepancyConstant m, fourierDiscrepancyConstant_nonneg m, fun h N ↦ ?_⟩
  let u (n : ℕ) (i : Fin d) := unitRepresentative (x (n + (h + 1)) i - x n i)
  have he (n : ℕ) : (fun i ↦ x (n + (h + 1)) i - x n i) = x (n + (h + 1)) - x n := rfl
  simpa only [u, unitRepresentative_coe, differenceDiscrepancy, he] using
    finite_fourier_rectangle_bound m hm u N

end
end VdC
