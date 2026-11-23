/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Cube
public import VdC.Rectangles

/-! The closed rectangles used to compute the finite discrepancy on the cube. -/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace VdC

noncomputable section
open Classical

/-- The product of the closed intervals with endpoints `a i` and `b i`. -/
def closedRectangle {d : ℕ} (a b : Fin d → UnitInterval) : Set (Cube d) :=
  Set.univ.pi fun i ↦ Subtype.val ⁻¹' Set.Icc (a i : ℝ) (b i : ℝ)

theorem measurableSet_closedRectangle {d : ℕ} (a b : Fin d → UnitInterval) :
    MeasurableSet (closedRectangle a b) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc.preimage measurable_subtype_coe

/-- The product-of-lengths formula is the actual Lebesgue mass in the closed cube. -/
theorem rectangleVolume_eq_measure {d : ℕ} (a b : Fin d → UnitInterval) :
    rectangleVolume a b = (cubeLebesgue d).real (closedRectangle a b) := by
  unfold rectangleVolume closedRectangle cubeLebesgue
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [unitIntervalLebesgue, comap_subtype_coe_apply measurableSet_Icc]
  have hi : Subtype.val '' (Subtype.val ⁻¹' Set.Icc (a i : ℝ) (b i : ℝ) : Set UnitInterval) =
      Set.Icc (a i : ℝ) (b i : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, (a i).property.1.trans hx.1, hx.2.trans (b i).property.2⟩, hx, rfl⟩
  rw [hi, Real.volume_Icc, ENNReal.toReal_ofReal', max_comm]

/-- The finite count is the Cesàro average of the closed rectangle's indicator. -/
theorem rectangleFrequency_eq_indicator_average {d : ℕ} (u : ℕ → Cube d) (N : ℕ)
    (a b : Fin d → UnitInterval) :
    rectangleFrequency u N a b =
      realCesaro (fun j ↦ if u j ∈ closedRectangle a b then 1 else 0) N := by
  classical
  unfold rectangleFrequency realCesaro
  rw [← Finset.sum_filter]
  have he : ((range N).filter fun j ↦ ∀ i, (a i : ℝ) ≤ u j i ∧ (u j i : ℝ) ≤ b i) =
      (range N).filter (fun j ↦ u j ∈ closedRectangle a b) := by
    apply Finset.filter_congr
    intro j _
    simp only [closedRectangle, Set.mem_univ_pi, Set.mem_preimage, Set.mem_Icc]
  rw [he]
  simp

/-- Any bound for a family containing the closed rectangles bounds the formal discrepancy. -/
theorem rectangleDiscrepancy_le_of_family_bound {d : ℕ} (u : ℕ → Cube d) (N : ℕ)
    (𝓡 : Set (Set (Cube d))) (h𝓡 : ∀ a b, closedRectangle a b ∈ 𝓡)
    (C : ℝ) (hC : ∀ B ∈ 𝓡,
      |realCesaro (fun j ↦ if u j ∈ B then 1 else 0) N - (cubeLebesgue d).real B| ≤ C) :
    rectangleDiscrepancy u N ≤ C := by
  classical
  unfold rectangleDiscrepancy
  apply csSup_le
  · let z : Fin d → UnitInterval := fun _ ↦ ⟨0, by simp⟩
    exact ⟨_, ⟨(z, z), rfl⟩⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  simpa only [rectangleFrequency_eq_indicator_average, rectangleVolume_eq_measure] using
    hC (closedRectangle a b) (h𝓡 a b)

end

end VdC
