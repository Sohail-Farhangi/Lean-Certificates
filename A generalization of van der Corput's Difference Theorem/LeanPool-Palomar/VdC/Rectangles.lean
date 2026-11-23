/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Difference
public import VdC.Cube

/-! # Rectangles -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

noncomputable section

def rectangleFrequency {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ)
    (a b : Fin d → UnitInterval) : ℝ := by
  classical
  exact (((range N).filter fun n => ∀ i, (a i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ b i).card : ℝ) / N

def rectangleVolume {d : ℕ} (a b : Fin d → UnitInterval) : ℝ :=
  ∏ i, max 0 ((b i : ℝ) - (a i : ℝ))

def rectangleDiscrepancy {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ) : ℝ :=
  sSup (Set.range fun ab : (Fin d → UnitInterval) × (Fin d → UnitInterval) =>
    |rectangleFrequency u N ab.1 ab.2 - rectangleVolume ab.1 ab.2|)

private theorem rectangle_deviation_le_one {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ)
    (a b : Fin d → UnitInterval) : |rectangleFrequency u N a b - rectangleVolume a b| ≤ 1 := by
  classical
  have hvol0 : 0 ≤ rectangleVolume a b := Finset.prod_nonneg fun _ _ => le_max_left ..
  have hvol1 : rectangleVolume a b ≤ 1 := by
    apply Finset.prod_le_one₀ (fun _ _ => le_max_left _ _)
    intro i _
    exact max_le zero_le_one (by linarith [(b i).property.2, (a i).property.1])
  have hf0 : 0 ≤ rectangleFrequency u N a b := by unfold rectangleFrequency; positivity
  have hf1 : rectangleFrequency u N a b ≤ 1 := by
    by_cases hN : N = 0
    · simp [rectangleFrequency, hN]
    have hNr : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [rectangleFrequency, div_le_iff₀ hNr, one_mul]
    exact_mod_cast (card_filter_le _ _).trans_eq (card_range N)
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem rectangle_deviation_le_discrepancy {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ)
    (a b : Fin d → UnitInterval) : |rectangleFrequency u N a b - rectangleVolume a b| ≤ rectangleDiscrepancy u N :=
  le_csSup ⟨1, by rintro _ ⟨⟨a, b⟩, rfl⟩; exact rectangle_deviation_le_one u N a b⟩ ⟨(a, b), rfl⟩

theorem rectangleDiscrepancy_mem_Icc {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ) :
    rectangleDiscrepancy u N ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  let z : UnitInterval := ⟨0, by simp⟩
  change 0 ≤ rectangleDiscrepancy u N ∧ rectangleDiscrepancy u N ≤ 1
  refine ⟨(abs_nonneg _).trans (rectangle_deviation_le_discrepancy u N (fun _ => z) (fun _ => z)), ?_⟩
  unfold rectangleDiscrepancy
  apply csSup_le ⟨_, Set.mem_range_self (fun _ => z, fun _ => z)⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact rectangle_deviation_le_one u N a b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def unitRepresentative (t : UnitAddCircle) : UnitInterval :=
  let y := AddCircle.equivIco (1 : ℝ) (0 : ℝ) t
  ⟨y, ⟨y.property.1, by simpa only [zero_add] using y.property.2.le⟩⟩

theorem unitRepresentative_coe (t : UnitAddCircle) : ((unitRepresentative t : ℝ) : UnitAddCircle) = t :=
  AddCircle.coe_equivIco ..

def differenceDiscrepancy {d : ℕ} (x : ℕ → Torus d) (h N : ℕ) : ℝ :=
  rectangleDiscrepancy (fun n i => unitRepresentative (x (n + (h + 1)) i - x n i)) N

def upperDifferenceDiscrepancy {d : ℕ} (x : ℕ → Torus d) (h : ℕ) : ℝ :=
  limsup (differenceDiscrepancy x h) atTop

/-- The explicit finite Fourier estimate used in the manuscript's two difference
theorems. Each frequency has its own constant, uniform over lag and length. -/
def CharacterRectangleEstimate {d : ℕ} (x : ℕ → Torus d) : Prop :=
  ∀ m : Fin d → ℤ, m ≠ 0 → ∃ K : ℝ, 0 ≤ K ∧ ∀ h N,
    ‖cesaro (fun n => torusCharacter m (x (n + (h + 1)) - x n)) N‖ ≤
      K * differenceDiscrepancy x h N

theorem spectral_character_of_rectangle_discrepancy {d : ℕ} (x : ℕ → Torus d)
    (hKH : CharacterRectangleEstimate x) (hD : Summable (fun h => upperDifferenceDiscrepancy x h ^ 2))
    (m : Fin d → ℤ) (hm : m ≠ 0) : SpectrallyLebesgue (fun n => torusCharacter m (x n)) := by
  obtain ⟨K, hK, hb⟩ := hKH m hm
  exact spectral_difference_character x m (differenceDiscrepancy x) K hK
    (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) hb hD

theorem weakMixing_character_of_rectangle_discrepancy {d : ℕ} (x : ℕ → Torus d)
    (hKH : CharacterRectangleEstimate x) (hD : Tendsto (realCesaro (upperDifferenceDiscrepancy x)) atTop (𝓝 0))
    (m : Fin d → ℤ) (hm : m ≠ 0) : NearlyWeakMixing (fun n => torusCharacter m (x n)) := by
  obtain ⟨K, hK, hb⟩ := hKH m hm
  exact weakMixing_difference_character x m (differenceDiscrepancy x) K hK
    (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) hb hD

end
end VdC
