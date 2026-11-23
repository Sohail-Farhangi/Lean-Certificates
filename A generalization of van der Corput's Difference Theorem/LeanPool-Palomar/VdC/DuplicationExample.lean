/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.DuplicationDiscrepancy
public import VdC.DuplicationSpectrum

/-! The example motivating the use of permissible pairs. -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

/-- The doubled-square construction works for every irrational coefficient. The lag
in the discrepancy definition is `h + 1`. -/
theorem duplicationCube_example {α : ℝ} (hα : Irrational α) :
    SpectrallyLebesgueDistribution (cubeLebesgue 1) (duplicationCube α) ∧
      ∀ h : ℕ, upperDifferenceDiscrepancy (cubeToTorus ∘ duplicationCube α) h = (1 : ℝ)/2 := by
  refine ⟨duplicationCube_spectrallyLebesgue hα, ?_⟩
  intro h
  rw [cubeToTorus_duplicationCube]
  exact duplication_upper_discrepancy_eq_half hα h

/-- Orthogonality would force every positive-lag difference to have zero upper
discrepancy, whereas the doubled-square example has upper discrepancy one half. -/
theorem duplicationCube_not_orthogonal {α : ℝ} (hα : Irrational α) :
    ¬ OrthogonalDistribution (cubeLebesgue 1) (duplicationCube α) := by
  intro ho
  let x := duplicationCube α
  let y : ℕ → Cube 1 := fun n i ↦ unitRepresentative
    (cubeToTorus (x (n+1)) i - cubeToTorus (x n) i)
  have hy : Equidistributed (cubeLebesgue 1) y := by
    apply equidistributed_of_cubeToTorus
    apply (equidistributed_torus_iff _).2
    intro m hm
    let f : C(Cube 1, ℂ) := (torusCharacter m).comp ⟨cubeToTorus, continuous_cubeToTorus 1⟩
    have hf : testMean (cubeLebesgue 1) f = 0 := by
      change (∫ x, torusCharacter m (cubeToTorus x) ∂cubeLebesgue 1) = 0
      rw [← integral_map_of_stronglyMeasurable (continuous_cubeToTorus 1).measurable
        (torusCharacter m).continuous.stronglyMeasurable, (cubeToTorus_measurePreserving 1).map_eq]
      exact (testMean_torusCharacter m).trans (ite_eq_right hm)
    have ht := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test f x)).1 (ho f hf) 1 Nat.one_pos
    apply ht.congr
    intro N
    unfold corr
    congr 1
    funext n
    have he : cubeToTorus (y n) = cubeToTorus (x (n+1)) - cubeToTorus (x n) :=
      funext fun i ↦ unitRepresentative_coe _
    rw [he, torusCharacter_point_sub]
    rfl
  have hzero := (tendsto_rectangleDiscrepancy_of_equidistributed hy).limsup_eq
  change upperDifferenceDiscrepancy (cubeToTorus ∘ x) 0 = 0 at hzero
  have hhalf := (duplicationCube_example hα).2 0
  change upperDifferenceDiscrepancy (cubeToTorus ∘ x) 0 = (1 : ℝ)/2 at hhalf
  linarith only [hzero, hhalf]

/-- There is a spectrally Lebesgue sequence in the unit interval with upper
difference discrepancy exactly one half at every positive lag. -/
theorem exampleNecessitatingPermissibleTriples :
    ∃ x : ℕ → Cube 1, SpectrallyLebesgueDistribution (cubeLebesgue 1) x ∧
      ∀ h : ℕ, upperDifferenceDiscrepancy (cubeToTorus ∘ x) h = (1 : ℝ)/2 :=
  ⟨duplicationCube (Real.sqrt 2), duplicationCube_example irrational_sqrt_two⟩

end VdC
