/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Uniformly bounded subgroups in the operator norm -/

@[expose] public section

open Topology

namespace JdLG

variable {R : Type*} [NormedRing R] (G : Subgroup Rˣ)

/-- The embedding of a subgroup of units into its ambient normed ring. -/
def boundedUnitsInclusion (g : G) : R := ↑(g : Rˣ)

/-- Inversion on a uniformly bounded subgroup of units is norm Lipschitz.
This applies to subgroups of the invertible bounded linear operators. -/
theorem norm_sub_of_boundedUnits_inv_le {C : ℝ} (hC : ∀ g : G, ‖boundedUnitsInclusion G g‖ ≤ C)
    (x y : G) :
    ‖boundedUnitsInclusion G x⁻¹ - boundedUnitsInclusion G y⁻¹‖ ≤
      C ^ 2 * ‖boundedUnitsInclusion G x - boundedUnitsInclusion G y‖ := by
  let a := boundedUnitsInclusion G x
  let b := boundedUnitsInclusion G y
  let ia := boundedUnitsInclusion G x⁻¹
  let ib := boundedUnitsInclusion G y⁻¹
  have hia : ‖ia‖ ≤ C := hC x⁻¹
  have hib : ‖ib‖ ≤ C := hC y⁻¹
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans hia
  have ha : ia * a = 1 := Units.inv_mul (x : Rˣ)
  have hb : b * ib = 1 := Units.mul_inv (y : Rˣ)
  change ‖ia - ib‖ ≤ C ^ 2 * ‖a - b‖
  have he : ia * (b - a) * ib = ia - ib := by
    rw [mul_sub, sub_mul, mul_assoc ia b, hb, ha, mul_one, one_mul]
  rw [← he, ← norm_sub_rev]
  calc
    ‖ia * (b - a) * ib‖ ≤ ‖ia * (b - a)‖ * ‖ib‖ := norm_mul_le _ _
    _ ≤ ‖ia‖ * ‖b - a‖ * ‖ib‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ C * ‖b - a‖ * C :=
      mul_le_mul (mul_le_mul_of_nonneg_right hia (norm_nonneg _)) hib (norm_nonneg _)
        (mul_nonneg hC₀ (norm_nonneg _))
    _ = C ^ 2 * ‖b - a‖ := by ring

/-- With the topology inherited from the ambient norm on the operators, a
uniformly bounded subgroup of invertible operators is a topological group. -/
theorem isTopologicalGroup_boundedUnits_induced {C : ℝ}
    (hC : ∀ g : G, ‖boundedUnitsInclusion G g‖ ≤ C) :
    @IsTopologicalGroup G (TopologicalSpace.induced (boundedUnitsInclusion G) inferInstance)
      inferInstance := by
  let : PseudoMetricSpace G := .induced (boundedUnitsInclusion G) inferInstance
  let : TopologicalSpace G := TopologicalSpace.induced (boundedUnitsInclusion G) inferInstance
  have hc : Continuous (boundedUnitsInclusion G) := continuous_induced_dom
  have hinv : LipschitzWith ⟨C ^ 2, sq_nonneg C⟩
      (fun g : G ↦ boundedUnitsInclusion G g⁻¹) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (boundedUnitsInclusion G x⁻¹) (boundedUnitsInclusion G y⁻¹) ≤
      C ^ 2 * dist (boundedUnitsInclusion G x) (boundedUnitsInclusion G y)
    simpa only [dist_eq_norm] using norm_sub_of_boundedUnits_inv_le G hC x y
  exact {
    continuous_mul := continuous_induced_rng.2
      ((hc.comp continuous_fst).mul (hc.comp continuous_snd))
    continuous_inv := continuous_induced_rng.2 hinv.continuous }

end JdLG
