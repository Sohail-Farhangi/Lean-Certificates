/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesFinite
public import JdLG.Quotient
public import Mathlib.Analysis.Convex.LinearIsometry
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A counterexample to the printed Theorem 1.2(iv)

The finite operator monoid in Example 2.1 is independent of the choice of
norm on the two-dimensional space. Its Euclidean realization has strictly
convex primal and dual norms, yet fails JdLG admissibility.
-/

@[expose] public section

namespace JdLG.PrintedClaimCounterexample

/-- The complex two-dimensional space with the Euclidean norm. -/
abbrev Plane := EuclideanSpace ℂ (Fin 2)

/-- The coordinate identification with the product space in Example 2.1. -/
noncomputable def coordinates : Plane ≃L[ℂ] ℂ × ℂ :=
  ((WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).trans (LinearEquiv.finTwoArrow ℂ ℂ))
    |>.toContinuousLinearEquiv

/-- The identity and the two diagonal projections, acting on the Euclidean plane. -/
noncomputable def representation : PaperExamplesFinite.Point →ₙ* (Plane →L[ℂ] Plane) :=
  coordinates.symm.conjContinuousAlgEquiv.toRingEquiv.toMulHom.comp PaperExamplesFinite.primal

theorem coordinate_intertwines (s : PaperExamplesFinite.Point) (x : Plane) :
    PaperExamplesFinite.primal s (coordinates x) = coordinates (representation s x) := by
  change PaperExamplesFinite.primal s (coordinates x) =
    coordinates (coordinates.symm (PaperExamplesFinite.primal s (coordinates x)))
  rw [coordinates.apply_symm_apply]

/-- A Hilbert-space dual is strictly convex, using Riesz's isometry over the reals. -/
theorem dual_strictlyConvex : StrictConvexSpace ℝ (StrongDual ℂ Plane) := by
  let e := (InnerProductSpace.toDual ℂ Plane).symm
  let f : StrongDual ℂ Plane →ₗᵢ[ℝ] Plane :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun r x ↦ by
        have h := e.map_smulₛₗ (r : ℂ) x
        have hstar : star (r : ℂ) = (r : ℂ) := by simp
        change e ((r : ℂ) • x) = star (r : ℂ) • e x at h
        rw [hstar] at h
        change e (r • x) = r • e x
        calc
          e (r • x) = e ((r : ℂ) • x) :=
            congrArg e (RCLike.real_smul_eq_coe_smul (K := ℂ) r x)
          _ = (r : ℂ) • e x := h
          _ = r • e x := (RCLike.real_smul_eq_coe_smul (K := ℂ) r (e x)).symm
      norm_map' := e.norm_map }
  exact f.strictConvexSpace

theorem weakly_compact :
    IsCompact (weakOperatorClosure representation : Set (Plane →WOT[ℂ] Plane)) := by
  change IsCompact (closure (Set.range (weakRepresentation representation)))
  exact (Set.finite_range _).isCompact.closure

theorem not_admissible : ¬ IsJdLGAdmissible representation := by
  intro h
  obtain ⟨hprimal, _⟩ := admissible_surjective_intertwiner
    (f := coordinates.toContinuousLinearMap) coordinates.surjective coordinate_intertwines h
  obtain ⟨P, _, _, _, _, hstable⟩ := decomposition_of_admissible hprimal
  obtain ⟨x, y, hx, hy, hxy⟩ := PaperExamplesFinite.primal_stable_not_add_closed
  exact hxy ((hstable (x + y)).2
    ((LinearMap.ker (closureAction PaperExamplesFinite.primal P).toLinearMap).add_mem
      ((hstable x).1 hx) ((hstable y).1 hy)))

/-- All the stated hypotheses of Theorem 1.2(iv) hold, whereas its conclusion fails. -/
theorem printed_theorem_1_2_iv_counterexample :
    StrictConvexSpace ℝ Plane ∧ StrictConvexSpace ℝ (StrongDual ℂ Plane) ∧
      IsCompact (weakOperatorClosure representation : Set (Plane →WOT[ℂ] Plane)) ∧
      ¬ IsJdLGAdmissible representation :=
  ⟨inferInstance, dual_strictlyConvex, weakly_compact, not_admissible⟩

end JdLG.PrintedClaimCounterexample
