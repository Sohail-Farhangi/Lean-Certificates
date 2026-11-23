/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Real.Sqrt

/-! # Strong continuity of weakly continuous unitary representations -/

@[expose] public section

open Filter
open scoped Topology

namespace JdLG

variable {X H : Type*} [TopologicalSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Weak continuity of a Hilbert-space valued map with constant norm implies
norm continuity. Control of the real part of the inner product with the
value at the base point controls the square of the norm distance. -/
theorem continuous_of_weaklyContinuous_of_constant_norm (u : X → H) (c : ℝ)
    (hnorm : ∀ x, ‖u x‖ = c) (hweak : ∀ f : StrongDual ℂ H, Continuous fun x ↦ f (u x)) :
    Continuous u := by
  apply continuous_iff_continuousAt.2
  intro y
  apply tendsto_iff_dist_tendsto_zero.2
  let N (x : X) : ℝ := c ^ 2 - 2 * (inner ℂ (u y) (u x)).re + c ^ 2
  have hN : Continuous N := by
    have hi := Complex.continuous_re.comp (hweak (innerSL ℂ (u y)))
    exact (continuous_const.sub (continuous_const.mul hi)).add continuous_const
  have hEq (x : X) : dist (u x) (u y) = Real.sqrt (N x) := by
    rw [dist_eq_norm, norm_sub_rev, ← Real.sqrt_sq (norm_nonneg (u y - u x))]
    congr 1
    have he := norm_sub_sq (𝕜 := ℂ) (u y) (u x)
    rwa [hnorm y, hnorm x] at he
  have hd : Continuous (fun x ↦ dist (u x) (u y)) :=
    (Real.continuous_sqrt.comp hN).congr fun x ↦ (hEq x).symm
  have ht : Tendsto (fun x ↦ dist (u x) (u y)) (𝓝 y) (𝓝 (dist (u y) (u y))) :=
    hd.continuousAt
  rwa [dist_self] at ht

/-- A weakly continuous family of unitary operators is strongly continuous,
in particular for a unitary representation as in §2.4. -/
theorem continuous_orbit_of_weaklyContinuous_unitary
    (U : X → H ≃ₗᵢ[ℂ] H)
    (hU : Continuous fun x ↦
      ContinuousLinearMapWOT.ofCLM (U x).toContinuousLinearEquiv.toContinuousLinearMap)
    (v : H) : Continuous (fun x ↦ U x v) :=
  continuous_of_weaklyContinuous_of_constant_norm (fun x ↦ U x v) ‖v‖
    (fun x ↦ (U x).norm_map v)
    (fun f ↦ (ContinuousLinearMapWOT.continuous_dual_apply v f).comp hU)

end JdLG
