/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OrthogonalDecomposition
public import SixProblems.PositiveDefinite
public import Mathlib.Topology.Sequences

@[expose] public section
noncomputable section

namespace SixProblems

open Filter Mixing.JdLGBridge Set
open scoped InnerProductSpace Topology

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A sequence which sends all translates of a stable coefficient to zero. -/
theorem exists_stable_coefficient_sequence [Countable G]
    (U : G →* (E ≃ₗᵢ[ℝ] E))
    (K : GroupIdeal (weakOperatorClosure (orthogonalActionCLM U).toMulHom))
    (v : E) (hv : K.projection (closureAction (orthogonalActionCLM U).toMulHom) v = 0) :
    ∃ g : ℕ → G, ∀ r s : G,
      Tendsto (fun n ↦ ⟪v,U (r * (g n)⁻¹ * s) v⟫_ℝ) atTop (𝓝 0) := by
  classical
  let π := (orthogonalActionCLM U).toMulHom
  let F (a : weakOperatorClosure π) (p : G × G) :=
    ⟪U p.1⁻¹ v, closureAction π a (U p.2 v)⟫_ℝ
  have hF : Continuous F := continuous_pi fun p ↦ by
    let f := innerSL ℝ (U p.1⁻¹ v)
    exact (ContinuousLinearMapWOT.continuous_dual_apply (U p.2 v) f).comp continuous_subtype_val
  have hF0 : F K.identity = 0 := by
    funext p
    change ⟪U p.1⁻¹ v, K.projection (closureAction π) (U p.2 v)⟫_ℝ = 0
    have h := K.projection_commutes (closureAction π) (closureInclusion π p.2) v
    change K.projection (closureAction π) (U p.2 v) = U p.2 (K.projection (closureAction π) v) at h
    rw [h, hv, map_zero, inner_zero_right]
  have hcl : F K.identity ∈ closure (range (F ∘ closureInclusion π)) := by
    rw [range_comp]
    exact mem_closure_image hF.continuousAt (denseRange_closureInclusion π K.identity)
  obtain ⟨a,ha,ht⟩ := mem_closure_iff_seq_limit.mp hcl
  choose j hj using ha
  refine ⟨fun n ↦ (j n)⁻¹,fun r s ↦ ?_⟩
  have hl := ((continuous_apply (r,s)).tendsto (F K.identity)).comp ht
  rw [hF0] at hl
  have he (n : ℕ) : (a n) (r,s) = ⟪v,U (r*((j n)⁻¹)⁻¹*s) v⟫_ℝ := by
    rw [← hj n]
    change ⟪U r⁻¹ v,U (j n) (U s v)⟫_ℝ = _
    rw [← (U r).inner_map_map]
    change ⟪(U r * U r⁻¹) v,(U r * (U (j n) * U s)) v⟫_ℝ = _
    rw [← map_mul, mul_inv_cancel, map_one, ← map_mul, ← map_mul, inv_inv, mul_assoc]
    rfl
  exact hl.congr he

end SixProblems
