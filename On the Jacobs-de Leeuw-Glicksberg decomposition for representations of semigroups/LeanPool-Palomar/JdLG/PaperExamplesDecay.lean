/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Orbits
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The shrinking scalar representation of Example 3.3

Scalar multiplication by `2⁻¹` generates a JdLG-admissible representation of
the additive semigroup of natural numbers. Every norm orbit is precompact,
every vector is almost weakly stable, and only zero is reversible.
-/

@[expose] public section

namespace JdLG.PaperExamplesDecay

open Filter
open scoped Topology

/-- The representation `z ↦ (1/2)^n z`, with the additive index written multiplicatively. -/
noncomputable def representation : Multiplicative ℕ →ₙ* (ℂ →L[ℂ] ℂ) where
  toFun n := ((2 : ℂ)⁻¹) ^ n.toAdd • ContinuousLinearMap.id ℂ ℂ
  map_mul' m n := by
    apply ContinuousLinearMap.ext
    intro z
    change ((2 : ℂ)⁻¹) ^ (m.toAdd + n.toAdd) * z =
      ((2 : ℂ)⁻¹) ^ m.toAdd * (((2 : ℂ)⁻¹) ^ n.toAdd * z)
    rw [pow_add, mul_assoc]

theorem representation_apply (n : ℕ) (z : ℂ) :
    representation (Multiplicative.ofAdd n) z = (2 : ℂ) ^ (-(n : ℤ)) * z := by
  change ((2 : ℂ)⁻¹) ^ n * z = (2 : ℂ) ^ (-(n : ℤ)) * z
  rw [zpow_neg, zpow_natCast, inv_pow]

private theorem scalar_tendsto_zero : Tendsto (fun n : ℕ ↦ ((2 : ℂ)⁻¹) ^ n) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  rw [norm_inv, Complex.norm_ofNat]
  norm_num

theorem tendsto_zero_in_operator_norm :
    Tendsto (fun n : ℕ ↦ representation (Multiplicative.ofAdd n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  change Tendsto (fun n : ℕ ↦ ‖((2 : ℂ)⁻¹) ^ n • ContinuousLinearMap.id ℂ ℂ‖) atTop (𝓝 0)
  simp_rw [norm_smul]
  simpa only [zero_mul] using
    (tendsto_zero_iff_norm_tendsto_zero.1 scalar_tendsto_zero).mul_const
      ‖ContinuousLinearMap.id ℂ ℂ‖

theorem tendsto_zero_in_weakOperatorTopology :
    Tendsto (fun n : ℕ ↦ weakRepresentation representation (Multiplicative.ofAdd n)) atTop
      (𝓝 (0 : ℂ →WOT[ℂ] ℂ)) :=
  (ContinuousLinearMapWOT.continuous_ofCLM.tendsto (0 : ℂ →L[ℂ] ℂ)).comp
    tendsto_zero_in_operator_norm

theorem zero_mem_weakOperatorClosure : (0 : ℂ →WOT[ℂ] ℂ) ∈ weakOperatorClosure representation := by
  change (0 : ℂ →WOT[ℂ] ℂ) ∈ closure (Set.range (weakRepresentation representation))
  exact mem_closure_of_tendsto tendsto_zero_in_weakOperatorTopology
    (.of_forall fun n ↦ Set.mem_range_self (Multiplicative.ofAdd n))

theorem weakOperatorClosure_compact :
    IsCompact (weakOperatorClosure representation : Set (ℂ →WOT[ℂ] ℂ)) := by
  change IsCompact (closure (Set.range (weakRepresentation representation)))
  have hc := tendsto_zero_in_weakOperatorTopology.isCompact_insert_range
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  rintro A ⟨n, rfl⟩
  exact Set.mem_insert_of_mem _ (Set.mem_range_self n.toAdd)

theorem admissible : IsJdLGAdmissible representation := by
  refine admissible_of_commutative weakOperatorClosure_compact fun m n ↦ ?_
  rw [← map_mul, ← map_mul, mul_comm m n]

theorem all_orbits_precompact (z : ℂ) : HasPrecompactOrbit representation z := by
  have h : Tendsto (fun n : ℕ ↦ representation (Multiplicative.ofAdd n) z) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ ↦ ((2 : ℂ)⁻¹) ^ n * z) atTop (𝓝 0)
    simpa only [zero_mul] using scalar_tendsto_zero.mul_const z
  change IsCompact (closure (Set.range fun n ↦ representation n z))
  have hc := h.isCompact_insert_range
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  rintro w ⟨n, rfl⟩
  exact Set.mem_insert_of_mem _ (Set.mem_range_self n.toAdd)

theorem all_vectors_almost_weakly_stable (z : ℂ) :
    IsAlmostWeaklyStable (closureAction representation) z :=
  ⟨⟨0, zero_mem_weakOperatorClosure⟩, rfl⟩

theorem reversible_iff_zero (z : ℂ) : IsReversible (closureAction representation) z ↔ z = 0 := by
  let A : weakOperatorClosure representation := ⟨0, zero_mem_weakOperatorClosure⟩
  constructor
  · intro h
    obtain ⟨B, hB⟩ := h A
    exact hB.symm.trans (map_zero (closureAction representation B))
  · rintro rfl B
    exact ⟨B, by simp⟩

end JdLG.PaperExamplesDecay
