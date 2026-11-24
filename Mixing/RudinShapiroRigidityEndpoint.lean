/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroHalfRigidity
public import Mixing.RudinShapiroSpectral
public import Mixing.ComplementaryMixingProduct
public import Mixing.RigidInjectivity

/-! # Sharpness of the one-half injectivity threshold -/

@[expose] public section
noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace Mixing

theorem rudinShapiro_coordinate_ne_zero (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    rudinShapiroSignLp p hp ≠ 0 := by
  intro h
  have he := rudinShapiroSignLp_autocorrelation p hp 0
  simp only [h, inner_zero_left] at he
  exact zero_ne_one he

/-- The coordinate sign is annihilated by every free ultrafilter limit, since
its cyclic subspace is strongly mixing. -/
theorem rudinShapiro_ultrafilterOperator_coordinate_zero (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (q : Ultrafilter (Multiplicative ℤ)) (hq : q ∈ freeUltrafilters (Multiplicative ℤ)) :
    ultrafilterOperator (rudinShapiroOrbitSystem p hp).koopmanRep q (rudinShapiroSignLp p hp) = 0 := by
  let U := (rudinShapiroOrbitSystem p hp).koopmanRep
  let x := rudinShapiroSignLp p hp
  have hDiag : Tendsto (fun g => ⟪x, U g x⟫_ℂ) cofinite (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(Set.finite_singleton (1 : Multiplicative ℤ)).compl_mem_cofinite] with g hg
    change g ≠ 1 at hg
    have hgz : g.toAdd ≠ 0 := fun he => hg (Multiplicative.ext he)
    have he := rudinShapiroSignLp_autocorrelation p hp g.toAdd
    rw [ofAdd_toAdd, ite_eq_right hgz] at he
    exact he.symm
  let W := cyclicClosedSubmodule U x
  let V := unitarySubmoduleAction U W.toSubmodule (cyclicClosedSubmodule_invariant U x)
  let : CompleteSpace W.toSubmodule := W.isClosed.completeSpace_coe
  let v : W.toSubmodule := ⟨x, mem_cyclicClosedSubmodule U x⟩
  have h := (isStronglyMixing_iff_isUMixing_free V).mp
    (isStronglyMixing_cyclicClosedSubmodule U x hDiag) q hq
  have he := (intertwines_unitarySubmoduleAction U W.toSubmodule
    (cyclicClosedSubmodule_invariant U x)).ultrafilter q v
  rw [h, zero_apply, map_zero] at he
  exact he.symm

/-- The explicit one-half rigid Rudin–Shapiro model realizes the sharp endpoint
in Proposition 7(i): its corresponding Koopman limit has a nonzero kernel. -/
theorem rudinShapiro_half_rigid_noninjective (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    ∃ q ∈ freeUltrafilters (Multiplicative ℤ),
      (rudinShapiroOrbitSystem p hp).IsPartiallyRigidAlong q (1/2) ∧
        ¬ Function.Injective (ultrafilterOperator (rudinShapiroOrbitSystem p hp).koopmanRep q) := by
  obtain ⟨q, hq, hr⟩ := rudinShapiro_half_rigid p hp
  refine ⟨q, hq, hr, fun hi => rudinShapiro_coordinate_ne_zero p hp (hi ?_)⟩
  rw [rudinShapiro_ultrafilterOperator_coordinate_zero p hp q hq, map_zero]

/-- No larger coefficient can satisfy partial rigidity along any free ultrafilter
for the measured Rudin–Shapiro model. -/
theorem rudinShapiro_rigidity_coefficient_le_half (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (q : Ultrafilter (Multiplicative ℤ)) (hq : q ∈ freeUltrafilters (Multiplicative ℤ))
    {α : ℝ} (hα : (rudinShapiroOrbitSystem p hp).IsPartiallyRigidAlong q α) : α ≤ 1/2 := by
  by_contra! h
  have hInjective := proposition7_i (rudinShapiroOrbitSystem p hp) q h hα
  apply rudinShapiro_coordinate_ne_zero p hp
  apply hInjective
  rw [rudinShapiro_ultrafilterOperator_coordinate_zero p hp q hq, map_zero]

end Mixing
