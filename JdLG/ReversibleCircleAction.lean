/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleCircle
public import JdLG.ReversibleAction

/-! # Reversibility of the circle rotation -/

@[expose] public section

open Set

namespace JdLG

/-- Translation by an arbitrary element of the period-one circle. -/
noncomputable def circleShift (a : UnitAddCircle) :
    C(UnitAddCircle, ℂ) →L[ℂ] C(UnitAddCircle, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ ⟨fun x ↦ x + a, continuous_id.add continuous_const⟩

theorem continuous_circleShift_apply (f : C(UnitAddCircle, ℂ)) :
    Continuous fun a ↦ circleShift a f := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_snd.add continuous_fst)

/-- The rotation representation in the circle example is JdLG-admissible and
its whole space of continuous functions is reversible. -/
theorem circleRotation_admissible_and_reversible (a : UnitAddCircle) :
    IsJdLGAdmissible (circleRotation a).toMulHom ∧
      ∀ f, IsReversible (closureAction (circleRotation a).toMulHom) f := by
  let A := circleRotation a
  let action : UnitAddCircle → (C(UnitAddCircle, ℂ) →WOT[ℂ] C(UnitAddCircle, ℂ)) :=
    fun z ↦ ContinuousLinearMapWOT.ofCLM (circleShift z)
  have hA : Continuous action :=
    ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun f l ↦
      l.continuous.comp (continuous_circleShift_apply f)
  have hsub' : range (weakRepresentation A.toMulHom) ⊆ range action := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n.toAdd • a, rfl⟩
  have hcompact : IsCompact
      (weakOperatorClosure A.toMulHom : Set (C(UnitAddCircle, ℂ) →WOT[ℂ] C(UnitAddCircle, ℂ))) := by
    apply (isCompact_range hA).of_isClosed_subset isClosed_closure
    exact closure_minimal hsub' (isCompact_range hA).isClosed
  have hadm : IsJdLGAdmissible A.toMulHom :=
    admissible_of_commutative hcompact fun m n ↦ by rw [← map_mul, ← map_mul, mul_comm m n]
  refine ⟨hadm, fun f ↦ (group_reversible_iff_precompactOrbit A hadm f).2 ?_⟩
  have hcompact' := isCompact_range (continuous_circleShift_apply f)
  apply hcompact'.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact'.isClosed
  rintro _ ⟨n, rfl⟩
  exact ⟨n.toAdd • a, rfl⟩

end JdLG
