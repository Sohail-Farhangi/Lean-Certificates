/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleTopology

/-! # The compact group action on the reversible subspace -/

@[expose] public section

open Set

namespace JdLG

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {π : S →ₙ* (E →L[𝕜] E)} (K : GroupIdeal (weakOperatorClosure π))

/-- The reversible subspace, given by the fixed vectors of the ideal projection. -/
def GroupIdeal.reversibleSubmodule : Submodule 𝕜 E :=
  ((K.projection (closureAction π) - 1 : E →L[𝕜] E).toLinearMap).ker

theorem GroupIdeal.mem_reversibleSubmodule (x : E) :
    x ∈ K.reversibleSubmodule ↔ K.projection (closureAction π) x = x := by
  change K.projection (closureAction π) x - x = 0 ↔ _
  exact sub_eq_zero

theorem GroupIdeal.reversibleSubmodule_eq_range :
    K.reversibleSubmodule = LinearMap.range (K.projection (closureAction π)).toLinearMap := by
  ext x
  exact (K.mem_reversibleSubmodule x).trans
    ((K.reversible_iff_fixed _ x).symm.trans (K.reversible_iff_mem_range _ x))

theorem GroupIdeal.isClosed_reversibleSubmodule : IsClosed (K.reversibleSubmodule : Set E) := by
  have h : (K.reversibleSubmodule : Set E) =
      {x | K.projection (closureAction π) x = x} := Set.ext K.mem_reversibleSubmodule
  rw [h]
  exact isClosed_eq (K.projection (closureAction π)).continuous continuous_id

instance [CompleteSpace E] : CompleteSpace K.reversibleSubmodule :=
  K.isClosed_reversibleSubmodule.completeSpace_coe

/-- The original semigroup action restricted to the reversible subspace. -/
def GroupIdeal.reversibleAction : S →ₙ* (K.reversibleSubmodule →L[𝕜] K.reversibleSubmodule) where
  toFun s := (π s).restrict fun {x} hx ↦
    (K.mem_reversibleSubmodule _).2 <|
      (K.projection_commutes (closureAction π) (closureInclusion π s) x).trans
      (congrArg (π s) ((K.mem_reversibleSubmodule x).1 hx))
  map_mul' s t := by
    ext x
    change π (s * t) (x : E) = π s (π t (x : E))
    rw [map_mul]
    rfl

/-- The compact group ideal acts by invertible operators on the reversible subspace. -/
noncomputable def GroupIdeal.reversibleGroupAction :
    K.carrier →* (K.reversibleSubmodule →L[𝕜] K.reversibleSubmodule) where
  toFun a := (K.operatorAction a).restrict fun {x} _ ↦
    (K.mem_reversibleSubmodule _).2 <| by
      change (closureAction π K.identity) ((closureAction π a.1) x) =
        (closureAction π a.1) x
      rw [← mul_apply_eq_comp, ← map_mul, K.identity_mul a.2]
  map_one' := by
    ext x
    exact (K.mem_reversibleSubmodule (x : E)).1 x.2
  map_mul' a b := by
    ext x
    change K.operatorAction (a * b) x = K.operatorAction a (K.operatorAction b x)
    rw [map_mul]
    rfl

theorem GroupIdeal.reversibleGroupAction_apply (a : K.carrier) (x : K.reversibleSubmodule) :
    (K.reversibleGroupAction a x : E) = K.operatorAction a x := rfl

theorem GroupIdeal.continuous_reversibleGroupAction_apply [CompleteSpace E]
    (hK : IsCompact K.carrier) (x : K.reversibleSubmodule) :
    Continuous fun a ↦ K.reversibleGroupAction a x :=
  (K.continuous_norm_eval hK (x : E)).subtype_mk _

/-- The reversible action factors through the compact group ideal via its retraction. -/
theorem GroupIdeal.reversibleAction_eq_comp :
    K.reversibleAction =
      K.reversibleGroupAction.toMulHom.comp (K.groupRetraction.comp (closureInclusion π)) := by
  ext s x
  change π s (x : E) = closureAction π (K.identity * closureInclusion π s) x
  rw [K.identity_mul_eq_mul_identity, map_mul, mul_apply_eq_comp]
  exact congrArg (π s) ((K.mem_reversibleSubmodule (x : E)).1 x.2).symm

end JdLG
