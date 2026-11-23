/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleSubspace
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # The reversible operator closure and the minimal group ideal -/

@[expose] public section

open Set Topology

namespace JdLG

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {π : S →ₙ* (E →L[𝕜] E)} (K : GroupIdeal (weakOperatorClosure π))

/-- The compact group ideal acts on the reversible subspace by WOT operators. -/
noncomputable def GroupIdeal.reversibleWotAction :
    K.carrier →ₙ* (K.reversibleSubmodule →WOT[𝕜] K.reversibleSubmodule) :=
  (weakRepresentation K.reversibleGroupAction.toMulHom)

theorem GroupIdeal.continuous_reversibleWotAction (hK : IsCompact K.carrier) :
    Continuous K.reversibleWotAction :=
  ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x f ↦
    f.continuous.comp (K.continuous_reversibleGroupAction_apply hK x)

omit [CompleteSpace E] in
theorem GroupIdeal.injective_reversibleWotAction :
    Function.Injective K.reversibleWotAction := by
  intro a b hab
  have hab' : K.reversibleGroupAction a = K.reversibleGroupAction b :=
    ContinuousLinearMapWOT.ofCLM_injective hab
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMapWOT.toCLM_injective
  apply ContinuousLinearMap.ext
  intro x
  let P := K.projection (closureAction π)
  let y : K.reversibleSubmodule := ⟨P x,
    (K.mem_reversibleSubmodule _).2 (K.projection_apply_apply _ x)⟩
  have e := congrArg Subtype.val (DFunLike.congr_fun hab' y)
  have hPx (c : K.carrier) : K.operatorAction c (P x) = K.operatorAction c x := by
    change closureAction π c.1 (closureAction π K.identity x) = closureAction π c.1 x
    rw [← mul_apply_eq_comp, ← map_mul, K.mul_identity c.2]
  change K.operatorAction a (P x) = K.operatorAction b (P x) at e
  exact (hPx a).symm.trans (e.trans (hPx b))

/-- The restricted WOT closure consists exactly of restrictions of the group ideal. -/
theorem GroupIdeal.weakOperatorClosure_reversibleAction_eq_range (hK : IsCompact K.carrier) :
    (weakOperatorClosure K.reversibleAction :
      Set (K.reversibleSubmodule →WOT[𝕜] K.reversibleSubmodule)) =
        range K.reversibleWotAction := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  have hc := K.continuous_reversibleWotAction hK
  let r := K.groupRetraction.comp (closureInclusion π)
  have hr : DenseRange r :=
    K.groupRetraction_surjective.denseRange.comp (denseRange_closureInclusion π)
      ((continuous_const_mul K.identity).subtype_mk _)
  have hcomp : (weakRepresentation K.reversibleAction :
      S → (K.reversibleSubmodule →WOT[𝕜] K.reversibleSubmodule)) =
        K.reversibleWotAction ∘ r := by
    funext s
    exact congrArg ContinuousLinearMapWOT.ofCLM (DFunLike.congr_fun K.reversibleAction_eq_comp s)
  change closure (range (weakRepresentation K.reversibleAction)) = _
  rw [hcomp, range_comp]
  apply le_antisymm
  · apply closure_minimal _ (isCompact_range hc).isClosed
    rintro _ ⟨a, _, rfl⟩
    exact mem_range_self a
  · exact hc.range_subset_closure_image_dense hr

/-- The identification of the group ideal and the weak operator closure of the
reversible action, as a multiplicative homeomorphism. -/
noncomputable def GroupIdeal.reversibleWotEquiv (hK : IsCompact K.carrier) :
    K.carrier ≃ₜ* weakOperatorClosure K.reversibleAction := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let i : K.carrier →ₙ* weakOperatorClosure K.reversibleAction :=
    K.reversibleWotAction.codRestrict _ fun a ↦ by
      rw [← SetLike.mem_coe, K.weakOperatorClosure_reversibleAction_eq_range hK]
      exact mem_range_self a
  have hi : Continuous i := (K.continuous_reversibleWotAction hK).subtype_mk _
  have hinj : Function.Injective i :=
    fun a b e ↦ K.injective_reversibleWotAction (congrArg Subtype.val e)
  have hsurj : Function.Surjective i := by
    intro b
    have hb := b.2
    rw [← SetLike.mem_coe, K.weakOperatorClosure_reversibleAction_eq_range hK] at hb
    obtain ⟨a, ha⟩ := hb
    exact ⟨a, Subtype.ext ha⟩
  let e : K.carrier ≃* weakOperatorClosure K.reversibleAction :=
    MulEquiv.ofBijective i ⟨hinj, hsurj⟩
  have he : Continuous e := hi
  exact
    { toMulEquiv := e
      continuous_toFun := he
      continuous_invFun := he.continuous_symm_of_equiv_compact_to_t2 }

end JdLG
