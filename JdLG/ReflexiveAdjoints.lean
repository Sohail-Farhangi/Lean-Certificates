/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Dual

/-! # Weak compactness of the adjoint representation on a reflexive space -/

@[expose] public section

open NormedSpace Set

namespace JdLG

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Reflexivity makes the Banach adjoint continuous in the weak operator
topologies on the space and on its dual. -/
theorem continuous_wot_banachAdjoint_of_reflexive
    (hrefl : Function.Surjective (inclusionInDoubleDual 𝕜 E)) :
    Continuous (fun A : E →WOT[𝕜] E ↦
      ContinuousLinearMapWOT.ofCLM (banachAdjoint A.toCLM)) := by
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro f F
  obtain ⟨x, rfl⟩ := hrefl F
  exact ContinuousLinearMapWOT.continuous_dual_apply x f

/-- The adjoint WOT compactness premise in Theorem 2.3(iv) follows from the
primal WOT compactness premise on a reflexive Banach space. -/
theorem isCompact_weakOperatorClosure_adjoint_of_reflexive
    {S : Type*} [Semigroup S] (π : S →ₙ* (E →L[𝕜] E))
    (hrefl : Function.Surjective (inclusionInDoubleDual 𝕜 E))
    (hπ : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :
    IsCompact (weakOperatorClosure (adjointRepresentation π) :
      Set (StrongDual 𝕜 E →WOT[𝕜] StrongDual 𝕜 E)) := by
  let adj (A : E →WOT[𝕜] E) := ContinuousLinearMapWOT.ofCLM (banachAdjoint A.toCLM)
  have hc : IsCompact (adj '' (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :=
    hπ.image (continuous_wot_banachAdjoint_of_reflexive hrefl)
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨s, rfl⟩
  exact ⟨weakRepresentation π s.unop, subset_closure (mem_range_self s.unop), rfl⟩

end JdLG

