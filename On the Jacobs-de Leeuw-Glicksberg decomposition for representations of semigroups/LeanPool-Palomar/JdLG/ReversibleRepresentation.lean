/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleCoefficients
public import JdLG.ReversibleSubspace
public import JdLG.ReversibleHilbertSum

/-! # The reversible action as a direct sum of finite-dimensional unitary representations -/

@[expose] public section

open Set

namespace JdLG

universe u v

variable {S : Type u} {E : Type v} [Semigroup S] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [CompleteSpace E] {π : S →ₙ* (E →L[ℂ] E)}

/-- Theorem 3.6 and Theorem 1.5(i) in the Banach-space case. On the reversible
subspace, the original representation is weakly equivalent to a unitary action
that is a Hilbert direct sum of finite-dimensional invariant subspaces. -/
theorem reversible_weaklyEquivalent_unitary_hilbertSum (hπ : IsJdLGAdmissible π) :
    ∃ (K : GroupIdeal (weakOperatorClosure π)) (_ : IsCompact K.carrier)
      (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (U : S →ₙ* (H ≃ₗᵢ[ℂ] H)) (I : Set (Submodule ℂ H)),
      WeaklyEquivalent K.reversibleAction (unitaryAsLinearRep U) ∧
        (∀ V ∈ I, FiniteDimensional ℂ V ∧ ∀ s x, x ∈ V → U s x ∈ V) ∧
        IsHilbertSum ℂ (fun i : I ↦ i.1) (fun i ↦ i.1.subtypeₗᵢ) := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  have hc := K.continuous_reversibleGroupAction_apply hK
  have hwot : Continuous fun g ↦ ContinuousLinearMapWOT.ofCLM (K.reversibleGroupAction g) :=
    ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x f ↦ f.continuous.comp (hc x)
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot _ hwot
  obtain ⟨H, hH, U, hweak, hU⟩ :=
    weaklyEquivalent_unitary_of_compact_group K.reversibleGroupAction hc hC.le hbound
  let : CompleteSpace H := hH.completeSpace_coe
  obtain ⟨I, hI, hsum⟩ := exists_invariant_hilbertSum_of_compact_unitary U hU
  let i := K.groupRetraction.comp (closureInclusion π)
  refine ⟨K, hK, H, inferInstance, inferInstance, inferInstance, U.toMulHom.comp i, I,
    ?_, ?_, hsum⟩
  · change WeaklyEquivalent K.reversibleAction ((unitaryAsLinearRep U.toMulHom).comp i)
    have h := congrArg (fun A ↦ WeaklyEquivalent A ((unitaryAsLinearRep U.toMulHom).comp i))
      K.reversibleAction_eq_comp
    exact h.mpr (hweak.comp i)
  · exact fun V hV ↦ ⟨(hI V hV).1, fun s x hx ↦ (hI V hV).2 (i s) x hx⟩

end JdLG
