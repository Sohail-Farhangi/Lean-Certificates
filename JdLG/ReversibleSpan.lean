/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleFiniteSystems
public import JdLG.ReversibleClosure

/-! # Finite unitary systems on the reversible subspace -/

@[expose] public section

open Set

namespace JdLG

section DenseRestriction

variable {S G 𝕜 E : Type*} [Semigroup S] [Group G] [TopologicalSpace G] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The irreducibility of a finite unitary system is preserved on restriction
to a dense represented subsemigroup, since its invariant subspaces are closed. -/
theorem SpannedByIrreducibleUnitarySystem.comp_of_denseRange
    {ρ : G →* (E →L[𝕜] E)} (hρ : ∀ x, Continuous fun g ↦ ρ g x)
    {W : Submodule 𝕜 E} (hW : SpannedByIrreducibleUnitarySystem ρ.toMulHom W)
    (i : S →ₙ* G) (hi : DenseRange i) :
    SpannedByIrreducibleUnitarySystem (ρ.toMulHom.comp i) W := by
  obtain ⟨hnz, ⟨n, U, J, hJ, hJW, hinter⟩, hirr⟩ := hW
  refine ⟨hnz, ⟨n, U.comp i, J, hJ, hJW, fun s ↦ hinter (i s)⟩, ?_⟩
  intro V hVW hV
  let : FiniteDimensional 𝕜 W := hJW ▸ inferInstanceAs (FiniteDimensional 𝕜 J.range)
  let : FiniteDimensional 𝕜 V :=
    FiniteDimensional.of_injective _ (Submodule.inclusion_injective hVW)
  apply hirr V hVW
  intro g x hx
  have hc : IsClosed ((fun t ↦ ρ t x) ⁻¹' (V : Set E)) :=
    V.isClosed_of_finiteDimensional.preimage (hρ x)
  have hs : range i ⊆ (fun t ↦ ρ t x) ⁻¹' (V : Set E) := by
    rintro _ ⟨s, rfl⟩
    exact hV s x hx
  exact closure_minimal hs hc (hi g)

end DenseRestriction

section Reversible

variable {S E : Type*} [Semigroup S] [NormedAddCommGroup E]
  [NormedSpace ℂ E] [CompleteSpace E] {π : S →ₙ* (E →L[ℂ] E)}
  (K : GroupIdeal (weakOperatorClosure π))

/-- The density assertion of equation (6) on the reversible subspace, for the
original semigroup action. The density uses its factorization through the
compact group ideal, where the Haar averaging proof applies. -/
theorem GroupIdeal.iSup_spannedByIrreducibleUnitarySystem_reversibleAction
    (hK : IsCompact K.carrier) :
    (⨆ W : {W : Submodule ℂ K.reversibleSubmodule //
      SpannedByIrreducibleUnitarySystem K.reversibleAction W}, W.1).topologicalClosure = ⊤ := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let i := K.groupRetraction.comp (closureInclusion π)
  have hi : DenseRange i :=
    K.groupRetraction_surjective.denseRange.comp (denseRange_closureInclusion π)
      ((continuous_const_mul K.identity).subtype_mk _)
  have hc := K.continuous_reversibleGroupAction_apply hK
  have hwot : Continuous fun g ↦ ContinuousLinearMapWOT.ofCLM (K.reversibleGroupAction g) :=
    ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x f ↦ f.continuous.comp (hc x)
  obtain ⟨C, _, hbound⟩ := exists_operatorBound_of_compact_wot _ hwot
  have htotal :=
    iSup_spannedByIrreducibleUnitarySystem_topologicalClosure_eq_top
      K.reversibleGroupAction hc C hbound
  apply top_unique
  rw [← htotal]
  apply Submodule.topologicalClosure_mono
  apply iSup_le
  intro W
  have hW := W.2.comp_of_denseRange hc i hi
  have he := congrArg (fun A ↦ SpannedByIrreducibleUnitarySystem A W.1)
    K.reversibleAction_eq_comp
  let J := {V : Submodule ℂ K.reversibleSubmodule |
    SpannedByIrreducibleUnitarySystem K.reversibleAction V}
  exact le_iSup (fun V : J ↦ V.1) ⟨W.1, he.mpr hW⟩

end Reversible

end JdLG
