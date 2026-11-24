/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mixing.SupportingJdLG.ReversibleOrbits
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # Reversible orbits and the group ideal of a weak operator closure -/

@[expose] public section

open Filter Set Topology

namespace Mixing.JdLGBridge

section GroupIdeal

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {π : S →ₙ* (E →L[𝕜] E)} (K : GroupIdeal (weakOperatorClosure π))

/-- The group ideal acts by its ambient norm-continuous linear operators. -/
noncomputable def GroupIdeal.operatorAction : K.carrier →ₙ* (E →L[𝕜] E) :=
  (closureAction π).comp ⟨Subtype.val, fun _ _ ↦ rfl⟩

theorem GroupIdeal.continuous_wot_operatorAction :
    Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (K.operatorAction a) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem GroupIdeal.isCompact_normOrbit [CompleteSpace E] (hK : IsCompact K.carrier)
    (x : E) : IsCompact (Set.range fun a ↦ K.operatorAction a x) := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : SeparatelyContinuousMul K.carrier := IsInducing.separatelyContinuousMul
    (⟨Subtype.val, fun _ _ ↦ rfl⟩ : K.carrier →ₙ* weakOperatorClosure π)
    (IsInducing.subtypeVal (t := K.carrier))
  exact isCompact_normOrbit_of_wot K.operatorAction K.continuous_wot_operatorAction x

/-- Every reversible vector has norm-precompact orbit. This proves the
forward implication in Theorem 3.1 without a separability hypothesis. -/
theorem precompactOrbit_of_reversible [CompleteSpace E] (hπ : IsJdLGAdmissible π) (x : E)
    (hx : IsReversible (closureAction π) x) : HasPrecompactOrbit π x := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  have hx' := (K.reversible_iff_fixed (closureAction π) x).1 hx
  have hsub : range (fun s ↦ π s x) ⊆ range (fun a ↦ K.operatorAction a x) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨K.groupRetraction (closureInclusion π s), ?_⟩
    change closureAction π (K.identity * closureInclusion π s) x = π s x
    rw [K.identity_mul_eq_mul_identity, map_mul]
    change closureAction π (closureInclusion π s) (K.projection (closureAction π) x) = π s x
    rw [hx']
    rfl
  have hcompact := K.isCompact_normOrbit hK x
  exact hcompact.of_isClosed_subset isClosed_closure (closure_minimal hsub hcompact.isClosed)

/-- The norm-precompact-orbit characterization under the separation hypothesis of
Theorem 3.1. -/
theorem reversible_iff_precompactOrbit_of_separated [CompleteSpace E]
    (hπ : IsJdLGAdmissible π)
    (hseparated : ∀ y : E, y ≠ 0 → HasPrecompactOrbit π y →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : S, δ ≤ ‖π s y‖) (x : E) :
    IsReversible (closureAction π) x ↔ HasPrecompactOrbit π x :=
  ⟨precompactOrbit_of_reversible hπ x, reversible_of_precompactOrbit_of_separated hπ hseparated x⟩

end GroupIdeal

section Representations

variable {G 𝕜 E : Type*} [Group G] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- Corollary 3.2. A unital group representation satisfies the norm-separation
hypothesis, since each operator has its represented inverse in the same
uniformly bounded family. -/
theorem group_reversible_iff_precompactOrbit (π : G →* (E →L[𝕜] E))
    (hπ : IsJdLGAdmissible π.toMulHom) (x : E) :
    IsReversible (closureAction π.toMulHom) x ↔ HasPrecompactOrbit π.toMulHom x := by
  apply reversible_iff_precompactOrbit_of_separated hπ
  let : CompactSpace (weakOperatorClosure π.toMulHom) := isCompact_iff_compactSpace.1 hπ.1
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot
    (fun a ↦ closureAction π.toMulHom a) continuous_subtype_val
  intro y hy _
  refine ⟨‖y‖ / C, div_pos (norm_pos_iff.2 hy) hC, ?_⟩
  intro g
  apply (div_le_iff₀ hC).2
  have hB : ‖π g⁻¹‖ ≤ C := hbound (closureInclusion π.toMulHom g⁻¹)
  have hnorm : ‖π g⁻¹ (π g y)‖ ≤ C * ‖π g y‖ := (π g⁻¹).le_of_opNorm_le hB _
  have hinv : π g⁻¹ (π g y) = y := by
    change (π g⁻¹ * π g) y = y
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hinv, mul_comm] at hnorm
  exact hnorm

end Representations

end Mixing.JdLGBridge
