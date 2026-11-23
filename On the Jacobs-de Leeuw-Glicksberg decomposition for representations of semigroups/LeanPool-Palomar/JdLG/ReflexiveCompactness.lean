/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ContractiveCriterion
public import JdLG.ReversibleOrbits
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-! # Weak operator compactness on reflexive Banach spaces -/

@[expose] public section

open NormedSpace Set

namespace JdLG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isCompact_weakBall_of_reflexive
    (hE : Function.Surjective (inclusionInDoubleDual ℂ E)) (r : ℝ) :
    IsCompact {x : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm x‖ ≤ r} := by
  let j := inclusionInDoubleDualWeak ℂ E
  have hsurj : Function.Surjective j := by
    intro p
    obtain ⟨x, hx⟩ := hE (WeakDual.toStrongDual p)
    refine ⟨toWeakSpace ℂ E x, ?_⟩
    change (inclusionInDoubleDual ℂ E x).toWeakDual = p
    exact (congrArg StrongDual.toWeakDual hx).trans (WeakDual.toWeakDual_toStrongDual p)
  have hset : {x : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm x‖ ≤ r} =
      j ⁻¹' (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r) := by
    ext x
    change ‖(toWeakSpace ℂ E).symm x‖ ≤ r ↔
      WeakDual.toStrongDual (j x) ∈ Metric.closedBall (0 : StrongDual ℂ (StrongDual ℂ E)) r
    have h : ‖WeakDual.toStrongDual (j x)‖ = ‖(toWeakSpace ℂ E).symm x‖ :=
      (inclusionInDoubleDualLi ℂ).norm_map ((toWeakSpace ℂ E).symm x)
    rw [← h]
    exact (mem_closedBall_zero_iff (a := WeakDual.toStrongDual (j x)) (r := r)).symm
  rw [hset]
  exact (isEmbedding_inclusionInDoubleDualWeak ℂ E).isCompact_preimage'
    (WeakDual.isCompact_closedBall 0 r) (hsurj.range_eq ▸ Set.subset_univ _)

/-- The remark after Theorem 1.2. For a reflexive Banach space,
relative WOT compactness of an operator family is equivalent to uniform
operator-norm boundedness. Reflexivity is surjectivity of the canonical
double-dual map. -/
theorem isCompact_weakOperatorClosure_iff_uniformlyBounded_of_reflexive {S : Type*}
    [Semigroup S] [CompleteSpace E] (hE : Function.Surjective (inclusionInDoubleDual ℂ E))
    (π : S →ₙ* (E →L[ℂ] E)) :
    IsCompact (weakOperatorClosure π : Set (E →WOT[ℂ] E)) ↔ ∃ C : ℝ, ∀ s, ‖π s‖ ≤ C := by
  constructor
  · intro hk
    let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hk
    obtain ⟨C, _, hC⟩ := exists_operatorBound_of_compact_wot (closureAction π)
      continuous_subtype_val
    exact ⟨C, fun s ↦ hC (closureInclusion π s)⟩
  · rintro ⟨C, hC⟩
    let R := max 0 C
    have hk : IsCompact {a : E →WOT[ℂ] E | ‖a.toCLM‖ ≤ R} :=
      isCompact_wot_operatorBall_of_compact_vectorBalls R (le_max_left _ _)
        (isCompact_weakBall_of_reflexive hE)
    change IsCompact (closure (range (weakRepresentation π)))
    exact hk.of_isClosed_subset isClosed_closure (closure_minimal
      (by rintro _ ⟨s, rfl⟩; exact (hC s).trans (le_max_right _ _)) hk.isClosed)

/-- The contractive criterion with reflexivity supplying weak operator
compactness of the represented contractions. -/
theorem admissible_of_reflexive_strictConvex_contractions {S : Type*} [Semigroup S] [Nonempty S]
    [CompleteSpace E] [StrictConvexSpace ℝ E] [StrictConvexSpace ℝ (StrongDual ℂ E)]
    (hE : Function.Surjective (inclusionInDoubleDual ℂ E))
    (π : S →ₙ* (E →L[ℂ] E)) (hπ : ∀ s, ‖π s‖ ≤ 1) :
    IsJdLGAdmissible π :=
  admissible_of_strictConvex_contractions π
    ((isCompact_weakOperatorClosure_iff_uniformlyBounded_of_reflexive hE π).2 ⟨1, hπ⟩) hπ

end JdLG
