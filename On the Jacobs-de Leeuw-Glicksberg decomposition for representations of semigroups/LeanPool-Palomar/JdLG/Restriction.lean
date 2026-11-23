/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Quotient
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Restriction to closed invariant subspaces

Hahn–Banach ensures continuity of the restriction map for the two weak
operator topologies. The image of the compact operator closure is exactly the
operator closure of the restricted representation.
-/

@[expose] public section

namespace JdLG

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Restriction of a semigroup representation to an invariant subspace. -/
def restrictedRepresentation (Y : Submodule 𝕜 E) (π : S →ₙ* (E →L[𝕜] E))
    (hY : ∀ s : S, ∀ x ∈ Y, π s x ∈ Y) : S →ₙ* (Y →L[𝕜] Y) where
  toFun s := (π s).restrict (hY s)
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change π (a * b) x = (π a * π b) x
    rw [map_mul]

variable (Y : Submodule 𝕜 E) [IsClosed (Y : Set E)] {π : S →ₙ* (E →L[𝕜] E)}
  (hY : ∀ s : S, ∀ x ∈ Y, π s x ∈ Y)

include hY in
private theorem invariant_on_weakOperatorClosure (a : weakOperatorClosure π) (x : E)
    (hx : x ∈ Y) : closureAction π a x ∈ Y := by
  apply (Submodule.Quotient.mk_eq_zero Y).mp
  change Y.mkQL (closureAction π a x) = 0
  apply (SeparatingDual.eq_zero_iff_forall_dual_eq_zero (R := 𝕜) _).mpr
  intro y
  have hclosed : IsClosed {u : E →WOT[𝕜] E | y (Y.mkQL (u x)) = 0} :=
    isClosed_eq (ContinuousLinearMapWOT.continuous_dual_apply x (y.comp Y.mkQL)) continuous_const
  have hsubset : Set.range (weakRepresentation π) ⊆ {u | y (Y.mkQL (u x)) = 0} := by
    rintro _ ⟨s, rfl⟩
    change y (Submodule.Quotient.mk (π s x)) = 0
    rw [(Submodule.Quotient.mk_eq_zero Y).mpr (hY s x hx), map_zero]
  exact closure_minimal hsubset hclosed a.2

private def restrictionOfClosure : weakOperatorClosure π →ₙ* (Y →L[𝕜] Y) :=
  restrictedRepresentation Y (closureAction π) (invariant_on_weakOperatorClosure Y hY)

private theorem continuous_weak_restrictionOfClosure :
    Continuous (weakRepresentation (restrictionOfClosure Y hY)) := by
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro x y
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq Y y
  have hEq : (fun a => y (weakRepresentation (restrictionOfClosure Y hY) a x)) =
      (fun a : weakOperatorClosure π => g (a.1 x)) := by
    funext a
    exact (hg (restrictionOfClosure Y hY a x)).symm
  rw [hEq]
  exact (ContinuousLinearMapWOT.continuous_dual_apply x.1 g).comp continuous_subtype_val

/-- The weak operator closure maps continuously and surjectively to the operator closure
of the restricted representation. -/
theorem exists_closure_restriction_map
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :
    ∃ φ : (weakOperatorClosure π) →ₙ* weakOperatorClosure (restrictedRepresentation Y π hY),
      Continuous φ ∧ Function.Surjective φ ∧
      ∀ a x, (closureAction (restrictedRepresentation Y π hY) (φ a) x : E) =
        closureAction π a x := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hcompact
  let g := weakRepresentation (restrictionOfClosure Y hY)
  have hcont : Continuous g := continuous_weak_restrictionOfClosure Y hY
  have hOriginal : g '' Set.range (closureInclusion π) =
      Set.range (weakRepresentation (restrictedRepresentation Y π hY)) := by
    rw [← Set.range_comp]
    rfl
  have hRange : Set.range g =
      (weakOperatorClosure (restrictedRepresentation Y π hY) : Set (Y →WOT[𝕜] Y)) := by
    change Set.range g = closure (Set.range (weakRepresentation (restrictedRepresentation Y π hY)))
    apply le_antisymm
    · rw [← hOriginal]
      exact hcont.range_subset_closure_image_dense (denseRange_closureInclusion π)
    · apply closure_minimal _ (isCompact_range hcont).isClosed
      rw [← hOriginal]
      exact Set.image_subset_range _ _
  let φ := g.codRestrict (weakOperatorClosure (restrictedRepresentation Y π hY)) fun a => by
    change g a ∈ (weakOperatorClosure (restrictedRepresentation Y π hY) : Set (Y →WOT[𝕜] Y))
    rw [← hRange]
    exact ⟨a, rfl⟩
  refine ⟨φ, hcont.subtype_mk _, ?_, fun _ _ => rfl⟩
  intro a
  obtain ⟨b, hb⟩ : a.1 ∈ Set.range g := hRange.symm ▸ a.2
  exact ⟨b, Subtype.ext hb⟩

/-- Theorem 2.3(i). An invariant closed subspace inherits admissibility, its projection is
the restriction of the ambient projection, and both summands are intersections. -/
theorem admissible_restriction (hπ : IsJdLGAdmissible π) :
    ∃ hρ : IsJdLGAdmissible (restrictedRepresentation Y π hY),
      (∀ x : Y, (admissibleProjection hρ x : E) = admissibleProjection hπ x) ∧
      (∀ x : Y, IsReversible (closureAction (restrictedRepresentation Y π hY)) x ↔
        IsReversible (closureAction π) (x : E)) ∧
      ∀ x : Y, IsAlmostWeaklyStable (closureAction (restrictedRepresentation Y π hY)) x ↔
        IsAlmostWeaklyStable (closureAction π) (x : E) := by
  obtain ⟨φ, hφcont, hφsurj, hφ⟩ := exists_closure_restriction_map Y hY hπ.1
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  let L := K.map φ hφsurj
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  have hcompact : IsCompact
      (weakOperatorClosure (restrictedRepresentation Y π hY) : Set (Y →WOT[𝕜] Y)) := by
    have hEq : Set.range (fun a => (φ a : Y →WOT[𝕜] Y)) =
        (weakOperatorClosure (restrictedRepresentation Y π hY) : Set (Y →WOT[𝕜] Y)) := by
      ext u
      constructor
      · rintro ⟨a, rfl⟩
        exact (φ a).2
      · intro hu
        obtain ⟨a, ha⟩ := hφsurj ⟨u, hu⟩
        exact ⟨a, congrArg Subtype.val ha⟩
    rw [← hEq]
    exact isCompact_range (continuous_subtype_val.comp hφcont)
  have hρ : IsJdLGAdmissible (restrictedRepresentation Y π hY) :=
    ⟨hcompact, L.identity, L.isMinimalIdempotent_identity,
      fun _ h => L.eq_identity_of_isMinimalIdempotent h⟩
  have hProj (x : Y) : (L.projection (closureAction (restrictedRepresentation Y π hY)) x : E) =
      K.projection (closureAction π) x := hφ K.identity x
  refine ⟨hρ, ?_, ?_, ?_⟩
  · rw [← K.projection_eq_admissibleProjection hπ, ← L.projection_eq_admissibleProjection hρ]
    exact hProj
  · intro x
    rw [L.reversible_iff_fixed, K.reversible_iff_fixed, ← hProj]
    exact ⟨congrArg Subtype.val, Subtype.ext⟩
  · intro x
    rw [L.stable_iff_projection_eq_zero, K.stable_iff_projection_eq_zero, ← hProj]
    refine ⟨congrArg Subtype.val, fun h => ?_⟩
    apply Subtype.ext
    exact h

end JdLG
