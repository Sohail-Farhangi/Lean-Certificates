/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Intertwining and quotient representations

A surjective Banach-space intertwiner induces a continuous surjective map on
the weak operator closures of the two represented semigroups. Pushing the
group ideal across that map gives the intertwining and summand formulas.
-/

@[expose] public section

namespace JdLG

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The projection determined by the unique minimal idempotent of the operator closure. -/
noncomputable def admissibleProjection {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) : E →L[𝕜] E := closureAction π hπ.2.exists.choose

theorem GroupIdeal.projection_eq_admissibleProjection {π : S →ₙ* (E →L[𝕜] E)}
    (K : GroupIdeal (weakOperatorClosure π)) (hπ : IsJdLGAdmissible π) :
    K.projection (closureAction π) = admissibleProjection hπ :=
  congrArg (closureAction π)
    (K.eq_identity_of_isMinimalIdempotent hπ.2.exists.choose_spec).symm

section Surjective

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [SeparatingDual 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

variable {π : S →ₙ* (E →L[𝕜] E)} {τ : S →ₙ* (F →L[𝕜] F)}
  {f : E →L[𝕜] F} (hfSurj : Function.Surjective f)
  (hf : ∀ s x, τ s (f x) = f (π s x))

omit [CompleteSpace E] [CompleteSpace F] in
include hf in
private theorem ker_le_comp_on_closure (a : weakOperatorClosure π) :
    LinearMap.ker f.toLinearMap ≤ LinearMap.ker (f.comp (closureAction π a)).toLinearMap := by
  intro x hx
  have hx' : f x = 0 := hx
  change f (closureAction π a x) = 0
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr
  intro y
  have hclosed : IsClosed {u : E →WOT[𝕜] E | y (f (u x)) = y 0} :=
    isClosed_eq (ContinuousLinearMapWOT.continuous_dual_apply x (y.comp f)) continuous_const
  have hsubset : Set.range (weakRepresentation π) ⊆ {u | y (f (u x)) = y 0} := by
    rintro _ ⟨s, rfl⟩
    change y (f (π s x)) = y 0
    rw [← hf s x, hx', map_zero]
  have hmem := closure_minimal hsubset hclosed a.2
  exact hmem

private noncomputable def quotientOperator (u : E →L[𝕜] E)
    (hu : LinearMap.ker f.toLinearMap ≤ LinearMap.ker (f.comp u).toLinearMap) : F →L[𝕜] F where
  toLinearMap := (f.toLinearMap.liftOfSurjective hfSurj) ⟨(f.comp u).toLinearMap, hu⟩
  cont := by
    apply (f.isQuotientMap hfSurj).continuous_iff.mpr
    convert (f.comp u).continuous using 1
    funext x
    exact LinearMap.equivOfSurjective_apply hfSurj hu

omit [SeparatingDual 𝕜 F] in
private theorem quotientOperator_apply (u : E →L[𝕜] E)
    (hu : LinearMap.ker f.toLinearMap ≤ LinearMap.ker (f.comp u).toLinearMap) (x : E) :
    quotientOperator hfSurj u hu (f x) = f (u x) :=
  LinearMap.equivOfSurjective_apply hfSurj hu

private noncomputable def quotientAction : (weakOperatorClosure π) →ₙ* (F →L[𝕜] F) := by
  let descend (a : weakOperatorClosure π) : F →L[𝕜] F :=
    quotientOperator hfSurj (closureAction π a) (ker_le_comp_on_closure hf a)
  have hDescend (a : weakOperatorClosure π) (x : E) :
      descend a (f x) = f (closureAction π a x) := quotientOperator_apply hfSurj _ _ x
  refine ⟨descend, fun a b => ?_⟩
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hfSurj y
  change descend (a * b) (f x) = descend a (descend b (f x))
  rw [hDescend (a * b) x, hDescend b x, hDescend a, map_mul]
  rfl

private theorem quotientAction_apply (a : weakOperatorClosure π) (x : E) :
    quotientAction hfSurj hf a (f x) = f (closureAction π a x) :=
  quotientOperator_apply hfSurj _ _ x

private theorem quotientAction_on_original (s : S) :
    quotientAction hfSurj hf (closureInclusion π s) = τ s := by
  ext y
  obtain ⟨x, rfl⟩ := hfSurj y
  rw [quotientAction_apply, closureAction_inclusion, hf]

private theorem continuous_weak_quotientAction :
    Continuous (weakRepresentation (quotientAction hfSurj hf)) := by
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro z y
  obtain ⟨x, rfl⟩ := hfSurj z
  change Continuous fun a => y (quotientAction hfSurj hf a (f x))
  simp only [quotientAction_apply]
  exact (ContinuousLinearMapWOT.continuous_dual_apply x (y.comp f)).comp continuous_subtype_val

private theorem range_weak_quotientAction
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :
    Set.range (weakRepresentation (quotientAction hfSurj hf)) =
      (weakOperatorClosure τ : Set (F →WOT[𝕜] F)) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hcompact
  let g := weakRepresentation (quotientAction hfSurj hf)
  have hcont : Continuous g := continuous_weak_quotientAction hfSurj hf
  have hOriginal : g '' Set.range (closureInclusion π) = Set.range (weakRepresentation τ) := by
    rw [← Set.range_comp]
    congr 1
    funext s
    change ContinuousLinearMapWOT.ofCLM (quotientAction hfSurj hf (closureInclusion π s)) =
      ContinuousLinearMapWOT.ofCLM (τ s)
    rw [quotientAction_on_original]
  change Set.range g = closure (Set.range (weakRepresentation τ))
  apply le_antisymm
  · rw [← hOriginal]
    exact hcont.range_subset_closure_image_dense (denseRange_closureInclusion π)
  · apply closure_minimal _ (isCompact_range hcont).isClosed
    rw [← hOriginal]
    exact Set.image_subset_range _ _

include hfSurj hf in
/-- Equation (3) of the paper. A surjective Banach-space intertwiner induces a continuous,
surjective semigroup homomorphism of weak operator closures. -/
theorem exists_closure_quotient_map
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :
    ∃ φ : (weakOperatorClosure π) →ₙ* weakOperatorClosure τ,
      Continuous φ ∧ Function.Surjective φ ∧
      ∀ a x, closureAction τ (φ a) (f x) = f (closureAction π a x) := by
  let g := weakRepresentation (quotientAction hfSurj hf)
  have hRange := range_weak_quotientAction hfSurj hf hcompact
  let φ := g.codRestrict (weakOperatorClosure τ) fun a => by
    change g a ∈ (weakOperatorClosure τ : Set (F →WOT[𝕜] F))
    rw [← hRange]
    exact ⟨a, rfl⟩
  refine ⟨φ, (continuous_weak_quotientAction hfSurj hf).subtype_mk _, ?_, ?_⟩
  · intro a
    obtain ⟨b, hb⟩ : a.1 ∈ Set.range g := hRange.symm ▸ a.2
    exact ⟨b, Subtype.ext hb⟩
  · exact quotientAction_apply hfSurj hf

include hfSurj hf in
/-- Theorem 2.3(ii). An onto Banach-space intertwiner preserves admissibility, intertwines
the JdLG projections and maps each summand onto its counterpart. -/
theorem admissible_quotient_and_proj {K : GroupIdeal (weakOperatorClosure π)}
    (hK : IsCompact K.carrier)
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :
    IsJdLGAdmissible τ ∧
      ∃ L : GroupIdeal (weakOperatorClosure τ), IsCompact L.carrier ∧
        (∀ x, L.projection (closureAction τ) (f x) = f (K.projection (closureAction π) x)) ∧
        (LinearMap.range (K.projection (closureAction π)).toLinearMap).map f.toLinearMap =
          LinearMap.range (L.projection (closureAction τ)).toLinearMap ∧
        (LinearMap.ker (K.projection (closureAction π)).toLinearMap).map f.toLinearMap =
          LinearMap.ker (L.projection (closureAction τ)).toLinearMap := by
  obtain ⟨φ, hφcont, hφsurj, hφ⟩ := exists_closure_quotient_map hfSurj hf hcompact
  let L := K.map φ hφsurj
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hcompact
  have hcompact' : IsCompact (weakOperatorClosure τ : Set (F →WOT[𝕜] F)) := by
    have hEq : Set.range (fun a => (φ a : F →WOT[𝕜] F)) =
        (weakOperatorClosure τ : Set (F →WOT[𝕜] F)) := by
      ext u
      constructor
      · rintro ⟨a, rfl⟩
        exact (φ a).2
      · intro hu
        obtain ⟨a, ha⟩ := hφsurj ⟨u, hu⟩
        exact ⟨a, congrArg Subtype.val ha⟩
    rw [← hEq]
    exact isCompact_range (continuous_subtype_val.comp hφcont)
  have hL : IsCompact L.carrier := hK.image hφcont
  have hτ : IsJdLGAdmissible τ := ⟨hcompact', L.identity, L.isMinimalIdempotent_identity,
    fun _ h => L.eq_identity_of_isMinimalIdempotent h⟩
  exact ⟨hτ, L, hL, K.projection_intertwines _ φ hφsurj _ f hφ,
    K.projection_range_kernel_map _ φ hφsurj _ f hfSurj hφ⟩

include hfSurj hf in
/-- Theorem 2.3(ii) in terms of the canonical projections of admissible representations. -/
theorem admissible_surjective_intertwiner [SeparatingDual 𝕜 E] (hπ : IsJdLGAdmissible π) :
    ∃ hτ : IsJdLGAdmissible τ,
      (∀ x, admissibleProjection hτ (f x) = f (admissibleProjection hπ x)) ∧
      (LinearMap.range (admissibleProjection hπ).toLinearMap).map f.toLinearMap =
        LinearMap.range (admissibleProjection hτ).toLinearMap ∧
      (LinearMap.ker (admissibleProjection hπ).toLinearMap).map f.toLinearMap =
        LinearMap.ker (admissibleProjection hτ).toLinearMap := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  obtain ⟨hτ, L, _, hP, hRange, hKer⟩ := admissible_quotient_and_proj hfSurj hf hK hπ.1
  rw [K.projection_eq_admissibleProjection hπ,
    L.projection_eq_admissibleProjection hτ] at hP hRange hKer
  exact ⟨hτ, hP, hRange, hKer⟩

end Surjective

section InvariantSubspace

variable (Y : Submodule 𝕜 E) (π : S →ₙ* (E →L[𝕜] E))
  (hY : ∀ s : S, ∀ x ∈ Y, π s x ∈ Y)

/-- The induced representation on the Banach quotient by a closed invariant subspace. -/
def quotientRepresentation : S →ₙ* ((E ⧸ Y) →L[𝕜] (E ⧸ Y)) := by
  let descend (s : S) : (E ⧸ Y) →L[𝕜] (E ⧸ Y) := Y.liftQL (Y.mkQL.comp (π s)) (by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero Y).mpr (hY s x hx))
  have hDescend (s : S) (x : E) : descend s (Y.mkQL x) = Y.mkQL (π s x) := rfl
  refine ⟨descend, fun a b => ?_⟩
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := Y.mkQ_surjective y
  change descend (a * b) (Y.mkQL x) = descend a (descend b (Y.mkQL x))
  rw [hDescend (a * b) x, hDescend b x, hDescend a, map_mul]
  rfl

theorem quotientRepresentation_mkQL (s : S) (x : E) :
    quotientRepresentation Y π hY s (Y.mkQL x) = Y.mkQL (π s x) := rfl

variable [IsClosed (Y : Set E)]

/-- Theorem 2.3(iii). On the quotient, the reversible and stable summands are the images of
the original summands and the new projection is induced by the original projection. -/
theorem admissible_quotient_representation [CompleteSpace E] [SeparatingDual 𝕜 E]
    [SeparatingDual 𝕜 (E ⧸ Y)] (hπ : IsJdLGAdmissible π) :
    ∃ hQ : IsJdLGAdmissible (quotientRepresentation Y π hY),
      (∀ x, admissibleProjection hQ (Y.mkQL x) = Y.mkQL (admissibleProjection hπ x)) ∧
      (LinearMap.range (admissibleProjection hπ).toLinearMap).map Y.mkQ =
        LinearMap.range (admissibleProjection hQ).toLinearMap ∧
      (LinearMap.ker (admissibleProjection hπ).toLinearMap).map Y.mkQ =
        LinearMap.ker (admissibleProjection hQ).toLinearMap :=
  admissible_surjective_intertwiner (f := Y.mkQL) Y.mkQ_surjective
    (quotientRepresentation_mkQL Y π hY) hπ

end InvariantSubspace

end JdLG
