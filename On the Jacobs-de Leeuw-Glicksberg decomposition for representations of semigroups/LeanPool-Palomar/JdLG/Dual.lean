/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The adjoint decomposition

Theorem 2.3(iv) follows by comparing the primal and adjoint weak operator closures and by
computing the range and kernel of the adjoint of the decomposition projection.
-/

@[expose] public section

open Set

namespace JdLG

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The Banach adjoint of an endomorphism, acting on the continuous dual. -/
noncomputable def banachAdjoint (A : E →L[𝕜] E) : StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E :=
  (ContinuousLinearMap.compL 𝕜 E E 𝕜).flip A

@[simp] theorem banachAdjoint_apply (A : E →L[𝕜] E) (f : StrongDual 𝕜 E) (x : E) :
    banachAdjoint A f x = f (A x) := rfl

theorem banachAdjoint_mul (A B : E →L[𝕜] E) :
    banachAdjoint (A * B) = banachAdjoint B * banachAdjoint A := by
  ext f x
  rfl

/-- The continuous functionals that vanish on the given set. -/
def continuousAnnihilator (A : Set E) : Set (StrongDual 𝕜 E) :=
  {f | ∀ x ∈ A, f x = 0}

theorem ker_banachAdjoint_eq_annihilator_range (A : E →L[𝕜] E) :
    ((banachAdjoint A).ker : Set (StrongDual 𝕜 E)) =
      continuousAnnihilator (A.range : Set E) := by
  ext f
  constructor
  · intro hf x hx
    obtain ⟨y, rfl⟩ := hx
    exact DFunLike.congr_fun hf y
  · intro hf
    change banachAdjoint A f = 0
    ext x
    exact hf (A x) ⟨x, rfl⟩

theorem range_banachAdjoint_eq_annihilator_ker (P : E →L[𝕜] E)
    (hP : ∀ x : E, P (P x) = P x) :
    ((banachAdjoint P).range : Set (StrongDual 𝕜 E)) =
      continuousAnnihilator (P.ker : Set E) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩ x hx
    change g (P x) = 0
    rw [show P x = 0 from hx, map_zero]
  · intro hf
    refine ⟨f, ?_⟩
    ext x
    have hker : x - P x ∈ P.ker := by
      change P (x - P x) = 0
      rw [map_sub, hP, sub_self]
    change f (P x) = f x
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hf _ hker)).symm

variable {S : Type*} [Semigroup S]

/-- The adjoint is a representation of the opposite semigroup. -/
noncomputable def adjointRepresentation (π : S →ₙ* (E →L[𝕜] E)) :
    Sᵐᵒᵖ →ₙ* (StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E) where
  toFun s := banachAdjoint (π s.unop)
  map_mul' a b := by
    change banachAdjoint (π (b.unop * a.unop)) = _
    rw [map_mul, banachAdjoint_mul]

/-- A compact closure of paired points still projects onto each factor when the original
pair has dense first coordinate. -/
theorem fst_image_closure_range_eq_univ {A B I : Type*}
    [TopologicalSpace A] [T2Space A] [CompactSpace A]
    [TopologicalSpace B] [CompactSpace B]
    (p : I → A × B) (hp : DenseRange (Prod.fst ∘ p)) :
    Prod.fst '' closure (range p) = univ := by
  have hclosed : IsClosed (Prod.fst '' closure (range p)) :=
    (isClosed_closure.isCompact.image continuous_fst).isClosed
  apply Set.eq_univ_of_univ_subset
  rw [← hp.closure_range]
  apply closure_minimal _ hclosed
  rintro _ ⟨i, rfl⟩
  exact ⟨p i, subset_closure ⟨i, rfl⟩, rfl⟩

/-- The corresponding statement for the second coordinate. -/
theorem snd_image_closure_range_eq_univ {A B I : Type*}
    [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [T2Space B] [CompactSpace B]
    (p : I → A × B) (hp : DenseRange (Prod.snd ∘ p)) :
    Prod.snd '' closure (range p) = univ := by
  have hclosed : IsClosed (Prod.snd '' closure (range p)) :=
    (isClosed_closure.isCompact.image continuous_snd).isClosed
  apply Set.eq_univ_of_univ_subset
  rw [← hp.closure_range]
  apply closure_minimal _ hclosed
  rintro _ ⟨i, rfl⟩
  exact ⟨p i, subset_closure ⟨i, rfl⟩, rfl⟩

variable [SeparatingDual 𝕜 E] [SeparatingDual 𝕜 (StrongDual 𝕜 E)]

/-- The adjoint relation extends from represented operators to both weak operator closures.
Compactness of the closure of paired points gives surjectivity onto each closure. -/
theorem exists_adjointClosureHom (π : S →ₙ* (E →L[𝕜] E))
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E)))
    (hdual : IsCompact (weakOperatorClosure (adjointRepresentation π) :
      Set (StrongDual 𝕜 E →WOT[𝕜] StrongDual 𝕜 E))) :
    ∃ φ : (weakOperatorClosure π)ᵐᵒᵖ →ₙ* weakOperatorClosure (adjointRepresentation π),
      Function.Surjective φ ∧ ∀ a : weakOperatorClosure π,
        closureAction (adjointRepresentation π) (φ (MulOpposite.op a)) =
          banachAdjoint (closureAction π a) := by
  let A := weakOperatorClosure π
  let B := weakOperatorClosure (adjointRepresentation π)
  let : CompactSpace A := isCompact_iff_compactSpace.mp hcompact
  let : CompactSpace B := isCompact_iff_compactSpace.mp hdual
  let p : S → A × B := fun s =>
    (closureInclusion π s, closureInclusion (adjointRepresentation π) (MulOpposite.op s))
  have hfst := fst_image_closure_range_eq_univ p (denseRange_closureInclusion π)
  have hsnd := snd_image_closure_range_eq_univ p (by
    intro b
    apply closure_mono _ (denseRange_closureInclusion (adjointRepresentation π) b)
    rintro _ ⟨s, rfl⟩
    exact ⟨s.unop, rfl⟩)
  have hrelation {a : A} {b : B} (hab : (a, b) ∈ closure (range p)) :
      closureAction (adjointRepresentation π) b = banachAdjoint (closureAction π a) := by
    ext f x
    have hfirst : Continuous (fun q : A × B => f (closureAction π q.1 x)) :=
      ((ContinuousLinearMapWOT.continuous_dual_apply x f).comp continuous_subtype_val).comp
        continuous_fst
    have hsecond : Continuous (fun q : A × B =>
        (closureAction (adjointRepresentation π) q.2 f) x) :=
      ((ContinuousLinearMapWOT.continuous_dual_apply f
        (NormedSpace.inclusionInDoubleDual 𝕜 E x)).comp continuous_subtype_val).comp continuous_snd
    exact closure_minimal (by rintro _ ⟨s, rfl⟩; rfl) (isClosed_eq hsecond hfirst) hab
  have hchoice (a : A) : ∃ b : B,
      closureAction (adjointRepresentation π) b = banachAdjoint (closureAction π a) := by
    have ha : a ∈ Prod.fst '' closure (range p) := hfst ▸ mem_univ a
    obtain ⟨⟨a', b⟩, hab, rfl⟩ := ha
    exact ⟨b, hrelation hab⟩
  choose b hb using hchoice
  have hinjective : Function.Injective (closureAction (adjointRepresentation π)) :=
    fun _ _ h => Subtype.ext (ContinuousLinearMapWOT.ringEquiv.injective h)
  let φ : Aᵐᵒᵖ →ₙ* B :=
    { toFun := fun a => b a.unop
      map_mul' := fun a a' => by
        apply hinjective
        rw [map_mul, hb, hb, hb, MulOpposite.unop_mul, map_mul, banachAdjoint_mul] }
  refine ⟨φ, ?_, hb⟩
  intro b'
  have hmem : b' ∈ Prod.snd '' closure (range p) := hsnd ▸ mem_univ b'
  obtain ⟨⟨a, b''⟩, hab, rfl⟩ := hmem
  refine ⟨MulOpposite.op a, hinjective ?_⟩
  exact (hb a).trans (hrelation hab).symm

/-- The opposite of a group ideal is a group ideal in the opposite semigroup. -/
def GroupIdeal.opposite {M : Type*} [Semigroup M] (K : GroupIdeal M) : GroupIdeal Mᵐᵒᵖ where
  carrier := MulOpposite.unop ⁻¹' K.carrier
  identity := MulOpposite.op K.identity
  identity_mem := K.identity_mem
  mul_mem_left a := fun {_b} hb => K.mul_mem_right hb a.unop
  mul_mem_right := fun {_a} ha b => K.mul_mem_left b.unop ha
  identity_mul := fun {_a} ha => congrArg MulOpposite.op (K.mul_identity ha)
  mul_identity := fun {_a} ha => congrArg MulOpposite.op (K.identity_mul ha)
  inverse_exists := fun {a} ha => by
    obtain ⟨b, hb, hba, hab⟩ := K.inverse_exists (a := a.unop) ha
    exact ⟨MulOpposite.op b, hb, congrArg MulOpposite.op hab, congrArg MulOpposite.op hba⟩

/-- Theorem 2.3(iv), with the stable and reversible summands given by the kernel and range
of the corresponding group-ideal projections. -/
theorem decomposition_adjoint_of_admissible (π : S →ₙ* (E →L[𝕜] E))
    (hπ : IsJdLGAdmissible π)
    (hdual : IsCompact (weakOperatorClosure (adjointRepresentation π) :
      Set (StrongDual 𝕜 E →WOT[𝕜] StrongDual 𝕜 E))) :
    IsJdLGAdmissible (adjointRepresentation π) ∧
      ∃ (K : GroupIdeal (weakOperatorClosure π))
        (K' : GroupIdeal (weakOperatorClosure (adjointRepresentation π))),
        K'.projection (closureAction (adjointRepresentation π)) =
          banachAdjoint (K.projection (closureAction π)) ∧
        (∀ f : StrongDual 𝕜 E,
          IsReversible (closureAction (adjointRepresentation π)) f ↔
            f ∈ continuousAnnihilator ((K.projection (closureAction π)).ker : Set E)) ∧
        (∀ f : StrongDual 𝕜 E,
          IsAlmostWeaklyStable (closureAction (adjointRepresentation π)) f ↔
            f ∈ continuousAnnihilator ((K.projection (closureAction π)).range : Set E)) := by
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  obtain ⟨φ, hφ, hAdj⟩ := exists_adjointClosureHom π hπ.1 hdual
  let K' := K.opposite.map φ hφ
  have hprojection : K'.projection (closureAction (adjointRepresentation π)) =
      banachAdjoint (K.projection (closureAction π)) := by
    simpa only [K', GroupIdeal.projection, GroupIdeal.map, GroupIdeal.opposite]
      using hAdj K.identity
  refine ⟨⟨hdual, K'.identity, K'.isMinimalIdempotent_identity, fun _ h =>
      K'.eq_identity_of_isMinimalIdempotent h⟩, K, K', hprojection, ?_, ?_⟩
  · intro f
    rw [K'.reversible_iff_mem_range, hprojection]
    exact Iff.of_eq (congrArg (fun A : Set (StrongDual 𝕜 E) => f ∈ A)
      (range_banachAdjoint_eq_annihilator_ker _ (K.projection_apply_apply _)))
  · intro f
    rw [K'.stable_iff_mem_ker, hprojection]
    exact Iff.of_eq (congrArg (fun A : Set (StrongDual 𝕜 E) => f ∈ A)
      (ker_banachAdjoint_eq_annihilator_range _))

end JdLG
