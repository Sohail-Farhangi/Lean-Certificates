/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesWapClosed
public import JdLG.ReversibleAction
public import JdLG.ReversibleTopology
public import JdLG.WeaklyAlmostPeriodic

/-!
# The right-translation decomposition of WAP on a monoid

Right translation is a weakly continuous, relatively weakly compact
representation on the complex WAP space. A bi-invariant mean gives its
Jacobs–de Leeuw–Glicksberg splitting. Point evaluations, obtained by
translating the evaluation at the unit, identify the stable summand with
the functions whose absolute value has mean zero.
-/

@[expose] public section

open MeasureTheory Set
open scoped BoundedContinuousFunction Topology

namespace JdLG.WapTranslation

variable (S : Type*) [Monoid S] [TopologicalSpace S] [SeparatelyContinuousMul S]

local notation "BC" => S →ᵇ ℂ

/-- Right translations of bounded continuous complex functions. -/
noncomputable def translation : S →ₙ* (BC →L[ℂ] BC) where
  toFun s := BoundedContinuousFunction.compContinuousCLM ℂ ℂ
    ⟨(· * s), continuous_mul_const s⟩
  map_mul' s t := by
    apply ContinuousLinearMap.ext
    intro f
    apply BoundedContinuousFunction.ext
    intro x
    change f (x * (s * t)) = f ((x * s) * t)
    rw [mul_assoc]

theorem translation_opNorm_le (s : S) : ‖translation S s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  exact (BoundedContinuousFunction.norm_compContinuous_le f
    (⟨(· * s), continuous_mul_const s⟩ : C(S, S))).trans_eq (one_mul _).symm

/-- The complex weakly almost periodic functions on the monoid. -/
noncomputable abbrev ComplexWap := wapVectorSubmodule (translation S)

instance : CompleteSpace (ComplexWap S) :=
  (isClosed_wapVectorSubmodule (translation S) (translation_opNorm_le S)).completeSpace_coe

/-- The restricted right-translation action on the WAP space. -/
noncomputable def action : S →ₙ* (ComplexWap S →L[ℂ] ComplexWap S) :=
  wapVectorRepresentation (translation S)

local notation "T" => weakOperatorClosure (action S)

instance : CompactSpace T := isCompact_iff_compactSpace.1
  (compact_weakOperatorClosure_wapVectorRepresentation (translation S) (translation_opNorm_le S))

instance : Nonempty T := ⟨closureInclusion (action S) 1⟩

noncomputable instance : MeasurableSpace T := borel T

instance : BorelSpace T := ⟨rfl⟩

/-- Evaluation at a fixed point of the monoid is a continuous linear functional. -/
noncomputable def evaluation (s : S) : StrongDual ℂ (ComplexWap S) :=
  (BoundedContinuousFunction.evalCLM ℂ s).comp (ComplexWap S).subtypeL

@[simp] theorem evaluation_apply (s : S) (f : ComplexWap S) : evaluation S s f = f.val s :=
  rfl

@[simp] theorem action_apply (s t : S) (f : ComplexWap S) :
    (action S s f).val t = f.val (t * s) := rfl

/-- The inclusion of the monoid into the compact weak operator closure of
its WAP translation action is continuous. -/
theorem continuous_closureInclusion : Continuous (closureInclusion (action S)) := by
  let e (a : T) (f : ComplexWap S) (s : S) :=
    evaluation S s (closureAction (action S) a f)
  have he : Continuous e := continuous_pi fun f ↦ continuous_pi fun s ↦
    continuous_closureAction_coefficient (action S) f (evaluation S s)
  have hi : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    apply ContinuousLinearMapWOT.toCLM_injective
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact BoundedContinuousFunction.ext fun s ↦ congrFun (congrFun hab f) s
  apply (he.isClosedEmbedding hi).isEmbedding.continuous_iff.2
  exact continuous_pi fun f ↦ continuous_pi fun s ↦ f.val.continuous.comp (continuous_const_mul s)

theorem admissible (m : WapBiInvariantMean (S := S)) : IsJdLGAdmissible (action S) :=
  admissible_of_WapBiInvariantMean (action S) (continuous_closureInclusion S) m

/-- The modulus of a complex WAP function, as a real WAP function. -/
noncomputable def absolute (f : ComplexWap S) : weaklyAlmostPeriodicSubmodule (S := S) :=
  wapPullback (closureInclusion (action S)) (continuous_closureInclusion S)
    ⟨fun a ↦ ‖evaluation S 1 (closureAction (action S) a f)‖,
      (continuous_closureAction_coefficient (action S) f (evaluation S 1)).norm⟩

@[simp] theorem absolute_apply (f : ComplexWap S) (s : S) :
    (absolute S f).val s = ‖f.val s‖ := by
  change ‖f.val (1 * s)‖ = ‖f.val s‖
  rw [one_mul]

set_option maxHeartbeats 1500000 in
-- The Haar pullback uses nested weak-operator and integral coercions.
/-- The stable vectors for right translation are exactly the complex WAP
functions whose absolute value has bi-invariant mean zero. -/
theorem stable_iff_absolute_mean_eq_zero (m : WapBiInvariantMean (S := S))
    (f : ComplexWap S) :
    IsAlmostWeaklyStable (closureAction (action S)) f ↔ m.functional (absolute S f) = 0 := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible (admissible S m)
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let π := closureAction (action S)
  let i : K.carrier →ₙ* T := ⟨Subtype.val, fun _ _ ↦ rfl⟩
  let M := m.toContinuousMean (closureInclusion (action S)) (continuous_closureInclusion S)
    (denseRange_closureInclusion (action S))
  let F := compactRealFunction (fun a ↦ ‖evaluation S 1 (π a f)‖)
    (continuous_closureAction_coefficient (action S) f (evaluation S 1)).norm
  have habsorb (s : T) : ∃ g : K.carrier, i g = i 1 * s :=
    ⟨⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩, rfl⟩
  have hmean : m.functional (absolute S f) =
      ∫ g : K.carrier, ‖evaluation S 1 (π (i g) f)‖ ∂normalizedHaar K.carrier :=
    M.apply_eq_groupIdealHaar i continuous_subtype_val Subtype.val_injective habsorb F
  constructor
  · intro hf
    have hp := (K.stable_iff_projection_eq_zero π f).1 hf
    have hz (g : K.carrier) : π (i g) f = 0 := by
      calc
        π (i g) f = π (i g * K.identity) f := congrArg (fun a ↦ π a f) (K.mul_identity g.2).symm
        _ = π (i g) (π K.identity f) := by rw [map_mul]; rfl
        _ = 0 := by rw [show π K.identity f = 0 from hp, map_zero]
    rw [hmean]
    simp only [hz, map_zero, norm_zero, integral_zero]
  · intro h
    have h' : (∫ g : K.carrier, ‖evaluation S 1 (π (i g) f)‖
        ∂normalizedHaar K.carrier) = 0 := hmean.symm.trans h
    have hc : Continuous (fun g : K.carrier ↦ ‖evaluation S 1 (π (i g) f)‖) :=
      (continuous_closureAction_coefficient (action S) f (evaluation S 1)).norm.comp
        continuous_subtype_val
    have ha := (integral_eq_zero_iff_of_nonneg (fun _ ↦ norm_nonneg _)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 h'
    have hz := (hc.ae_eq_iff_eq (normalizedHaar K.carrier) continuous_zero).1 ha
    apply (K.stable_iff_projection_eq_zero π f).2
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro s
    let g : K.carrier := ⟨closureInclusion (action S) s * K.identity,
      K.mul_mem_left (closureInclusion (action S) s) K.identity_mem⟩
    have hcoeff := norm_eq_zero.1 (congrFun hz g)
    have heq : π (i g) f = action S s (π K.identity f) := by
      change π (closureInclusion (action S) s * K.identity) f = _
      rw [map_mul]
      rfl
    rw [heq, evaluation_apply, action_apply, one_mul] at hcoeff
    exact hcoeff

/-- The WAP space splits into the reversible translation subspace and the
closed subspace of functions of absolute mean zero. -/
theorem decomposition_of_biInvariantMean (m : WapBiInvariantMean (S := S)) :
    ∃ R N : Submodule ℂ (ComplexWap S), IsClosed (R : Set (ComplexWap S)) ∧
      IsClosed (N : Set (ComplexWap S)) ∧ IsCompl R N ∧
      (∀ f, f ∈ R ↔ IsReversible (closureAction (action S)) f) ∧
      ∀ f, f ∈ N ↔ m.functional (absolute S f) = 0 := by
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible (admissible S m)
  let π := closureAction (action S)
  let P := (K.projection π).toLinearMap
  refine ⟨P.range, P.ker, K.isClosed_range_projection π, K.isClosed_ker_projection π,
    K.range_isCompl_ker π, fun f ↦ (K.reversible_iff_mem_range π f).symm, fun f ↦ ?_⟩
  exact (K.stable_iff_mem_ker π f).symm.trans (stable_iff_absolute_mean_eq_zero S m f)

end JdLG.WapTranslation
