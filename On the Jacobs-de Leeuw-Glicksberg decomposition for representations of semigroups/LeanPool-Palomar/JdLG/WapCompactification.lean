/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesWapAction
public import JdLG.WeaklyAlmostPeriodic

/-! # The real weakly almost periodic compactification -/

@[expose] public section

open Set
open scoped BoundedContinuousFunction Topology

namespace JdLG

variable {S : Type*} [Semigroup S] [TopologicalSpace S] [SeparatelyContinuousMul S]

local notation "BC" => S →ᵇ ℝ
local notation "V" => ℝ × (S →ᵇ ℝ)

/-- Keep an extra evaluation coordinate so that the construction also works
for semigroups without an identity. -/
noncomputable def wapEvaluationAction : S →ₙ* (V →L[ℝ] V) where
  toFun s :=
    ((BoundedContinuousFunction.evalCLM ℝ (β := ℝ) s).comp (ContinuousLinearMap.snd ℝ ℝ BC)).prod
      ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ
        ⟨(· * s), continuous_mul_const s⟩).comp (ContinuousLinearMap.snd ℝ ℝ BC))
  map_mul' s t := by
    apply ContinuousLinearMap.ext
    intro a
    apply Prod.ext
    · rfl
    · apply BoundedContinuousFunction.ext
      intro u
      change a.2 (u * (s * t)) = a.2 (u * s * t)
      rw [mul_assoc]

private theorem wapEvaluationAction_le_one (s : S) :
    ‖wapEvaluationAction s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [one_mul, Prod.norm_def]
  refine max_le (le_trans (a.2.norm_coe_le_norm s) (le_max_right _ _)) ?_
  exact (BoundedContinuousFunction.norm_compContinuous_le _ _).trans (le_max_right _ _)

theorem wapEvaluationAction_isWap (a : V) (h : IsWeaklyAlmostPeriodic a.2) :
    IsWapVector (wapEvaluationAction (S := S)) a := by
  let Z := closure (range fun s : S ↦ toWeakSpace ℝ BC (rightTranslateBC a.2 s))
  let K := Icc (-‖a.2‖) ‖a.2‖ ×ˢ Z
  let j (p : ℝ × WeakSpace ℝ BC) : WeakSpace ℝ V :=
    toWeakSpace ℝ V (p.1, (toWeakSpace ℝ BC).symm p.2)
  have hj : Continuous j := by
    apply WeakBilin.continuous_of_continuous_eval
    intro L
    have h₁ : Continuous (fun p : ℝ × WeakSpace ℝ BC ↦ L (p.1, 0)) :=
      (L.continuous.comp (continuous_id.prodMk continuous_const)).comp continuous_fst
    have h₂ := (WeakBilin.eval_continuous (topDualPairing ℝ BC).flip
      (L.comp (ContinuousLinearMap.inr ℝ ℝ BC))).comp
        (continuous_snd : Continuous (Prod.snd : ℝ × WeakSpace ℝ BC → WeakSpace ℝ BC))
    refine (h₁.add h₂).congr fun p ↦ ?_
    change L (p.1, 0) + L (0, (toWeakSpace ℝ BC).symm p.2) =
      L (p.1, (toWeakSpace ℝ BC).symm p.2)
    rw [← map_add]
    simp
  have hk : IsCompact K := isCompact_Icc.prod h
  have hi := hk.image hj
  refine hi.of_isClosed_subset isClosed_closure (closure_minimal ?_ hi.isClosed)
  rintro _ ⟨s, rfl⟩
  refine ⟨(a.2 s, toWeakSpace ℝ BC (rightTranslateBC a.2 s)), ⟨?_, ?_⟩, ?_⟩
  · exact ⟨a.2.neg_norm_le_apply s, a.2.apply_le_norm s⟩
  · exact subset_closure (mem_range_self s)
  · simp only [j, LinearEquiv.symm_apply_apply]
    rfl

/-- A compact semitopological semigroup containing the weak operator limits
of the WAP translation action. -/
noncomputable abbrev WapCompactification (S : Type*) [Semigroup S] [TopologicalSpace S]
    [SeparatelyContinuousMul S] :=
  ↥(weakOperatorClosure (wapVectorRepresentation (wapEvaluationAction (S := S))))

noncomputable instance : CompactSpace (WapCompactification S) :=
  isCompact_iff_compactSpace.1
    (compact_weakOperatorClosure_wapVectorRepresentation _ wapEvaluationAction_le_one)

/-- The canonical map from the original semigroup. -/
noncomputable def toWapCompactification : S →ₙ* WapCompactification S :=
  closureInclusion _

theorem denseRange_toWapCompactification : DenseRange (toWapCompactification (S := S)) :=
  denseRange_closureInclusion _


theorem continuous_toWapCompactification :
    Continuous (toWapCompactification (S := S)) := by
  apply continuous_induced_rng.mpr
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro a L
  let W := wapVectorSubmodule (wapEvaluationAction (S := S))
  let ρ := wapVectorRepresentation (wapEvaluationAction (S := S))
  let K : Set (WeakSpace ℝ W) := weakVectorOrbit ρ a
  let : CompactSpace K := isCompact_iff_compactSpace.1
    (wapVectorRepresentation_all_orbits (wapEvaluationAction (S := S)) a)
  let m₁ : StrongDual ℝ W := (ContinuousLinearMap.fst ℝ ℝ BC).comp W.subtypeL
  let m₂ (s : S) : StrongDual ℝ W :=
    ((BoundedContinuousFunction.evalCLM ℝ (β := ℝ) s).comp
      (ContinuousLinearMap.snd ℝ ℝ BC)).comp W.subtypeL
  let profile (k : K) : ℝ × (S → ℝ) :=
    (m₁ ((toWeakSpace ℝ W).symm k.val), fun s ↦ m₂ s ((toWeakSpace ℝ W).symm k.val))
  have hv : Continuous (Subtype.val : K → WeakSpace ℝ W) := continuous_subtype_val
  have hc : Continuous profile :=
    ((WeakBilin.eval_continuous (topDualPairing ℝ W).flip m₁).comp
        hv).prodMk
      (continuous_pi fun s ↦ (WeakBilin.eval_continuous (topDualPairing ℝ W).flip
        (m₂ s)).comp hv)
  have hi : Function.Injective profile := by
    intro u v huv
    apply Subtype.ext
    apply (toWeakSpace ℝ W).symm.injective
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun p : ℝ × (S → ℝ) ↦ p.1) huv
    · apply BoundedContinuousFunction.ext
      intro s
      exact congrArg (fun p : ℝ × (S → ℝ) ↦ p.2 s) huv
  let orbit (s : S) : K :=
    ⟨toWeakSpace ℝ W (ρ s a), subset_closure (mem_range_self s)⟩
  have ho : Continuous orbit := by
    apply (hc.isClosedEmbedding hi).isEmbedding.isInducing.continuous_iff.mpr
    have h : profile ∘ orbit = fun s ↦ (a.val.2 s, fun t ↦ a.val.2 (t * s)) := by
      funext s
      apply Prod.ext
      · change m₁ ((toWeakSpace ℝ W).symm (toWeakSpace ℝ W (ρ s a))) = _
        rw [LinearEquiv.symm_apply_apply]
        rfl
      · funext t
        change m₂ t ((toWeakSpace ℝ W).symm (toWeakSpace ℝ W (ρ s a))) = _
        rw [LinearEquiv.symm_apply_apply]
        rfl
    rw [h]
    exact a.val.2.continuous.prodMk
      (continuous_pi fun t ↦ a.val.2.continuous.comp (continuous_const_mul t))
  have hL := ((WeakBilin.eval_continuous (topDualPairing ℝ W).flip L).comp
    continuous_subtype_val).comp ho
  change Continuous fun s ↦ L (ρ s a)
  refine hL.congr fun s ↦ ?_
  change L ((toWeakSpace ℝ W).symm (toWeakSpace ℝ W (ρ s a))) = L (ρ s a)
  rw [LinearEquiv.symm_apply_apply]

/-- The value of the extension is the extra coordinate of the translated
vector. -/
noncomputable def extendWap (f : weaklyAlmostPeriodicSubmodule (S := S)) :
    C(WapCompactification S, ℝ) := by
  let W := wapVectorSubmodule (wapEvaluationAction (S := S))
  let a : W := ⟨(0, f.val), wapEvaluationAction_isWap (0, f.val) f.property⟩
  let F : StrongDual ℝ W := (ContinuousLinearMap.fst ℝ ℝ BC).comp W.subtypeL
  refine ⟨fun T ↦ F ((closureAction _ T) a), ?_⟩
  exact (ContinuousLinearMapWOT.continuous_dual_apply a F).comp
    (continuous_subtype_val : Continuous (Subtype.val : WapCompactification S → _))

@[simp]
theorem extendWap_toWapCompactification (f : weaklyAlmostPeriodicSubmodule (S := S)) (s : S) :
    extendWap f (toWapCompactification s) = f.val s := rfl

theorem extendWap_unique (f : weaklyAlmostPeriodicSubmodule (S := S))
    (g : C(WapCompactification S, ℝ)) (h : ∀ s, g (toWapCompactification s) = f.val s) :
    g = extendWap f := by
  apply ContinuousMap.ext
  intro a
  exact congrFun (denseRange_toWapCompactification.equalizer g.continuous
    (extendWap f).continuous (funext h)) a

open scoped CompactlySupported in
/-- On a compact semitopological semigroup every bounded continuous function is WAP. -/
theorem isWap_of_compactSemigroup [CompactSpace S] [T2Space S] [Nonempty S] (f : BC) :
    IsWeaklyAlmostPeriodic f := by
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  exact isWap_pullbackBC (MulHom.id S) continuous_id f.toContinuousMap

section Equivalence

variable [Nonempty S]

instance : Nonempty (WapCompactification S) :=
  Nonempty.map toWapCompactification inferInstance

/-- Restriction along the compactification maps continuous functions to WAP functions. -/
noncomputable def restrictWap :
    C(WapCompactification S, ℝ) →ₗ[ℝ] weaklyAlmostPeriodicSubmodule (S := S) := by
  letI : MeasurableSpace (WapCompactification S) := borel (WapCompactification S)
  letI : BorelSpace (WapCompactification S) := ⟨rfl⟩
  exact wapPullback toWapCompactification continuous_toWapCompactification

@[simp]
theorem restrictWap_apply (g : C(WapCompactification S, ℝ)) (s : S) :
    (restrictWap g).val s = g (toWapCompactification s) := rfl

/-- Restriction and extension identify the spaces of continuous and WAP tests
as isometric normed vector spaces. -/
noncomputable def wapCompactificationLinearIso :
    C(WapCompactification S, ℝ) ≃ₗᵢ[ℝ] weaklyAlmostPeriodicSubmodule (S := S) where
  toLinearEquiv :=
    { restrictWap (S := S) with
      invFun := extendWap
      left_inv := fun g ↦ (extendWap_unique (restrictWap g) g (fun _ ↦ rfl)).symm
      right_inv := fun f ↦ Subtype.ext
        (BoundedContinuousFunction.ext (extendWap_toWapCompactification f)) }
  norm_map' g := by
    change ‖(restrictWap g).val‖ = ‖g‖
    apply le_antisymm
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg g)).2 fun s ↦
        g.norm_coe_le_norm (toWapCompactification s)
    · apply (ContinuousMap.norm_le g (norm_nonneg (restrictWap g).val)).2
      intro t
      exact denseRange_toWapCompactification.induction_on t
        (isClosed_le g.continuous.norm continuous_const)
        (fun s ↦ (restrictWap g).val.norm_coe_le_norm s)

/-- Products of real WAP functions are WAP. The product on the compactification
restricts to the pointwise product on the semigroup. -/
theorem isWap_mul {f g : BC} (hf : IsWeaklyAlmostPeriodic f)
    (hg : IsWeaklyAlmostPeriodic g) : IsWeaklyAlmostPeriodic (f * g) := by
  let h := restrictWap (extendWap ⟨f, hf⟩ * extendWap ⟨g, hg⟩)
  have hh : h.val = f * g := by
    apply BoundedContinuousFunction.ext
    intro s
    rfl
  exact hh ▸ h.property

end Equivalence

end JdLG

