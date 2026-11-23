/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ContinuousTestDual
public import JdLG.MeasuredTransfer
public import JdLG.WapSubspace

/-! # Weakly almost periodic pullbacks from compact semitopological hosts -/

@[expose] public section

open Set
open scoped BoundedContinuousFunction CompactlySupported Topology

namespace JdLG

section WAP

variable {S : Type*} [Semigroup S] [TopologicalSpace S] [SeparatelyContinuousMul S]

local notation "BC" => S →ᵇ ℝ

section Pullback

variable {T : Type*} [Semigroup T] [TopologicalSpace T] [SeparatelyContinuousMul T]
  [CompactSpace T] [T2Space T] [Nonempty T] [MeasurableSpace T] [BorelSpace T]

local notation "CT" => C(T, ℝ)

/-- Pullback from a compact space into bounded continuous functions. -/
noncomputable def pullbackBC (i : C(S, T)) : CT →L[ℝ] BC :=
  ({ toFun := fun f ↦ (BoundedContinuousFunction.mkOfCompact f).compContinuous i
     map_add' := fun _ _ ↦ BoundedContinuousFunction.ext fun _ ↦ rfl
     map_smul' := fun _ _ ↦ BoundedContinuousFunction.ext fun _ ↦ rfl } :
       CT →ₗ[ℝ] BC).mkContinuous 1 fun f ↦ by
    rw [one_mul]
    exact (BoundedContinuousFunction.norm_compContinuous_le _ i).trans le_rfl

theorem isWap_pullbackBC (i : S →ₙ* T) (hi : Continuous i) (f : CT) :
    IsWeaklyAlmostPeriodic (pullbackBC ⟨i, hi⟩ f) := by
  let j : C(S, T) := ⟨i, hi⟩
  let F (u : T) : CT := ⟨fun v ↦ f (v * u), f.continuous.comp (continuous_mul_const u)⟩
  let G (u : T) := toWeakSpace ℝ BC (pullbackBC j (F u))
  have hG : Continuous G := by
    apply WeakBilin.continuous_of_continuous_eval
    intro Λ
    exact continuous_dual_of_separatelyContinuous F
      (fun v ↦ f.continuous.comp (continuous_const_mul v)) ‖f‖
      (fun u v ↦ f.norm_coe_le_norm (v * u)) (Λ.comp (pullbackBC j))
  have hK : IsCompact (range G) := isCompact_range hG
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨s, rfl⟩
  refine ⟨i s, congrArg (toWeakSpace ℝ BC)
    (BoundedContinuousFunction.ext fun t ↦ ?_)⟩
  change f (i t * i s) = f (i (t * s))
  rw [map_mul i]

/-- Pullback to the real weakly almost periodic subspace. -/
noncomputable def wapPullback (i : S →ₙ* T) (hi : Continuous i) :
    CT →ₗ[ℝ] weaklyAlmostPeriodicSubmodule (S := S) where
  toFun f := ⟨pullbackBC ⟨i, hi⟩ f, isWap_pullbackBC i hi f⟩
  map_add' f g := Subtype.ext (map_add (pullbackBC ⟨i, hi⟩) f g)
  map_smul' c f := Subtype.ext (map_smul (pullbackBC ⟨i, hi⟩) c f)

/-- A WAP mean acts on the compact host by integrating pullbacks. -/
noncomputable def wapContinuousFunctional (m : WapBiInvariantMean (S := S))
    (i : S →ₙ* T) (hi : Continuous i) : C_c(T, ℝ) →ₚ[ℝ] ℝ where
  toFun f := m.functional (wapPullback i hi f.toContinuousMap)
  map_add' f g := by
    change m.functional (wapPullback i hi (f.toContinuousMap + g.toContinuousMap)) = _
    rw [map_add, map_add]
  map_smul' c f := by
    change m.functional (wapPullback i hi (c • f.toContinuousMap)) = _
    rw [map_smul, map_smul]
    rfl
  monotone' _ _ h := m.monotone' _ _ fun s ↦ h (i s)

theorem wapContinuousFunctional_one (m : WapBiInvariantMean (S := S))
    (i : S →ₙ* T) (hi : Continuous i) :
    wapContinuousFunctional m i hi (compactRealFunction (fun _ ↦ 1) continuous_const) = 1 := by
  have h : wapPullback i hi (compactRealFunction (fun _ ↦ 1) continuous_const).toContinuousMap =
      ⟨1, isWap_one⟩ := Subtype.ext (BoundedContinuousFunction.ext fun _ ↦ rfl)
  change m.functional (wapPullback i hi (compactRealFunction (fun _ ↦ 1)
    continuous_const).toContinuousMap) = 1
  exact (congrArg m.functional h).trans m.one'

/-- The left-invariant mean on a compact host induced by a WAP mean. -/
noncomputable def WapBiInvariantMean.toContinuousMean (m : WapBiInvariantMean (S := S))
    (i : S →ₙ* T) (hi : Continuous i) (hd : DenseRange i) :
    LeftInvariantContinuousMean (fun s : T ↦ continuous_const_mul s) where
  functional := wapContinuousFunctional m i hi
  normalized := wapContinuousFunctional_one m i hi
  translate t f := by
    refine MeasuredMean.continuousFunctional_translate_of_dense i (wapContinuousFunctional m i hi)
      (wapContinuousFunctional_one m i hi) (· * ·) (fun s ↦ continuous_mul_const s)
      (fun s ↦ continuous_const_mul s) hd (fun s g ↦ ?_) t f
    exact m.left' s _ _ fun t ↦ by
      change g (i s * i t) = g (i (s * t))
      rw [map_mul i]

theorem WapBiInvariantMean.toContinuousMean_rightInvariant (m : WapBiInvariantMean (S := S))
    (i : S →ₙ* T) (hi : Continuous i) (hd : DenseRange i) :
    (m.toContinuousMean i hi hd).IsRightInvariant (fun s ↦ continuous_mul_const s) := by
  intro t f
  refine MeasuredMean.continuousFunctional_translate_of_dense i (wapContinuousFunctional m i hi)
    (wapContinuousFunctional_one m i hi) (fun a b ↦ b * a) (fun s ↦ continuous_const_mul s)
    (fun s ↦ continuous_mul_const s) hd (fun s g ↦ ?_) t f
  exact m.right' s _ _ fun t ↦ by
    change g (i t * i s) = g (i (t * s))
    rw [map_mul i]

end Pullback
end WAP

section Operator

variable {S E : Type*} [Semigroup S] [TopologicalSpace S] [SeparatelyContinuousMul S]
  [Nonempty S] [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : S →ₙ* (E →L[ℂ] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)] (hπ : Continuous (closureInclusion π))
  (m : WapBiInvariantMean (S := S))

include hπ m

/-- Theorem 1.3. A bi-invariant mean on the real WAP functions makes a
relatively WOT-compact representation JdLG-admissible. -/
theorem admissible_of_WapBiInvariantMean : IsJdLGAdmissible π := by
  let : Nonempty (weakOperatorClosure π) := ⟨closureInclusion π (Classical.choice inferInstance)⟩
  let mean := m.toContinuousMean (closureInclusion π) hπ (denseRange_closureInclusion π)
  exact ⟨isCompact_iff_compactSpace.mpr inferInstance,
    mean.existsUnique_minimalIdempotent_of_biInvariant
      (m.toContinuousMean_rightInvariant (closureInclusion π) hπ (denseRange_closureInclusion π))⟩

/-- The absolute coefficient raised to a positive power as a WAP test. -/
noncomputable def wapCoefficientMoment (x : E) (f : StrongDual ℂ E)
    (p : ℝ) (hp : 0 < p) : ℝ := by
  let : Nonempty (weakOperatorClosure π) := ⟨closureInclusion π (Classical.choice inferInstance)⟩
  exact m.functional (wapPullback (closureInclusion π) hπ
    ⟨(fun t ↦ ‖f (closureAction π t x)‖ ^ p),
      (continuous_closureAction_coefficient π x f).norm.rpow_const (fun _ ↦ Or.inr hp.le)⟩)

/-- Lemma 4.1 on the actual semigroup WAP mean. Both power quantifiers
are consequences of the same compact group-ideal Haar formula. -/
theorem stable_iff_wapCoefficientMoments (x : E) :
    (IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ (p : ℝ) (hp : 0 < p) (f : StrongDual ℂ E), wapCoefficientMoment π hπ m x f p hp = 0) ∧
    (IsAlmostWeaklyStable (closureAction π) x ↔
      ∃ (p : ℝ) (hp : 0 < p), ∀ f : StrongDual ℂ E, wapCoefficientMoment π hπ m x f p hp = 0) := by
  let : Nonempty (weakOperatorClosure π) := ⟨closureInclusion π (Classical.choice inferInstance)⟩
  let mean := m.toContinuousMean (closureInclusion π) hπ (denseRange_closureInclusion π)
  have hm := m.toContinuousMean_rightInvariant (closureInclusion π) hπ
    (denseRange_closureInclusion π)
  exact almostWeaklyStable_iff_biInvariantMeanMoments mean hm (closureAction π) x
    (continuous_closureAction_coefficient π x)

end Operator
end JdLG
