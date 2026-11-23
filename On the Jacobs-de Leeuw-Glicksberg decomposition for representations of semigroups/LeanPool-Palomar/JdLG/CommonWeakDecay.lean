/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Restriction
public import JdLG.SeparableWeakDecay

/-! # Simultaneous density-one weak decay on the stable subspace -/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace JdLG

variable {S E : Type*} [Semigroup S] [MeasurableSpace S] [TopologicalSpace S]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (π : S →ₙ* (E →L[ℂ] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]
  (hπ : Measurable (closureInclusion π))
  (ν : ℕ → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))

include hπ hprob

/-- Corollary 4.3, expressed with normalized averaging probabilities. The
kernel of the group-ideal projection is the almost weakly stable subspace,
and its norm separability suffices for one common set of times. -/
theorem exists_common_folner_density_one_weakDecay (hν : LeftFolnerProbabilities ν atTop)
    (hadm : IsJdLGAdmissible π) (K : GroupIdeal (weakOperatorClosure π))
    [SeparableSpace (K.projection (closureAction π)).ker]
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFm : ∀ n, MeasurableSet (F n))
    (hsupp : ∀ n, ν n (F n)ᶜ = 0)
    (hescape : ∀ C : Set S, IsCompact C → Tendsto (fun n ↦ (ν n).real C) atTop (𝓝 0)) :
    ∃ A : Set S, MeasurableSet A ∧ Tendsto (fun n ↦ (ν n).real A) atTop (𝓝 1) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        Tendsto (fun s ↦ toWeakSpace ℂ E (π s x)) (cocompact S ⊓ 𝓟 A) (𝓝 0) := by
  let Y := (K.projection (closureAction π)).ker
  let : IsClosed (Y : Set E) := K.isClosed_ker_projection (closureAction π)
  let : CompleteSpace Y := (K.isClosed_ker_projection (closureAction π)).completeSpace_coe
  have hInv (s : S) (x : E) (hx : x ∈ Y) : π s x ∈ Y := by
    change K.projection (closureAction π) x = 0 at hx
    change K.projection (closureAction π) (closureAction π (closureInclusion π s) x) = 0
    rw [K.projection_commutes, hx, map_zero]
  let ρ := restrictedRepresentation Y π hInv
  obtain ⟨hρ, _, _, hstable⟩ := admissible_restriction Y hInv hadm
  obtain ⟨r, hrc, _, hreval⟩ := exists_closure_restriction_map Y hInv hadm.1
  let : CompactSpace (weakOperatorClosure ρ) := isCompact_iff_compactSpace.mp hρ.1
  let : MeasurableSpace (weakOperatorClosure ρ) := borel (weakOperatorClosure ρ)
  let : BorelSpace (weakOperatorClosure ρ) := ⟨rfl⟩
  have hr (s : S) : r (closureInclusion π s) = closureInclusion ρ s := by
    apply Subtype.ext
    apply ContinuousLinearMapWOT.toCLM_injective
    apply ContinuousLinearMap.ext
    intro x
    exact Subtype.ext (hreval (closureInclusion π s) x)
  have hρm : Measurable (closureInclusion ρ) := by
    have he : (r ∘ closureInclusion π) = closureInclusion ρ := funext hr
    exact he ▸ hrc.measurable.comp hπ
  let y := denseSeq Y
  have hdecay (n : ℕ) := exists_folner_density_one_weakDecay_of_separable ρ hρm ν hprob
    hν hρ F hF hFm hsupp ((hstable (y n)).2
      ((K.stable_iff_mem_ker (closureAction π) _).2 (y n).property))
  obtain ⟨A, hA, hd, ht⟩ := exists_common_density_one_tendsto_cocompact ν hprob F hF hFm hsupp
    (fun n s ↦ toWeakSpace ℂ Y (ρ s (y n))) (fun _ ↦ 0) hdecay
  let L := cocompact S ⊓ 𝓟 A
  have hcont : Continuous fun t : weakOperatorClosure π ↦
      ContinuousLinearMapWOT.ofCLM (closureAction π t) := continuous_subtype_val
  obtain ⟨C, hC, hBound⟩ := exists_operatorBound_of_compact_wot (closureAction π) hcont
  have hWeakEval {v : Y} {f : StrongDual ℂ E}
      (hv : Tendsto (fun s ↦ toWeakSpace ℂ Y (ρ s v)) L (𝓝 0)) :
      Tendsto (fun s ↦ f (π s (v : E))) L (𝓝 0) := by
    have he := WeakBilin.eval_continuous (topDualPairing ℂ Y).flip (f.comp Y.subtypeL)
    have h := he.continuousAt.tendsto.comp hv
    change Tendsto (fun s ↦ f (π s (v : E))) L (𝓝 (f 0)) at h
    rwa [map_zero] at h
  have hDense (v : Y) (f : StrongDual ℂ E) :
      Tendsto (fun s ↦ f (π s (v : E))) L (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    let D := ‖f‖ * C + 1
    have hD : 0 < D := add_pos_of_nonneg_of_pos (mul_nonneg (norm_nonneg _) hC.le) zero_lt_one
    have hδ : 0 < ε / 2 / D := div_pos (half_pos hε) hD
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq Y) v (ε / 2 / D) hδ
    filter_upwards [(Metric.tendsto_nhds.1 (hWeakEval (f := f) (ht n))) (ε / 2) (half_pos hε)]
      with s hs
    have hdiff : ‖(v : E) - y n‖ < ε / 2 / D := by
      change dist v (y n) < ε / 2 / D at hn
      rw [dist_eq_norm] at hn
      exact hn
    have hsmall : ‖f (π s ((v : E) - y n))‖ < ε / 2 := calc
      _ ≤ ‖f‖ * ‖π s ((v : E) - y n)‖ := f.le_opNorm _
      _ ≤ ‖f‖ * (C * ‖(v : E) - y n‖) := mul_le_mul_of_nonneg_left
        ((π s).le_of_opNorm_le (hBound (closureInclusion π s)) _) (norm_nonneg f)
      _ = (‖f‖ * C) * ‖(v : E) - y n‖ := (mul_assoc _ _ _).symm
      _ ≤ D * ‖(v : E) - y n‖ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
      _ < ε / 2 := by rw [mul_comm]; exact (lt_div_iff₀ hD).mp hdiff
    rw [dist_zero_right] at hs ⊢
    have he : f (π s (v : E)) = f (π s ((v : E) - y n)) + f (π s (y n : E)) := by
      rw [map_sub, map_sub, sub_add_cancel]
    rw [he]
    exact (norm_add_le _ _).trans_lt ((add_lt_add hsmall hs).trans_eq (add_halves ε))
  refine ⟨A, hA, hd, fun x ↦ ⟨fun hx ↦ ?_, fun hv ↦ ?_⟩⟩
  · let v : Y := ⟨x, (K.stable_iff_mem_ker (closureAction π) _).1 hx⟩
    have hi : Function.Injective (topDualPairing ℂ E).flip :=
      separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℂ E)
    have hweak := WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℂ E).flip hi
      (f := fun s ↦ toWeakSpace ℂ E (π s x)) (x := 0) (l := L)
    apply hweak.2
    intro f
    change Tendsto (fun s ↦ f (π s x)) L (𝓝 (f 0))
    simpa only [map_zero] using hDense v f
  · refine (stable_iff_folnerWeakReturns π hπ ν hprob hν hadm x).2 fun U hU h0 ↦ ?_
    exact density_one_returns_of_tendsto_cocompact ν hprob hescape _ hd hv U (hU.mem_nhds h0)

omit hprob in
/-- Corollary 4.3 for normalized restrictions of the underlying measure
to the compact blocks of a left Følner sequence. -/
theorem exists_common_weakDecay_of_measuredFolnerSequence [T2Space S] [BorelSpace S]
    (μ : Measure S) [IsFiniteMeasureOnCompacts μ]
    (hadm : IsJdLGAdmissible π) (K : GroupIdeal (weakOperatorClosure π))
    [SeparableSpace (K.projection (closureAction π)).ker]
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFpos : ∀ n, μ (F n) ≠ 0)
    (hGrow : Tendsto (fun n ↦ μ (F n)) atTop (𝓝 ⊤))
    (hν : LeftFolnerProbabilities (fun n ↦ normalizedRestrictedMeasure μ (F n)) atTop) :
    ∃ A : Set S, MeasurableSet A ∧
      Tendsto (fun n ↦ (normalizedRestrictedMeasure μ (F n)).real A) atTop (𝓝 1) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        Tendsto (fun s ↦ toWeakSpace ℂ E (π s x)) (cocompact S ⊓ 𝓟 A) (𝓝 0) :=
  exists_common_folner_density_one_weakDecay π hπ _ (fun n ↦
    normalizedRestrictedMeasure_probability μ (hFpos n) (hF n).measure_ne_top)
    hν hadm K F hF (fun n ↦ (hF n).isClosed.measurableSet)
    (fun n ↦ normalizedRestrictedMeasure_compl μ (hF n).isClosed.measurableSet)
    (fun _ hC ↦ normalizedRestrictedMeasure_real_tendsto_zero μ F hGrow
      hC.isClosed.measurableSet hC.measure_ne_top)

end JdLG
