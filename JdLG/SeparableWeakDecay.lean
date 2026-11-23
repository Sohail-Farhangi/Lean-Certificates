/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.DensityDiagonal
public import JdLG.FolnerCriteria
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Density-one weak decay on norm-separable spaces

A countable family of dual tests separates points of a separable Banach
space. On compact weak sets it induces the weak topology, so the countable
density-one selection applies without changing the tests in the conclusion.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace JdLG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SeparableSpace E]

/-- Norming functionals at a norm-dense sequence separate points. -/
theorem exists_separating_dual_sequence :
    ∃ f : ℕ → StrongDual ℂ E, Function.Injective (fun x : E ↦ fun n ↦ f n x) := by
  choose f hf hg using fun n ↦ exists_dual_vector'' ℂ (denseSeq E n)
  refine ⟨f, fun x y h ↦ ?_⟩
  by_contra hne
  let z := x - y
  have hz : 0 < ‖z‖ := norm_pos_iff.2 (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 (denseRange_denseSeq E) z (‖z‖ / 3) (by positivity)
  have hzero : f n z = 0 := by
    change f n (x - y) = 0
    have he : f n x = f n y := congrFun h n
    rw [map_sub, he, sub_self]
  have hfn : ‖denseSeq E n‖ ≤ ‖denseSeq E n - z‖ := calc
    ‖denseSeq E n‖ = ‖f n (denseSeq E n - z)‖ := by
      rw [map_sub, hzero, sub_zero, hg n, RCLike.norm_ofReal, abs_norm]
    _ ≤ ‖denseSeq E n - z‖ := by
      simpa only [one_mul] using (f n).le_of_opNorm_le (hf n) (denseSeq E n - z)
  change dist z (denseSeq E n) < ‖z‖ / 3 at hn
  rw [dist_comm, dist_eq_norm] at hn
  have ht : ‖z‖ ≤ ‖denseSeq E n‖ + ‖denseSeq E n - z‖ := by
    have h : z = denseSeq E n + (z - denseSeq E n) := by abel
    conv_lhs => rw [h]
    exact (norm_add_le _ _).trans_eq (congrArg (‖denseSeq E n‖ + ·) (norm_sub_rev _ _))
  linarith

/-- Compact subsets of the weak topology on a norm-separable Banach space
are first-countable in their induced topology. -/
theorem firstCountableTopology_weakCompact_of_separable {K : Set (WeakSpace ℂ E)}
    (hK : IsCompact K) : FirstCountableTopology K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨f, hf⟩ := exists_separating_dual_sequence (E := E)
  let eval (x : K) (n : ℕ) := f n ((toWeakSpace ℂ E).symm x.val)
  have hc : Continuous eval :=
    continuous_pi fun n ↦ (WeakBilin.eval_continuous (topDualPairing ℂ E).flip (f n)).comp
      continuous_subtype_val
  have hi : Function.Injective eval := fun _ _ h ↦
    Subtype.ext ((toWeakSpace ℂ E).symm.injective (hf h))
  exact (hc.isClosedEmbedding hi).isEmbedding.firstCountableTopology

variable {S : Type*} [Semigroup S] [MeasurableSpace S] [TopologicalSpace S] [CompleteSpace E]
  (π : S →ₙ* (E →L[ℂ] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]
  (hπ : Measurable (closureInclusion π))
  (ν : ℕ → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))

include hπ hprob

/-- The forward implication in Theorem 4.2(ix) when the acting Banach
space is norm separable. The set obtained has full density and weak
convergence along its cocompact filter. -/
theorem exists_folner_density_one_weakDecay_of_separable
    (hν : LeftFolnerProbabilities ν atTop) (hadm : IsJdLGAdmissible π)
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFm : ∀ n, MeasurableSet (F n))
    (hsupp : ∀ n, ν n (F n)ᶜ = 0) {x : E} (hx : IsAlmostWeaklyStable (closureAction π) x) :
    ∃ A : Set S, MeasurableSet A ∧ Tendsto (fun n ↦ (ν n).real A) atTop (𝓝 1) ∧
      Tendsto (fun s ↦ toWeakSpace ℂ E (π s x)) (cocompact S ⊓ 𝓟 A) (𝓝 0) := by
  let eval (t : weakOperatorClosure π) := toWeakSpace ℂ E (closureAction π t x)
  let K := range eval
  have hK : IsCompact K := isCompact_range (continuous_weakOrbit_closureAction π x)
  let : FirstCountableTopology K := firstCountableTopology_weakCompact_of_separable hK
  obtain ⟨u, hu⟩ := hx
  have hmem : (0 : WeakSpace ℂ E) ∈ K := ⟨u, by
    change toWeakSpace ℂ E (closureAction π u x) = 0
    rw [hu, map_zero]⟩
  let y : K := ⟨0, hmem⟩
  let ψ (t : weakOperatorClosure π) : K := ⟨eval t, ⟨t, rfl⟩⟩
  let φ (s : S) : K := ψ (closureInclusion π s)
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  have hc : Continuous ψ := (continuous_weakOrbit_closureAction π x).subtype_mk _
  have hm : Measurable φ := hc.measurable.comp hπ
  have hr (U : Set K) (hU : IsOpen U) (hyU : y ∈ U) :
      Tendsto (fun n ↦ (ν n).real (φ ⁻¹' U)) atTop (𝓝 1) := by
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
    exact folnerWeakReturns_of_stable π hπ ν hprob hν hadm ⟨u, hu⟩ V hV hyU
  obtain ⟨A, hA, hAd, hAt⟩ := exists_density_one_tendsto_cocompact_of_countableBasis
    ν hprob F hF hFm hsupp φ hm y hr
  exact ⟨A, hA, hAd, continuous_subtype_val.continuousAt.tendsto.comp hAt⟩

end JdLG
