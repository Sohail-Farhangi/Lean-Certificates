/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesWapAction
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Sequences

/-!
# Norm closedness of the WAP subspace

Along a fixed ultrafilter the weak limits of norm-approximating WAP vectors
are Cauchy in norm. Their norm limit is the weak limit for the original
vector. The Stone–Čech compactification then gives weak compactness.
-/

@[expose] public section

namespace JdLG

open Filter Set
open scoped Topology

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem IsWapVector.ultrafilter_converges {ρ : S →ₙ* (E →L[𝕜] E)} {x : E}
    (hx : IsWapVector ρ x) (u : Ultrafilter S) :
    ∃ y : E, Tendsto (fun s ↦ toWeakSpace 𝕜 E (ρ s x))
      (u : Filter S) (𝓝 (toWeakSpace 𝕜 E y)) := by
  let f := fun s ↦ toWeakSpace 𝕜 E (ρ s x)
  have hm : weakVectorOrbit ρ x ∈ u.map f := by
    change ∀ᶠ s in (u : Filter S), f s ∈ closure (range f)
    exact Eventually.of_forall fun _ ↦ subset_closure (mem_range_self _)
  obtain ⟨w, -, hw⟩ := hx.ultrafilter_le_nhds' _ hm
  exact ⟨(toWeakSpace 𝕜 E).symm w, by
    rw [LinearEquiv.apply_symm_apply]
    exact hw⟩

theorem IsWapVector.of_ultrafilter_converges {ρ : S →ₙ* (E →L[𝕜] E)} {x : E}
    (h : ∀ u : Ultrafilter S, ∃ y : E, Tendsto (fun s ↦ toWeakSpace 𝕜 E (ρ s x))
      (u : Filter S) (𝓝 (toWeakSpace 𝕜 E y))) : IsWapVector ρ x := by
  let f := fun s ↦ toWeakSpace 𝕜 E (ρ s x)
  have he : Continuous (Ultrafilter.extend f) := by
    let : TopologicalSpace S := ⊥
    refine isDenseInducing_pure.continuous_extend fun u ↦ ?_
    obtain ⟨y, hy⟩ := h u
    exact ⟨toWeakSpace 𝕜 E y, hy.mono_left (ultrafilter_comap_pure_nhds u)⟩
  have hc := isCompact_range he
  have hs : range f ⊆ range (Ultrafilter.extend f) := by
    rintro _ ⟨s, rfl⟩
    exact ⟨pure s, ultrafilter_extend_pure f s⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

private theorem norm_le_of_weak_tendsto {ι : Type*} {p : Filter ι} [NeBot p]
    {f : ι → E} {y : E} {C : ℝ}
    (h : Tendsto (fun n ↦ toWeakSpace 𝕜 E (f n)) p (𝓝 (toWeakSpace 𝕜 E y)))
    (hC : ∀ n, ‖f n‖ ≤ C) : ‖y‖ ≤ C := by
  have hc := isClosed_weak_norm_le (𝕜 := 𝕜) (E := E) C
  have hm := mem_closure_of_tendsto h (s := {w : WeakSpace 𝕜 E |
    ‖(toWeakSpace 𝕜 E).symm w‖ ≤ C}) (Eventually.of_forall fun n ↦ by
      simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using hC n)
  rw [hc.closure_eq] at hm
  exact ((toWeakSpace 𝕜 E).symm_apply_apply y) ▸ hm

private theorem wap_pairing_injective : Function.Injective (topDualPairing 𝕜 E).flip := by
  intro x y h
  by_contra hne
  obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := 𝕜) hne
  exact hf (LinearMap.congr_fun h f)

/-- Weakly almost periodic vectors of a contraction representation form a
norm-closed subspace of a Banach space. -/
theorem isClosed_wapVectorSubmodule [CompleteSpace E]
    (ρ : S →ₙ* (E →L[𝕜] E)) (hρ : ∀ s, ‖ρ s‖ ≤ 1) :
    IsClosed (wapVectorSubmodule ρ : Set E) := by
  apply isSeqClosed_iff_isClosed.1
  intro xs x hxsWap hxs
  change IsWapVector ρ x
  apply IsWapVector.of_ultrafilter_converges
  intro p
  choose y hy using fun n ↦ (show IsWapVector ρ (xs n) from hxsWap n).ultrafilter_converges p
  have hbound (s : S) (z : E) : ‖ρ s z‖ ≤ ‖z‖ := by
    simpa only [one_mul] using (ρ s).le_of_opNorm_le (hρ s) z
  have hdist (n m : ℕ) : dist (y n) (y m) ≤ dist (xs n) (xs m) := by
    rw [dist_eq_norm, dist_eq_norm]
    apply norm_le_of_weak_tendsto (𝕜 := 𝕜) (f := fun s ↦ ρ s (xs n - xs m))
      (p := (p : Filter S))
    · simpa only [map_sub] using (hy n).sub (hy m)
    · exact fun s ↦ hbound s _
  have hyCauchy : CauchySeq y :=
    Metric.cauchySeq_iff.2 fun ε hε ↦ ((Metric.cauchySeq_iff.1 hxs.cauchySeq) ε hε).imp
      fun N hN n hn m hm ↦ (hdist n m).trans_lt (hN n hn m hm)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hyCauchy
  refine ⟨z, (WeakBilin.tendsto_iff_forall_eval_tendsto _ wap_pairing_injective).2 fun f ↦ ?_⟩
  change Tendsto (fun s ↦ f (ρ s x)) (p : Filter S) (𝓝 (f z))
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := ε / (3 * (‖f‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n, hn₁, hn₂⟩ := ((Metric.tendsto_nhds.1 hxs δ hδ).and
    (Metric.tendsto_nhds.1 hz δ hδ)).exists
  have hp := (WeakBilin.tendsto_iff_forall_eval_tendsto _ wap_pairing_injective).1 (hy n) f
  change Tendsto (fun s ↦ f (ρ s (xs n))) (p : Filter S) (𝓝 (f (y n))) at hp
  refine (Metric.tendsto_nhds.1 hp (ε / 3) (by positivity)).mono fun s hs ↦ ?_
  have hmul : ‖f‖ * δ ≤ ε / 3 := calc
    _ ≤ (‖f‖ + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ = _ := by dsimp [δ]; field_simp
  have he₁ : dist (f (ρ s x)) (f (ρ s (xs n))) ≤ ε / 3 := by
    rw [dist_comm, dist_eq_norm, ← map_sub, ← map_sub]
    exact ((f.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hbound s _).trans (by
        simpa only [dist_eq_norm] using hn₁.le)) (norm_nonneg f))).trans hmul
  have he₂ : dist (f (y n)) (f z) ≤ ε / 3 := by
    rw [dist_eq_norm, ← map_sub]
    exact ((f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (by
      simpa only [dist_eq_norm] using hn₂.le) (norm_nonneg f))).trans hmul
  have ht₁ := dist_triangle (f (ρ s x)) (f (ρ s (xs n))) (f z)
  have ht₂ := dist_triangle (f (ρ s (xs n))) (f (y n)) (f z)
  linarith

end JdLG
