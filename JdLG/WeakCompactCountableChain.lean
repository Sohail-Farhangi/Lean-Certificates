/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.WeakCompactFragmentation
public import JdLG.SeparableWeakDecay
public import Mathlib.Order.Zorn

/-!
# Countable chain condition for weakly compact sets

Norm fragmentation and maximal disjoint families of small open sets give a
separable subspace containing a weakly compact set with the countable chain
condition. On this compact set countably many Hahn–Banach extensions of
dual tests on that subspace generate the induced topology.
-/

@[expose] public section

namespace JdLG

open Filter Set TopologicalSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "W" => WeakSpace ℂ E

private theorem exists_dense_family_of_small_weakOpens {K : Set W} (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Set (Set K), D.Pairwise Disjoint ∧ Dense (⋃₀ D) ∧
      ∀ U ∈ D, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, ∀ y ∈ U, weakDist x.val y.val < ε := by
  classical
  let P (U : Set K) := IsOpen U ∧ U.Nonempty ∧
    ∀ x ∈ U, ∀ y ∈ U, weakDist x.val y.val < ε
  let C : Set (Set (Set K)) := {D | D.Pairwise Disjoint ∧ ∀ U ∈ D, P U}
  obtain ⟨D, hD⟩ := zorn_subset C fun c hc hchain ↦ by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun A hA ↦ subset_sUnion_of_mem hA⟩
    · intro U hU V hV hUV
      obtain ⟨A, hAc, hUA⟩ := mem_sUnion.1 hU
      obtain ⟨B, hBc, hVB⟩ := mem_sUnion.1 hV
      rcases hchain.total hAc hBc with hAB | hBA
      · exact (hc hBc).1 (hAB hUA) hVB hUV
      · exact (hc hAc).1 hUA (hBA hVB) hUV
    · intro U hU
      obtain ⟨A, hA, hUA⟩ := mem_sUnion.1 hU
      exact (hc hA).2 U hUA
  refine ⟨D, hD.prop.1, ?_, hD.prop.2⟩
  by_contra hn
  have hO : ((closure (⋃₀ D))ᶜ).Nonempty := by
    simpa only [nonempty_compl, dense_iff_closure_eq] using hn
  obtain ⟨U, hUo, hUn, hUs, hUd⟩ := exists_small_weakOpen_subset hK
    isClosed_closure.isOpen_compl hO ε hε
  have hdis (V : Set K) (hV : V ∈ D) : Disjoint U V :=
    disjoint_left.2 fun _ hx hy ↦ hUs hx (subset_closure (mem_sUnion_of_mem hy hV))
  have hbig : insert U D ∈ C := by
    refine ⟨?_, ?_⟩
    · exact hD.prop.1.insert (fun V hV _ ↦ ⟨hdis V hV, (hdis V hV).symm⟩)
    · intro V hV
      rcases mem_insert_iff.1 hV with rfl | hVD
      · exact ⟨hUo, hUn, hUd⟩
      · exact hD.prop.2 V hVD
  have hUD : U ∈ D := hD.2 hbig (subset_insert _ _) (mem_insert _ _)
  obtain ⟨x, hx⟩ := hUn
  exact disjoint_left.1 (hdis U hUD) hx hx

/-- A weakly compact set with the countable chain condition is contained in a
closed norm-separable subspace of the ambient normed space. -/
theorem exists_separable_closedSpan_of_weakCompact_ccc {K : Set W} (hK : IsCompact K)
    (hccc : ∀ D : Set (Set K), D.Pairwise Disjoint →
      (∀ U ∈ D, IsOpen U ∧ U.Nonempty) → D.Countable) :
    ∃ M : Submodule ℂ E, IsClosed (M : Set E) ∧ IsSeparable (M : Set E) ∧
      K ⊆ toWeakSpace ℂ E '' (M : Set E) := by
  classical
  let ε (n : ℕ) : ℝ := 1 / (n + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose D hDpair hDdense hDsmall using fun n ↦ exists_dense_family_of_small_weakOpens hK
    (ε n) (hε n)
  have hD (n : ℕ) : Countable (D n) := hccc _ (hDpair n)
    fun U hU ↦ ⟨(hDsmall n U hU).1, (hDsmall n U hU).2.1⟩
  let anchor (n : ℕ) (U : D n) : K := (hDsmall n U.val U.property).2.1.choose
  let a (n : ℕ) (U : D n) : E := (toWeakSpace ℂ E).symm (anchor n U).val
  let B := ⋃ n : ℕ, range (a n)
  have hB : B.Countable := countable_iUnion fun n ↦ by
    let : Countable (D n) := hD n
    exact countable_range _
  let M := (Submodule.span ℂ B).topologicalClosure
  refine ⟨M, Submodule.isClosed_topologicalClosure _, hB.isSeparable.span.closure, ?_⟩
  intro x hx
  refine ⟨(toWeakSpace ℂ E).symm x, ?_, LinearEquiv.apply_symm_apply _ _⟩
  have hnear (n : ℕ) : (toWeakSpace ℂ E).symm x ∈ Metric.cthickening (ε n) (M : Set E) := by
    let T := toWeakSpace ℂ E '' Metric.cthickening (ε n) (M : Set E)
    have hT : IsClosed T := isClosed_weak_image_of_closed_convex Metric.isClosed_cthickening
      ((M.restrictScalars ℝ).convex.cthickening (ε n))
    have hsub : ⋃₀ D n ⊆ (Subtype.val : K → W) ⁻¹' T := by
      intro y hy
      obtain ⟨U, hU, hyU⟩ := mem_sUnion.1 hy
      let u : D n := ⟨U, hU⟩
      have ha : a n u ∈ M := Submodule.le_topologicalClosure _
        (Submodule.subset_span (mem_iUnion.2 ⟨n, mem_range_self u⟩))
      have hd := (hDsmall n U hU).2.2 y hyU (anchor n u) (hDsmall n U hU).2.1.choose_spec
      refine ⟨(toWeakSpace ℂ E).symm y.val,
        Metric.mem_cthickening_of_dist_le _ (a n u) _ _ ha hd.le,
        LinearEquiv.apply_symm_apply _ _⟩
    have hn : (⟨x, hx⟩ : K) ∈ (Subtype.val : K → W) ⁻¹' T :=
      closure_minimal hsub (hT.preimage continuous_subtype_val) ((hDdense n) ⟨x, hx⟩)
    obtain ⟨z, hz, hz'⟩ := hn
    change toWeakSpace ℂ E z = x at hz'
    rw [← hz', LinearEquiv.symm_apply_apply]
    exact hz
  change (toWeakSpace ℂ E).symm x ∈ (M : Set E)
  rw [← (Submodule.isClosed_topologicalClosure (Submodule.span ℂ B)).closure_eq,
    Metric.closure_eq_iInter_cthickening]
  refine mem_iInter.2 fun δ ↦ mem_iInter.2 fun hδ ↦ ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hle : ε n ≤ δ := by
    dsimp [ε]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    exact (div_le_iff₀ hden).2 (by nlinarith [(div_lt_iff₀ hδ).1 hn])
  exact Metric.cthickening_mono hle _ (hnear n)

/-- A weakly compact set with the countable chain condition has a first-countable
relative weak topology, even when the ambient space is nonseparable. -/
theorem firstCountableTopology_weakCompact_of_ccc {K : Set W} (hK : IsCompact K)
    (hccc : ∀ D : Set (Set K), D.Pairwise Disjoint →
      (∀ U ∈ D, IsOpen U ∧ U.Nonempty) → D.Countable) : FirstCountableTopology K := by
  obtain ⟨M, _, hM, hsub⟩ := exists_separable_closedSpan_of_weakCompact_ccc hK hccc
  let : SeparableSpace M := hM.separableSpace
  let : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨f, hf⟩ := exists_separating_dual_sequence (E := M)
  choose g hg _ using fun n ↦ exists_extension_norm_eq M (f n)
  let a (x : K) : M := ⟨(toWeakSpace ℂ E).symm x.val, by
    obtain ⟨v, hv, hveq⟩ := hsub x.property
    rw [← hveq, LinearEquiv.symm_apply_apply]
    exact hv⟩
  let eval (x : K) (n : ℕ) := g n ((toWeakSpace ℂ E).symm x.val)
  have hc : Continuous eval :=
    continuous_pi fun n ↦ (WeakBilin.eval_continuous (topDualPairing ℂ E).flip (g n)).comp
      continuous_subtype_val
  have hi : Function.Injective eval := by
    intro x y h
    apply Subtype.ext ((toWeakSpace ℂ E).symm.injective ?_)
    have h₁ : (fun n ↦ f n (a x)) = fun n ↦ f n (a y) := by
      funext n
      rw [← hg n (a x), ← hg n (a y)]
      exact congrFun h n
    exact congrArg (fun z : M ↦ (z : E)) (hf h₁)
  exact (hc.isClosedEmbedding hi).isEmbedding.firstCountableTopology

end JdLG
