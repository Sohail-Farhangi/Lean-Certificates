/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleTopology
public import JdLG.UltrafilterMoreGroup
public import JdLG.UltrafilterMoreDensity

/-!
# Reversible IP-star returns and difference-product projection limits

The norm IP-star characterization, Lemma 5.1(ii), and Theorem 5.2(iii)
of Barthmann, Farhangi and Kuznetsova, arXiv:2509.24003v3.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace JdLG

variable {S G 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Theorem 5.3(i). A vector is reversible exactly when all its norm return sets
are IP-star. -/
theorem reversible_iff_norm_return_isIPStar [Nonempty S]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) (x : E) :
    IsReversible (closureAction π) x ↔
      ∀ ε > (0 : ℝ), IsIPStar {s | ‖x - π s x‖ < ε} := by
  refine ⟨fun hx ε hε ↦ ?_, reversible_of_norm_return_isIPStar hπ⟩
  exact norm_return_isIPStar_of_reversible_of_precompact hπ hx
    (precompactOrbit_of_reversible hπ x hx) hε

/-- Lemma 5.1(ii). When `p` in the source Stone–Čech semigroup is the product
`q⁻¹q` in the ambient group of right quotients, it fixes reversible vectors. -/
theorem reversible_tendsto_of_inverse_product [Group G]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) {p q : Ultrafilter S}
    (hp : p.map ι = ultrafilterInverse (q.map ι) * q.map ι)
    {x : E} (hx : IsReversible (closureAction π) x) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 (toWeakSpace 𝕜 E x)) := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  exact K.reversible_tendsto_of_inverse_product hπ hK continuous_inv hι hp hx

/-- Theorem 5.2(iii). A difference product of an ultrafilter in the closed
smallest ideal converges to the canonical JdLG projection. -/
theorem ultrafilter_limit_eq_jdlg_projection_of_inverse_product [Group G] [Nonempty S]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) :
    ∃ e : weakOperatorClosure π, IsMinimalIdempotent e ∧
      (∀ p q : Ultrafilter S, q ∈ closure (smallestIdeal (Ultrafilter S)) →
        p.map ι = ultrafilterInverse (q.map ι) * q.map ι →
        Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (e : E →WOT[𝕜] E))) ∧
      (∀ x : E, IsReversible (closureAction π) x ↔
        x ∈ LinearMap.range (closureAction π e).toLinearMap) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        x ∈ LinearMap.ker (closureAction π e).toLinearMap := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  refine ⟨K.identity, K.isMinimalIdempotent_identity, ?_, K.reversible_iff_mem_range _,
    K.stable_iff_mem_ker _⟩
  intro p q hq hp
  exact K.tendsto_projection_of_inverse_product_smallestIdeal hπ hK continuous_inv hι hq hp

/-- The bad sets for a vector have zero upper Banach density in every weak neighborhood
test. This is the density input used in Lemma 5.1(iv). -/
def WeakBadSetsMeanZero (π : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  ∀ U : Set (WeakSpace 𝕜 E), IsOpen U → (0 : WeakSpace 𝕜 E) ∈ U →
    ∀ m : LeftInvariantSetMean S, m.mass {s | toWeakSpace 𝕜 E (π s x) ∉ U} = 0

omit [CompleteSpace E] in
/-- The implication of Lemma 5.1(iv) from its upper Banach density input. -/
theorem weak_tendsto_zero_of_essential_of_badSetsMeanZero
    {π : S →ₙ* (E →L[𝕜] E)} {x : E} (hx : WeakBadSetsMeanZero π x)
    {p : Ultrafilter S} (hp : p ∈ essentialUltrafilters S) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hV, h0⟩ := mem_nhds_iff.mp hU
  have hGood : {s | toWeakSpace 𝕜 E (π s x) ∈ V} ∈ p := by
    by_contra hNot
    obtain ⟨m, hm⟩ := hp _ (Ultrafilter.compl_mem_iff_notMem.mpr hNot)
    change 0 < m.mass {s | toWeakSpace 𝕜 E (π s x) ∉ V} at hm
    rw [hx V hV h0 m] at hm
    exact (lt_irrefl 0) hm
  exact mem_of_superset hGood fun _ hs ↦ hVU hs

omit [CompleteSpace E] in
private theorem tendsto_projection_of_split_limits
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) (p : Ultrafilter S)
    (hRev : ∀ x : E, IsReversible (closureAction π) x →
      Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 (toWeakSpace 𝕜 E x)))
    (hStable : ∀ x : E, IsAlmostWeaklyStable (closureAction π) x →
      Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 0)) :
    Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (K.identity : E →WOT[𝕜] E)) := by
  let a := Ultrafilter.extend (closureInclusion π) p
  let P := K.projection (closureAction π)
  have hPoint (x : E) : closureAction π a x = P x := by
    let y := x - P x
    have hfixed : IsReversible (closureAction π) (P x) :=
      (K.reversible_iff_fixed (closureAction π) (P x)).mpr
        (K.projection_apply_apply (closureAction π) x)
    have hZero : P y = 0 := by
      change P (x - P x) = 0
      rw [map_sub, K.projection_apply_apply (closureAction π) x, sub_self]
    have hstable := (K.stable_iff_projection_eq_zero (closureAction π) y).2 hZero
    have hAx : closureAction π a (P x) = P x := (toWeakSpace 𝕜 E).injective
      (tendsto_nhds_unique (tendsto_weakOrbit_ultrafilterExtend hπ p (P x)) (hRev _ hfixed))
    have hAy : closureAction π a y = 0 := by
      apply (toWeakSpace 𝕜 E).injective
      rw [map_zero]
      exact tendsto_nhds_unique (tendsto_weakOrbit_ultrafilterExtend hπ p y) (hStable _ hstable)
    calc
      closureAction π a x = closureAction π a (y + P x) := by rw [show y + P x = x from
        sub_add_cancel x (P x)]
      _ = P x := by rw [map_add, hAx, hAy, zero_add]
  have he : a = K.identity := Subtype.ext <| ContinuousLinearMapWOT.ext hPoint
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  have hLimit := tendsto_ultrafilterExtend (closureInclusion π) p
  change Tendsto _ _ (𝓝 a) at hLimit
  rw [he] at hLimit
  exact (continuous_subtype_val.tendsto K.identity).comp hLimit

omit [CompleteSpace E] in
/-- Theorem 5.2(ii) from mean-zero bad sets for almost weakly stable vectors. -/
theorem GroupIdeal.tendsto_projection_of_essential_idempotent_of_badSetsMeanZero
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π))
    (hZero : ∀ x : E, IsAlmostWeaklyStable (closureAction π) x → WeakBadSetsMeanZero π x)
    {p : Ultrafilter S} (hp : p ∈ essentialUltrafilters S) (hpp : p * p = p) :
    Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (K.identity : E →WOT[𝕜] E)) :=
  tendsto_projection_of_split_limits hπ K p (fun _ hx ↦ reversible_tendsto_of_idempotent hπ hx hpp)
    (fun x hx ↦ weak_tendsto_zero_of_essential_of_badSetsMeanZero (hZero x hx) hp)

/-- Theorem 5.2(iv) from mean-zero bad sets for almost weakly stable vectors. -/
theorem GroupIdeal.tendsto_projection_of_inverse_product_essential_of_badSetsMeanZero [Group G]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π))
    (hZero : ∀ x : E, IsAlmostWeaklyStable (closureAction π) x → WeakBadSetsMeanZero π x)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) {p q : Ultrafilter S}
    (hq : q ∈ essentialUltrafilters S)
    (hp : p.map ι = ultrafilterInverse (q.map ι) * q.map ι) :
    Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (K.identity : E →WOT[𝕜] E)) := by
  obtain ⟨r, hr, heq⟩ := inverse_product_mem_ultrafilterMap_essentialUltrafilters hι.1 hq q
  have hrp : r = p := ultrafilter_map_injective hι.1 (heq.trans hp.symm)
  exact tendsto_projection_of_split_limits hπ K p
    (fun _ hx ↦ JdLG.reversible_tendsto_of_inverse_product hπ hι hp hx)
    (fun x hx ↦ weak_tendsto_zero_of_essential_of_badSetsMeanZero (hZero x hx) (hrp ▸ hr))

end JdLG
