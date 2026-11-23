/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleTopology
public import JdLG.UltrafilterMoreGroup
public import Mathlib.Data.Fintype.Card

/-!
# Difference-star return sets

The ultrafilter definition from Section 2.5.2 and the norm return
characterization in Theorem 5.3(iii), arXiv:2509.24003v3.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace JdLG

variable {S G : Type*} [Semigroup S] [Group G]

/-- A free ultrafilter contains every cofinite set. -/
def IsFreeUltrafilter (p : Ultrafilter S) : Prop := (p : Filter S) ≤ cofinite

private theorem free_mul_of_free_right {p q : Ultrafilter S} (hq : IsFreeUltrafilter q)
    (hCancel : ∀ s : S, Function.Injective (s * ·)) : IsFreeUltrafilter (p * q) := by
  intro A hA
  change ∀ᶠ z in ((p * q : Ultrafilter S) : Filter S), z ∈ A
  rw [Ultrafilter.eventually_mul]
  apply Filter.Eventually.of_forall
  intro s
  apply hq
  rw [mem_cofinite] at hA ⊢
  exact Set.Finite.preimage (hCancel s).injOn hA

private theorem free_mul_of_free_left {p q : Ultrafilter S} (hp : IsFreeUltrafilter p)
    (hLeft : ∀ s : S, Function.Injective (s * ·))
    (hRight : ∀ s : S, Function.Injective (· * s)) : IsFreeUltrafilter (p * q) := by
  rcases q.le_cofinite_or_eq_pure with hq | ⟨s, rfl⟩
  · exact free_mul_of_free_right hq hLeft
  intro A hA
  change ∀ᶠ z in ((p * pure s : Ultrafilter S) : Filter S), z ∈ A
  rw [Ultrafilter.eventually_mul]
  simp only [Ultrafilter.coe_pure, Filter.eventually_pure]
  apply hp
  rw [mem_cofinite] at hA ⊢
  exact Set.Finite.preimage (hRight s).injOn hA

/-- The smallest ideal of the Stone–Čech semigroup of an infinite cancellative
semigroup contains only free ultrafilters. -/
theorem free_of_mem_smallestIdeal_of_rightQuotients [Infinite S]
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) {p : Ultrafilter S}
    (hp : p ∈ smallestIdeal (Ultrafilter S)) : IsFreeUltrafilter p := by
  have hLeft (s : S) : Function.Injective (s * ·) := fun _ _ hab ↦
    hι.1 (mul_left_cancel (by simpa only [map_mul] using congrArg ι hab))
  have hRight (s : S) : Function.Injective (· * s) := fun _ _ hab ↦
    hι.1 (mul_right_cancel (by simpa only [map_mul] using congrArg ι hab))
  let B : Set (Ultrafilter S) := {p | IsFreeUltrafilter p}
  have hNonempty : B.Nonempty := ⟨hyperfilter S, hyperfilter_le_cofinite⟩
  have hIdeal : IsTwoSidedIdeal B :=
    ⟨fun _ _ hb ↦ free_mul_of_free_right hb hLeft,
      fun _ ha _ ↦ free_mul_of_free_left ha hLeft hRight⟩
  exact smallestIdeal_subset hNonempty hIdeal hp

@[simp]
theorem ultrafilter_mul_pure_one (p : Ultrafilter G) : p * (pure 1 : Ultrafilter G) = p := by
  apply Ultrafilter.coe_injective
  apply Filter.ext'
  intro P
  simp only [Ultrafilter.eventually_mul, Ultrafilter.coe_pure, Filter.eventually_pure, mul_one]

/-- The ordered product of the inverse-product factors in the ambient quotient group. -/
def ultrafilterDifferenceProduct (ι : S →ₙ* G) (ps : List (Ultrafilter S)) : Ultrafilter G :=
  ps.foldr (fun q z ↦ (ultrafilterInverse (q.map ι) * q.map ι) * z) (pure 1)

/-- The paper's `Δ^{ℓ*}` test in the group of right quotients. An ambient product is
tested just when it is the pushforward of a source ultrafilter. -/
def IsDeltaStar (ι : S →ₙ* G) (ℓ : ℕ) (A : Set S) : Prop :=
  ∀ ps : List (Ultrafilter S), ps.length = ℓ →
    (∀ p ∈ ps, IsFreeUltrafilter p) →
    ∀ r : Ultrafilter S, r.map ι = ultrafilterDifferenceProduct ι ps → A ∈ r

private theorem ultrafilterExtend_differenceProduct {K : Type*} [Group K]
    [TopologicalSpace K] [T2Space K] [CompactSpace K] [IsTopologicalGroup K]
    (F : G →* K) (ι : S →ₙ* G) (ps : List (Ultrafilter S)) :
    Ultrafilter.extend F (ultrafilterDifferenceProduct ι ps) = 1 := by
  induction ps with
  | nil =>
    change Ultrafilter.extend F (pure 1 : Ultrafilter G) = 1
    rw [ultrafilter_extend_pure, map_one]
  | cons p ps ih =>
    change Ultrafilter.extend F.toMulHom
      ((ultrafilterInverse (p.map ι) * p.map ι) * ultrafilterDifferenceProduct ι ps) = 1
    rw [ultrafilterExtend_mul continuous_const_mul continuous_mul_const F.toMulHom,
      ultrafilterExtend_mul continuous_const_mul continuous_mul_const F.toMulHom]
    change (Ultrafilter.extend F (ultrafilterInverse (p.map ι)) *
      Ultrafilter.extend F (p.map ι)) * Ultrafilter.extend F (ultrafilterDifferenceProduct ι ps) = 1
    rw [ultrafilterExtend_map_inv F continuous_inv, inv_mul_cancel, ih, mul_one]

section Returns

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Reversible vectors satisfy the `Δ^{ℓ*}` norm-return test. -/
theorem norm_return_isDeltaStar_of_reversible {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι)
    {x : E} (hx : IsReversible (closureAction π) x) (ℓ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IsDeltaStar ι ℓ {s | ‖x - π s x‖ < ε} := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  obtain ⟨F, hF⟩ := K.exists_ultrafilterExtend_rightFractionLift hπ hK hι
  intro ps _ _ p hp
  have hR : K.groupRetraction (Ultrafilter.extend (closureInclusion π) p) = 1 := by
    rw [hF, hp, ultrafilterExtend_differenceProduct]
  have hNorm := tendsto_normOrbit_of_precompact_of_weak (precompactOrbit_of_reversible hπ x hx)
    (K.reversible_tendsto_of_retraction_eq_one hπ hR hx)
  change ∀ᶠ s in (p : Filter S), ‖x - π s x‖ < ε
  simpa only [dist_comm, dist_eq_norm] using (Metric.tendsto_nhds.mp hNorm) ε hε

omit [CompleteSpace E] in
private theorem ultrafilterLimit_intoClosure_eq_of_wot_limit
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) (p : Ultrafilter S)
    {e : weakOperatorClosure π}
    (he : Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (e : E →WOT[𝕜] E))) :
    Ultrafilter.extend (closureInclusion π) p = e := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  have h := (continuous_subtype_val.tendsto _).comp
    (tendsto_ultrafilterExtend (closureInclusion π) p)
  exact Subtype.ext (tendsto_nhds_unique h he)

/-- Any positive number of copies of a single free smallest-ideal ultrafilter yields
a difference product converging to the JdLG projection. -/
theorem exists_replicate_differenceProduct_to_projection [Infinite S]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) (hK : IsCompact K.carrier)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) (n : ℕ) :
    ∃ q : Ultrafilter S, IsFreeUltrafilter q ∧ ∃ p : Ultrafilter S,
      p.map ι = ultrafilterDifferenceProduct ι (List.replicate (n + 1) q) ∧
      Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (K.identity : E →WOT[𝕜] E)) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  obtain ⟨q, hq, _⟩ := exists_idempotent_ultrafilter_in_smallestIdeal (S := S)
  obtain ⟨p, _, hp⟩ := inverse_product_mem_ultrafilterMap_closure_smallestIdeal hι
    (subset_closure hq) q
  have hLimit := K.tendsto_projection_of_inverse_product_smallestIdeal
    hπ hK continuous_inv hι (subset_closure hq) hp
  have hLimit' := ultrafilterLimit_intoClosure_eq_of_wot_limit hπ p hLimit
  refine ⟨q, free_of_mem_smallestIdeal_of_rightQuotients hι hq, ?_⟩
  induction n with
  | zero =>
    refine ⟨p, ?_, hLimit⟩
    simpa only [Nat.zero_add, List.replicate_one, ultrafilterDifferenceProduct, List.foldr_cons,
      List.foldr_nil, ultrafilter_mul_pure_one] using hp
  | succ n ih =>
    obtain ⟨r, hr, hR⟩ := ih
    refine ⟨p * r, ?_, ?_⟩
    · change p.map ι = _ at hp
      rw [ultrafilter_map_mul, hp, hr]
      simp only [List.replicate_succ, ultrafilterDifferenceProduct, List.foldr_cons]
    · have hR' := ultrafilterLimit_intoClosure_eq_of_wot_limit hπ r hR
      have hEq := ultrafilterExtend_mul continuous_const_mul continuous_mul_const
        (closureInclusion π) p r
      rw [hLimit', hR', K.identity_idempotent] at hEq
      have hProduct := tendsto_ultrafilterExtend (closureInclusion π) (p * r)
      rw [hEq] at hProduct
      exact (continuous_subtype_val.tendsto K.identity).comp hProduct

/-- Theorem 5.3(iii) on an infinite cancellative left reversible semigroup, using its
group of right quotients. The parameter `n + 1` is the positive number of factors. -/
theorem reversible_iff_norm_return_isDeltaStar_of_infinite [Infinite S]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) (n : ℕ) (x : E) :
    IsReversible (closureAction π) x ↔
      ∀ ε > (0 : ℝ), IsDeltaStar ι (n + 1) {s | ‖x - π s x‖ < ε} := by
  constructor
  · exact fun hx _ hε ↦ norm_return_isDeltaStar_of_reversible hπ hι hx (n + 1) hε
  · intro hx
    obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
    obtain ⟨q, hq, p, hp, hLim⟩ := exists_replicate_differenceProduct_to_projection hπ K hK hι n
    have hNorm : Tendsto (fun s ↦ π s x) (p : Filter S) (𝓝 x) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hp' := hx ε hε (List.replicate (n + 1) q) List.length_replicate
        (fun r hr ↦ (List.eq_of_mem_replicate hr).symm ▸ hq) p hp
      change ∀ᶠ s in (p : Filter S), ‖x - π s x‖ < ε at hp'
      simpa only [dist_comm, dist_eq_norm] using hp'
    let eval : (E →WOT[𝕜] E) → WeakSpace 𝕜 E := fun A ↦ toWeakSpace 𝕜 E (A x)
    have hEval : Continuous eval := WeakBilin.continuous_of_continuous_eval _ fun f ↦
      ContinuousLinearMapWOT.continuous_dual_apply x f
    have hWeak := (hEval.tendsto _).comp hLim
    exact (K.reversible_iff_fixed (closureAction π) x).mpr
      ((toWeakSpace 𝕜 E).injective
        (tendsto_nhds_unique hWeak (((toWeakSpaceCLM 𝕜 E).continuous.tendsto x).comp hNorm)))

/-- The unit convention for a semigroup representation in Section 2.4. On a semigroup
that has an identity, the representation sends it to the identity operator. -/
def PreservesIdentityWhenPresent (π : S →ₙ* (E →L[𝕜] E)) : Prop :=
  ∀ e : S, (∀ s : S, e * s = s ∧ s * e = s) → π e = 1

omit [CompleteSpace E] in
private theorem reversible_of_finite [Finite S] [Nonempty S]
    {π : S →ₙ* (E →L[𝕜] E)} (hUnit : PreservesIdentityWhenPresent π)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) (x : E) :
    IsReversible (closureAction π) x := by
  have hsurj (s : S) : Function.Surjective (s * ·) :=
    Finite.surjective_of_injective fun a b hab ↦
      hι.1 (mul_left_cancel (by simpa only [map_mul] using congrArg ι hab))
  obtain ⟨s₀⟩ := ‹Nonempty S›
  obtain ⟨e, he⟩ := hsurj s₀ s₀
  have he' : ι e = 1 := by
    have h := congrArg ι he
    rw [map_mul] at h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  have hUnits : ∀ s : S, e * s = s ∧ s * e = s := fun s ↦
    ⟨hι.1 (by rw [map_mul, he', one_mul]), hι.1 (by rw [map_mul, he', mul_one])⟩
  intro a
  have ha : (a : E →WOT[𝕜] E) ∈ range (weakRepresentation π) := by
    have h := a.property
    change (a : E →WOT[𝕜] E) ∈ closure (range (weakRepresentation π)) at h
    rwa [(Set.finite_range (weakRepresentation π)).isClosed.closure_eq] at h
  obtain ⟨s, hs⟩ := ha
  have ha' : closureInclusion π s = a := Subtype.ext hs
  obtain ⟨t, ht⟩ := hsurj s e
  change s * t = e at ht
  have ht' : t * s = e := by
    have hst : ι s * ι t = 1 := by rw [← map_mul, ht, he']
    apply hι.1
    rw [map_mul, he']
    exact mul_eq_one_iff_inv_eq.mp hst ▸ inv_mul_cancel (ι s)
  refine ⟨closureInclusion π t, ?_⟩
  rw [← ha']
  change (π t * π s) x = x
  rw [← map_mul, ht', hUnit e hUnits]
  rfl

/-- Theorem 5.3(iii). For a positive number of difference factors, the norm return
sets are difference-star exactly for reversible vectors. -/
theorem reversible_iff_norm_return_isDeltaStar [Nonempty S]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (hUnit : PreservesIdentityWhenPresent π)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) (n : ℕ) (x : E) :
    IsReversible (closureAction π) x ↔
      ∀ ε > (0 : ℝ), IsDeltaStar ι (n + 1) {s | ‖x - π s x‖ < ε} := by
  by_cases h : Finite S
  · let _ : Finite S := h
    exact ⟨fun hx _ hε ↦ norm_return_isDeltaStar_of_reversible hπ hι hx (n + 1) hε,
      fun _ ↦ reversible_of_finite hUnit hι x⟩
  · let _ : Infinite S := not_finite_iff_infinite.mp h
    exact reversible_iff_norm_return_isDeltaStar_of_infinite hπ hι n x

end Returns

end JdLG
