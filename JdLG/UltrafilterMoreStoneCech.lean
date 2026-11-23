/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreFractions
public import JdLG.Ultrafilters

/-!
# Inverse translates in the Stone–Čech compactification

The map into the Stone–Čech semigroup of a group of right quotients and
the inverse-translate property of the closure of the smallest ideal.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace JdLG

variable {S T G : Type*}

/-- Ultrafilter pushforward is continuous for the Stone–Čech topologies of discrete sets. -/
theorem continuous_ultrafilter_map (f : S → T) :
    Continuous (fun p : Ultrafilter S ↦ p.map f) :=
  ultrafilterBasis_is_basis.continuous_iff.2 <|
    Set.forall_mem_range.mpr fun A ↦ ultrafilter_isOpen_basic (f ⁻¹' A)

/-- Pushforward along an injective map is injective on ultrafilters. -/
theorem ultrafilter_map_injective {f : S → T} (hf : Function.Injective f) :
    Function.Injective (fun p : Ultrafilter S ↦ p.map f) := by
  intro p q hpq
  apply Ultrafilter.coe_injective
  exact Filter.map_injective hf (congrArg (·.toFilter) hpq)

theorem ultrafilter_map_mul [Semigroup S] [Semigroup T] (f : S →ₙ* T) (p q : Ultrafilter S) :
    (p * q).map f = p.map f * q.map f := by
  apply Ultrafilter.coe_injective
  apply Filter.ext'
  intro P
  simp only [Ultrafilter.coe_map, Filter.eventually_map, Ultrafilter.eventually_mul, map_mul]

theorem pure_mul_as_map [Semigroup S] (s : S) (p : Ultrafilter S) :
    (pure s : Ultrafilter S) * p = p.map (s * ·) := by
  apply Ultrafilter.coe_injective
  apply Filter.ext'
  intro P
  simp only [Ultrafilter.eventually_mul, Ultrafilter.coe_pure, Filter.eventually_pure,
    Ultrafilter.coe_map, Filter.eventually_map]

/-- Every point of the smallest ideal has a right identity in that ideal. -/
theorem exists_idempotent_right_identity_of_mem_smallestIdeal
    [Semigroup T] [Nonempty T] [TopologicalSpace T] [T2Space T] [CompactSpace T]
    (continuousRight : ∀ b : T, Continuous (· * b)) {p : T} (hp : p ∈ smallestIdeal T) :
    ∃ e ∈ smallestIdeal T, e * e = e ∧ p * e = p := by
  obtain ⟨L, hCompact, hL, hpL⟩ :=
    exists_compact_minimalLeftIdeal_of_mem_smallestIdeal continuousRight hp
  obtain ⟨e, he, hee⟩ := exists_idempotent_in_compact_subsemigroup continuousRight
    L hL.1 hCompact fun a _ _ hb ↦ hL.2.1 a hb
  have hRange := principal_eq_of_minimalLeftIdeal hL he
  obtain ⟨a, ha⟩ := hRange.symm ▸ hpL
  refine ⟨e, minimalLeftIdeal_subset_smallestIdeal hL he, hee, ?_⟩
  rw [← ha, mul_assoc, hee]

section InverseTranslate

variable [Semigroup S] [Group G] {ι : S →ₙ* G}

/-- The inverse map on the group induces this map on its ultrafilters. -/
def ultrafilterInverse (p : Ultrafilter G) : Ultrafilter G := p.map Inv.inv

private theorem pure_inv_mul_mapped_pure_mul (ι : S →ₙ* G) (s : S) (q : Ultrafilter S) :
    (pure (ι s)⁻¹ : Ultrafilter G) * (((pure s : Ultrafilter S) * q).map ι) = q.map ι := by
  rw [pure_mul_as_map, pure_mul_as_map, Ultrafilter.map_map, Ultrafilter.map_map]
  congr 1
  funext z
  simp only [Function.comp_apply, map_mul, inv_mul_cancel_left]

/-- If a compact family of source ultrafilters admits preimages under every principal left
translation, the family embedded in the quotient group is closed under the inverse left
translates used in Section 2.5.2. -/
theorem inverse_product_mem_ultrafilterMap_of_surj_principal
    (ι : S →ₙ* G) {B : Set (Ultrafilter S)} (hB : IsClosed B)
    (hSurj : ∀ s : S, ∀ p ∈ B, ∃ r ∈ B, (pure s : Ultrafilter S) * r = p)
    {p : Ultrafilter S} (hp : p ∈ B) (q : Ultrafilter S) :
    ultrafilterInverse (q.map ι) * p.map ι ∈ (fun r : Ultrafilter S ↦ r.map ι) '' B := by
  let C := (fun r : Ultrafilter S ↦ r.map ι) '' B
  have hC : IsClosed C := (hB.isCompact.image (continuous_ultrafilter_map ι)).isClosed
  let f : Ultrafilter S → Ultrafilter G :=
    fun r ↦ ultrafilterInverse (r.map ι) * p.map ι
  have hf : Continuous f := (Ultrafilter.continuous_mul_left (p.map ι)).comp
    ((continuous_ultrafilter_map Inv.inv).comp (continuous_ultrafilter_map ι))
  have hDense : range (pure : S → Ultrafilter S) ⊆ f ⁻¹' C := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨r, hr, hsr⟩ := hSurj s p hp
    refine ⟨r, hr, ?_⟩
    change r.map ι = ultrafilterInverse ((pure s : Ultrafilter S).map ι) * p.map ι
    rw [← hsr, ultrafilterInverse, Ultrafilter.map_pure, Ultrafilter.map_pure]
    exact (pure_inv_mul_mapped_pure_mul ι s r).symm
  exact closure_minimal hDense (hC.preimage hf) (denseRange_pure q)

private theorem principal_mul_preimage_smallestIdeal [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) (s : S) {p : Ultrafilter S}
    (hp : p ∈ smallestIdeal (Ultrafilter S)) :
    ∃ q ∈ smallestIdeal (Ultrafilter S), (pure s : Ultrafilter S) * q = p := by
  have hLarge : range (s * ·) ∈ p :=
    isThicklySyndetic_iff_forall_mem_closure_smallestIdeal.mp
      (thicklySyndetic_principal_right_ideal hι.isLeftReversible s) p (subset_closure hp)
  have hInject : Function.Injective (s * ·) := by
    intro a b hab
    apply hι.1
    exact mul_left_cancel (by simpa only [map_mul] using congrArg ι hab)
  let q := p.comap hInject hLarge
  have hMul : (pure s : Ultrafilter S) * q = p := by
    rw [pure_mul_as_map]
    exact Ultrafilter.coe_injective (Filter.map_comap_of_mem hLarge)
  obtain ⟨e, he, _, hpe⟩ :=
    exists_idempotent_right_identity_of_mem_smallestIdeal Ultrafilter.continuous_mul_left hp
  have hqe : q * e = q := by
    apply ultrafilter_map_injective hInject
    have hMul' : (pure s : Ultrafilter S) * (q * e) = (pure s : Ultrafilter S) * q := by
      rw [← mul_assoc, hMul, hpe]
    simpa only [pure_mul_as_map] using hMul'
  refine ⟨q, ?_, hMul⟩
  rw [← hqe]
  exact (smallestIdeal_isTwoSidedIdeal (M := Ultrafilter S)).1 q he

/-- Principal left multiplication preserves surjectivity on the closure of the smallest ideal
of the Stone–Čech semigroup of a semigroup embedded in its group of right quotients. -/
theorem principal_mul_surj_closure_smallestIdeal [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) (s : S) {p : Ultrafilter S}
    (hp : p ∈ closure (smallestIdeal (Ultrafilter S))) :
    ∃ q ∈ closure (smallestIdeal (Ultrafilter S)), (pure s : Ultrafilter S) * q = p := by
  let C := closure (smallestIdeal (Ultrafilter S))
  let L := fun q : Ultrafilter S ↦ (pure s : Ultrafilter S) * q
  have hL : Continuous L := by
    simpa only [L, pure_mul_as_map] using continuous_ultrafilter_map (s * ·)
  have hClosed : IsClosed (L '' C) := (isClosed_closure.isCompact.image hL).isClosed
  have hSubset : smallestIdeal (Ultrafilter S) ⊆ L '' C := by
    intro a ha
    obtain ⟨q, hq, hqa⟩ := principal_mul_preimage_smallestIdeal hι s ha
    exact ⟨q, subset_closure hq, hqa⟩
  exact closure_minimal hSubset hClosed hp

/-- The inverse-translate property used in Theorem 5.2(iii). In the quotient group,
`q⁻¹ * p` still belongs to the embedded closure of the smallest ideal. -/
theorem inverse_product_mem_ultrafilterMap_closure_smallestIdeal [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) {p : Ultrafilter S}
    (hp : p ∈ closure (smallestIdeal (Ultrafilter S))) (q : Ultrafilter S) :
    ultrafilterInverse (q.map ι) * p.map ι ∈ (fun r : Ultrafilter S ↦ r.map ι) ''
      closure (smallestIdeal (Ultrafilter S)) :=
  inverse_product_mem_ultrafilterMap_of_surj_principal ι isClosed_closure
    (fun s _ hs ↦ principal_mul_surj_closure_smallestIdeal hι s hs) hp q

end InverseTranslate

end JdLG
