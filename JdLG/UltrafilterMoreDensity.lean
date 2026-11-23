/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreStoneCech
public import Mathlib.Tactic.Linarith

/-!
# Essential ultrafilters on discrete semigroups

Upper Banach density is used here through positivity of a left invariant mean
on sets. The resulting essential ultrafilters form a closed two-sided ideal
and admit the inverse translates in the group of right quotients.
-/

@[expose] public section

open Filter Set

namespace JdLG

/-- A left invariant mean evaluated on indicator functions, in its finitely additive form. -/
structure LeftInvariantSetMean (S : Type*) [Semigroup S] where
  mass : Set S → ℝ
  nonneg (A : Set S) : 0 ≤ mass A
  empty : mass ∅ = 0
  univ : mass univ = 1
  add_disjoint {A B : Set S} (h : Disjoint A B) : mass (A ∪ B) = mass A + mass B
  invariant (s : S) (A : Set S) : mass ((s * ·) ⁻¹' A) = mass A

variable {S : Type*} [Semigroup S]

theorem LeftInvariantSetMean.mass_mono (m : LeftInvariantSetMean S) {A B : Set S}
    (h : A ⊆ B) : m.mass A ≤ m.mass B := by
  have hAdd := m.add_disjoint (disjoint_sdiff_right (s := A) (t := B))
  rw [union_sdiff_self, union_eq_right.mpr h] at hAdd
  linarith [m.nonneg (B \ A)]

theorem LeftInvariantSetMean.mass_compl (m : LeftInvariantSetMean S) (A : Set S) :
    m.mass Aᶜ = 1 - m.mass A := by
  have hAdd := m.add_disjoint (disjoint_compl_right : Disjoint A Aᶜ)
  rw [union_compl_self, m.univ] at hAdd
  linarith

theorem LeftInvariantSetMean.mass_union_le (m : LeftInvariantSetMean S) (A B : Set S) :
    m.mass (A ∪ B) ≤ m.mass A + m.mass B := by
  have hAdd := m.add_disjoint (disjoint_sdiff_right (s := A) (t := B))
  rw [union_sdiff_self] at hAdd
  rw [hAdd]
  exact add_le_add le_rfl (m.mass_mono sdiff_subset)

/-- Convolving on the right by an ultrafilter preserves left invariance. -/
def LeftInvariantSetMean.rightConvolve (m : LeftInvariantSetMean S) (p : Ultrafilter S) :
    LeftInvariantSetMean S where
  mass A := m.mass {s | (s * ·) ⁻¹' A ∈ p}
  nonneg _ := m.nonneg _
  empty := by simp [m.empty]
  univ := by
    have h : {s : S | (s * ·) ⁻¹' (Set.univ : Set S) ∈ p} = Set.univ := by
      ext s
      exact iff_true_intro (Filter.univ_mem (f := (p : Filter S)))
    rw [h, m.univ]
  add_disjoint := by
    intro A B hAB
    have hDisjoint : Disjoint {s | (s * ·) ⁻¹' A ∈ p} {s | (s * ·) ⁻¹' B ∈ p} := by
      apply Set.disjoint_left.mpr
      intro s hs ht
      have h := inter_mem hs ht
      rw [← preimage_inter, Set.disjoint_iff_inter_eq_empty.mp hAB, preimage_empty] at h
      exact p.empty_notMem h
    have hUnion : {s | (s * ·) ⁻¹' (A ∪ B) ∈ p} =
        {s | (s * ·) ⁻¹' A ∈ p} ∪ {s | (s * ·) ⁻¹' B ∈ p} := by
      ext s
      simp only [mem_ofPred_eq, mem_union, preimage_union, Ultrafilter.union_mem_iff]
    rw [hUnion, m.add_disjoint hDisjoint]
  invariant s A := by
    have h : {x | (x * ·) ⁻¹' ((s * ·) ⁻¹' A) ∈ p} =
        (s * ·) ⁻¹' {x | (x * ·) ⁻¹' A ∈ p} := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage]
      have heq : (x * ·) ⁻¹' ((s * ·) ⁻¹' A) = ((s * x) * ·) ⁻¹' A := by
        ext y
        simp only [mem_preimage, mul_assoc]
      rw [heq]
    rw [h, m.invariant]

/-- Positive upper Banach density in terms of an indicator mean. -/
def HasPositiveBanachDensity (A : Set S) : Prop :=
  ∃ m : LeftInvariantSetMean S, 0 < m.mass A

/-- The space `D*` of ultrafilters for which every member has positive upper Banach density. -/
def essentialUltrafilters (S : Type*) [Semigroup S] : Set (Ultrafilter S) :=
  {p | ∀ A ∈ p, HasPositiveBanachDensity A}

theorem mem_essentialUltrafilters_of_dominates (m : LeftInvariantSetMean S) {p : Ultrafilter S}
    (h : ∀ A : Set S, m.mass Aᶜ = 0 → A ∈ p) : p ∈ essentialUltrafilters S := by
  intro A hA
  refine ⟨m, ?_⟩
  by_contra hNot
  have hZero : m.mass A = 0 := le_antisymm (le_of_not_gt hNot) (m.nonneg A)
  exact (Ultrafilter.compl_mem_iff_notMem.mp (h Aᶜ (by rwa [compl_compl]))) hA

/-- Every left invariant mean on sets is positive on the members of some ultrafilter. -/
theorem essentialUltrafilters_nonempty (m : LeftInvariantSetMean S) :
    (essentialUltrafilters S).Nonempty := by
  let F : Filter S :=
    { sets := {A | m.mass Aᶜ = 0}
      univ_sets := by simp [m.empty]
      sets_of_superset := fun {A B} hA hAB ↦
        le_antisymm ((m.mass_mono (compl_subset_compl.mpr hAB)).trans_eq hA) (m.nonneg Bᶜ)
      inter_sets := fun {A B} hA hB ↦ by
        change m.mass (A ∩ B)ᶜ = 0
        rw [compl_inter]
        apply le_antisymm _ (m.nonneg (Aᶜ ∪ Bᶜ))
        exact (m.mass_union_le Aᶜ Bᶜ).trans_eq (by rw [hA, hB, add_zero]) }
  have hF : F.NeBot := by
    refine Filter.neBot_iff.mpr fun hb ↦ ?_
    have he := Filter.empty_mem_iff_bot.mpr hb
    change m.mass (∅ : Set S)ᶜ = 0 at he
    simp [m.univ] at he
  let p := @Ultrafilter.of S F hF
  exact ⟨p, mem_essentialUltrafilters_of_dominates m fun A hA ↦ Ultrafilter.of_le F hA⟩

theorem isClosed_essentialUltrafilters : IsClosed (essentialUltrafilters S) := by
  have hEq : essentialUltrafilters S = ⋂ A : {A : Set S // ¬ HasPositiveBanachDensity A},
      {p : Ultrafilter S | A.1 ∉ p} := by
    ext p
    simp only [essentialUltrafilters, mem_ofPred_eq, mem_iInter]
    constructor
    · exact fun h A hA ↦ A.2 (h A.1 hA)
    · exact fun h A hA ↦ by_contradiction fun hNot ↦ h ⟨A, hNot⟩ hA
  rw [hEq]
  exact isClosed_iInter fun A ↦ (ultrafilter_isOpen_basic A.1).isClosed_compl

/-- The essential ultrafilters are a two-sided ideal. -/
theorem essentialUltrafilters_isTwoSidedIdeal : IsTwoSidedIdeal (essentialUltrafilters S) := by
  constructor
  · intro q p hp A hA
    change (∀ᶠ z in ((q * p : Ultrafilter S) : Filter S), z ∈ A) at hA
    rw [Ultrafilter.eventually_mul] at hA
    obtain ⟨s, hs⟩ := hA.exists
    obtain ⟨m, hm⟩ := hp ((s * ·) ⁻¹' A) hs
    exact ⟨m, (m.invariant s A) ▸ hm⟩
  · intro p hp q A hA
    change (∀ᶠ z in ((p * q : Ultrafilter S) : Filter S), z ∈ A) at hA
    rw [Ultrafilter.eventually_mul] at hA
    obtain ⟨m, hm⟩ := hp {s | (s * ·) ⁻¹' A ∈ q} hA
    exact ⟨m.rightConvolve q, hm⟩

theorem closure_smallestIdeal_subset_essentialUltrafilters (m : LeftInvariantSetMean S) :
    closure (smallestIdeal (Ultrafilter S)) ⊆ essentialUltrafilters S :=
  closure_minimal (smallestIdeal_subset (essentialUltrafilters_nonempty m)
    essentialUltrafilters_isTwoSidedIdeal) isClosed_essentialUltrafilters

variable {G : Type*} [Group G] {ι : S →ₙ* G}

/-- Each principal left translation is onto the essential ultrafilters. -/
theorem principal_mul_surj_essentialUltrafilters (hι : Function.Injective ι)
    (s : S) {p : Ultrafilter S} (hp : p ∈ essentialUltrafilters S) :
    ∃ q ∈ essentialUltrafilters S, (pure s : Ultrafilter S) * q = p := by
  have hInject : Function.Injective (s * ·) := by
    intro a b hab
    apply hι
    exact mul_left_cancel (by simpa only [map_mul] using congrArg ι hab)
  have hLarge : range (s * ·) ∈ p := by
    by_contra hNot
    obtain ⟨m, hm⟩ := hp (range (s * ·))ᶜ (Ultrafilter.compl_mem_iff_notMem.mpr hNot)
    have hRange : m.mass (range (s * ·)) = 1 := by
      rw [← m.invariant s]
      simp [m.univ]
    rw [m.mass_compl, hRange, sub_self] at hm
    exact lt_irrefl _ hm
  let q := p.comap hInject hLarge
  refine ⟨q, ?_, ?_⟩
  · intro A hA
    obtain ⟨m, hm⟩ := hp ((s * ·) '' A) ((p.mem_comap hInject hLarge).mp hA)
    rw [← m.invariant s, preimage_image_eq _ hInject] at hm
    exact ⟨m, hm⟩
  · rw [pure_mul_as_map]
    exact Ultrafilter.coe_injective (Filter.map_comap_of_mem hLarge)

/-- The inverse translates of essential ultrafilters used in Theorem 5.2(iv) remain in `D*`. -/
theorem inverse_product_mem_ultrafilterMap_essentialUltrafilters
    (hι : Function.Injective ι) {p : Ultrafilter S} (hp : p ∈ essentialUltrafilters S)
    (q : Ultrafilter S) :
    ultrafilterInverse (q.map ι) * p.map ι ∈
      (fun r : Ultrafilter S ↦ r.map ι) '' essentialUltrafilters S :=
  inverse_product_mem_ultrafilterMap_of_surj_principal ι isClosed_essentialUltrafilters
    (fun s _ hs ↦ principal_mul_surj_essentialUltrafilters hι s hs) hp q

end JdLG
