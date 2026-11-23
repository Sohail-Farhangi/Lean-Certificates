/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreIdeal
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.Rat.Lemmas

/-! # Thickness, smallest ideals, and density in the group of right quotients -/

public section

open Filter Set

namespace JdLG

variable {S G : Type*} [Semigroup S] [Group G]

/-- A group of right quotients contains the semigroup as a thick set. -/
theorem IsGroupOfRightQuotients.isThick_range {ι : S →ₙ* G} [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) : IsThick (range ι) := by
  classical
  have hAll (F : Finset G) : ∃ x : S, ∀ g ∈ F, g * ι x ∈ range ι := by
    induction F using Finset.induction_on with
    | empty => exact ⟨Classical.arbitrary S, by simp⟩
    | @insert g F _ ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨a, b, rfl⟩ := hι.2 g
      obtain ⟨u, v, huv⟩ := hι.isLeftReversible x b
      refine ⟨x * u, fun g hg ↦ ?_⟩
      rcases Finset.mem_insert.mp hg with rfl | hg
      · refine ⟨a * v, ?_⟩
        simp [huv, map_mul, mul_assoc]
      · obtain ⟨z, hz⟩ := hx g hg
        exact ⟨z * u, by rw [map_mul, map_mul, ← mul_assoc, hz]⟩
  intro F
  obtain ⟨x, hx⟩ := hAll F
  exact ⟨ι x, hx⟩

/-- In the ambient Stone–Čech space, the image of the source consists exactly of
ultrafilters containing the embedded semigroup. -/
theorem ultrafilterMap_range_eq {ι : S →ₙ* G} (hι : Function.Injective ι) :
    range (fun p : Ultrafilter S ↦ p.map ι) = {q | range ι ∈ q} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change ι ⁻¹' range ι ∈ q
    rw [preimage_range]
    exact Filter.univ_mem
  · intro hp
    exact ⟨p.comap hι hp, Ultrafilter.coe_injective (Filter.map_comap_of_mem hp)⟩

/-- The smallest ideal of the embedded Stone–Čech semigroup is its intersection
with the ambient smallest ideal. -/
theorem ultrafilterMap_smallestIdeal_eq_inter {ι : S →ₙ* G} [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) :
    (fun p : Ultrafilter S ↦ p.map ι) '' smallestIdeal (Ultrafilter S) =
      range (fun p : Ultrafilter S ↦ p.map ι) ∩ smallestIdeal (Ultrafilter G) := by
  let C := (fun p : Ultrafilter S ↦ p.map ι) '' smallestIdeal (Ultrafilter S)
  let P := (fun p : Ultrafilter S ↦ p.map ι) ⁻¹' smallestIdeal (Ultrafilter G)
  obtain ⟨e, he, _⟩ := exists_idempotent_ultrafilter_in_smallestIdeal (S := S)
  obtain ⟨k, hk, _⟩ := exists_idempotent_ultrafilter_in_smallestIdeal (S := G)
  have hP : P.Nonempty := by
    obtain ⟨r, _, hr⟩ := ultrafilter_image_smallestIdeal_isLeftIdeal hι k ⟨e, he, rfl⟩
    refine ⟨r, ?_⟩
    change r.map ι ∈ smallestIdeal (Ultrafilter G)
    change r.map ι = k * e.map ι at hr
    rw [hr]
    exact smallestIdeal_isTwoSidedIdeal.2 hk _
  have hIdealP : IsTwoSidedIdeal P := by
    constructor
    · intro a b hb
      change (a * b).map ι ∈ smallestIdeal (Ultrafilter G)
      rw [ultrafilter_map_mul]
      exact smallestIdeal_isTwoSidedIdeal.1 _ hb
    · intro a ha b
      change (a * b).map ι ∈ smallestIdeal (Ultrafilter G)
      rw [ultrafilter_map_mul]
      exact smallestIdeal_isTwoSidedIdeal.2 ha _
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, rfl⟩, smallestIdeal_subset hP hIdealP hp⟩
  · rintro ⟨⟨p, rfl⟩, hp⟩
    obtain ⟨L, _, hL, hLp⟩ := exists_compact_minimalLeftIdeal_of_mem_smallestIdeal
      Ultrafilter.continuous_mul_left hp
    have h₁ : e.map ι * p.map ι ∈ L := hL.2.1 _ hLp
    have h₂ : e.map ι * p.map ι ∈ C :=
      ⟨e * p, smallestIdeal_isTwoSidedIdeal.2 he _, ultrafilter_map_mul ι e p⟩
    obtain ⟨a, ha⟩ := (principal_eq_of_minimalLeftIdeal hL h₁).symm ▸ hLp
    rw [← ha]
    exact ultrafilter_image_smallestIdeal_isLeftIdeal hι a h₂

/-- The corresponding intersection identity for the closures of the smallest ideals. -/
theorem ultrafilterMap_closure_smallestIdeal_eq_inter {ι : S →ₙ* G} [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) :
    (fun p : Ultrafilter S ↦ p.map ι) '' closure (smallestIdeal (Ultrafilter S)) =
      range (fun p : Ultrafilter S ↦ p.map ι) ∩ closure (smallestIdeal (Ultrafilter G)) := by
  let f : Ultrafilter S → Ultrafilter G := fun p ↦ p.map ι
  have hf : Continuous f := continuous_ultrafilter_map ι
  have hR : IsClopen (range f) := by
    dsimp only [f]
    rw [ultrafilterMap_range_eq hι.1]
    exact ⟨ultrafilter_isClosed_basic (range ι), ultrafilter_isOpen_basic (range ι)⟩
  have himage : f '' closure (smallestIdeal (Ultrafilter S)) =
      closure (f '' smallestIdeal (Ultrafilter S)) :=
    subset_antisymm (image_closure_subset_closure_image hf)
      (closure_minimal (image_mono subset_closure) (isClosed_closure.isCompact.image hf).isClosed)
  change f '' closure (smallestIdeal (Ultrafilter S)) = _
  rw [himage, ultrafilterMap_smallestIdeal_eq_inter hι]
  refine subset_antisymm (closure_minimal (inter_subset_inter_right _ subset_closure)
      (hR.isClosed.inter isClosed_closure)) ?_
  intro p hp
  apply mem_closure_iff.mpr
  intro U hU hpU
  obtain ⟨y, hy, hyK⟩ := mem_closure_iff.mp hp.2 (U ∩ range f) (hU.inter hR.isOpen) ⟨hpU, hp.1⟩
  exact ⟨y, hy.1, hy.2, hyK⟩

/-- Left amenability implies left reversibility. -/
theorem leftReversible_of_leftInvariantSetMean (m : LeftInvariantSetMean S) :
    IsLeftReversible S := by
  intro a b
  have hrange (s : S) : m.mass (range (s * ·)) = 1 := by
    rw [← m.invariant s]
    simp [m.univ]
  have hNonempty : (range (a * ·) ∩ range (b * ·)).Nonempty := by
    by_contra h
    have hd : Disjoint (range (a * ·)) (range (b * ·)) :=
      Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp h)
    have hadd := m.add_disjoint hd
    have hBound := m.mass_mono (subset_univ (range (a * ·) ∪ range (b * ·)))
    rw [hrange, hrange] at hadd
    linarith [m.univ]
  obtain ⟨_, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hNonempty
  exact ⟨u, v, hu.trans hv.symm⟩

/-- A left invariant mean on the semigroup extends to the group of right
quotients by pulling back sets to the semigroup. -/
def LeftInvariantSetMean.extendRightQuotients {ι : S →ₙ* G} (m : LeftInvariantSetMean S)
    (hι : IsGroupOfRightQuotients ι) : LeftInvariantSetMean G where
  mass A := m.mass (ι ⁻¹' A)
  nonneg A := m.nonneg _
  empty := m.empty
  univ := m.univ
  add_disjoint h := m.add_disjoint (h.preimage ι)
  invariant g A := by
    let v (A : Set G) := m.mass (ι ⁻¹' A)
    have hl (s : S) (A : Set G) : v ((ι s * ·) ⁻¹' A) = v A := by
      have hpre : ι ⁻¹' ((ι s * ·) ⁻¹' A) = (s * ·) ⁻¹' (ι ⁻¹' A) := by
        ext a
        simp only [mem_preimage, map_mul]
      exact (congrArg m.mass hpre).trans (m.invariant s _)
    have hi (s : S) (A : Set G) : v (((ι s)⁻¹ * ·) ⁻¹' A) = v A := by
      have heq : (ι s * ·) ⁻¹' (((ι s)⁻¹ * ·) ⁻¹' A) = A := by
        ext a
        simp only [mem_preimage, inv_mul_cancel_left]
      have h := hl s (((ι s)⁻¹ * ·) ⁻¹' A)
      rw [heq] at h
      exact h.symm
    obtain ⟨a, b, rfl⟩ := hι.2 g
    change v ((ι a * (ι b)⁻¹ * ·) ⁻¹' A) = v A
    have heq : (ι a * (ι b)⁻¹ * ·) ⁻¹' A = ((ι b)⁻¹ * ·) ⁻¹' ((ι a * ·) ⁻¹' A) := by
      ext c
      simp only [mem_preimage, mul_assoc]
    rw [heq, hi, hl]

/-- Every embedded essential ultrafilter remains essential in the group of right quotients. -/
theorem ultrafilterMap_essentialUltrafilters_subset {ι : S →ₙ* G}
    (hι : IsGroupOfRightQuotients ι) :
    (fun p : Ultrafilter S ↦ p.map ι) '' essentialUltrafilters S ⊆ essentialUltrafilters G := by
  rintro _ ⟨p, hp, rfl⟩ A hA
  obtain ⟨m, hm⟩ := hp (ι ⁻¹' A) hA
  exact ⟨m.extendRightQuotients hι, hm⟩

/-- The nonnegative integers embed in their additive group of differences. -/
theorem nat_int_groupOfRightQuotients :
    IsGroupOfRightQuotients (Int.ofNatHom.toMultiplicative.toMulHom) := by
  constructor
  · intro a b hab
    change ((a.toAdd : ℕ) : ℤ) = ((b.toAdd : ℕ) : ℤ) at hab
    exact congrArg Multiplicative.ofAdd (Int.ofNat.inj hab)
  · intro g
    refine ⟨Multiplicative.ofAdd g.toAdd.toNat, Multiplicative.ofAdd (-g.toAdd).toNat, ?_⟩
    change g.toAdd = (g.toAdd.toNat : ℤ) + -(((-g.toAdd).toNat : ℕ) : ℤ)
    omega

/-- The nonzero integers form a multiplicative subsemigroup. -/
def nonzeroIntSemigroup : Subsemigroup ℤ where
  carrier := {x | x ≠ 0}
  mul_mem' := mul_ne_zero

/-- The canonical embedding of the nonzero integers into the nonzero rationals. -/
def nonzeroInt_to_ratUnits : nonzeroIntSemigroup →ₙ* ℚˣ where
  toFun a := Units.mk0 (((a : ℤ) : ℚ)) (by exact_mod_cast a.property)
  map_mul' a b := Units.ext (Int.cast_mul (a : ℤ) (b : ℤ))

/-- The nonzero rationals form the multiplicative group of right quotients of the
nonzero integers. -/
theorem nonzeroInt_rat_groupOfRightQuotients : IsGroupOfRightQuotients nonzeroInt_to_ratUnits := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have h := congrArg (fun q : ℚˣ ↦ (q : ℚ)) hab
    change ((a : ℤ) : ℚ) = ((b : ℤ) : ℚ) at h
    exact_mod_cast h
  · intro g
    have hnd : ((g : ℚ).num : ℚ) / ((g : ℚ).den : ℚ) = (g : ℚ) := Rat.num_div_den _
    have hn : (g : ℚ).num ≠ 0 := by
      intro h
      apply g.ne_zero
      rw [← hnd, h, Int.cast_zero, zero_div]
    have hd : ((g : ℚ).den : ℤ) ≠ 0 := by
      exact_mod_cast Rat.den_nz (g : ℚ)
    refine ⟨⟨(g : ℚ).num, hn⟩, ⟨(g : ℚ).den, hd⟩, ?_⟩
    apply Units.ext
    change (g : ℚ) = ((g : ℚ).num : ℚ) * ((((g : ℚ).den : ℕ) : ℤ) : ℚ)⁻¹
    rw [Int.cast_natCast, ← div_eq_mul_inv, hnd]

end JdLG
