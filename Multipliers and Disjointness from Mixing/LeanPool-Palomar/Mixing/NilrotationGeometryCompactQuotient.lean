/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.LocalAtTarget

/-! # Compact quotients represented by closed saturated subsets -/

@[expose] public section
noncomputable section

namespace Mixing

open Set Topology
open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nilrotation_quotient_preimage_subgroup_image (H L : Subgroup G) (hL : L ≤ H) :
    QuotientGroup.mk ⁻¹' (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ L)) = (H : Set G) := by
  rw [QuotientGroup.preimage_image_mk_eq_mul]
  ext g
  constructor
  · rintro ⟨h, hH, l, hL', rfl⟩
    exact H.mul_mem hH (hL hL')
  · intro hg
    exact ⟨g, hg, 1, L.one_mem, mul_one g⟩

/-- The quotient by the restricted subgroup is the corresponding closed saturated
subspace of the larger quotient. -/
noncomputable def subgroupQuotientHomeomorph (H L : Subgroup G) (hL : L ≤ H) :
    H ⧸ L.subgroupOf H ≃ₜ (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ L)) := by
  let Q : Set (G ⧸ L) := QuotientGroup.mk '' (H : Set G)
  let F (h : H) : Q := ⟨QuotientGroup.mk (h : G), mem_image_of_mem _ h.2⟩
  let q : H → H ⧸ L.subgroupOf H := QuotientGroup.mk
  let ePreimage : H ≃ₜ (QuotientGroup.mk ⁻¹' Q : Set G) :=
    Homeomorph.setCongr (nilrotation_quotient_preimage_subgroup_image H L hL).symm
  have hF : IsOpenQuotientMap F := by
    have hQ := (QuotientGroup.isOpenQuotientMap_mk (N := L)).restrictPreimage Q
    have he : F = (Q.restrictPreimage QuotientGroup.mk) ∘ ePreimage := by
      funext h
      apply Subtype.ext
      rfl
    rw [he]
    exact ⟨hQ.surjective.comp ePreimage.surjective, hQ.continuous.comp ePreimage.continuous,
      hQ.isOpenMap.comp ePreimage.isOpenMap⟩
  let f : H ⧸ L.subgroupOf H → Q :=
    Quotient.lift F fun h k hk ↦ by
      apply Subtype.ext
      have he : h⁻¹ * k ∈ L.subgroupOf H := QuotientGroup.leftRel_apply.mp hk
      exact QuotientGroup.eq.mpr he
  have hfEval (h : H) : f (q h) = F h := rfl
  have hfBij : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      change f (q x) = f (q y) at hxy
      rw [hfEval, hfEval] at hxy
      apply QuotientGroup.eq.mpr
      change (x : G)⁻¹ * (y : G) ∈ L
      have he : (QuotientGroup.mk (x : G) : G ⧸ L) = QuotientGroup.mk (y : G) :=
        congrArg Subtype.val hxy
      exact QuotientGroup.eq.mp he
    · intro y
      obtain ⟨h, rfl⟩ := hF.surjective y
      exact ⟨q h, hfEval h⟩
  have hOpenQ : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have hcont : Continuous f := hOpenQ.continuous_comp_iff.mp hF.continuous
  have hopen : IsOpenMap f := by
    intro U hU
    have he : f '' U = F '' (q ⁻¹' U) := by
      calc
        _ = f '' (q '' (q ⁻¹' U)) := by rw [image_preimage_eq U hOpenQ.surjective]
        _ = _ := by rw [image_image]; rfl
    rw [he]
    exact hF.isOpenMap _ (hOpenQ.continuous.isOpen_preimage _ hU)
  exact (Equiv.ofBijective f hfBij).toHomeomorphOfContinuousOpen hcont hopen

theorem compactSpace_subgroup_quotient_of_closed (H L : Subgroup G)
    (hL : L ≤ H) (hH : IsClosed (H : Set G)) [CompactSpace (G ⧸ L)] :
    CompactSpace (H ⧸ L.subgroupOf H) := by
  have hQ : IsClosed (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ L)) := by
    apply (QuotientGroup.isQuotientMap_mk L).isClosed_preimage.mp
    rw [nilrotation_quotient_preimage_subgroup_image H L hL]
    exact hH
  let : CompactSpace (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ L)) :=
    isCompact_iff_compactSpace.mp hQ.isCompact
  exact (subgroupQuotientHomeomorph H L hL).symm.compactSpace

end Mixing
