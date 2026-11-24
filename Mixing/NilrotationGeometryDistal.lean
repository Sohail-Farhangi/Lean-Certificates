/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationGeometryConnectivity
public import Mixing.NilrotationGeometryVerticalGroup
public import Mathlib.Topology.Algebra.ProperAction.Basic

/-! # Distality of nilpotent homogeneous actions -/

@[expose] public section
noncomputable section

namespace Mixing

open Filter Set
open scoped Topology commutatorElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The closed subgroup defining a level of the nilpotent quotient tower. -/
def nilrotationClosedLayer (L : Subgroup G) (n : ℕ) : Subgroup G :=
  ((⊤ : Subgroup G).lowerCentralSeries n ⊔ L).topologicalClosure

theorem nilrotationClosedLayer_succ_le (L : Subgroup G) (n : ℕ) :
    nilrotationClosedLayer L (n + 1) ≤ nilrotationClosedLayer L n :=
  Subgroup.topologicalClosure_mono (sup_le_sup_right
    (Subgroup.lowerCentralSeries_antitone (H := ⊤) (Nat.le_succ n)) _)

/-- Each upstairs stabilizer is normal in the next coarser stabilizer. -/
theorem nilrotationClosedLayer_le_normalizer (L : Subgroup G) (n : ℕ) :
    nilrotationClosedLayer L n ≤ Subgroup.normalizer (nilrotationClosedLayer L (n + 1) : Set G) := by
  apply Subgroup.topologicalClosure_minimal
  · apply sup_le
    · rw [Subgroup.le_normalizer_iff_commutator_le_right]
      exact (Subgroup.commutator_mono_right le_top).trans
        ((show (⊤ : Subgroup G).lowerCentralSeries (n + 1) ≤
          (⊤ : Subgroup G).lowerCentralSeries (n + 1) ⊔ L from le_sup_left).trans
            (Subgroup.le_topologicalClosure _))
    · exact (le_sup_right.trans (Subgroup.le_topologicalClosure _)).trans Subgroup.le_normalizer
  · exact nilrotation_closed_normalizer _ (Subgroup.isClosed_topologicalClosure _)

/-- Right translation by a normalizer element on a homogeneous quotient. -/
def nilrotationNormalizerRightTranslate (L : Subgroup G) (b : Subgroup.normalizer (L : Set G)) :
    G ⧸ L → G ⧸ L :=
  Quotient.map' (fun x : G ↦ x * (b : G)) fun x y h ↦ by
    apply QuotientGroup.leftRel_apply.mpr
    have he : (x * (b : G))⁻¹ * (y * (b : G)) = (b : G)⁻¹ * (x⁻¹ * y) * (b : G) := by group
    rw [he]
    exact (Subgroup.mem_normalizer_iff''.mp b.2 _).mp (QuotientGroup.leftRel_apply.mp h)

theorem nilrotationNormalizerRightTranslate_continuous (L : Subgroup G)
    (b : Subgroup.normalizer (L : Set G)) :
    Continuous (nilrotationNormalizerRightTranslate L b) := by
  rw [← (QuotientGroup.isOpenQuotientMap_mk (N := L)).continuous_comp_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nilrotationNormalizerRightTranslate_smul (L : Subgroup G)
    (b : Subgroup.normalizer (L : Set G))
    (g : G) (x : G ⧸ L) :
    nilrotationNormalizerRightTranslate L b (g • x) = g • nilrotationNormalizerRightTranslate L b x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  change QuotientGroup.mk (g * x * (b : G)) = (QuotientGroup.mk (g * (x * (b : G))) : G ⧸ L)
  rw [mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nilrotationNormalizerRightTranslate_fixed (L : Subgroup G)
    (b : Subgroup.normalizer (L : Set G))
    (x : G ⧸ L) (hx : nilrotationNormalizerRightTranslate L b x = x) :
    (b : G) ∈ L := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  have hx' : (QuotientGroup.mk x : G ⧸ L) = QuotientGroup.mk (x * (b : G)) := hx.symm
  have hm := QuotientGroup.eq.mp hx'
  rwa [← mul_assoc, inv_mul_cancel, one_mul] at hm

private theorem nilrotationClosedLayer_fibre_eq (L : Subgroup G) (n : ℕ)
    {I : Type*} (t : I → G) {l : Filter I} [l.NeBot] :
    ∀ (x y z : G ⧸ nilrotationClosedLayer L n),
      Tendsto (fun i ↦ t i • x) l (𝓝 z) → Tendsto (fun i ↦ t i • y) l (𝓝 z) → x = y := by
  induction n with
  | zero =>
    intro x y _ _ _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    apply QuotientGroup.eq.mpr
    change x⁻¹ * y ∈ ((⊤ : Subgroup G) ⊔ L).topologicalClosure
    rw [top_sup_eq]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_top _)
  | succ n ih =>
    let H := nilrotationClosedLayer L (n + 1)
    let B := nilrotationClosedLayer L n
    let p : G ⧸ H → G ⧸ B := Subgroup.quotientMapOfLE (nilrotationClosedLayer_succ_le L n)
    have hp : Continuous p := by
      rw [← (QuotientGroup.isOpenQuotientMap_mk (N := H)).continuous_comp_iff]
      exact QuotientGroup.continuous_mk
    have hact (g : G) (q : G ⧸ H) : p (g • q) = g • p q := by
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
      rfl
    intro x y z hx hy
    have hb : p x = p y := ih (p x) (p y) (p z)
      (((hp.tendsto z).comp hx).congr fun i ↦ hact _ _)
      (((hp.tendsto z).comp hy).congr fun i ↦ hact _ _)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have hxy : x⁻¹ * y ∈ B := QuotientGroup.eq.mp hb
    let b : Subgroup.normalizer (H : Set G) :=
      ⟨x⁻¹ * y, nilrotationClosedLayer_le_normalizer L n hxy⟩
    have htrans : nilrotationNormalizerRightTranslate H b (QuotientGroup.mk x) =
        QuotientGroup.mk y := by
      change QuotientGroup.mk (x * (x⁻¹ * y)) = (QuotientGroup.mk y : G ⧸ H)
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hy' : Tendsto (fun i ↦ t i • (QuotientGroup.mk y : G ⧸ H)) l
        (𝓝 (nilrotationNormalizerRightTranslate H b z)) :=
      (((nilrotationNormalizerRightTranslate_continuous H b).tendsto z).comp hx).congr fun i ↦ by
        change nilrotationNormalizerRightTranslate H b (t i • QuotientGroup.mk x) =
          t i • (QuotientGroup.mk y : G ⧸ H)
        rw [nilrotationNormalizerRightTranslate_smul, htrans]
    let : IsClosed (H : Set G) := Subgroup.isClosed_topologicalClosure _
    have hz := tendsto_nhds_unique hy' hy
    exact QuotientGroup.eq.mpr (nilrotationNormalizerRightTranslate_fixed H b z hz)

/-- The action of a nilpotent topological group on its quotient by a closed subgroup
is distal. Any common limit of translates of two points under the same nontrivial
filter forces the original points equal. -/
theorem nilrotation_distal_quotient (L : Subgroup G) (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    {I : Type*} (t : I → G) {l : Filter I} [l.NeBot] {x y z : G ⧸ L}
    (hx : Tendsto (fun i ↦ t i • x) l (𝓝 z))
    (hy : Tendsto (fun i ↦ t i • y) l (𝓝 z)) : x = y := by
  have he : nilrotationClosedLayer L n = L := by
    unfold nilrotationClosedLayer
    rw [hn, bot_sup_eq]
    exact le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl hL)
      (Subgroup.le_topologicalClosure _)
  have hh := nilrotationClosedLayer_fibre_eq L n t (l := l)
  rw [he] at hh
  exact hh x y z hx hy

end Mixing
