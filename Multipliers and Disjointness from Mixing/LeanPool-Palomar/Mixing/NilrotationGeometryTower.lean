/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactQuotientSkew
public import Mixing.NilrotationGeometryDenseAction
public import Mixing.NilrotationGeometryDistal
public import Mixing.NilrotationGeometryPrincipalExtension
public import Mathlib.Topology.Metrizable.Urysohn

/-! # Compact group extensions of nilpotent homogeneous rotations -/

@[expose] public section
noncomputable section

namespace Mixing

open Function MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped commutatorElement

namespace Nilrotation

/-- The Borel sigma-algebra on a homogeneous quotient, available in the
`Mixing.Nilrotation` scope. -/
scoped instance quotientMeasurableSpace {G : Type*} [Group G] [TopologicalSpace G]
    {H : Subgroup G} : MeasurableSpace (G ⧸ H) := borel _

scoped instance quotientBorelSpace {G : Type*} [Group G] [TopologicalSpace G]
    {H : Subgroup G} : BorelSpace (G ⧸ H) := ⟨rfl⟩

end Nilrotation

open scoped Nilrotation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Projection between homogeneous quotients is continuous. -/
theorem nilrotationQuotientMap_continuous {L H : Subgroup G} (h : L ≤ H) :
    Continuous (Subgroup.quotientMapOfLE h) := by
  rw [← (QuotientGroup.isOpenQuotientMap_mk (N := L)).continuous_comp_iff]
  change Continuous (QuotientGroup.mk : G → G ⧸ H)
  exact QuotientGroup.continuous_mk

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nilrotationQuotientMap_surjective {L H : Subgroup G} (h : L ≤ H) :
    Surjective (Subgroup.quotientMapOfLE h) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk g, rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nilrotationQuotientMap_smul {L H : Subgroup G} (h : L ≤ H) (g : G) (x : G ⧸ L) :
    Subgroup.quotientMapOfLE h (g • x) = g • Subgroup.quotientMapOfLE h x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nilrotationQuotientMap_comp {L H B : Subgroup G} (hLH : L ≤ H) (hHB : H ≤ B) :
    Subgroup.quotientMapOfLE hHB ∘ Subgroup.quotientMapOfLE hLH =
      Subgroup.quotientMapOfLE (hLH.trans hHB) := by
  funext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem nilrotationQuotient_compactSpace {L H : Subgroup G} (h : L ≤ H)
    [CompactSpace (G ⧸ L)] : CompactSpace (G ⧸ H) :=
  (nilrotationQuotientMap_surjective h).compactSpace (nilrotationQuotientMap_continuous h)

theorem nilrotationQuotient_map_preserves {L H : Subgroup G} (h : L ≤ H)
    (μ : Measure (G ⧸ L))
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ) (g : G) :
    MeasurePreserving (fun x : G ⧸ H ↦ g • x)
      (μ.map (Subgroup.quotientMapOfLE h)) (μ.map (Subgroup.quotientMapOfLE h)) := by
  have hm := (nilrotationQuotientMap_continuous h).measurable
  have hc : Measurable (fun x : G ⧸ H ↦ g • x) := (continuous_const_smul g).measurable
  refine ⟨hc, ?_⟩
  rw [Measure.map_map hc hm, show (fun x : G ⧸ H ↦ g • x) ∘ Subgroup.quotientMapOfLE h =
      Subgroup.quotientMapOfLE h ∘ (fun x : G ⧸ L ↦ g • x)
    from funext (fun x ↦ (nilrotationQuotientMap_smul h g x).symm),
    ← Measure.map_map hm (hμ g).measurable, (hμ g).map_eq]

/-- The system given by integer powers of a fixed left translation and
a homogeneous invariant probability. -/
def nilrotationQuotientSystem (L : Subgroup G) (a : G) (μ : Measure (G ⧸ L))
    [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ) :
    System (Multiplicative ℤ) (G ⧸ L) where
  measure := μ
  probability := inferInstance
  act g x := a ^ g.toAdd • x
  act_one := by funext x; simp
  act_mul g h := by
    funext x
    change a ^ (g.toAdd + h.toAdd) • x = a ^ g.toAdd • (a ^ h.toAdd • x)
    rw [zpow_add, mul_smul]
  preserves g := hμ (a ^ g.toAdd)

omit [IsTopologicalGroup G] in
@[simp]
theorem nilrotationQuotientSystem_act (L : Subgroup G) (a : G) (μ : Measure (G ⧸ L))
    [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (n : ℤ) (x : G ⧸ L) :
    (nilrotationQuotientSystem L a μ hμ).act (Multiplicative.ofAdd n) x = a ^ n • x := rfl

/-- Every vertical translation preserves the homogeneous invariant probability:
the dense image of the central subgroup acts by inverse left translations. -/
theorem nilrotationVerticalAction_measurePreserving (C L : Subgroup G)
    [(L.subgroupOf (nilrotationVerticalClosure C L)).Normal]
    [FirstCountableTopology (NilrotationVerticalGroup C L)]
    [HasOuterApproxClosed (G ⧸ L)] (hC : ⁅C, (⊤ : Subgroup G)⁆ ≤ L)
    (μ : Measure (G ⧸ L)) [IsFiniteMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (k : NilrotationVerticalGroup C L) :
    MeasurePreserving (nilrotationVerticalTranslate C L k) μ μ := by
  let K := NilrotationVerticalGroup C L
  let : MulAction K (G ⧸ L) := nilrotationVerticalMulAction C L
  let : ContinuousSMul K (G ⧸ L) := ⟨nilrotation_continuous_verticalTranslate C L⟩
  refine measurePreserving_smul_of_denseRange (K := K) (nilrotation_verticalImage C L)
    (nilrotation_denseRange_verticalImage C L) μ (fun c ↦ ?_) k
  have heq : (fun x : G ⧸ L ↦ nilrotation_verticalImage C L c • x) =
      (fun x : G ⧸ L ↦ (c : G)⁻¹ • x) :=
    funext (nilrotation_verticalImage_translate_of_commutator_le C L hC c)
  exact heq.symm ▸ hμ _

private theorem nilrotation_disjoint_of_subsingleton {R X : Type*} [MeasurableSpace R]
    [MeasurableSpace X] [Subsingleton X]
    (S : System (Multiplicative ℤ) R) (T : System (Multiplicative ℤ) X) : Disjoint S T := by
  intro η hη
  let := hη.probability
  apply Measure.ext_prod
  intro A B hA hB
  by_cases h : B.Nonempty
  · obtain ⟨b, hb⟩ := h
    have hBu : B = univ := Set.eq_univ_of_forall fun x ↦ Subsingleton.elim b x ▸ hb
    rw [hBu, Measure.prod_prod, measure_univ, mul_one, Set.prod_univ]
    exact hη.fst.measure_preimage hA.nullMeasurableSet
  · rw [Set.not_nonempty_iff_eq_empty.mp h, prod_empty, measure_empty, measure_empty]

/-- A closed quotient obtained by adjoining a subgroup central modulo the
stabilizer is a compact principal extension. -/
theorem nilrotationQuotient_disjoint_vertical [SecondCountableTopology G]
    {R : Type*} [MeasurableSpace R]
    [StandardBorelSpace R] (S : System (Multiplicative ℤ) R)
    (hWeak : IsWeaklyMixing S.koopmanZeroRep) (C L : Subgroup G)
    [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (hC : ⁅C, (⊤ : Subgroup G)⁆ ≤ L) (a : G) (μ : Measure (G ⧸ L))
    [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hDisj : let h := nilrotation_lattice_le_verticalClosure C L
             let ν := μ.map (Subgroup.quotientMapOfLE h)
             letI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
               (nilrotationQuotientMap_continuous h).measurable.aemeasurable).mpr inferInstance
             Disjoint S (nilrotationQuotientSystem _ a ν (nilrotationQuotient_map_preserves h μ hμ))) :
    Disjoint S (nilrotationQuotientSystem L a μ hμ) := by
  let H := nilrotationVerticalClosure C L
  let h := nilrotation_lattice_le_verticalClosure C L
  let p : G ⧸ L → G ⧸ H := Subgroup.quotientMapOfLE h
  let ν := μ.map p
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    (nilrotationQuotientMap_continuous h).measurable.aemeasurable).mpr inferInstance
  let : IsClosed (L : Set G) := hL
  let : IsClosed (H : Set G) := Subgroup.isClosed_topologicalClosure _
  let : CompactSpace (G ⧸ H) := nilrotationQuotient_compactSpace h
  let : MetricSpace (G ⧸ L) := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (G ⧸ H) := TopologicalSpace.metrizableSpaceMetric _
  let : Countable (Multiplicative ℤ) := by change Countable ℤ; infer_instance
  let E := nilrotationQuotientSystem L a μ hμ
  let B := nilrotationQuotientSystem H a ν (nilrotationQuotient_map_preserves h μ hμ)
  let π : FactorMap E B := ⟨p, ⟨(nilrotationQuotientMap_continuous h).measurable, rfl⟩,
    fun _ ↦ funext (nilrotationQuotientMap_smul h _)⟩
  let : (L.subgroupOf H).Normal := nilrotation_verticalLattice_normal_of_commutator_le C L hC hL
  let K := NilrotationVerticalGroup C L
  let : IsClosed ((L.subgroupOf H : Subgroup H) : Set H) := hL.preimage continuous_subtype_val
  let : CompactSpace K := nilrotation_verticalGroup_compactSpace C L
  let : T2Space K := QuotientGroup.instT2Space
  let : SecondCountableTopology H := Subtype.secondCountableTopology (H : Set G)
  let : SecondCountableTopology K := QuotientGroup.instSecondCountableTopology _
  let : IsTopologicalGroup K := by dsimp [K]; infer_instance
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric _
  let : MulAction K (G ⧸ L) := nilrotationVerticalMulAction C L
  let : ContinuousSMul K (G ⧸ L) := ⟨nilrotation_continuous_verticalTranslate C L⟩
  let U : PositiveCompacts K := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let m : Measure K := haarMeasure U
  let : IsProbabilityMeasure m := ⟨haarMeasure_self (K₀ := U)⟩
  let : IsMulRightInvariant m := isMulRightInvariant_of_haar_probability m
  exact principalExtension_disjoint_of_weakMixing E B π m
    (nilrotationQuotientMap_continuous h) (nilrotationQuotientMap_surjective h)
    (nilrotationVerticalProjection_translate C L) (nilrotationVerticalTranslate_free C L)
    (fun _ _ ↦ nilrotationVerticalProjection_eq_iff C L |>.mp)
    (nilrotationVerticalAction_measurePreserving C L hC μ hμ)
    (fun _ _ _ ↦ (nilrotation_verticalTranslate_smul C L _ _ _).symm) S hWeak hDisj

/-- Adjoining a lower-central subgroup to the next coarser closed layer recovers
the current closed layer. -/
theorem nilrotationClosedLayer_vertical (L : Subgroup G) (i : ℕ) :
    nilrotationVerticalClosure ((⊤ : Subgroup G).lowerCentralSeries i)
      (nilrotationClosedLayer L (i + 1)) = nilrotationClosedLayer L i := by
  apply le_antisymm
  · apply Subgroup.topologicalClosure_minimal
    · exact sup_le (le_sup_left.trans (Subgroup.le_topologicalClosure _))
        (nilrotationClosedLayer_succ_le L i)
    · exact Subgroup.isClosed_topologicalClosure _
  · exact Subgroup.topologicalClosure_mono (sup_le_sup_left
      (le_sup_right.trans (Subgroup.le_topologicalClosure _)) _)

theorem nilrotationClosedLayer_lattice_le (L : Subgroup G) (i : ℕ) :
    L ≤ nilrotationClosedLayer L i :=
  le_sup_right.trans (Subgroup.le_topologicalClosure _)

theorem nilrotationClosedLayer_zero (L : Subgroup G) : nilrotationClosedLayer L 0 = ⊤ := by
  unfold nilrotationClosedLayer
  rw [Subgroup.lowerCentralSeries_zero, top_sup_eq]
  exact le_antisymm le_top (Subgroup.le_topologicalClosure _)

theorem nilrotationClosedLayer_last (L : Subgroup G) (hL : IsClosed (L : Set G))
    (i : ℕ) (hi : (⊤ : Subgroup G).lowerCentralSeries i = ⊥) :
    nilrotationClosedLayer L i = L := by
  unfold nilrotationClosedLayer
  rw [hi, bot_sup_eq]
  exact le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl hL)
    (Subgroup.le_topologicalClosure _)

/-- An algebraic lower-central layer is central modulo the next closed layer. -/
theorem nilrotationClosedLayer_commutator_le (L : Subgroup G) (i : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G)⁆ ≤
      nilrotationClosedLayer L (i + 1) :=
  le_sup_left.trans (Subgroup.le_topologicalClosure _)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem nilrotationQuotientMap_le_eq {L : Subgroup G} (h : L ≤ L) :
    Subgroup.quotientMapOfLE h = (id : G ⧸ L → G ⧸ L) := by
  funext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

omit [IsTopologicalGroup G] in
theorem nilrotationQuotientSystem_eq_of_measure {L : Subgroup G} (a : G)
    {μ ν : Measure (G ⧸ L)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hν : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) ν ν) (he : μ = ν) :
    nilrotationQuotientSystem L a μ hμ = nilrotationQuotientSystem L a ν hν := by
  subst ν
  rfl

/-- Every compact nilpotent homogeneous rotation is disjoint from every
weakly mixing probability system on a standard Borel space. -/
theorem nilrotationQuotient_disjoint_of_weakMixing [SecondCountableTopology G]
    {R : Type*} [MeasurableSpace R]
    [StandardBorelSpace R] (S : System (Multiplicative ℤ) R)
    (hWeak : IsWeaklyMixing S.koopmanZeroRep) (L : Subgroup G)
    [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ) :
    Disjoint S (nilrotationQuotientSystem L a μ hμ) := by
  let T (H : Subgroup G) (h : L ≤ H) : System (Multiplicative ℤ) (G ⧸ H) :=
    let ν := μ.map (Subgroup.quotientMapOfLE h)
    letI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
      (nilrotationQuotientMap_continuous h).measurable.aemeasurable).mpr inferInstance
    nilrotationQuotientSystem H a ν (nilrotationQuotient_map_preserves h μ hμ)
  have hTower (i : ℕ) : Disjoint S (T (nilrotationClosedLayer L i)
      (nilrotationClosedLayer_lattice_le L i)) := by
    induction i with
    | zero =>
      generalize_proofs h
      revert h
      rw [nilrotationClosedLayer_zero]
      intro h
      let := QuotientGroup.subsingleton_quotient_top (G := G)
      exact nilrotation_disjoint_of_subsingleton S (T ⊤ h)
    | succ i ih =>
      let H := nilrotationClosedLayer L (i + 1)
      let C := (⊤ : Subgroup G).lowerCentralSeries i
      let hH := nilrotationClosedLayer_lattice_le L (i + 1)
      let : CompactSpace (G ⧸ H) := nilrotationQuotient_compactSpace hH
      let ν := μ.map (Subgroup.quotientMapOfLE hH)
      let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
        (nilrotationQuotientMap_continuous hH).measurable.aemeasurable).mpr inferInstance
      have hc : ⁅C, (⊤ : Subgroup G)⁆ ≤ H := nilrotationClosedLayer_commutator_le L i
      apply nilrotationQuotient_disjoint_vertical S hWeak C H
        (Subgroup.isClosed_topologicalClosure _) hc a ν (nilrotationQuotient_map_preserves hH μ hμ)
      let h := nilrotation_lattice_le_verticalClosure C H
      let V := nilrotationVerticalClosure C H
      have he : ν.map (Subgroup.quotientMapOfLE h) = μ.map (Subgroup.quotientMapOfLE (hH.trans h)) := by
        change (μ.map _).map _ = _
        rw [Measure.map_map (nilrotationQuotientMap_continuous h).measurable
          (nilrotationQuotientMap_continuous hH).measurable, nilrotationQuotientMap_comp]
      change Disjoint S (nilrotationQuotientSystem V a (ν.map _) _)
      have hSystem : nilrotationQuotientSystem V a (ν.map (Subgroup.quotientMapOfLE h))
          (nilrotationQuotient_map_preserves h ν (nilrotationQuotient_map_preserves hH μ hμ)) =
          T V (hH.trans h) :=
        nilrotationQuotientSystem_eq_of_measure a _ _ he
      rw [hSystem]
      change Disjoint S (T V (hH.trans h))
      have eV : V = nilrotationClosedLayer L i := nilrotationClosedLayer_vertical L i
      exact (congrArg (fun J ↦ ∀ p : L ≤ J, Disjoint S (T J p)) eV).mpr
        (fun _ ↦ ih) (hH.trans h)
  have hend := hTower n
  generalize_proofs h at hend
  revert hend
  have eL := nilrotationClosedLayer_last L hL n hn
  revert h
  rw [eL]
  intro h hend
  have hId := nilrotationQuotientMap_le_eq h
  have hμId : μ.map (Subgroup.quotientMapOfLE h) = μ := by rw [hId, Measure.map_id]
  have hSystem : T L h = nilrotationQuotientSystem L a μ hμ :=
    nilrotationQuotientSystem_eq_of_measure a _ _ hμId
  rwa [← hSystem]

end Mixing
