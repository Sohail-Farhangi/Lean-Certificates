/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactHomogeneousSkew
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # The Haar homogeneous-quotient form of Theorem 2.1 -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure

namespace Mixing

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Normalized Haar measure on a compact group is also right invariant. -/
theorem isMulRightInvariant_of_haar_probability (mK : Measure K)
    [IsHaarMeasure mK] [IsProbabilityMeasure mK] : IsMulRightInvariant mK := by
  constructor
  intro r
  let R : K → K := fun k ↦ k * r
  let ν := mK.map R
  have hR : Continuous R := (Homeomorph.mulRight r).continuous
  have hRm : Measurable R := hR.measurable
  have hνprob : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hRm.aemeasurable).mpr
    inferInstance
  have hνhaar : IsHaarMeasure ν := by
    change IsHaarMeasure (mK.map (fun k : K ↦ MulOpposite.op r • k))
    infer_instance
  exact isHaarMeasure_eq_of_isProbabilityMeasure ν mK

variable [SecondCountableTopology K]
variable {G X Y : Type*} [CommGroup G] [Countable G] [MeasurableSpace X] [MeasurableSpace Y]

/-- Theorem 2.1 in the homogeneous representation over the compact-group quotient
`K ⧸ H`, with the quotient of normalized Haar measure as fibre measure. -/
theorem theorem2_1_homogeneous_quotient (S : System G X) (T : System G Y)
    (hWeak : IsWeaklyMixing S.koopmanZeroRep) (hDisj : Disjoint S T)
    (c : MeasurableSkewCocycle (K := K) T) (H : Subgroup K)
    [MeasurableSpace (K ⧸ H)] [BorelSpace (K ⧸ H)] [MeasurableEq (Y × (K ⧸ H))]
    [StandardBorelSpace (Y × K)] [Nonempty (Y × K)]
    [StandardBorelSpace (X × (Y × K))] [Nonempty (X × (Y × K))]
    (mK : Measure K) [IsHaarMeasure mK] [IsProbabilityMeasure mK] :
    Disjoint S (homogeneousSkewSystem T c mK (QuotientGroup.mk : K → K ⧸ H)
      QuotientGroup.continuous_mk.measurable (fun _ _ ↦ rfl)) := by
  have : IsMulRightInvariant mK := isMulRightInvariant_of_haar_probability mK
  exact disjoint_homogeneousSkew_of_weakMixing T c mK (QuotientGroup.mk : K → K ⧸ H)
    QuotientGroup.continuous_mk.measurable (fun _ _ ↦ rfl) S hWeak hDisj

end Mixing
