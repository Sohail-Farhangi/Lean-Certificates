/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactConditionalJoinings
public import Mixing.SigmaCompactWitness

@[expose] public section
noncomputable section

namespace Mixing

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

private theorem nnreal_half_add_half : (1 / 2 : ℝ≥0) + (1 / 2 : ℝ≥0) = 1 := by norm_num

/-- The midpoint of a pair of probability measures. -/
def probabilityMidpoint {W : Type*} [MeasurableSpace W]
    (r : ProbabilityMeasure W × ProbabilityMeasure W) : ProbabilityMeasure W :=
  probabilityConvexCombination (1 / 2) (1 / 2) (by norm_num) r.1 r.2

/-- The underlying measure of a midpoint uses the usual extended nonnegative weights. -/
theorem probabilityMidpoint_toMeasure {W : Type*} [MeasurableSpace W]
    (r : ProbabilityMeasure W × ProbabilityMeasure W) :
    (probabilityMidpoint r : Measure W) =
      (1 / 2 : ℝ≥0∞) • (r.1 : Measure W) + (1 / 2 : ℝ≥0∞) • (r.2 : Measure W) := by
  change (1 / 2 : ℝ≥0) • (r.1 : Measure W) + (1 / 2 : ℝ≥0) • (r.2 : Measure W) = _
  simp only [← Measure.coe_nnreal_smul, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_one, ENNReal.coe_two]

private theorem probabilityMidpoint_diagonal {W : Type*} [MeasurableSpace W]
    (δ : ProbabilityMeasure W) : probabilityMidpoint (δ, δ) = δ := by
  apply Subtype.ext
  change (1 / 2 : ℝ≥0) • (δ : Measure W) + (1 / 2 : ℝ≥0) • (δ : Measure W) = _
  rw [← add_smul, nnreal_half_add_half, one_smul]
  rfl

private theorem probabilityMidpoint_map_eq_of_equal_maps
    {W V : Type*} [MeasurableSpace W] [MeasurableSpace V] {f : W → V}
    (hf : Measurable f) {r : ProbabilityMeasure W × ProbabilityMeasure W}
    (h : r.1.map f = r.2.map f) : (probabilityMidpoint r).map f = r.1.map f := by
  apply Subtype.ext
  have he := congrArg ProbabilityMeasure.toMeasure h
  change (r.1 : Measure W).map f = (r.2 : Measure W).map f at he
  change ((1 / 2 : ℝ≥0) • (r.1 : Measure W) + (1 / 2 : ℝ≥0) • (r.2 : Measure W)).map f =
    (r.1 : Measure W).map f
  rw [Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable, ← he, ← add_smul, nnreal_half_add_half, one_smul]

variable {G X Y : Type*} [Group G]
variable [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace Y] [CompactSpace Y] [MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Select a midpoint decomposition measurably. For a joint law with the
given first marginal and diagonal invariance, the output laws have those
properties and share its second marginal. The outputs are unequal whenever
an unequal decomposition with those constraints exists. -/
theorem exists_measurable_joining_midpoint_witness (S : System G X) (T : System G Y)
    (hS : ∀ g, Continuous (S.act g)) (hT : ∀ g, Continuous (T.act g)) :
    ∃ k : ProbabilityMeasure (X × Y) → ProbabilityMeasure (X × Y) × ProbabilityMeasure (X × Y),
      Measurable k ∧
      (∀ δ, probabilityMidpoint (k δ) = δ) ∧
      (∀ δ ∈ probabilityJoiningLaws S T,
        (k δ).1 ∈ probabilityJoiningLaws S T ∧ (k δ).2 ∈ probabilityJoiningLaws S T ∧
        (k δ).1.map Prod.snd = δ.map Prod.snd ∧ (k δ).2.map Prod.snd = δ.map Prod.snd) ∧
      ∀ δ, (∃ ξ ∈ probabilityJoiningLaws S T, ∃ η ∈ probabilityJoiningLaws S T,
        ξ.map Prod.snd = η.map Prod.snd ∧ ξ ≠ η ∧ probabilityMidpoint (ξ, η) = δ) →
          (k δ).1 ≠ (k δ).2 := by
  let : BorelSpace (ProbabilityMeasure (X × Y)) := probabilityMeasure_borelSpace (X := X × Y)
  let Q (ξ : ProbabilityMeasure (X × Y)) := ξ.map Prod.snd
  have hQ : Continuous Q := ProbabilityMeasure.continuous_map continuous_snd
  let K := probabilityJoiningLaws S T
  let E : Set (ProbabilityMeasure (X × Y) × ProbabilityMeasure (X × Y)) :=
    (K ×ˢ K) ∩ {r | Q r.1 = Q r.2}
  have hK := isClosed_probabilityJoiningLaws S T hS hT
  have hE : IsClosed E := (hK.prod hK).inter
    (isClosed_eq (hQ.comp continuous_fst) (hQ.comp continuous_snd))
  let D := {r ∈ E | r.1 ≠ r.2}
  have hD : IsSigmaCompact D := isSigmaCompact_closed_and_ne hE continuous_fst continuous_snd
  have hMid : Continuous (probabilityMidpoint (W := X × Y)) :=
    continuous_probabilityConvexCombination _ _ nnreal_half_add_half
  obtain ⟨k, hkm, hkIn, hkOut⟩ := exists_measurable_witness_of_isSigmaCompact
    probabilityMidpoint hMid hD (fun δ => (δ, δ)) (measurable_id.prodMk measurable_id)
  refine ⟨k, hkm, ?_, ?_, ?_⟩
  · intro δ
    by_cases h : δ ∈ probabilityMidpoint '' D
    · exact (hkIn δ h).2
    · rw [hkOut δ h, probabilityMidpoint_diagonal]
  · intro δ hδ
    by_cases h : δ ∈ probabilityMidpoint '' D
    · obtain ⟨hr, hMidEq⟩ := hkIn δ h
      have hEqual : (k δ).1.map Prod.snd = (k δ).2.map Prod.snd := hr.1.2
      have hLeft := probabilityMidpoint_map_eq_of_equal_maps measurable_snd hEqual
      rw [hMidEq] at hLeft
      exact ⟨hr.1.1.1, hr.1.1.2, hLeft.symm, hEqual.symm.trans hLeft.symm⟩
    · rw [hkOut δ h]
      exact ⟨hδ, hδ, rfl, rfl⟩
  · intro δ h
    obtain ⟨ξ, hξ, η, hη, hEqual, hne, hMidEq⟩ := h
    have h : δ ∈ probabilityMidpoint '' D := ⟨(ξ, η), ⟨⟨⟨hξ, hη⟩, hEqual⟩, hne⟩, hMidEq⟩
    exact (hkIn δ h).1.2

end Mixing
