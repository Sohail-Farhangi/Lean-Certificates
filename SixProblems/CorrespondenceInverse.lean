/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Correspondence

@[expose] public section
noncomputable section

namespace SixProblems

open Filter MeasureTheory Mixing
open scoped Topology BoundedContinuousFunction

variable {G K : Type} [Group G] [DecidableEq G] [Countable G]
variable [Group K] [MetricSpace K] [CompactSpace K] [IsTopologicalGroup K]
variable [MeasurableSpace K] [BorelSpace K]

/-- The inverse correspondence property of the full shift along a fixed sequence.
This asks for convergence along the entire sequence of Følner blocks. -/
def HasFolnerGenericRealizations (F : LeftFolnerSequence G) (K : Type) [TopologicalSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [OpensMeasurableSpace K] : Prop :=
  ∀ ν : ProbabilityMeasure (G → K),
    (∀ a : G, (ν : Measure (G → K)).map (fun x j ↦ x (j * a)) = (ν : Measure (G → K))) →
    ∃ x : G → K, Tendsto
      (fun n ↦ finiteEmpiricalLaw (F.blocks n) (F.nonempty n) (fun g j ↦ x (j * g)))
      atTop (𝓝 ν)

/-- The correspondence direction of Theorem 4.8, with the generic-realization
property stated explicitly. The property is used on the shift law of the
coordinate process associated to the proposed observable. -/
theorem measureTheoreticVdC_of_folnerVdC_of_genericRealizations (F : LeftFolnerSequence G)
    (hGen : HasFolnerGenericRealizations F K) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] (hm : IsFolnerVdC F R m) :
    IsMeasureTheoreticVdC R m := by
  intro X _ _ S f hf hDif
  let p : X → G → K := fun x g ↦ f (S.act g x)
  have hp : Measurable p := Measurable.of_eval fun g ↦ hf.comp (S.preserves g).measurable
  let μ := S.measure.map p
  let hProb : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  let ν : ProbabilityMeasure (G → K) := ⟨μ, hProb⟩
  have hInvariant (a : G) : μ.map (fun x j ↦ x (j * a)) = μ := by
    have hpShift : correspondenceShift (K := K) a ∘ p = p ∘ S.act a := by
      funext x g
      simp [p, S.act_mul]
    change (S.measure.map p).map (⇑(correspondenceShift (K := K) a)) = μ
    rw [Measure.map_map (correspondenceShift (K := K) a).continuous.measurable hp,
      hpShift, ← Measure.map_map hp (S.preserves a).measurable, (S.preserves a).map_eq]
  obtain ⟨x, hx⟩ := hGen ν hInvariant
  have : IsProbabilityMeasure (S.measure.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have hTest (u : C(G → K, ℝ)) : Tendsto
      (fun n ↦ finiteAverage (F.blocks n) (fun g ↦ u (correspondenceShift g x)))
      atTop (𝓝 (∫ y, u y ∂μ)) := by
    have hu := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hx)
      (BoundedContinuousFunction.mkOfCompact u)
    refine hu.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    rw [integral_finiteEmpiricalLaw]
    rfl
  have hGe (h : G) (hr : h ∈ R) :
      IsFolnerUniformlyDistributed F (fun g ↦ x (h * g) * (x g)⁻¹) m := by
    intro v
    have hv := hTest (v.comp (correspondenceDifference h))
    have hMap : μ.map (correspondenceDifference h) = m := by
      unfold μ
      rw [Measure.map_map (correspondenceDifference h).continuous.measurable hp]
      convert hDif h hr using 2
      funext y
      simp [p, correspondenceDifference, S.act_one]
    have hEnd : (∫ y, v (correspondenceDifference h y) ∂μ) = ∫ y, v y ∂m := by
      rw [← integral_map (correspondenceDifference h).continuous.aemeasurable
        v.continuous.aestronglyMeasurable, hMap]
    change Tendsto _ _ (𝓝 (∫ y, v (correspondenceDifference h y) ∂μ)) at hv
    rw [hEnd] at hv
    refine hv.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    congr 1
    funext g
    change v (x (h * g) * (x (1 * g))⁻¹) = _
    simp only [one_mul, Function.comp_apply]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro v
  have hv := hTest ((v.toContinuousMap).comp (correspondenceOrigin (G := G) (K := K)))
  have hMap : μ.map (correspondenceOrigin (G := G) (K := K)) = S.measure.map f := by
    unfold μ
    rw [Measure.map_map (correspondenceOrigin (G := G) (K := K)).continuous.measurable hp]
    congr 1
    funext y
    simp [p, correspondenceOrigin, S.act_one]
  have hEnd : (∫ y, v (correspondenceOrigin y) ∂μ) = ∫ y, v y ∂(S.measure.map f) := by
    change (∫ y, v.toContinuousMap (correspondenceOrigin y) ∂μ) =
      ∫ y, v.toContinuousMap y ∂(S.measure.map f)
    rw [← integral_map (correspondenceOrigin (G := G) (K := K)).continuous.aemeasurable
      v.continuous.aestronglyMeasurable, hMap]
  change Tendsto _ _ (𝓝 (∫ y, v (correspondenceOrigin y) ∂μ)) at hv
  rw [hEnd] at hv
  apply tendsto_nhds_unique _ (hm x hGe v.toContinuousMap)
  refine hv.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  congr 1
  funext g
  change v (x (1 * g)) = _
  rw [one_mul]
  rfl

/-- Theorem 4.8 under its explicit inverse-correspondence input. -/
theorem folnerVdC_iff_measureTheoretic_of_genericRealizations (F : LeftFolnerSequence G)
    (hGen : HasFolnerGenericRealizations F K) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] :
    IsFolnerVdC F R m ↔ IsMeasureTheoreticVdC R m :=
  ⟨measureTheoreticVdC_of_folnerVdC_of_genericRealizations F hGen R m,
    folnerVdC_of_measureTheoretic F R m⟩

end SixProblems
