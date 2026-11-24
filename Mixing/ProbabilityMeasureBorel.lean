/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.WeakProbabilityOperations
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! # Agreement of the Borel and Giry σ-algebras on compact probability spaces -/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace Topology
open scoped ENNReal

namespace Mixing

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [CompactSpace X]

private theorem continuous_integral_in_test (μ : ProbabilityMeasure X) :
    Continuous (fun f : C(X, ℝ) ↦ ∫ x, f x ∂(μ : Measure X)) := by
  let L := ContinuousMap.toLp (E := ℝ) 1 (μ : Measure X) ℝ
  have he (f : C(X, ℝ)) : (∫ x, L f x ∂(μ : Measure X)) = ∫ x, f x ∂(μ : Measure X) :=
    integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 1) (μ : Measure X) f)
  simpa only [Function.comp_def, he] using MeasureTheory.continuous_integral.comp L.continuous

private theorem measurable_integral_in_probability (f : C(X, ℝ)) :
    Measurable (fun μ : ProbabilityMeasure X ↦ ∫ x, f x ∂(μ : Measure X)) := by
  have hPos : Measurable (fun μ : Measure X ↦ (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal) :=
    (Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).ennreal_toReal
  have hNeg : Measurable (fun μ : Measure X ↦ (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal) :=
    (Measure.measurable_lintegral f.continuous.measurable.neg.ennreal_ofReal).ennreal_toReal
  have hμ : Measurable (fun μ : ProbabilityMeasure X ↦ (μ : Measure X)) := measurable_subtype_coe
  have he (μ : ProbabilityMeasure X) : (∫ x, f x ∂(μ : Measure X)) =
      (∫⁻ x, ENNReal.ofReal (f x) ∂(μ : Measure X)).toReal -
        (∫⁻ x, ENNReal.ofReal (-f x) ∂(μ : Measure X)).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  simp_rw [he]
  exact (hPos.sub hNeg).comp hμ

variable [T2Space X] [SecondCountableTopology X] [PseudoMetrizableSpace X]

/-- Measurable probabilities for a compact second-countable metrizable space carry
the Borel σ-algebra of weak convergence. -/
theorem probabilityMeasure_borelSpace : BorelSpace (ProbabilityMeasure X) := by
  constructor
  apply le_antisymm
  · change @Measurable (ProbabilityMeasure X) (ProbabilityMeasure X) (borel _) inferInstance id
    borelize (ProbabilityMeasure X)
    have hm : Measurable (fun μ : ProbabilityMeasure X ↦ (μ : Measure X)) := by
      apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure BorelSpace.measurable_eq
        isPiSystem_isOpen
      intro A hA
      have hl : LowerSemicontinuous (fun μ : ProbabilityMeasure X ↦ (μ : Measure X) A) :=
        lowerSemicontinuous_iff_le_liminf.mpr fun μ ↦
          ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hA
      exact hl.measurable
    exact hm.subtype_mk
  · let d : ℕ → C(X, ℝ) := denseSeq C(X, ℝ)
    let E : ProbabilityMeasure X → ℕ → ℝ := fun μ n ↦ ∫ x, d n x ∂(μ : Measure X)
    have hE : Continuous E := continuous_pi fun n ↦ ProbabilityMeasure.continuous_integral_continuousMap (d n)
    have hi : Function.Injective E := by
      intro μ ν hμν
      have hInt : (fun f : C(X, ℝ) ↦ ∫ x, f x ∂(μ : Measure X)) =
          fun f ↦ ∫ x, f x ∂(ν : Measure X) :=
        (denseRange_denseSeq C(X, ℝ)).equalizer (continuous_integral_in_test μ)
          (continuous_integral_in_test ν) hμν
      have ht : Tendsto (fun _ : Unit ↦ μ) (pure ()) (𝓝 ν) :=
        ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f ↦ by
          have heq : (∫ x, f x ∂(μ : Measure X)) = ∫ x, f x ∂(ν : Measure X) :=
            congrFun hInt (⟨f, f.continuous⟩ : C(X, ℝ))
          rw [← heq]
          exact tendsto_const_nhds
      exact tendsto_nhds_unique tendsto_const_nhds ht
    have he := (hE.isClosedEmbedding hi).isEmbedding
    have hm : Measurable E := Measurable.of_eval fun n ↦ measurable_integral_in_probability (d n)
    have hb : borel (ProbabilityMeasure X) = (borel (ℕ → ℝ)).comap E := by
      exact he.eq_induced ▸ borel_comap
    rw [hb, ← BorelSpace.measurable_eq (α := ℕ → ℝ)]
    exact hm.comap_le

end Mixing
