/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Probability.Kernel.Basic

/-! # Products, convex combinations and kernels of probability measures -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace Mixing

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The product of two probabilities as a probability measure. -/
noncomputable def probabilityProduct (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    ProbabilityMeasure (X × Y) :=
  μ.prod ν

/-- A convex combination of two probability measures. -/
noncomputable def probabilityConvexCombination (a b : ℝ≥0) (h : a + b = 1)
    (μ ν : ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨a • (μ : Measure X) + b • (ν : Measure X), ⟨by
    simp only [add_apply, smul_apply, measure_univ]
    change (a : ℝ≥0∞) * 1 + (b : ℝ≥0∞) * 1 = 1
    rw [mul_one, mul_one, ← ENNReal.coe_add, h, ENNReal.coe_one]⟩⟩

/-- The product with a fixed probability in the first coordinate is weakly continuous. -/
theorem continuous_probabilityProduct_left_fixed
    [TopologicalSpace X] [TopologicalSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]
    [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    (μ : ProbabilityMeasure X) :
    Continuous (probabilityProduct (Y := Y) μ) :=
  ProbabilityMeasure.continuous_prod.comp (continuous_const.prodMk continuous_id)

section WeakTopology

variable [TopologicalSpace X] [BorelSpace X] [CompactSpace X]

/-- Fixed-weight convex combinations are jointly weakly continuous. -/
theorem continuous_probabilityConvexCombination (a b : ℝ≥0) (h : a + b = 1) :
    Continuous (fun pair : ProbabilityMeasure X × ProbabilityMeasure X ↦
      probabilityConvexCombination a b h pair.1 pair.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  have hInt (ν : ProbabilityMeasure X) : Integrable f (ν : Measure X) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF := ProbabilityMeasure.continuous_integral_continuousMap f
  convert (continuous_const.mul (hF.comp continuous_fst)).add
    (continuous_const.mul (hF.comp continuous_snd)) using 1
  funext pair
  change ∫ x, f x ∂(a • (pair.1 : Measure X) + b • (pair.2 : Measure X)) =
    (a : ℝ) * (∫ x, f x ∂(pair.1 : Measure X)) + (b : ℝ) * (∫ x, f x ∂(pair.2 : Measure X))
  rw [integral_add_measure (hInt pair.1).smul_measure_nnreal (hInt pair.2).smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def,
    smul_eq_mul, smul_eq_mul]

end WeakTopology

/-- A Markov kernel as a function taking values in probability measures. -/
def probabilityOfMarkovKernel (κ : Kernel Z X) [IsMarkovKernel κ] (z : Z) :
    ProbabilityMeasure X :=
  ⟨κ z, inferInstance⟩

theorem measurable_probabilityOfMarkovKernel (κ : Kernel Z X) [IsMarkovKernel κ] :
    Measurable (probabilityOfMarkovKernel κ) :=
  κ.measurable.subtype_mk

/-- Evaluation on a measurable event is measurable in the Giry σ-algebra. -/
theorem measurable_probabilityEvaluation {A : Set X} (hA : MeasurableSet A) :
    Measurable (fun ν : ProbabilityMeasure X ↦ (ν : Measure X) A) :=
  (Measure.measurable_coe hA).comp measurable_subtype_coe

/-- A measurable family of probability measures as a Markov kernel. -/
def markovKernelOfProbability (f : Z → ProbabilityMeasure X) (hf : Measurable f) :
    Kernel Z X where
  toFun z := f z
  measurable' := measurable_subtype_coe.comp hf

instance (f : Z → ProbabilityMeasure X) (hf : Measurable f) :
    IsMarkovKernel (markovKernelOfProbability f hf) :=
  ⟨fun z ↦ inferInstanceAs (IsProbabilityMeasure (f z : Measure X))⟩

@[simp]
theorem markovKernelOfProbability_apply (f : Z → ProbabilityMeasure X) (hf : Measurable f)
    (z : Z) : markovKernelOfProbability f hf z = (f z : Measure X) := rfl

end Mixing
