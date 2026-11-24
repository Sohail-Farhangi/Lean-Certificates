/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.JoiningEmbeddings
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory Topology

variable {Z Y Y' : Type*} [MeasurableSpace Z] [MeasurableSpace Y] [MeasurableSpace Y']

/-- The kernel for countably many conditionally independent samples from a
probability kernel. Measurability is checked first on finite rectangles. -/
def independentCopies (κ : Kernel Z Y) [IsMarkovKernel κ] : Kernel Z (ℕ → Y) where
  toFun z := Measure.infinitePi (fun _ : ℕ ↦ κ z)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_squareCylinders.symm
      (isPiSystem_squareCylinders (fun _ : ℕ ↦ by
        intro a ha b hb _
        exact ha.inter hb) (fun _ ↦ .univ))
    rintro _ ⟨s, t, ht, rfl⟩
    have h (i : ℕ) : MeasurableSet (t i) := ht i (mem_univ i)
    simp_rw [Measure.infinitePi_pi _ (fun i _ ↦ h i)]
    exact s.measurable_prod fun i _ ↦ κ.measurable_coe (h i)

instance (κ : Kernel Z Y) [IsMarkovKernel κ] : IsMarkovKernel (independentCopies κ) :=
  ⟨fun z ↦ by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ κ z))
    infer_instance⟩

theorem independentCopies_map_eval (κ : Kernel Z Y) [IsMarkovKernel κ]
    (z : Z) (i : ℕ) : (independentCopies κ z).map (fun y ↦ y i) = κ z :=
  Measure.infinitePi_map_eval _ i

/-- Independent copies commute with coordinatewise pushforward. -/
theorem independentCopies_map_pi (κ : Kernel Z Y) [IsMarkovKernel κ]
    {f : Y → Y'} (hf : Measurable f) (z : Z) :
    (independentCopies κ z).map (fun w i ↦ f (w i)) =
      Measure.infinitePi (fun _ : ℕ ↦ (κ z).map f) :=
  Measure.infinitePi_map_pi _ (fun _ ↦ hf)

/-- A sample mean of bounded measurable real observations. -/
def independentSampleMean (f : Y → ℝ) (n : ℕ) (w : ℕ → Y) : ℝ :=
  (∑ i ∈ Finset.range n, f (w i)) / n

/-- Conditional strong law for the independent copies of a kernel. -/
theorem ae_independentSampleMean (κ : Kernel Z Y) [IsMarkovKernel κ] (z : Z)
    (f : Y → ℝ) (hf : Measurable f) (hInt : Integrable f (κ z)) :
    ∀ᵐ w ∂independentCopies κ z,
      Tendsto (fun n ↦ independentSampleMean f n w) atTop (𝓝 (∫ y, f y ∂κ z)) := by
  let P := independentCopies κ z
  let X (i : ℕ) (w : ℕ → Y) := f (w i)
  have hMap (i : ℕ) : MeasurePreserving (fun w : ℕ → Y ↦ w i) P (κ z) :=
    ⟨measurable_pi_apply i, independentCopies_map_eval κ z i⟩
  have hX (i : ℕ) : Measurable (X i) := hf.comp (hMap i).measurable
  have hInd : iIndepFun X P := iIndepFun_infinitePi (X := fun _ y ↦ f y) (fun _ ↦ hf)
  have hIdent (i : ℕ) : IdentDistrib (X i) (X 0) P P := by
    refine ⟨(hX i).aemeasurable, (hX 0).aemeasurable, ?_⟩
    change P.map (f ∘ fun w : ℕ → Y ↦ w i) = P.map (f ∘ fun w : ℕ → Y ↦ w 0)
    rw [← Measure.map_map hf (hMap i).measurable, ← Measure.map_map hf (hMap 0).measurable,
      (hMap i).map_eq, (hMap 0).map_eq]
  have hLaw := strong_law_ae_real X ((hMap 0).integrable_comp_of_integrable hInt)
    (fun i j hij ↦ hInd.indepFun hij) hIdent
  have hExpect : ∫ w, X 0 w ∂P = ∫ y, f y ∂κ z := by
    rw [← (hMap 0).map_eq]
    exact (integral_map (hMap 0).measurable.aemeasurable hf.aestronglyMeasurable).symm
  rwa [hExpect] at hLaw

end Mixing
