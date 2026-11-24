/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.MulAction

/-! # Extending measure preservation from a dense set of transformations -/

@[expose] public section

namespace Mixing

open MeasureTheory

/-- For a continuous action, preservation of a finite Borel measure by a dense set of
parameters implies preservation by every parameter. -/
theorem measurePreserving_smul_of_denseRange
    {D K X : Type*} [TopologicalSpace K] [FirstCountableTopology K]
    [TopologicalSpace X] [HasOuterApproxClosed X]
    [SMul K X] [ContinuousSMul K X] [MeasurableSpace X] [BorelSpace X]
    (d : D → K) (hd : DenseRange d) (μ : Measure X) [IsFiniteMeasure μ]
    (hInv : ∀ i, MeasurePreserving (fun x : X ↦ d i • x) μ μ)
    (k : K) : MeasurePreserving (fun x : X ↦ k • x) μ μ := by
  have hmeas : Measurable (fun x : X ↦ k • x) := (continuous_const_smul k).measurable
  refine ⟨hmeas, ?_⟩
  let := μ.isFiniteMeasure_map (fun x : X ↦ k • x)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
  let F (a : K) : ℝ := ∫ x, f (a • x) ∂μ
  have hF : Continuous F := by
    apply continuous_of_dominated (bound := fun _ : X ↦ ‖f‖)
    · exact fun a ↦ (f.continuous.comp (continuous_const_smul a)).aestronglyMeasurable
    · exact fun a ↦ ae_of_all _ fun x ↦ f.norm_coe_le_norm (a • x)
    · exact integrable_const ‖f‖
    · exact ae_of_all _ fun x ↦
        f.continuous.comp (continuous_smul.comp (continuous_id.prodMk continuous_const))
  change F k = ∫ x, f x ∂μ
  have hdF (i : D) : F (d i) = ∫ x, f x ∂μ := by
    change (∫ x, f (d i • x) ∂μ) = ∫ x, f x ∂μ
    rw [← integral_map (hInv i).measurable.aemeasurable f.continuous.aestronglyMeasurable,
      (hInv i).map_eq]
  exact hd.induction_on k (isClosed_eq hF continuous_const) hdF

end Mixing
