/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MeasuredMeans
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Coefficient moments and weak returns for a measured mean

The argument for Theorem 4.2(ii) and (iii) uses the topology induced by all
dual evaluations. A positive normalized mean gives a full-mass filter, so
the topology supplies all finite intersections of coefficient tests.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace JdLG.MeasuredMean

variable {S : Type*} [MeasurableSpace S] {μ : Measure S}
  (m : MeasuredMean μ)

/-- When all open preimages are measurable, convergence in the full-mass
filter is the assertion that each neighborhood has return mass one. -/
theorem tendsto_fullMassFilter_iff {X : Type*} [TopologicalSpace X]
    (φ : S → X) (y : X) (hφ : ∀ U : Set X, IsOpen U → MeasurableSet (φ ⁻¹' U)) :
    Tendsto φ m.fullMassFilter (𝓝 y) ↔
      ∀ U : Set X, ∀ hU : IsOpen U, y ∈ U → m.mass (φ ⁻¹' U) (hφ U hU) = 1 := by
  constructor
  · intro h U hU hy
    exact (m.mem_fullMassFilter_iff (hφ U hU)).1 ((tendsto_def.1 h) U (hU.mem_nhds hy))
  · intro h
    apply tendsto_def.2
    intro V hV
    obtain ⟨U, hUV, hU, hy⟩ := mem_nhds_iff.1 hV
    have hmem := (m.mem_fullMassFilter_iff (hφ U hU)).2 (h U hU hy)
    exact m.fullMassFilter.sets_of_superset hmem (preimage_mono hUV)

private theorem mass_strictThreshold_eq_one_iff {f : S → ℝ} (hf : Measurable f) (ε : ℝ) :
    m.mass {s | f s < ε} (measurableSet_lt hf measurable_const) = 1 ↔
      m.mass {s | ε ≤ f s} (measurableSet_le measurable_const hf) = 0 := by
  have heq : {s | f s < ε}ᶜ = {s | ε ≤ f s} := by
    ext s
    simp
  have h := m.mass_compl_add (measurableSet_lt hf (measurable_const (a := ε)))
  have h' : m.mass {s | f s < ε} (measurableSet_lt hf measurable_const) +
      m.mass {s | ε ≤ f s} (measurableSet_le measurable_const hf) = 1 := by
    simpa only [heq] using h
  constructor <;> intro h₀ <;> linarith

/-- The positive-power moment of the absolute value of a bounded measurable
function is an actual `L∞` element. -/
theorem memLp_norm_rpow {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    {g : S → F} (hg : Measurable g) {p : ℝ} (hp : 0 < p)
    {C : ℝ} (hC : ∀ s, ‖g s‖ ≤ C) : MemLp (fun s ↦ ‖g s‖ ^ p) ∞ μ := by
  have hm := (Real.continuous_rpow_const hp.le).measurable.comp hg.norm
  refine memLp_top_of_bound hm.aestronglyMeasurable (C ^ p) (ae_of_all _ fun s ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (hC s) hp.le

/-- Vanishing of one positive-power moment is equivalent to convergence to
zero in the mean filter for the underlying bounded scalar coefficient. -/
theorem norm_rpow_value_eq_zero_iff {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F]
    {g : S → F} (hg : Measurable g) {p : ℝ} (hp : 0 < p) {C : ℝ} (hC : ∀ s, ‖g s‖ ≤ C) :
    m.value (fun s ↦ ‖g s‖ ^ p) (memLp_norm_rpow hg hp hC) = 0 ↔
      Tendsto g m.fullMassFilter (𝓝 0) := by
  let f : S → ℝ := fun s ↦ ‖g s‖ ^ p
  have hfm : Measurable f := (Real.continuous_rpow_const hp.le).measurable.comp hg.norm
  have hnonneg (s : S) : 0 ≤ f s := Real.rpow_nonneg (norm_nonneg _) p
  have hfC (s : S) : f s ≤ C ^ p := Real.rpow_le_rpow (norm_nonneg _) (hC s) hp.le
  rw [m.value_eq_zero_iff_mass_tail_eq_zero hfm (memLp_norm_rpow hg hp hC) hnonneg _ hfC]
  constructor
  · intro h
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hpε : 0 < ε ^ p := Real.rpow_pos_of_pos hε _
    have hmeas := measurableSet_lt hfm (measurable_const (a := ε ^ p))
    have hset := (m.mem_fullMassFilter_iff hmeas).2
      ((m.mass_strictThreshold_eq_one_iff hfm (ε ^ p)).2 (h _ hpε))
    exact m.fullMassFilter.sets_of_superset hset fun s hs ↦ by
      change dist (g s) 0 < ε
      rw [dist_zero_right]
      exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hp).1 hs
  · intro h ε hε
    have hmeas := measurableSet_lt hfm (measurable_const (a := ε))
    apply (m.mass_strictThreshold_eq_one_iff hfm ε).1
    apply (m.mem_fullMassFilter_iff hmeas).1
    have hroot : 0 < ε ^ p⁻¹ := Real.rpow_pos_of_pos hε _
    have ht := Metric.tendsto_nhds.1 h (ε ^ p⁻¹) hroot
    exact m.fullMassFilter.sets_of_superset ht fun s hs ↦ by
      change dist (g s) 0 < ε ^ p⁻¹ at hs
      rw [dist_zero_right] at hs
      change ‖g s‖ ^ p < ε
      have hlt := (Real.rpow_lt_rpow_iff (norm_nonneg _) hroot.le hp).2 hs
      rwa [← Real.rpow_mul hε.le, inv_mul_cancel₀ hp.ne', Real.rpow_one] at hlt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The equivalence of Theorem 4.2(ii) and (iii). The hypotheses are the
measurability and boundedness of the indicated tests. The left-invariance of
the mean is needed for its comparison with almost weak stability. -/
theorem weakReturns_iff_coefficientMoments (φ : S → E)
    (hopen : ∀ U : Set (WeakSpace ℂ E), IsOpen U →
      MeasurableSet ((fun s ↦ toWeakSpace ℂ E (φ s)) ⁻¹' U))
    (hmeas : ∀ f : StrongDual ℂ E, Measurable fun s ↦ f (φ s))
    (C : StrongDual ℂ E → ℝ) (hC : ∀ f : StrongDual ℂ E, ∀ s, ‖f (φ s)‖ ≤ C f)
    (p : ℝ) (hp : 0 < p) :
    (∀ U : Set (WeakSpace ℂ E), ∀ hU : IsOpen U, 0 ∈ U →
      m.mass ((fun s ↦ toWeakSpace ℂ E (φ s)) ⁻¹' U) (hopen U hU) = 1) ↔
      ∀ f : StrongDual ℂ E,
        m.value (fun s ↦ ‖f (φ s)‖ ^ p) (memLp_norm_rpow (hmeas f) hp (hC f)) = 0 := by
  rw [← m.tendsto_fullMassFilter_iff _ _ hopen]
  have hi : Function.Injective (topDualPairing ℂ E).flip :=
    separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℂ E)
  have hweak := WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℂ E).flip hi
    (f := fun s ↦ φ s) (x := 0) (l := m.fullMassFilter)
  refine hweak.trans ?_
  change (∀ f : StrongDual ℂ E, Tendsto (fun s ↦ f (φ s)) m.fullMassFilter (𝓝 (f 0))) ↔ _
  simp only [map_zero]
  exact forall_congr' fun f ↦ (m.norm_rpow_value_eq_zero_iff (hmeas f) hp (hC f)).symm

end JdLG.MeasuredMean
