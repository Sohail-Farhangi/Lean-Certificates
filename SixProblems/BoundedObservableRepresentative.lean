/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Definitions
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Essentially bounded observables and bounded measurable representatives -/

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped ENNReal

theorem MemLp_exists_measurable_bounded_aeEq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : MemLp f ∞ μ) :
    ∃ b : X → ℂ, Measurable b ∧ f =ᵐ[μ] b ∧ ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C := by
  let f' := hf.aestronglyMeasurable.mk f
  let C := lpNorm f ∞ μ
  let A : Set X := {x | ‖f' x‖ ≤ C}
  let b := A.indicator f'
  have hf' : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hm : MeasurableSet A := measurableSet_le hf'.norm measurable_const
  refine ⟨b, hf'.indicator hm, ?_, C, fun x ↦ ?_⟩
  · filter_upwards [hf.aestronglyMeasurable.ae_eq_mk, ae_le_lpNorm_exponent_top hf] with x hx hb
    have hAx : x ∈ A := by
      change ‖f' x‖ ≤ C
      have he : f x = f' x := hx
      rw [← he]
      exact hb
    exact hx.trans (indicator_of_mem hAx f').symm
  · by_cases hx : x ∈ A
    · simpa only [b, indicator_of_mem hx] using (show ‖f' x‖ ≤ C from hx)
    · simpa only [b, indicator_of_notMem hx, norm_zero] using
        (lpNorm_nonneg (f := f) (p := ∞) (μ := μ))

theorem correlation_congr_ae {G X : Type*} [Group G] [MeasurableSpace X] (S : System G X)
    {f b : X → ℂ} (hEq : f =ᵐ[S.measure] b) (g : G) : correlation S f g = correlation S b g := by
  apply integral_congr_ae
  filter_upwards [hEq, (S.preserves g).quasiMeasurePreserving.ae_eq_comp hEq] with x hx hg
  exact congrArg₂ (· * ·) hg (congrArg (starRingEnd ℂ) hx)

/-- Condition (e) of Theorem 2.2 can be tested on all `L∞` observables. -/
theorem niceVdC_iff_memLp_top {G : Type} [Group G] {R : Set G} : NiceVdC R ↔
    ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X] (S : System G X) (f : X → ℂ),
      MemLp f ∞ S.measure → ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
        ‖∫ x, f x ∂S.measure‖ ^ 2 - ε ≤ ‖correlation S f r⁻¹‖ := by
  constructor
  · intro h X _ _ S f hf ε hε
    obtain ⟨b,hb,hEq,hBound⟩ := MemLp_exists_measurable_bounded_aeEq hf
    obtain ⟨r,hr,hI⟩ := h S b hb hBound ε hε
    exact ⟨r,hr, by rwa [integral_congr_ae hEq, correlation_congr_ae S hEq]⟩
  · intro h X _ _ S f hf ⟨C, hC⟩ ε hε
    exact h S f (memLp_top_of_bound hf.aestronglyMeasurable C (.of_forall hC)) ε hε

end SixProblems
