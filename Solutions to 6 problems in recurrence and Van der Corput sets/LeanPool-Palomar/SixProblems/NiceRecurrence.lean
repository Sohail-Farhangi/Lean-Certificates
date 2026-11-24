/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Definitions
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set

variable {G X : Type*} [Group G] [MeasurableSpace X]

theorem event_return_measure_inv (S : System G X) {A : Set X} (hA : MeasurableSet A) (g : G) :
    S.measure (A ∩ S.act g⁻¹ ⁻¹' A) = S.measure (A ∩ S.act g ⁻¹' A) := by
  have hEq : S.act g ⁻¹' (A ∩ S.act g⁻¹ ⁻¹' A) = A ∩ S.act g ⁻¹' A := by
    ext x
    have h : S.act g⁻¹ (S.act g x) = x := by
      change (S.act g⁻¹ ∘ S.act g) x = x
      rw [← S.act_mul, inv_mul_cancel, S.act_one]
      rfl
    simp [h, and_comm]
  have hMeas := hA.inter ((S.preserves g⁻¹).measurable hA)
  rw [← hEq, (S.preserves g).measure_preimage hMeas.nullMeasurableSet]

theorem correlation_indicatorOne (S : System G X) {A : Set X} (hA : MeasurableSet A) (g : G) :
    correlation S (A.indicator (fun _ : X ↦ (1 : ℂ))) g =
      (S.measure (A ∩ S.act g ⁻¹' A)).toReal := by
  classical
  let f := A.indicator (fun _ : X ↦ (1 : ℂ))
  let B := A ∩ S.act g ⁻¹' A
  have hB : MeasurableSet B := hA.inter ((S.preserves g).measurable hA)
  have he (x : X) : f (S.act g x) * (starRingEnd ℂ) (f x) =
      B.indicator (fun _ : X ↦ (1 : ℂ)) x := by
    by_cases hx : x ∈ A <;> by_cases hy : S.act g x ∈ A <;> simp [f, B, hx, hy]
  change (∫ x, f (S.act g x) * (starRingEnd ℂ) (f x) ∂S.measure) = _
  simp_rw [he]
  rw [integral_indicator hB, setIntegral_const, Complex.real_smul, mul_one]
  rfl

/-- Testing the bounded-function condition on indicator functions gives
nice event recurrence, the implication (e) to (a) of Theorem 2.2. -/
theorem niceRecurrence_of_niceVdC {G : Type} [Group G] {R : Set G}
    (hR : NiceVdC R) : NiceRecurrence R := by
  classical
  intro X _ _ S A hA ε hε
  let f := A.indicator (fun _ : X ↦ (1 : ℂ))
  have hf : Measurable f := measurable_const.indicator hA
  have hB (x : X) : ‖f x‖ ≤ 1 := by
    by_cases h : x ∈ A <;> simp [f,h]
  obtain ⟨r, hr, hr'⟩ := hR S f hf ⟨1,hB⟩ ε hε
  refine ⟨r,hr,?_⟩
  change ‖∫ x, A.indicator (fun _ : X ↦ (1 : ℂ)) x ∂S.measure‖ ^ 2 - ε ≤
    ‖correlation S f r⁻¹‖ at hr'
  rw [integral_indicator hA, setIntegral_const, Complex.real_smul, mul_one,
    correlation_indicatorOne S hA, event_return_measure_inv S hA,
    Complex.norm_real, Complex.norm_real, Measure.real_def, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_of_nonneg ENNReal.toReal_nonneg] at hr'
  exact hr'

/-- The implication (a) to (b) of Theorem 2.2. -/
theorem ergodicNiceRecurrence_of_niceRecurrence {G : Type} [Group G] {R : Set G}
    (hR : NiceRecurrence R) : ErgodicNiceRecurrence R :=
  fun S _ A hA ε hε ↦ hR S A hA ε hε

end SixProblems
