/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Spectral measures on the circle -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Haar probability measure on the unit circle. -/
def circleHaar : Measure UnitAddCircle := AddCircle.haarAddCircle

instance circleHaar_probability : IsProbabilityMeasure circleHaar := by
  unfold circleHaar
  infer_instance

/-- Fourier coefficient, with the manuscript's sign convention. -/
def measureFourier (μ : Measure UnitAddCircle) (n : ℤ) : ℂ :=
  ∫ x, fourier (-n) x ∂μ

/-- Realization of the nonnegative-lag correlation sequence by a positive finite measure. -/
def HasSpectrum (r : ℕ → ℂ) (μ : FiniteMeasure UnitAddCircle) : Prop :=
  ∀ h : ℕ, measureFourier μ (h : ℤ) = r h

theorem measureFourier_neg (μ : Measure UnitAddCircle) (n : ℤ) :
    measureFourier μ (-n) = conj (measureFourier μ n) := by
  simp only [measureFourier, ← integral_conj, ← fourier_neg, neg_neg]

theorem measureFourier_zero (μ : Measure UnitAddCircle) :
    measureFourier μ 0 = (μ.real Set.univ : ℂ) := by
  simp only [measureFourier, neg_zero, fourier_zero, integral_const, Complex.real_smul,
    mul_one]

theorem measureFourier_dirac_zero (n : ℤ) :
    measureFourier (Measure.dirac (0 : UnitAddCircle)) n = 1 := by
  rw [measureFourier, integral_dirac, fourier_eval_zero]

theorem measureFourier_add (μ ν : Measure UnitAddCircle) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (n : ℤ) :
    measureFourier (μ + ν) n = measureFourier μ n + measureFourier ν n := by
  have hint (ρ : Measure UnitAddCircle) [IsFiniteMeasure ρ] :
      Integrable (fourier (T := 1) (-n)) ρ :=
    (fourier (-n)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_add_measure (hint μ) (hint ν)

theorem measureFourier_smul (μ : Measure UnitAddCircle) (c : ℝ≥0∞) (n : ℤ) :
    measureFourier (c • μ) n = (c.toReal : ℂ) * measureFourier μ n := by
  rw [measureFourier, integral_smul_measure]
  rfl

private def integrationFunctional (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] :
    C(UnitAddCircle, ℂ) →L[ℂ] ℂ := by
  have hint (f : C(UnitAddCircle, ℂ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let I : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (hint f) (hint g)
      map_smul' := fun a f => integral_smul a f }
  exact I.mkContinuous (μ.real Set.univ) fun f => by
    change ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖
    simpa [mul_comm] using norm_integral_le_of_norm_le_const
      (ae_of_all (μ := μ) fun x => f.norm_coe_le_norm x)

private theorem integrationFunctional_apply (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (f : C(UnitAddCircle, ℂ)) :
    integrationFunctional μ f = ∫ x, f x ∂μ := rfl

/-- A positive finite circle measure is determined by its Fourier coefficients. -/
theorem measure_eq_of_fourier {μ ν : Measure UnitAddCircle} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a, measureFourier μ a = measureFourier ν a) : μ = ν := by
  let Δ := integrationFunctional μ - integrationFunctional ν
  let K := LinearMap.ker Δ.toLinearMap
  have hK : IsClosed (K : Set C(UnitAddCircle, ℂ)) := isClosed_eq Δ.continuous continuous_const
  have he : Submodule.span ℂ (Set.range (@fourier 1)) ≤ K := by
    apply Submodule.span_le.2
    rintro f ⟨a, rfl⟩
    change integrationFunctional μ (fourier a) - integrationFunctional ν (fourier a) = 0
    rw [sub_eq_zero, integrationFunctional_apply, integrationFunctional_apply]
    simpa [measureFourier] using h (-a)
  have htop := (Submodule.span ℂ (Set.range (@fourier 1))).topologicalClosure_minimal he hK
  rw [span_fourier_closure_eq_top] at htop
  have hh (f : C(UnitAddCircle, ℂ)) : integrationFunctional μ f = integrationFunctional ν f := by
    have hk : f ∈ K := htop (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ C(UnitAddCircle, ℂ)))
    change integrationFunctional μ f - integrationFunctional ν f = 0 at hk
    exact sub_eq_zero.mp hk
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : C(UnitAddCircle, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hEq := hh g
  simp only [integrationFunctional_apply, g, ContinuousMap.coe_mk] at hEq
  exact Complex.ofReal_injective (by simpa only [integral_complex_ofReal] using hEq)

/-- Nonnegative-lag Fourier data already determine a positive finite measure. -/
theorem measure_eq_of_fourier_nat {μ ν : Measure UnitAddCircle} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ a : ℕ, measureFourier μ (a : ℤ) = measureFourier ν (a : ℤ)) : μ = ν := by
  apply measure_eq_of_fourier
  intro n
  cases n with
  | ofNat a => exact h a
  | negSucc a =>
    change measureFourier μ (-((a + 1 : ℕ) : ℤ)) = measureFourier ν (-((a + 1 : ℕ) : ℤ))
    rw [measureFourier_neg, measureFourier_neg, h]

end

end VdC
