/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Difference criteria and joint equidistribution -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace VdC.Submission

noncomputable section

def BoundedSeq (x : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖x n‖ ≤ C

noncomputable def cesaro (x : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, x n) / (N : ℂ)

noncomputable def realCesaro (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, x n) / (N : ℝ)

noncomputable def corr (x y : ℕ → ℂ) (h N : ℕ) : ℂ :=
  cesaro (fun n => x (n + h) * star (y n)) N

def CorrLimits (x y : ℕ → ℂ) (N : ℕ → ℕ) (r : ℕ → ℂ) : Prop :=
  ∀ h, Tendsto (fun q => corr x y h (N q)) atTop (𝓝 (r h))

structure PermissibleTriple (x y : ℕ → ℂ) (N : ℕ → ℕ) : Prop where
  boundedX : BoundedSeq x
  boundedY : BoundedSeq y
  strictMono : StrictMono N
  xx : ∃ r, CorrLimits x x N r
  xy : ∃ r, CorrLimits x y N r
  yx : ∃ r, CorrLimits y x N r
  yy : ∃ r, CorrLimits y y N r

def NearlyOrthogonal (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r → ∀ h, 0 < h → r h = 0

def NearlyWeakMixing (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ y N r, PermissibleTriple x y N → CorrLimits x y N r →
    Tendsto (realCesaro (fun h => ‖r (h + 1)‖)) atTop (𝓝 0)

def circleHaar : Measure UnitAddCircle :=
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  AddCircle.haarAddCircle

def measureFourier (μ : Measure UnitAddCircle) (n : ℤ) : ℂ :=
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  ∫ x, fourier (-n) x ∂μ

def HasSpectrum (r : ℕ → ℂ) (μ : FiniteMeasure UnitAddCircle) : Prop :=
  ∀ h : ℕ, measureFourier μ (h : ℤ) = r h

def SpectrallyLebesgue (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r →
    ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧
      (μ : Measure UnitAddCircle) ≪ circleHaar

section ContinuousTests

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

noncomputable def testMean (μ : Measure X) (f : C(X, ℂ)) : ℂ := ∫ x, f x ∂μ

def Equidistributed (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f))

def OrthogonalDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → NearlyOrthogonal (fun n => f (x n))

def SpectrallyLebesgueDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → SpectrallyLebesgue (fun n => f (x n))

def WeaklyMixingDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → NearlyWeakMixing (fun n => f (x n))

end ContinuousTests

abbrev UnitInterval := Set.Icc (0 : ℝ) 1
abbrev Cube (d : ℕ) := Fin d → UnitInterval

noncomputable def unitIntervalLebesgue : Measure UnitInterval :=
  Measure.comap ((↑) : UnitInterval → ℝ) volume

noncomputable def cubeLebesgue (d : ℕ) : Measure (Cube d) :=
  Measure.pi fun _ => unitIntervalLebesgue

abbrev Torus (d : ℕ) := Fin d → UnitAddCircle

def cubeToTorus {d : ℕ} (x : Cube d) : Torus d := fun i => ((x i : ℝ) : UnitAddCircle)

def rectangleFrequency {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ)
    (a b : Fin d → UnitInterval) : ℝ := by
  classical
  exact (((range N).filter fun n => ∀ i, (a i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ b i).card : ℝ) / N

def rectangleVolume {d : ℕ} (a b : Fin d → UnitInterval) : ℝ :=
  ∏ i, max 0 ((b i : ℝ) - (a i : ℝ))

def rectangleDiscrepancy {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ) : ℝ :=
  sSup (Set.range fun ab : (Fin d → UnitInterval) × (Fin d → UnitInterval) =>
    |rectangleFrequency u N ab.1 ab.2 - rectangleVolume ab.1 ab.2|)

def unitRepresentative (t : UnitAddCircle) : UnitInterval :=
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let y := AddCircle.equivIco (1 : ℝ) (0 : ℝ) t
  ⟨y, ⟨y.property.1, by simpa only [zero_add] using y.property.2.le⟩⟩

def differenceDiscrepancy {d : ℕ} (x : ℕ → Torus d) (h N : ℕ) : ℝ :=
  rectangleDiscrepancy (fun n i => unitRepresentative (x (n + (h + 1)) i - x n i)) N

def upperDifferenceDiscrepancy {d : ℕ} (x : ℕ → Torus d) (h : ℕ) : ℝ :=
  limsup (differenceDiscrepancy x h) atTop

/-- Theorem 3.2. Square-summable upper lag discrepancies imply Lebesgue spectrum. -/
theorem spectral_difference {d : ℕ} (x : ℕ → Cube d)
    (h : Summable (fun j ↦ upperDifferenceDiscrepancy (fun n ↦ cubeToTorus (x n)) j ^ 2)) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x := by
  sorry

/-- Theorem 3.3. Cesàro-small upper lag discrepancies imply weak mixing. -/
theorem weak_mixing_difference {d : ℕ} (x : ℕ → Cube d)
    (h : Tendsto (realCesaro (upperDifferenceDiscrepancy (fun n ↦ cubeToTorus (x n))))
      atTop (𝓝 0)) :
    WeaklyMixingDistribution (cubeLebesgue d) x := by
  sorry

/-- Theorem 3.5. Orthogonality is equivalent to equidistribution at each positive lag. -/
theorem orthogonality_lag_pairs {d : ℕ} (x : ℕ → Cube d) :
    OrthogonalDistribution (cubeLebesgue d) x ↔ ∀ h : ℕ, 0 < h →
      Equidistributed ((cubeLebesgue d).prod (cubeLebesgue d)) (fun n ↦ (x n, x (n+h))) := by
  sorry

end

end VdC.Submission
