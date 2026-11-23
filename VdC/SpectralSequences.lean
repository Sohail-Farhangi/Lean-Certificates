/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Basic
public import VdC.Spectrum

/-! # Spectral classes of bounded sequences -/

@[expose] public section

open MeasureTheory

namespace VdC

/-- Every convergent autocorrelation subsequence has an absolutely
continuous positive finite spectral measure. -/
def SpectrallyLebesgue (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r →
    ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧
      (μ : Measure UnitAddCircle) ≪ circleHaar

/-- Every convergent autocorrelation subsequence has a singular
positive finite spectral measure. -/
def SpectrallySingular (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r →
    ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧
      (μ : Measure UnitAddCircle).MutuallySingular circleHaar

end VdC
