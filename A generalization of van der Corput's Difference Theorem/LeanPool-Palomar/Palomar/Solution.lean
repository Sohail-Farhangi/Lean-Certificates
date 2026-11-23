/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Difference criteria and joint equidistribution -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace VdC

noncomputable section

namespace Submission

/-- Theorem 3.2. Square-summable upper lag discrepancies imply Lebesgue spectrum. -/
theorem spectral_difference {d : ℕ} (x : ℕ → Cube d)
    (h : Summable (fun j ↦ upperDifferenceDiscrepancy (fun n ↦ cubeToTorus (x n)) j ^ 2)) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x := 
  cube_spectral_difference_theorem x h

/-- Theorem 3.3. Cesàro-small upper lag discrepancies imply weak mixing. -/
theorem weak_mixing_difference {d : ℕ} (x : ℕ → Cube d)
    (h : Tendsto (realCesaro (upperDifferenceDiscrepancy (fun n ↦ cubeToTorus (x n))))
      atTop (𝓝 0)) :
    WeaklyMixingDistribution (cubeLebesgue d) x := 
  cube_weakMixing_difference_theorem x h

/-- Theorem 3.5. Orthogonality is equivalent to equidistribution at each positive lag. -/
theorem orthogonality_lag_pairs {d : ℕ} (x : ℕ → Cube d) :
    OrthogonalDistribution (cubeLebesgue d) x ↔ ∀ h : ℕ, 0 < h →
      Equidistributed ((cubeLebesgue d).prod (cubeLebesgue d)) (fun n ↦ (x n, x (n+h))) := 
  cube_orthogonal_iff_lag_pairs x

end Submission

end

end VdC
