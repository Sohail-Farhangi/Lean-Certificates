/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.CompactSpectrum

/-! # Mixing Hierarchy -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

/-- Absolutely continuous spectral measures give vanishing self-correlations by
Riemann–Lebesgue, hence the required Cesàro vanishing for all bounded tests. -/
theorem SpectrallyLebesgue.nearlyWeakMixing {x : ℕ → ℂ} (hx : SpectrallyLebesgue x) :
    NearlyWeakMixing x := by
  apply nearlyWeakMixing_of_self_mean hx.1
  intro M r hM hr
  obtain ⟨μ, hμ, hAc⟩ := hx.2 M r hM hr
  change ∀ h : ℕ, measureFourier (μ : Measure UnitAddCircle) (h : ℤ) = r h at hμ
  have hFourier := tendsto_measureFourier_zero_of_ac (μ : Measure UnitAddCircle) hAc
  have hnorm := (hFourier.comp (tendsto_add_atTop_nat 1)).norm
  apply realCesaro_tendsto_zero_of_tendsto_zero (fun _ => norm_nonneg _)
  simpa only [Function.comp_def, hμ, norm_zero] using hnorm

end VdC
