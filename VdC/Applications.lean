/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.LagPairs
public import VdC.Selection
public import VdC.Torus
public import VdC.MixingHierarchy
public import VdC.SpectralScalars
public import VdC.SpectralResults

/-! # Applications -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

section

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

def SpectrallyLebesgueDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → SpectrallyLebesgue (fun n => f (x n))

def WeaklyMixingDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → NearlyWeakMixing (fun n => f (x n))

def SpectrallySingularDistribution (y : ℕ → Y) : Prop :=
  ∀ g : C(Y, ℂ), SpectrallySingular (fun n => g (y n))

def CompactDistribution (y : ℕ → Y) : Prop :=
  ∀ g : C(Y, ℂ), CompactSeq (fun n => g (y n))

theorem WeaklyMixingDistribution.equidistributed (μ : Measure X) [IsProbabilityMeasure μ]
    {x : ℕ → X} (hx : WeaklyMixingDistribution μ x) : Equidistributed μ x :=
  equidistributed_of_centered_tests μ x fun f hf => (hx f hf).cesaro_zero

omit [BorelSpace X] [CompactSpace X] in
theorem SpectrallyLebesgueDistribution.weaklyMixing (μ : Measure X) {x : ℕ → X}
    (hx : SpectrallyLebesgueDistribution μ x) : WeaklyMixingDistribution μ x :=
  fun f hf => (hx f hf).nearlyWeakMixing

omit [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
theorem CompactDistribution.spectrallySingular {y : ℕ → Y} (hy : CompactDistribution y) :
    SpectrallySingularDistribution y := fun g => spectrallySingular_of_compactSeq (hy g)

/-- PropertiesOfsLSequences(i), singular-indicator version. -/
theorem equidistributed_selected_of_sl_singular (μ : Measure X) [IsProbabilityMeasure μ]
    {x : ℕ → X} (hx : SpectrallyLebesgueDistribution μ x) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hd : HasPositiveLowerDensity (Set.range σ)) (hc : SpectrallySingular (selectionWeight (Set.range σ))) :
    Equidistributed μ (x ∘ σ) := by
  apply equidistributed_of_centered_tests
  intro f hf
  change Tendsto (cesaro fun k => f (x (σ k))) atTop (𝓝 0)
  exact tendsto_cesaro_selected_zero (fun n => f (x n)) hσ hd
    (cesaro_product_tendsto_zero_of_ac_singular (hx f hf) hc)

/-- PropertiesOfsLSequences(i), compact-indicator version. -/
theorem equidistributed_selected_of_wm_compact (μ : Measure X) [IsProbabilityMeasure μ]
    {x : ℕ → X} (hx : WeaklyMixingDistribution μ x) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hd : HasPositiveLowerDensity (Set.range σ)) (hc : CompactSeq (selectionWeight (Set.range σ))) :
    Equidistributed μ (x ∘ σ) := by
  apply equidistributed_of_centered_tests
  intro f hf
  change Tendsto (cesaro fun k => f (x (σ k))) atTop (𝓝 0)
  exact tendsto_cesaro_selected_zero (fun n => f (x n)) hσ hd
    (nearlyWeakMixing_mul_compact (hx f hf) hc)

/-- PropertiesOfsLSequences(ii), compact second factor. -/
theorem equidistributed_pair_of_wm_compact [T2Space X] [T2Space Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {x : ℕ → X} {y : ℕ → Y} (hx : WeaklyMixingDistribution μ x)
    (hy : Equidistributed ν y) (hc : CompactDistribution y) :
    Equidistributed (μ.prod ν) (fun n => (x n, y n)) := by
  apply (equidistributed_prod_iff μ ν x y).2
  apply product_means_of_centered_tests μ ν x y (hx.equidistributed μ) hy
  intro f g hf _
  exact nearlyWeakMixing_mul_compact (hx f hf) (hc g)

/-- PropertiesOfsLSequences(ii), spectrally singular second factor. -/
theorem equidistributed_pair_of_sl_singular [T2Space X] [T2Space Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {x : ℕ → X} {y : ℕ → Y} (hx : SpectrallyLebesgueDistribution μ x)
    (hy : Equidistributed ν y) (hc : SpectrallySingularDistribution y) :
    Equidistributed (μ.prod ν) (fun n => (x n, y n)) := by
  apply (equidistributed_prod_iff μ ν x y).2
  apply product_means_of_centered_tests μ ν x y ((hx.weaklyMixing μ).equidistributed μ) hy
  intro f g hf _
  exact cesaro_product_tendsto_zero_of_ac_singular (hx f hf) (hc g)

end

noncomputable section

/-- The classical difference theorem, using Haar uniform distribution. -/
theorem equidistributed_of_torus_differences {d : ℕ} (x : ℕ → Torus d)
    (h : ∀ h : ℕ, 0 < h → Equidistributed (torusHaar d) (fun n => x (n + h) - x n)) :
    Equidistributed (torusHaar d) x := by
  apply (equidistributed_torus_iff x).2
  intro m hm
  apply NearlyOrthogonal.tendsto_cesaro_zero
  apply (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test (torusCharacter m) x)).2
  intro k hk
  change Tendsto (cesaro fun n => torusCharacter m (x (n + k)) * star (torusCharacter m (x n))) atTop (𝓝 0)
  simpa only [torusCharacter_point_sub] using
    (equidistributed_torus_iff _).1 (h k hk) m hm

/-- The modulo-one sum corollary for a weakly mixing and a compact distribution. -/
theorem equidistributed_torus_add_of_wm_compact {d : ℕ} {x y : ℕ → Torus d}
    (hx : WeaklyMixingDistribution (torusHaar d) x) (hy : CompactDistribution y) :
    Equidistributed (torusHaar d) (fun n => x n + y n) := by
  apply (equidistributed_torus_iff _).2
  intro m hm
  have h0 : testMean (torusHaar d) (torusCharacter m) = 0 := by simp [testMean_torusCharacter, hm]
  simpa only [torusCharacter_point_add, id_eq] using nearlyWeakMixing_mul_compact (hx _ h0) (hy (torusCharacter m))

/-- The modulo-one sum corollary for absolutely continuous and singular spectra. -/
theorem equidistributed_torus_add_of_sl_singular {d : ℕ} {x y : ℕ → Torus d}
    (hx : SpectrallyLebesgueDistribution (torusHaar d) x) (hy : SpectrallySingularDistribution y) :
    Equidistributed (torusHaar d) (fun n => x n + y n) := by
  apply (equidistributed_torus_iff _).2
  intro m hm
  have h0 : testMean (torusHaar d) (torusCharacter m) = 0 := by simp [testMean_torusCharacter, hm]
  simpa only [torusCharacter_point_add] using
    cesaro_product_tendsto_zero_of_ac_singular (hx _ h0) (hy (torusCharacter m))

end
end VdC
