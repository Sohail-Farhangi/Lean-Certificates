/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.ErgodicDiscrete
public import VdC.ErgodicWeakMixing

/-! # Ergodic Cube Examples -/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped Topology

namespace VdC

private theorem ae_imp_of_imp_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {P : Prop} {Q : X → Prop} (h : P → ∀ᵐ x ∂μ, Q x) : ∀ᵐ x ∂μ, P → Q x := by
  by_cases hP : P
  · exact (h hP).mono (fun _ hq _ => hq)
  · exact Eventually.of_forall fun _ hp => (hP hp).elim

/-- All six assertions of `LemmaConstructingSequences` on the same full-measure
set. The weak-mixing hypothesis is product ergodicity and the discrete-spectrum
hypothesis is the ordinary dense L² Koopman eigenvector span. -/
theorem ae_constructingSequences_cube {d : ℕ} {T : Cube d → Cube d} {A : Set (Cube d)}
    (hT : Ergodic T (cubeLebesgue d)) (hA : MeasurableSet A) (hpos : 0 < cubeLebesgue d A) :
    ∀ᵐ x ∂cubeLebesgue d,
      (Ergodic (fun p : Cube d × Cube d => (T p.1, T p.2)) ((cubeLebesgue d).prod (cubeLebesgue d)) →
        WeaklyMixingDistribution (cubeLebesgue d) (orbitSequence T x)) ∧
      (KoopmanLebesgueSpectrum (cubeLebesgue d) T →
        SpectrallyLebesgueDistribution (cubeLebesgue d) (orbitSequence T x)) ∧
      (KoopmanDiscreteSpectrumLp hT.toMeasurePreserving → CompactDistribution (orbitSequence T x)) ∧
      (KoopmanDiscreteSpectrumLp hT.toMeasurePreserving →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
          HasPositiveLowerDensity (Set.range σ) ∧ CompactSeq (selectionWeight (Set.range σ))) ∧
      (KoopmanSingularSpectrum (cubeLebesgue d) T → SpectrallySingularDistribution (orbitSequence T x)) ∧
      (KoopmanSingularSpectrum (cubeLebesgue d) T →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
          HasPositiveLowerDensity (Set.range σ) ∧ SpectrallySingular (selectionWeight (Set.range σ))) := by
  filter_upwards [ae_imp_of_imp_ae (fun h => ae_orbit_weaklyMixing hT (koopmanWeakMixing_of_prod_ergodic h)),
    ae_imp_of_imp_ae (ae_orbit_spectrallyLebesgue hT),
    ae_imp_of_imp_ae (fun h => ae_orbit_compact hT (koopmanDiscreteSpectrum_of_Lp hT h)),
    ae_imp_of_imp_ae (fun h => ae_visits_compact hT (koopmanDiscreteSpectrum_of_Lp hT h) hA hpos),
    ae_imp_of_imp_ae (ae_orbit_spectrallySingular hT),
    ae_imp_of_imp_ae (fun h => ae_visits_spectrallySingular hT h hA hpos)] with x h₁ h₂ h₃ h₄ h₅ h₆
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

end VdC
