/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.FourierTests
public import VdC.RectangleTransfer

/-! # Cube Difference -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

noncomputable section

theorem spectrallyLebesgueDistribution_of_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : SpectrallyLebesgueDistribution (torusHaar d) (fun n => cubeToTorus (x n))) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x := by
  intro f hf
  apply spectrallyLebesgue_of_meanSquare_approximation (bounded_test f x)
  intro ε hε
  obtain ⟨g, hg, herr⟩ := exists_centered_torus_approx ((hx.weaklyMixing _).equidistributed _) f hf ε hε
  exact ⟨fun n => g (cubeToTorus (x n)), hx g hg, herr⟩

theorem weaklyMixingDistribution_of_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : WeaklyMixingDistribution (torusHaar d) (fun n => cubeToTorus (x n))) :
    WeaklyMixingDistribution (cubeLebesgue d) x := by
  intro f hf
  apply nearlyWeakMixing_of_cesaro_l2_approx (bounded_test f x)
  intro ε hε
  obtain ⟨g, hg, herr⟩ := exists_centered_torus_approx (hx.equidistributed _) f hf ε hε
  exact ⟨fun n => g (cubeToTorus (x n)), hx g hg, herr⟩

private def pullbackTest {d : ℕ} (g : C(Torus d, ℂ)) : C(Cube d, ℂ) :=
  g.comp ⟨cubeToTorus, continuous_cubeToTorus d⟩

private theorem testMean_pullbackTest {d : ℕ} (g : C(Torus d, ℂ)) :
    testMean (cubeLebesgue d) (pullbackTest g) = testMean (torusHaar d) g := by
  unfold testMean
  rw [← (cubeToTorus_measurePreserving d).map_eq,
    integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable g.continuous.stronglyMeasurable]
  rfl

theorem cube_sLebesgue_iff_characters {d : ℕ} (x : ℕ → Cube d) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      SpectrallyLebesgue (fun n => torusCharacter m (cubeToTorus (x n))) := by
  constructor
  · intro hx m hm
    exact hx (pullbackTest (torusCharacter m)) (by simp [testMean_pullbackTest, testMean_torusCharacter, hm])
  · intro h
    exact spectrallyLebesgueDistribution_of_cubeToTorus ((spectralLebesgueDistribution_iff_torus_characters _).2 h)

theorem cube_weakMixing_iff_characters {d : ℕ} (x : ℕ → Cube d) :
    WeaklyMixingDistribution (cubeLebesgue d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      NearlyWeakMixing (fun n => torusCharacter m (cubeToTorus (x n))) := by
  constructor
  · intro hx m hm
    exact hx (pullbackTest (torusCharacter m)) (by simp [testMean_pullbackTest, testMean_torusCharacter, hm])
  · intro h
    exact weaklyMixingDistribution_of_cubeToTorus ((weaklyMixingDistribution_iff_torus_characters _).2 h)

/-- GeneralizationOfClassicalvdC. The lag-difference discrepancies are those
of the coordinatewise modulo-one representatives. -/
theorem cube_spectral_difference_theorem {d : ℕ} (x : ℕ → Cube d)
    (h : Summable (fun j => upperDifferenceDiscrepancy (fun n => cubeToTorus (x n)) j ^ 2)) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x :=
  spectrallyLebesgueDistribution_of_cubeToTorus <|
    spectral_difference_theorem _ (characterRectangleEstimate_all _) h

/-- WeakMixingUDvdC. The limsup at each lag is taken before the lag average. -/
theorem cube_weakMixing_difference_theorem {d : ℕ} (x : ℕ → Cube d)
    (h : Tendsto (realCesaro (upperDifferenceDiscrepancy (fun n => cubeToTorus (x n)))) atTop (𝓝 0)) :
    WeaklyMixingDistribution (cubeLebesgue d) x :=
  weaklyMixingDistribution_of_cubeToTorus <|
    weakMixing_difference_theorem _ (characterRectangleEstimate_all _) h

/-- The Fourier-coefficient hypothesis from the preliminary spectral criterion. -/
theorem cube_spectral_difference_from_fourier {d : ℕ} (x : ℕ → Cube d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Summable (fun j => limsup (fun N =>
      ‖cesaro (fun n => torusCharacter m (cubeToTorus (x (n + (j + 1))) - cubeToTorus (x n))) N‖ ^ 2) atTop)) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x :=
  spectrallyLebesgueDistribution_of_cubeToTorus (spectral_difference_from_fourier _ h)

/-- The Fourier-coefficient hypothesis from the preliminary weak mixing criterion. -/
theorem cube_weakMixing_difference_from_fourier {d : ℕ} (x : ℕ → Cube d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Tendsto (realCesaro (fun j => limsup (fun N =>
      ‖cesaro (fun n => torusCharacter m (cubeToTorus (x (n + (j + 1))) - cubeToTorus (x n))) N‖) atTop))
      atTop (𝓝 0)) : WeaklyMixingDistribution (cubeLebesgue d) x :=
  weaklyMixingDistribution_of_cubeToTorus (weakMixing_difference_from_fourier _ h)

/-- UniformDistributionvanderCorputsDifferenceTheorem on the closed cube. -/
theorem equidistributed_of_cube_differences {d : ℕ} (x : ℕ → Cube d)
    (h : ∀ h : ℕ, 0 < h → Equidistributed (torusHaar d)
      (fun n => cubeToTorus (x (n + h)) - cubeToTorus (x n))) :
    Equidistributed (cubeLebesgue d) x :=
  equidistributed_of_cubeToTorus (equidistributed_of_torus_differences _ h)

end
end VdC
