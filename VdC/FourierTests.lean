/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Rectangles
public import VdC.Applications

/-! # Fourier Tests -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

private theorem center_add (f g : C(X, ℂ)) : center μ (f + g) = center μ f + center μ g := by
  ext x
  simp [center, testMean_add]
  ring

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
private theorem center_smul (c : ℂ) (f : C(X, ℂ)) : center μ (c • f) = c • center μ f := by
  ext x
  simp [center, testMean_smul, mul_sub]

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
private theorem center_zero : center μ (0 : C(X, ℂ)) = 0 := by
  ext x
  simp [center, testMean]

omit [BorelSpace X] in
private theorem norm_testMean_le (f : C(X, ℂ)) : ‖testMean μ f‖ ≤ ‖f‖ := by
  simpa [testMean] using norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall fun a => ContinuousMap.norm_coe_le_norm f a)

private theorem centered_test_approximation (x : ℕ → X) (f : C(X, ℂ)) (hf : testMean μ f = 0)
    (s : Set C(X, ℂ)) (hd : (Submodule.span ℂ s).topologicalClosure = ⊤)
    (P : (ℕ → ℂ) → Prop) (hzero : P (fun _ => 0))
    (hadd : ∀ u v, P u → P v → P (fun n => u n + v n))
    (hsmul : ∀ u, ∀ c : ℂ, P u → P (fun n => c * u n))
    (hs : ∀ g ∈ s, P (fun n => center μ g (x n)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℕ → ℂ, P u ∧ ∀ᶠ N in atTop, realCesaro (fun n => ‖f (x n) - u n‖ ^ 2) N ≤ ε := by
  have hspan : ∀ g ∈ Submodule.span ℂ s, P (fun n => center μ g (x n)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg => exact hs g hg
    | zero => simpa only [center_zero, ContinuousMap.zero_apply] using hzero
    | add g k _ _ hg hk => simpa only [center_add, ContinuousMap.add_apply] using hadd _ _ hg hk
    | smul c g _ hg => simpa only [center_smul, ContinuousMap.smul_apply, smul_eq_mul] using hsmul _ c hg
  have hclose : f ∈ closure (↑(Submodule.span ℂ s) : Set C(X, ℂ)) := by
    change f ∈ (Submodule.span ℂ s).topologicalClosure
    rw [hd]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hclose (Real.sqrt ε / 2) (by positivity)
  rw [dist_eq_norm] at hdist
  refine ⟨fun n => center μ g (x n), hspan g hg, Eventually.of_forall fun N => ?_⟩
  have hnorm (n : ℕ) : ‖f (x n) - center μ g (x n)‖ ≤ Real.sqrt ε := by
    have hmean : ‖testMean μ g‖ ≤ ‖f - g‖ := by
      simpa [testMean_sub, hf] using norm_testMean_le μ (f - g)
    have ht := (norm_add_le (f (x n) - g (x n)) (testMean μ g)).trans
      (add_le_add (ContinuousMap.norm_coe_le_norm (f - g) (x n)) hmean)
    have he : f (x n) - center μ g (x n) = (f (x n) - g (x n)) + testMean μ g := by
      simp [center]
      ring
    rw [he]
    linarith only [ht, hdist]
  have hsqr (n : ℕ) : ‖f (x n) - center μ g (x n)‖ ^ 2 ≤ ε := by
    rw [← Real.sq_sqrt hε.le]
    gcongr
    exact hnorm n
  by_cases hN : 0 < N
  · exact (realCesaro_mono hsqr N).trans_eq (realCesaro_const_pos ε hN)
  · simp [realCesaro, Nat.eq_zero_of_not_pos hN, hε.le]

end

noncomputable section

private theorem center_torusCharacter_nonzero {d : ℕ} {m : Fin d → ℤ} (hm : m ≠ 0) :
    center (torusHaar d) (torusCharacter m) = torusCharacter m := by
  ext x
  simp [center, testMean_torusCharacter, hm]

private theorem center_torusCharacter_zero {d : ℕ} :
    center (torusHaar d) (torusCharacter (0 : Fin d → ℤ)) = 0 := by
  unfold center
  rw [testMean_torusCharacter, ite_eq_left rfl, torusCharacter_zero]
  ext x
  simp

/-- Integer characters suffice for the spectral Lebesgue definition on the torus. -/
theorem spectralLebesgueDistribution_iff_torus_characters {d : ℕ} (x : ℕ → Torus d) :
    SpectrallyLebesgueDistribution (torusHaar d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      SpectrallyLebesgue (fun n => torusCharacter m (x n)) := by
  constructor
  · intro h m hm
    exact h _ (by simp [testMean_torusCharacter, hm])
  · intro h f hf
    apply spectrallyLebesgue_of_meanSquare_approximation (bounded_test f x)
    apply centered_test_approximation _ x f hf _ (torusCharacters_dense d) SpectrallyLebesgue
      spectrallyLebesgue_zero (fun _ _ hu hv => hu.add hv) (fun _ c hu => hu.const_mul c)
    rintro _ ⟨m, rfl⟩
    by_cases hm : m = 0
    · subst m
      simpa only [center_torusCharacter_zero, ContinuousMap.zero_apply] using spectrallyLebesgue_zero
    · simpa only [center_torusCharacter_nonzero hm] using h m hm

/-- Integer characters suffice for the weak mixing definition on the torus. -/
theorem weaklyMixingDistribution_iff_torus_characters {d : ℕ} (x : ℕ → Torus d) :
    WeaklyMixingDistribution (torusHaar d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      NearlyWeakMixing (fun n => torusCharacter m (x n)) := by
  constructor
  · intro h m hm
    exact h _ (by simp [testMean_torusCharacter, hm])
  · intro h f hf
    have hzero : NearlyWeakMixing (fun _ => 0) := by
      apply (NearlyOrthogonal.nearlyWeakMixing (x := fun _ => 0))
      apply (nearlyOrthogonal_iff_corr_tendsto_zero ⟨0, le_rfl, by simp⟩).2
      intro k hk
      have he : corr (fun _ => 0) (fun _ => 0) k = fun _ => 0 := by ext N; simp [corr, cesaro]
      rw [he]
      exact tendsto_const_nhds
    apply nearlyWeakMixing_of_cesaro_l2_approx (bounded_test f x)
    apply centered_test_approximation _ x f hf _ (torusCharacters_dense d) NearlyWeakMixing hzero
    · intro u v hu hv
      simpa only [one_mul] using hu.add_const_mul hv 1
    · intro u c hu
      simpa only [zero_add] using hzero.add_const_mul hu c
    · rintro _ ⟨m, rfl⟩
      by_cases hm : m = 0
      · subst m
        simpa only [center_torusCharacter_zero, ContinuousMap.zero_apply] using hzero
      · simpa only [center_torusCharacter_nonzero hm] using h m hm

/-- PreliminaryVersionOfUniformDistributionLebesgueSpectrumvdC on the torus. -/
theorem spectral_difference_from_fourier {d : ℕ} (x : ℕ → Torus d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Summable (fun j => limsup
      (fun N => ‖cesaro (fun n => torusCharacter m (x (n + (j + 1)) - x n)) N‖ ^ 2) atTop)) :
    SpectrallyLebesgueDistribution (torusHaar d) x := by
  apply (spectralLebesgueDistribution_iff_torus_characters x).2
  intro m hm
  apply spectrallyLebesgue_of_limsup_square_summable (bounded_test (torusCharacter m) x)
  simpa only [torusCharacter_point_sub, corr] using h m hm

/-- PreliminaryVersionOfUniformDistributionWeakMixingvdC on the torus. -/
theorem weakMixing_difference_from_fourier {d : ℕ} (x : ℕ → Torus d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Tendsto (realCesaro (fun j => limsup
      (fun N => ‖cesaro (fun n => torusCharacter m (x (n + (j + 1)) - x n)) N‖) atTop)) atTop (𝓝 0)) :
    WeaklyMixingDistribution (torusHaar d) x := by
  apply (weaklyMixingDistribution_iff_torus_characters x).2
  intro m hm
  apply nearlyWeakMixing_of_upper_corr (bounded_test (torusCharacter m) x)
  simpa only [torusCharacter_point_sub, corr] using h m hm

/-- Torus version of GeneralizationOfClassicalvdC with the finite rectangle
estimate supplied as a hypothesis. -/
theorem spectral_difference_theorem {d : ℕ} (x : ℕ → Torus d) (hKH : CharacterRectangleEstimate x)
    (hD : Summable (fun h => upperDifferenceDiscrepancy x h ^ 2)) :
    SpectrallyLebesgueDistribution (torusHaar d) x :=
  (spectralLebesgueDistribution_iff_torus_characters x).2
    (spectral_character_of_rectangle_discrepancy x hKH hD)

/-- Torus version of WeakMixingUDvdC with the finite rectangle estimate
supplied as a hypothesis. -/
theorem weakMixing_difference_theorem {d : ℕ} (x : ℕ → Torus d) (hKH : CharacterRectangleEstimate x)
    (hD : Tendsto (realCesaro (upperDifferenceDiscrepancy x)) atTop (𝓝 0)) :
    WeaklyMixingDistribution (torusHaar d) x :=
  (weaklyMixingDistribution_iff_torus_characters x).2
    (weakMixing_character_of_rectangle_discrepancy x hKH hD)

end
end VdC
