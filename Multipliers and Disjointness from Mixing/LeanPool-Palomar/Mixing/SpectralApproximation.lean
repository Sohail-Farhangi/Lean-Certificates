/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CyclicL2
public import Mixing.StrongMixing
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Pointwise trigonometric approximation and spectral disjointness -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace Mixing

/-- If the integrals of a pointwise-convergent sequence over every measurable
set tend to zero, then the pointwise limit vanishes almost everywhere. The
argument uses the increasing sets on which the entire convergent sequence
and its limit are bounded by an integer. -/
theorem ae_eq_zero_of_setIntegral_tendsto_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X → ℂ} {F : X → ℂ} (hm : ∀ n, Measurable (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hTest : ∀ A : Set X, MeasurableSet A → Tendsto (fun n => ∫ x in A, f n x ∂μ) atTop (𝓝 0)) :
    F =ᵐ[μ] 0 := by
  have hF : Measurable F := measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr hlim)
  let A (k : ℕ) := {x | ‖F x‖ ≤ k} ∩ ⋂ n, {x | ‖f n x‖ ≤ k}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    (measurableSet_le hF.norm measurable_const).inter
      (MeasurableSet.iInter fun n => measurableSet_le (hm n).norm measurable_const)
  have hAll (x : X) : ∃ k : ℕ, x ∈ A k := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto (fun n => f n x) (hlim x))
    obtain ⟨k, hk⟩ := exists_nat_ge (max C ‖F x‖)
    refine ⟨k, (le_max_right _ _).trans hk, Set.mem_iInter.mpr fun n => ?_⟩
    exact (hC _ (Set.mem_range_self n)).trans ((le_max_left _ _).trans hk)
  have hCut (k : ℕ) : F =ᵐ[μ.restrict (A k)] 0 := by
    have hi : Integrable F (μ.restrict (A k)) := Integrable.of_bound hF.aestronglyMeasurable k
      ((ae_restrict_iff' (hA k)).mpr (.of_forall fun _ hx => hx.1))
    apply hi.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro B hB _
    rw [Measure.restrict_restrict hB, Set.inter_comm]
    have hAB := (hA k).inter hB
    have ht := tendsto_integral_of_dominated_convergence (μ := μ.restrict (A k ∩ B)) (fun _ => (k : ℝ))
      (fun n => (hm n).aestronglyMeasurable) (integrable_const _)
      (fun n => (ae_restrict_iff' hAB).mpr (.of_forall fun x hx => Set.mem_iInter.mp hx.1.2 n))
      (.of_forall hlim)
    exact tendsto_nhds_unique ht (hTest (A k ∩ B) hAB)
  have hCut' (k : ℕ) : ∀ᵐ x ∂μ, x ∈ A k → F x = 0 :=
    (ae_restrict_iff' (hA k)).mp (hCut k)
  filter_upwards [ae_all_iff.mpr hCut'] with x hx
  obtain ⟨k, hk⟩ := hAll x
  exact hx k hk

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator injectivity underlying Corollary 5(iii). The assumptions
are pointwise convergence on the unitary characters, weak operator
convergence of the evaluated polynomials, and a countable zero set. -/
theorem ultrafilterOperator_injective_of_trigonometric_approximation
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (p : Ultrafilter G)
    (a : ℕ → G →₀ ℂ) (F : (G →* Circle) → ℂ)
    (hPt : ∀ χ, Tendsto (fun n => trigonometricPolynomial (a n) χ) atTop (𝓝 (F χ)))
    (hW : Tendsto (fun n => ContinuousLinearMapWOT.ofCLM (trigonometricOperator U (a n)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (ultrafilterOperator U p))))
    (hF : {χ | F χ = 0}.Countable) :
    Function.Injective (ultrafilterOperator U p) := by
  change Function.Injective (ultrafilterOperator U p).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change ultrafilterOperator U p x = 0 at hx
  let μ := vectorSpectralMeasure U x
  let f (n : ℕ) : RepresentationSpectrum U → ℂ := spectralPolynomial U (a n)
  let g (z : RepresentationSpectrum U) := F (spectralPointCharacter U z)
  have hlim (z : RepresentationSpectrum U) : Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
    simpa only [f, spectralPolynomial_apply] using hPt (spectralPointCharacter U z)
  have hTest (A : Set (RepresentationSpectrum U)) (hA : MeasurableSet A) :
      Tendsto (fun n => ∫ z in A, f n z ∂μ) atTop (𝓝 0) := by
    let w := cyclicSpectralIsometry U x (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ))
    have hInner (n : ℕ) : (∫ z in A, f n z ∂μ) =
        ⟪w, trigonometricOperator U (a n) x⟫_ℂ := by
      simpa only [f, μ, w, spectralCalculus_spectralPolynomial] using
        (inner_cyclicSpectralIsometry_indicator U x hA (spectralPolynomial U (a n))).symm
    have ht := ((ContinuousLinearMapWOT.continuous_dual_apply x
      (InnerProductSpace.toDual ℂ H w)).tendsto _).comp hW
    change Tendsto (fun n => ⟪w, trigonometricOperator U (a n) x⟫_ℂ) atTop
      (𝓝 ⟪w, ultrafilterOperator U p x⟫_ℂ) at ht
    simpa only [hInner, hx, inner_zero_right] using ht
  have hg : g =ᵐ[μ] 0 := ae_eq_zero_of_setIntegral_tendsto_zero
    (fun n => (spectralPolynomial U (a n)).continuous.measurable) hlim hTest
  let _ : NullSingletonClass μ := vectorSpectralMeasure_noAtoms_of_ultrafilterOperator_apply_eq_zero U x p hx
  have hZ : {z | g z = 0}.Countable := hF.preimage (spectralPointCharacter_injective U)
  have hFalse : ∀ᵐ _ ∂μ, False := by
    filter_upwards [hZ.ae_notMem μ, hg] with z hz hz'
    exact hz hz'
  have hMass : μ Set.univ = 0 := by
    simpa only [ae_iff, not_false_eq_true, Set.ofPred_true] using hFalse
  have hNorm := vectorSpectralMeasure_mass U x
  change (μ Set.univ).toReal = ‖x‖ ^ 2 at hNorm
  rw [hMass, ENNReal.toReal_zero] at hNorm
  rw [Submodule.mem_bot, ← norm_eq_zero]
  exact sq_eq_zero_iff.mp hNorm.symm

/-- Corollary 5(iii), spectral disjointness from actions mixing along the
same ultrafilter. -/
theorem spectrallyDisjoint_of_trigonometric_approximation
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K)) (p : Ultrafilter G)
    (a : ℕ → G →₀ ℂ) (F : (G →* Circle) → ℂ)
    (hPt : ∀ χ, Tendsto (fun n => trigonometricPolynomial (a n) χ) atTop (𝓝 (F χ)))
    (hW : Tendsto (fun n => ContinuousLinearMapWOT.ofCLM (trigonometricOperator U (a n)))
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM (ultrafilterOperator U p))))
    (hF : {χ | F χ = 0}.Countable) (hV : ultrafilterOperator V p = 0) :
    SpectrallyDisjoint U V :=
  spectrallyDisjoint_of_ultrafilterOperator_injective U V p
    (ultrafilterOperator_injective_of_trigonometric_approximation U p a F hPt hW hF) hV

end Mixing
