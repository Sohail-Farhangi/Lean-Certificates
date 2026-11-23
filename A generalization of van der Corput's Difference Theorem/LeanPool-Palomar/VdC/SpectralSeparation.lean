/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Distribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Spectral Separation -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Distinct squared-mean limits for the same continuous tests force mutual singularity. -/
theorem mutuallySingular_of_distinct_squared_mean_limits (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (F : ℕ → C(X, ℂ)) {a b : ℂ} (hab : a ≠ b)
    (ha : Tendsto (fun n => ∫ x, ‖F n x - a‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hb : Tendsto (fun n => ∫ x, ‖F n x - b‖ ^ 2 ∂ν) atTop (𝓝 0)) : μ.MutuallySingular ν := by
  have hmeasure (ρ : Measure X) [IsFiniteMeasure ρ] (c : ℂ)
      (hc : Tendsto (fun n => ∫ x, ‖F n x - c‖ ^ 2 ∂ρ) atTop (𝓝 0)) :
      TendstoInMeasure ρ (fun n x => F n x) atTop (fun _ => c) := by
    apply tendstoInMeasure_iff_measureReal_dist.2
    intro ε hε
    have ht : Tendsto (fun n => (∫ x, ‖F n x - c‖ ^ 2 ∂ρ) / ε ^ 2) atTop (𝓝 0) := by
      simpa only [zero_div] using hc.div_const (ε ^ 2)
    refine squeeze_zero (fun _ => measureReal_nonneg) ?_ ht
    · intro n
      have hf : Integrable (fun x => ‖F n x - c‖ ^ 2) ρ :=
        ((F n).continuous.sub continuous_const).norm.pow 2 |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hM := mul_meas_ge_le_integral_of_nonneg (μ := ρ)
        (Eventually.of_forall fun x => sq_nonneg ‖F n x - c‖) hf (ε ^ 2)
      have hh : ρ.real { x | ε ≤ dist (F n x) c } ≤ ρ.real { x | ε ^ 2 ≤ ‖F n x - c‖ ^ 2 } :=
        measureReal_mono (fun x hx => by
          change ε ≤ dist (F n x) c at hx
          rw [dist_eq_norm] at hx
          exact pow_le_pow_left₀ hε.le hx 2)
      apply (le_div_iff₀ (sq_pos_of_pos hε)).2
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left hh (sq_nonneg ε)).trans hM
  obtain ⟨φ, hφ, hμ⟩ := (hmeasure μ a ha).exists_seq_tendsto_ae
  obtain ⟨ψ, hψ, hν⟩ := ((hmeasure ν b hb).comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  let E := {x | Tendsto (fun n => F (φ (ψ n)) x) atTop (𝓝 a)}
  have hE : MeasurableSet E :=
    measurableSet_tendsto_fun (fun n => (F (φ (ψ n))).continuous.measurable) measurable_const
  refine ⟨Eᶜ, hE.compl, ?_, ?_⟩
  · exact ae_iff.1 (hμ.mono fun x hx => hx.comp hψ.tendsto_atTop)
  · rw [compl_compl]
    have hbad : ∀ᵐ x ∂ν, x ∉ E := hν.mono fun x hb' ha' => hab (tendsto_nhds_unique ha' hb')
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.1 hbad

/-- If the real Gram coefficients of bounded continuous tests are controlled
by a decaying Toeplitz envelope, the Cesàro means tend to zero in mean square. -/
theorem tendsto_squareIntegral_cesaro_of_gram (μ : Measure X) [IsFiniteMeasure μ]
    (u : ℕ → C(X, ℂ)) (D : ℕ → ℝ) (hD : ∀ h, 0 ≤ D h)
    (hlim : Tendsto D atTop (𝓝 0))
    (hGram : ∀ i j : ℕ, (testMean μ (u i * star (u j))).re ≤ D (i-j+(j-i))) :
    Tendsto (fun N => ∫ x, ‖cesaro (fun n => u n x) N‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hform (N : ℕ) : (∫ x, ‖cesaro (fun n => u n x) N‖ ^ 2 ∂μ) =
      (∑ i ∈ range N, ∑ j ∈ range N, (testMean μ (u i * star (u j))).re) / (N : ℝ)^2 := by
    have hpoint (x : X) : ‖cesaro (fun i => u i x) N‖ ^ 2 =
        (∑ i ∈ range N, ∑ j ∈ range N, (u i x * star (u j x)).re) / (N : ℝ)^2 := by
      let z := cesaro (fun i => u i x) N
      have hz : ‖z‖ ^ 2 = (z * star z).re := by
        rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hz]
      change (cesaro (fun i => u i x) N * star (cesaro (fun i => u i x) N)).re = _
      rw [star_cesaro, cesaro, cesaro, div_mul_div_comm, Finset.sum_mul]
      simp only [Finset.mul_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, pow_two,
        Complex.div_ofReal_re, Complex.re_sum]
    rw [show (fun x => ‖cesaro (fun n => u n x) N‖ ^ 2) = _ from funext hpoint, integral_div]
    congr 1
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro j _
        exact integral_re (test_integrable μ (u i * star (u j)))
      · intro j _
        exact (test_integrable μ (u i * star (u j))).re
    · intro i _
      exact integrable_finsetSum _ (fun j _ => (test_integrable μ (u i * star (u j))).re)
  have hbound (N : ℕ) : (∫ x, ‖cesaro (fun n => u n x) N‖ ^ 2 ∂μ) ≤
      2 * (D 0 / (N : ℝ) + realCesaro (fun h => D (h+1)) N) := by
    rw [hform]
    by_cases hN : N = 0
    · simp [hN, realCesaro]
    have hNr : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    have ht := (sum_le_sum fun i _ => sum_le_sum fun j _ => hGram i j).trans
      (double_toeplitz_bound D hD N)
    apply (div_le_iff₀ (sq_pos_of_pos hNr)).2
    convert ht using 1
    rw [realCesaro]
    field_simp
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) hbound
  have hh := realCesaro_tendsto_zero_of_tendsto_zero (fun h => hD (h+1))
    (hlim.comp (tendsto_add_atTop_nat 1))
  simpa only [add_zero, mul_zero] using ((tendsto_const_div_atTop_nhds_zero_nat (D 0)).add hh).const_mul 2

end
end VdC
