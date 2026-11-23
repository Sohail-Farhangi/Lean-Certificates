/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.ErgodicExamples

/-! # Ergodic Weak Mixing -/

@[expose] public section

open Filter Finset Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

private theorem realCesaro_sq_bound {u : ℕ → ℝ} (N : ℕ) :
    (realCesaro u N)^2 ≤ realCesaro (fun n => (u n)^2) N := by
  by_cases hN : N = 0
  · simp [realCesaro, hN]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h : (∑ n ∈ range N, u n)^2 ≤ (N : ℝ) * ∑ n ∈ range N, (u n)^2 := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_mul_sq_le_sq_mul_sq (range N) (fun _n => (1 : ℝ)) (fun n => u n))
  rw [realCesaro, realCesaro, div_pow]
  refine (div_le_div_of_nonneg_right h (sq_nonneg (N:ℝ))).trans_eq ?_
  field_simp [hNr]

private theorem realCesaro_tendsto_zero_of_sq {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (h : Tendsto (realCesaro (fun n => (u n)^2)) atTop (𝓝 0)) :
    Tendsto (realCesaro u) atTop (𝓝 0) := by
  have ht := squeeze_zero (fun N => sq_nonneg (realCesaro u N)) (realCesaro_sq_bound (u := u)) h
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (realCesaro_nonneg hu _)] using hs

section

variable {X : Type*} [MeasurableSpace X]

/-- The usual weak-mixing hypothesis that the product system is ergodic implies
the autocorrelation Cesàro criterion used for the orbit examples. -/
theorem koopmanWeakMixing_of_prod_ergodic {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hprod : Ergodic (fun p : X × X => (T p.1, T p.2)) (μ.prod μ)) :
    KoopmanWeakMixing μ T := by
  intro f hf hmean
  obtain ⟨C, hC, hb⟩ := hf.2
  let P (p : X × X) := (T p.1, T p.2)
  let g (p : X × X) := f p.1 * star (f p.2)
  have hm : Measurable g := (hf.1.comp measurable_fst).mul
    (Complex.continuous_conj.measurable.comp (hf.1.comp measurable_snd))
  have hg (p : X × X) : ‖g p‖ ≤ C*C := by
    change ‖f p.1 * star (f p.2)‖ ≤ _
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb _) (hb _) (norm_nonneg _) hC
  have hgm : (∫ p, g p ∂(μ.prod μ)) = 0 := by
    change (∫ p : X × X, f p.1 * star (f p.2) ∂(μ.prod μ)) = 0
    rw [integral_prod_mul (μ := μ) (ν := μ) f (fun x => star (f x)), hmean, zero_mul]
  have hp : ∀ᵐ p ∂(μ.prod μ), Tendsto (cesaro (fun n => g (P^[n] p))) atTop (𝓝 0) := by
    have he := ae_tendsto_orbitCesaro hprod hm (mul_nonneg hC hC) hg
    rwa [hgm] at he
  have hIt (n : ℕ) (p : X × X) : P^[n] p = (T^[n] p.1, T^[n] p.2) := by
    induction n with
    | zero => cases p; rfl
    | succ n IH => simp only [iterate_succ_apply', IH, P]
  let F (n : ℕ) (x : X) := f (T^[n] x) * star (f x)
  let G (n : ℕ) (p : X × X) := g (P^[n] p) * star (g p)
  have hgF (n : ℕ) (p : X × X) : G n p = F n p.1 * star (F n p.2) := by
    dsimp only [F, G, g]
    rw [hIt]
    simp only [star_mul, star_star]
    ring
  have hiG (n : ℕ) : Integrable (G n) (μ.prod μ) := by
    apply Integrable.of_bound (((hm.comp (hprod.measurable.iterate n)).mul
      (Complex.continuous_conj.measurable.comp hm)).aestronglyMeasurable) ((C*C)^2)
    exact Eventually.of_forall fun p => by
      change ‖g (P^[n] p) * star (g p)‖ ≤ _
      rw [norm_mul, norm_star, pow_two]
      exact mul_le_mul (hg _) (hg _) (norm_nonneg _) (mul_nonneg hC hC)
  let r := koopmanCorrelation μ T f
  have hiCorr (n : ℕ) : (∫ p, G n p ∂(μ.prod μ)) = (‖r n‖^2 : ℝ) := by
    have hc : (∫ x, star (F n x) ∂μ) = star (∫ x, F n x ∂μ) := integral_conj
    simp_rw [hgF]
    rw [integral_prod_mul (μ := μ) (ν := μ) (F n) (fun x => star (F n x)), hc]
    change r n * star (r n) = Complex.ofReal (‖r n‖^2)
    rw [Complex.ofReal_pow]
    exact Complex.mul_conj' (r n)
  let A (N : ℕ) (p : X × X) := cesaro (fun n => G n p) N
  have hA (N : ℕ) (p : X × X) : A N p = cesaro (fun n => g (P^[n] p)) N * star (g p) := by
    simp only [A, G, cesaro, ← Finset.sum_mul]
    ring
  have hiA (N : ℕ) : AEStronglyMeasurable (A N) (μ.prod μ) := by
    have hm' : Measurable (fun p => cesaro (fun n => g (P^[n] p)) N) := by
      apply Measurable.div_const
      exact Finset.measurable_sum _ (fun n _ => hm.comp (hprod.measurable.iterate n))
    rw [funext (hA N)]
    exact (hm'.mul (Complex.continuous_conj.measurable.comp hm)).aestronglyMeasurable
  have hAt : Tendsto (fun N => ∫ p, A N p ∂(μ.prod μ)) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (μ := μ.prod μ) (F := A) (f := fun _ => (0:ℂ))
      (fun _ => (C*C)^2) hiA (integrable_const _) ?_ ?_
    · simpa only [integral_zero] using ht
    · intro N
      exact ae_of_all _ fun p => by
        rw [hA, norm_mul, norm_star, pow_two]
        apply mul_le_mul (norm_cesaro_le _ (mul_nonneg hC hC) (fun n => hg _) N) (hg p)
        · exact norm_nonneg _
        · exact mul_nonneg hC hC
    · filter_upwards [hp] with p hp'
      simpa only [hA, zero_mul] using hp'.mul_const (star (g p))
  have hsum (N : ℕ) : (∫ p, A N p ∂(μ.prod μ)) = Complex.ofReal (realCesaro (fun n => ‖r n‖^2) N) := by
    simp only [A, cesaro, div_eq_mul_inv, integral_mul_const, integral_finsetSum _ (fun i _ => hiG i), hiCorr,
      realCesaro, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_inv, Complex.ofReal_sum]
  have hsq0 : Tendsto (realCesaro (fun h => ‖r h‖^2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hsum, Complex.ofReal_re, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hAt
  have hbound (h : ℕ) : |‖r h‖^2| ≤ (C*C)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    have hi : ∀ᵐ y ∂μ, ‖F h y‖ ≤ C*C := ae_of_all _ fun y => by
      simp only [F, norm_mul, norm_star]
      exact mul_le_mul (hb _) (hb _) (norm_nonneg _) hC
    change ‖∫ y, F h y ∂μ‖ ≤ C*C
    simpa only [MeasureTheory.probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hi
  have hshift := tendsto_realCesaro_shift_sub_zero (sq_nonneg _) hbound 1
  have hsq : Tendsto (realCesaro (fun h => ‖r (h+1)‖^2)) atTop (𝓝 0) := by
    simpa only [sub_add_cancel, add_zero] using hshift.add hsq0
  exact realCesaro_tendsto_zero_of_sq (fun _ => norm_nonneg _) hsq

end
end VdC
