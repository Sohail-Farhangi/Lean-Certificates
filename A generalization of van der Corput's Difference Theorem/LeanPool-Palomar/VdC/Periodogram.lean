/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The finite Fourier measures of bounded complex sequences. -/

@[expose] public section

namespace VdC

open Filter Finset MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal NNReal Topology

noncomputable section

abbrev periodogramHaar : Measure UnitAddCircle := AddCircle.haarAddCircle

def windowPolynomial (u : ℕ → ℂ) (N : ℕ) : C(UnitAddCircle, ℂ) :=
  ∑ i ∈ range N, u i • _root_.fourier (i : ℤ)

private theorem windowPolynomial_apply (u : ℕ → ℂ) (N : ℕ) (t : UnitAddCircle) :
    windowPolynomial u N t = ∑ i ∈ range N, u i * _root_.fourier (i : ℤ) t := by
  simp [windowPolynomial, ContinuousMap.sum_apply, smul_eq_mul]

def windowDensity (u : ℕ → ℂ) (N : ℕ) (t : UnitAddCircle) : ℝ :=
  ‖windowPolynomial u N t‖ ^ 2 / (N : ℝ)

theorem windowDensity_nonneg (u : ℕ → ℂ) (N : ℕ) (t : UnitAddCircle) :
    0 ≤ windowDensity u N t := by unfold windowDensity; positivity

private theorem continuous_windowDensity (u : ℕ → ℂ) (N : ℕ) :
    Continuous (windowDensity u N) := by
  unfold windowDensity
  exact ((windowPolynomial u N).continuous.norm.pow 2).div_const _

theorem integral_density (u : ℕ → ℂ) (N : ℕ) : Integrable (windowDensity u N) periodogramHaar :=
  (continuous_windowDensity u N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The positive finite measure of density `|∑_{j<N} u_j e(jt)|²/N`. -/
def periodogram (u : ℕ → ℂ) (N : ℕ) : FiniteMeasure UnitAddCircle := by
  let f := windowDensity u N
  refine ⟨periodogramHaar.withDensity (fun x ↦ ENNReal.ofReal (f x)), ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integral_density u N)
      (ae_of_all _ fun x ↦ windowDensity_nonneg u N x)]
  exact ENNReal.ofReal_lt_top

private theorem density_expand (u : ℕ → ℂ) (N : ℕ) :
    (fun t : UnitAddCircle ↦ (windowDensity u N t : ℂ)) =
      ∑ i ∈ range N, ∑ j ∈ range N, fun t : UnitAddCircle ↦
        (u i * conj (u j) / (N : ℂ)) * _root_.fourier ((i : ℤ) - (j : ℤ)) t := by
  funext t
  simp only [windowDensity, Complex.ofReal_div, Complex.ofReal_natCast, ← Complex.normSq_eq_norm_sq,
    ← Complex.mul_conj,
    windowPolynomial_apply, Finset.sum_apply, map_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, ← fourier_neg, sub_eq_add_neg, fourier_add]
  ring

private theorem periodogram_fourier_eq_double_sum (u : ℕ → ℂ) (N : ℕ) (h : ℤ) :
    (∫ t, _root_.fourier (-h) t ∂((periodogram u N : FiniteMeasure UnitAddCircle) : Measure UnitAddCircle)) =
    ∑ i ∈ range N, ∑ j ∈ range N, if (i : ℤ) - (j : ℤ) = h then u i * conj (u j) / (N : ℂ) else 0 := by
  let f := windowDensity u N
  have hm : Measurable fun x ↦ (f x).toNNReal :=
    (continuous_real_toNNReal.comp (continuous_windowDensity u N)).measurable
  have hfourier : (∫ t, _root_.fourier (-h) t ∂((periodogram u N : FiniteMeasure UnitAddCircle) : Measure UnitAddCircle)) =
      fourierCoeff (fun t : UnitAddCircle ↦ (windowDensity u N t : ℂ)) h := by
    change (∫ t, _root_.fourier (-h) t ∂periodogramHaar.withDensity (fun x ↦ ENNReal.ofReal (f x))) = _
    rw [show (fun x ↦ ENNReal.ofReal (f x)) = fun x ↦ (Real.toNNReal (f x) : ℝ≥0∞) by rfl,
      integral_withDensity_eq_integral_smul hm (fun x ↦ _root_.fourier (-h) x)]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      change ((↑(Real.toNNReal (f x)) : ℝ) : ℂ) * _root_.fourier (-h) x =
        _root_.fourier (-h) x * (f x : ℂ)
      rw [Real.coe_toNNReal _ (windowDensity_nonneg u N x), mul_comm]
  rw [hfourier, density_expand]
  let term (i j : ℕ) (t : UnitAddCircle) :=
    (u i * conj (u j) / (N : ℂ)) * _root_.fourier ((i : ℤ) - (j : ℤ)) t
  have hint (i j : ℕ) : Integrable (term i j) periodogramHaar :=
    (continuous_const.mul (_root_.fourier ((i : ℤ) - (j : ℤ))).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change fourierCoeff (∑ i ∈ range N, ∑ j ∈ range N, term i j) h = _
  rw [fourierCoeff.sum _ _ (fun i _ ↦ integrable_finsetSum' _ (fun j _ ↦ hint i j)), Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fourierCoeff.sum _ _ (fun j _ ↦ hint i j), Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [term]
  rw [fourierCoeff.const_mul, fourierCoeff_fourier]
  by_cases hij : (i : ℤ) - (j : ℤ) = h
  · rw [ite_eq_left hij, hij, Pi.single_eq_same, mul_one]
  · rw [ite_eq_right hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero]

/-- The Fourier coefficients of the finite periodogram are the truncated correlations. -/
theorem periodogram_fourier (u : ℕ → ℂ) (N h : ℕ) :
    (∫ t, _root_.fourier (-(h : ℤ)) t ∂((periodogram u N : FiniteMeasure UnitAddCircle) : Measure UnitAddCircle)) =
      (∑ j ∈ range (N - h), u (j + h) * conj (u j)) / (N : ℂ) := by
  rw [periodogram_fourier_eq_double_sum, Finset.sum_comm]
  have innerSum (j : ℕ) :
      (∑ i ∈ range N, if (i : ℤ) - (j : ℤ) = (h : ℤ) then u i * conj (u j) / (N : ℂ) else 0) =
        if j + h ∈ range N then u (j + h) * conj (u j) / (N : ℂ) else 0 := by
    simp only [show ∀ i : ℕ, (i : ℤ) - (j : ℤ) = (h : ℤ) ↔ i = j + h by intro i; omega]
    exact Finset.sum_ite_eq' _ _ _
  simp_rw [innerSum, ← Finset.sum_filter]
  have heq : (range N).filter (fun j ↦ j + h ∈ range N) = range (N - h) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [heq, Finset.sum_div]

theorem periodogram_mass_le (u : ℕ → ℂ) (N : ℕ) (C : ℝ≥0)
    (hC : ∀ k, ‖u k‖ ≤ C) : (periodogram u N).mass ≤ C ^ 2 := by
  have hzero := periodogram_fourier u N 0
  simp only [Nat.cast_zero, neg_zero, fourier_zero, integral_const, Complex.real_smul,
    mul_one, FiniteMeasure.measureReal_eq_coe_coeFn, Nat.sub_zero, add_zero] at hzero
  change (((periodogram u N).mass : ℝ) : ℂ) =
      (∑ j ∈ range N, u j * conj (u j)) / (N : ℂ) at hzero
  have he : ((periodogram u N).mass : ℝ) =
      ‖(∑ j ∈ range N, u j * conj (u j)) / (N : ℂ)‖ := by
    rw [← hzero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change ((periodogram u N).mass : ℝ) ≤ ((C ^ 2 : ℝ≥0) : ℝ)
  rw [he, NNReal.coe_pow, norm_div, Complex.norm_natCast]
  by_cases hN : N = 0
  · simp [hN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [div_le_iff₀ hN', mul_comm]
  calc
    _ ≤ ∑ j ∈ range N, ‖u j * conj (u j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range N, (C : ℝ) ^ 2 := Finset.sum_le_sum fun j _ ↦ by
      rw [norm_mul, Complex.norm_conj, sq]
      exact mul_le_mul (hC j) (hC j) (norm_nonneg _) C.coe_nonneg
    _ = _ := by simp

/-- Removing the last `h` terms changes a normalized bounded average by at most `h C / N`. -/
theorem norm_truncated_average_sub (u : ℕ → ℂ) (N h : ℕ) (C : ℝ)
    (hC₀ : 0 ≤ C) (hC : ∀ k, ‖u k‖ ≤ C) :
    ‖(∑ k ∈ range (N - h), u k) / (N : ℂ) - (∑ k ∈ range N, u k) / (N : ℂ)‖ ≤
      (h : ℝ) * C / (N : ℝ) := by
  rw [← sub_div, norm_div, Complex.norm_natCast, norm_sub_rev,
    ← Finset.sum_Ico_eq_sub _ (Nat.sub_le N h)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ k ∈ Ico (N - h) N, ‖u k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Ico (N - h) N, C := Finset.sum_le_sum fun k _ ↦ hC k
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show N - (N - h) ≤ h by omega)) hC₀

/-- Integration of a continuous complex function depends continuously on a finite measure. -/
theorem continuous_finiteMeasure_integral (g : C(UnitAddCircle, ℂ)) :
    Continuous fun μ : FiniteMeasure UnitAddCircle ↦ ∫ x, g x ∂(μ : Measure UnitAddCircle) := by
  let gr : C(UnitAddCircle, ℝ) := ⟨fun x ↦ (g x).re, Complex.continuous_re.comp g.continuous⟩
  let gi : C(UnitAddCircle, ℝ) := ⟨fun x ↦ (g x).im, Complex.continuous_im.comp g.continuous⟩
  have hr := FiniteMeasure.continuous_integral_continuousMap gr
  have hi := FiniteMeasure.continuous_integral_continuousMap gi
  have h : (fun μ : FiniteMeasure UnitAddCircle ↦ ∫ x, g x ∂(μ : Measure UnitAddCircle)) =
    fun μ : FiniteMeasure UnitAddCircle ↦
      Complex.ofReal (∫ x, gr x ∂(μ : Measure UnitAddCircle)) +
        Complex.ofReal (∫ x, gi x ∂(μ : Measure UnitAddCircle)) * Complex.I := by
    funext μ
    have hg : Integrable g (μ : Measure UnitAddCircle) :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    apply Complex.ext
    · simpa [Complex.add_re, Complex.mul_re, gr] using (integral_re (𝕜 := ℂ) hg).symm
    · simpa [Complex.add_im, Complex.mul_im, gi] using (integral_im (𝕜 := ℂ) hg).symm
  rw [h]
  exact (Complex.continuous_ofReal.comp hr).add ((Complex.continuous_ofReal.comp hi).mul continuous_const)

end

end VdC
