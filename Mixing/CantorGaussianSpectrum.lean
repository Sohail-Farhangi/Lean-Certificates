/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorGaussianCore
public import Mixing.CantorSumFactor
public import Mixing.CyclicIntertwiner

/-! # Spectral overlap between the Cantor and stationary Gaussian systems -/

@[expose] public section

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing

private noncomputable def cantorFibre (m : ℤ) : Lp ℂ 2 example5CantorSystem.measure :=
  circlePairFourierLp example5CantorSystem.measure ![0, m]

private theorem cantorFibre_coeff (m n j : ℤ) :
    ⟪cantorFibre m, example5CantorSystem.koopmanRep (Multiplicative.ofAdd j) (cantorFibre n)⟫_ℂ =
      if m = n then cantorFourier ((-n * j : ℤ) : ℝ) else 0 := by
  have h := (cantorSkew_inner_character ![0, m] ![0, n] (Multiplicative.ofAdd j)).trans
    (example5_cantor_character_correlation (-(0 : ℤ)) (-m) n 0 j)
  change ⟪cantorFibre m, example5CantorSystem.koopmanRep (Multiplicative.ofAdd j) (cantorFibre n)⟫_ℂ =
    cantorFourier ((-n * j - (-(0 : ℤ) + 0) : ℤ) : ℝ) *
      ∫ y : UnitAddCircle, fourier (-m + n) y ∂AddCircle.haarAddCircle at h
  rw [h]
  by_cases hm : m = n
  · subst m
    simp
  · rw [ite_eq_right hm, integral_haar_fourier_zero (-m + n) (by omega), mul_zero]

private theorem cantorFibre_meanZero (m : ℤ) (hm : m ≠ 0) :
    cantorFibre m ∈ meanZero example5CantorSystem.measure := by
  rw [mem_meanZero_iff_integral]
  have ha := circlePairFourierLp_ae_eq example5CantorSystem.measure ![0, m]
  change cantorFibre m =ᵐ[example5CantorSystem.measure] example5CantorCharacter 0 m at ha
  rw [integral_congr_ae ha]
  simp only [example5CantorCharacter, fourier_zero, one_mul]
  change (∫ x : UnitAddCircle × UnitAddCircle, fourier m x.2
    ∂cantorCircleMeasure.prod AddCircle.haarAddCircle) = _
  rw [integral_fun_snd (fun y : UnitAddCircle ↦ fourier m y), integral_haar_fourier_zero m hm, smul_zero]

private theorem cantorFourier_neg_int_eq_conj (n : ℤ) :
    cantorFourier ((-n : ℤ) : ℝ) = conj (cantorFourier n) := by
  have hp : (∫ x, fourier (-n) x ∂cantorCircleMeasure) = cantorFourier (n : ℝ) := by
    simpa only [neg_neg] using cantorCircleMeasure_integral_fourier (-n)
  rw [← cantorCircleMeasure_integral_fourier n, ← hp, ← integral_conj]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  simpa only [neg_neg] using (fourier_neg (n := -n) (x := x))

private noncomputable def cantorOppositeModes : Lp ℂ 2 example5CantorSystem.measure :=
  cantorFibre 2 + cantorFibre (-2)

private theorem cantorOppositeModes_autocorrelation (j : ℤ) :
    ⟪cantorOppositeModes,
      example5CantorSystem.koopmanRep (Multiplicative.ofAdd j) cantorOppositeModes⟫_ℂ =
        (example5GaussianCovariance j : ℂ) := by
  unfold cantorOppositeModes
  simp only [map_add, inner_add_left, inner_add_right, cantorFibre_coeff]
  norm_num
  have hArg : (2 : ℝ) * (j : ℝ) = (((-(-2 * j) : ℤ)) : ℝ) := by push_cast; ring
  rw [hArg, cantorFourier_neg_int_eq_conj, example5GaussianCovariance_fourier]
  push_cast
  norm_num
  apply Complex.ext
  · simp [Complex.add_re, Complex.conj_re]
    ring
  · simp [Complex.add_im, Complex.conj_im]

private theorem example5GaussianVector_meanZero :
    example5GaussianVector ∈ meanZero example5GaussianSystem.measure := by
  rw [mem_meanZero_iff_integral, integral_congr_ae example5GaussianVector_ae]
  change (∫ x, ((x 0 : ℝ) : ℂ) ∂example5GaussianMeasure) = 0
  rw [integral_complex_ofReal, example5Gaussian_coordinate_integral, Complex.ofReal_zero]

/-- The explicit stationary Gaussian system has nontrivial spectral overlap with the
Cantor skew rotation. The intertwiner comes from equal coefficients of the Gaussian
coordinate and the sum of the two opposite fibre-frequency vectors. -/
theorem example5Gaussian_not_spectrallyDisjoint :
    ¬ SpectrallyDisjoint example5CantorSystem.koopmanZeroRep example5GaussianSystem.koopmanZeroRep := by
  let x : meanZero example5CantorSystem.measure :=
    ⟨cantorOppositeModes, (meanZero example5CantorSystem.measure).add_mem
      (cantorFibre_meanZero 2 (by decide)) (cantorFibre_meanZero (-2) (by decide))⟩
  let y : meanZero example5GaussianSystem.measure := ⟨example5GaussianVector, example5GaussianVector_meanZero⟩
  have hx : x ≠ 0 := by
    intro h
    have hz : cantorOppositeModes = 0 := congrArg Subtype.val h
    have h₀ := cantorOppositeModes_autocorrelation 0
    rw [hz, inner_zero_left, example5GaussianCovariance_zero] at h₀
    norm_num at h₀
  refine not_spectrallyDisjoint_of_equal_diagonal_coefficients _ _ x y hx fun g ↦ ?_
  change
    ⟪cantorOppositeModes, example5CantorSystem.koopmanRep (Multiplicative.ofAdd g.toAdd)
      cantorOppositeModes⟫_ℂ =
    ⟪example5GaussianVector, example5GaussianSystem.koopmanRep (Multiplicative.ofAdd g.toAdd)
      example5GaussianVector⟫_ℂ
  rw [cantorOppositeModes_autocorrelation, example5GaussianVector_autocorrelation]

end Mixing
