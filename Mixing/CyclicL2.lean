/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CyclicMeasure
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Realizing the cyclic spectral measure in the original Hilbert space -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable section

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

instance vectorSpectralMeasure_regular (x : H) : (vectorSpectralMeasure U x).Regular :=
  RealRMK.regular_rieszMeasure _

/-- Apply a continuous spectral multiplier to the chosen vector. -/
def spectralVectorLinear (x : H) : C(RepresentationSpectrum U, ℂ) →ₗ[ℂ] H where
  toFun f := spectralCalculus U f x
  map_add' f g := by rw [map_add, add_apply]
  map_smul' a f := by rw [map_smul, smul_apply, RingHom.id_apply]

set_option maxHeartbeats 1200000 in
theorem spectralVectorLinear_inner (x : H) (f g : C(RepresentationSpectrum U, ℂ)) :
    ⟪spectralVectorLinear U x f, spectralVectorLinear U x g⟫_ℂ =
      ∫ z, g z * conj (f z) ∂vectorSpectralMeasure U x := by
  change ⟪spectralCalculus U f x, spectralCalculus U g x⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change ⟪x, (star (spectralCalculus U f) * spectralCalculus U g) x⟫_ℂ = _
  rw [← map_star, ← map_mul, ← integral_vectorSpectralMeasure]
  apply integral_congr_ae
  exact .of_forall fun z => by
    change conj (f z) * g z = g z * conj (f z)
    exact mul_comm _ _

theorem spectralVectorLinear_norm (x : H) (f : C(RepresentationSpectrum U, ℂ)) :
    ‖spectralVectorLinear U x f‖ = ‖ContinuousMap.toLp 2 (vectorSpectralMeasure U x) ℂ f‖ := by
  have h := (spectralVectorLinear_inner U x f f).trans
    (ContinuousMap.inner_toLp (vectorSpectralMeasure U x) f f).symm
  have hNorm := congrArg Complex.re h
  simp only [show ∀ y : H, (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ),
    show ∀ y : Lp ℂ 2 (vectorSpectralMeasure U x), (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2
      from inner_self_eq_norm_sq (𝕜 := ℂ)] at hNorm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hNorm

/-- The vector's cyclic spectral isometry, extending continuous multipliers to
all of the spectral `L²` space. -/
def cyclicSpectralIsometry (x : H) : Lp ℂ 2 (vectorSpectralMeasure U x) →ₗᵢ[ℂ] H :=
  (spectralVectorLinear U x).extendOfIsometry
    (ContinuousMap.toLp_denseRange (p := 2) ℂ (vectorSpectralMeasure U x) ℂ ENNReal.ofNat_ne_top)
    (spectralVectorLinear_norm U x)

theorem cyclicSpectralIsometry_toLp (x : H) (f : C(RepresentationSpectrum U, ℂ)) :
    cyclicSpectralIsometry U x (ContinuousMap.toLp 2 (vectorSpectralMeasure U x) ℂ f) =
      spectralCalculus U f x :=
  LinearMap.extendOfIsometry_eq _ _ _ f

theorem inner_cyclicSpectralIsometry_spectralCalculus (x : H)
    (w : Lp ℂ 2 (vectorSpectralMeasure U x)) (f : C(RepresentationSpectrum U, ℂ)) :
    ⟪cyclicSpectralIsometry U x w, spectralCalculus U f x⟫_ℂ =
      ⟪w, ContinuousMap.toLp 2 (vectorSpectralMeasure U x) ℂ f⟫_ℂ := by
  rw [← cyclicSpectralIsometry_toLp]
  exact (cyclicSpectralIsometry U x).inner_map_map _ _

theorem inner_cyclicSpectralIsometry_indicator (x : H)
    {A : Set (RepresentationSpectrum U)} (hA : MeasurableSet A)
    (f : C(RepresentationSpectrum U, ℂ)) :
    ⟪cyclicSpectralIsometry U x (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ)),
      spectralCalculus U f x⟫_ℂ =
      ∫ z in A, f z ∂vectorSpectralMeasure U x := by
  rw [inner_cyclicSpectralIsometry_spectralCalculus, L2.inner_indicatorConstLp_one]
  exact integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (vectorSpectralMeasure U x) f).filter_mono ae_restrict_le)

/-- A vector in an ultrafilter operator's kernel has no spectral atoms.
The test vector for a point mass is the image of its indicator under the
cyclic spectral isometry. Its matrix coefficient has constant nonzero
modulus if the point mass is positive. -/
theorem vectorSpectralMeasure_noAtoms_of_ultrafilterOperator_apply_eq_zero
    (x : H) (p : Ultrafilter G) (hx : ultrafilterOperator U p x = 0) :
    NullSingletonClass (vectorSpectralMeasure U x) := by
  constructor
  intro z
  let μ := vectorSpectralMeasure U x
  let A := ({z} : Set (RepresentationSpectrum U))
  have hA : MeasurableSet A := measurableSet_singleton _
  let w := cyclicSpectralIsometry U x (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ))
  have hcoeff (g : G) : ⟪w, U g x⟫_ℂ = (μ.real A : ℂ) * spectralCoefficient U g z := by
    change ⟪w, linearRepresentation U g x⟫_ℂ = _
    rw [← spectralCalculus_spectralCoefficient U g]
    change ⟪cyclicSpectralIsometry U x (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ)),
      spectralCalculus U (spectralCoefficient U g) x⟫_ℂ = _
    rw [inner_cyclicSpectralIsometry_indicator U x hA]
    change (∫ t in {z}, spectralCoefficient U g t ∂μ) = _
    rw [integral_singleton]
    rfl
  have hNorm (g : G) : ‖⟪w, U g x⟫_ℂ‖ = μ.real A := by
    rw [hcoeff, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
      spectralCoefficient_apply, Circle.norm_coe, mul_one]
  have hlim := (tendsto_ultrafilterOperator_coeff U p w x).norm
  have hzero : μ.real A = 0 := by
    rw [hx, inner_zero_right, norm_zero] at hlim
    have he : Tendsto (fun g : G => ‖⟪w, U g x⟫_ℂ‖) (p : Filter G) (𝓝 (μ.real A)) :=
      tendsto_const_nhds.congr' (.of_forall fun g => (hNorm g).symm)
    exact tendsto_nhds_unique he hlim
  exact (measureReal_eq_zero_iff (measure_ne_top μ A)).mp hzero

end

end Mixing
