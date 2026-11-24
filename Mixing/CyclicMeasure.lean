/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CyclicSpectral
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Spectral measures of vectors -/

@[expose] public section

open Filter MeasureTheory Set
open scoped CompactlySupported ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable section

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

instance : MeasurableSpace (RepresentationSpectrum U) := borel _
instance : BorelSpace (RepresentationSpectrum U) := ⟨rfl⟩

variable {X : Type*} [TopologicalSpace X]

/-- A real continuous test function regarded as a complex-valued test function. -/
def complexify (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun z => Complex.ofReal (f z), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem complexify_apply (f : C(X, ℝ)) (z : X) :
    complexify f z = Complex.ofReal (f z) := rfl

theorem complexify_add (f g : C(X, ℝ)) : complexify (f + g) = complexify f + complexify g := by
  ext z
  simp [complexify_apply]

theorem complexify_real_smul (a : ℝ) (f : C(X, ℝ)) :
    complexify (a • f) = (a : ℂ) • complexify f := by
  ext z
  simp [complexify_apply, smul_eq_mul]

theorem complexify_star (f : C(X, ℝ)) : star (complexify f) = complexify f := by
  ext z
  simp [ContinuousMap.star_apply, complexify_apply]

theorem complexify_one : complexify (1 : C(X, ℝ)) = 1 := by
  ext z
  simp

theorem complexify_sqrt_mul_self {f : C(X, ℝ)} (hf : ∀ z, 0 ≤ f z) :
    let g : C(X, ℝ) := ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩
    complexify g * complexify g = complexify f := by
  intro g
  ext z
  simp only [ContinuousMap.mul_apply, complexify_apply, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (Real.mul_self_sqrt (hf z))

/-- Evaluation of the calculus on a vector is a positive functional on
real-valued test functions. -/
def vectorStateLinear (x : H) : C(RepresentationSpectrum U, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).re
  map_add' f g := by
    rw [complexify_add, map_add]
    simp only [add_apply, inner_add_right, Complex.add_re]
  map_smul' a f := by
    rw [complexify_real_smul, map_smul]
    simp only [smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, smul_eq_mul]

theorem vectorStateLinear_nonneg (x : H) (f : C(RepresentationSpectrum U, ℝ))
    (hf : 0 ≤ f) : 0 ≤ vectorStateLinear U x f := by
  let g : C(RepresentationSpectrum U, ℝ) :=
    ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩
  let A := spectralCalculus U (complexify g)
  have hStar : A.adjoint = A := by
    change star (spectralCalculus U (complexify g)) = spectralCalculus U (complexify g)
    rw [← map_star, complexify_star]
  have hg : complexify g * complexify g = complexify f :=
    complexify_sqrt_mul_self (fun z => hf z)
  change 0 ≤ (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).re
  rw [← hg, map_mul]
  change 0 ≤ (⟪x, A (A x)⟫_ℂ).re
  have h := A.adjoint_inner_right x (A x)
  rw [hStar] at h
  rw [h]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (A x)).ge.trans' (sq_nonneg _)

theorem vectorStateLinear_mono (x : H) : Monotone (vectorStateLinear U x) := by
  intro f g hfg
  have hSub : 0 ≤ g - f := fun z => sub_nonneg.mpr (hfg z)
  have h := vectorStateLinear_nonneg U x (g - f) hSub
  rwa [map_sub, sub_nonneg] at h

/-- The real-valued positive functional used in the Riesz–Markov construction. -/
def vectorState (x : H) : C_c(RepresentationSpectrum U, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap :=
    (vectorStateLinear U x).comp
      ({ toFun := fun f => f.toContinuousMap
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } :
        C_c(RepresentationSpectrum U, ℝ) →ₗ[ℝ] C(RepresentationSpectrum U, ℝ))
  monotone' _ _ hfg := vectorStateLinear_mono U x hfg

/-- The finite positive spectral measure of a vector on the representation spectrum. -/
def vectorSpectralMeasure (x : H) : Measure (RepresentationSpectrum U) :=
  RealRMK.rieszMeasure (vectorState U x)

instance vectorSpectralMeasure_isFinite (x : H) : IsFiniteMeasure (vectorSpectralMeasure U x) := by
  constructor
  let f : C_c(RepresentationSpectrum U, ℝ) :=
    { toFun := 1
      hasCompactSupport' := HasCompactSupport.of_compactSpace 1 }
  apply (RealRMK.rieszMeasure_le_of_eq_one (Λ := vectorState U x)
    (f := f) (fun _ => zero_le_one) isCompact_univ (fun _ _ => rfl)).trans_lt
  exact ENNReal.ofReal_lt_top

theorem integral_vectorSpectralMeasure_real (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    ∫ z, f z ∂vectorSpectralMeasure U x = (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).re := by
  let fc : C_c(RepresentationSpectrum U, ℝ) :=
    { toContinuousMap := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  have h := RealRMK.integral_rieszMeasure (vectorState U x) fc
  change (∫ z, f z ∂vectorSpectralMeasure U x) = _ at h
  exact h

theorem inner_spectralCalculus_complexify_im (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).im = 0 := by
  let A := spectralCalculus U (complexify f)
  have hStar : A.adjoint = A := by
    change star (spectralCalculus U (complexify f)) = spectralCalculus U (complexify f)
    rw [← map_star, complexify_star]
  have he : conj ⟪x, A x⟫_ℂ = ⟪x, A x⟫_ℂ := by
    rw [inner_conj_symm, ← A.adjoint_inner_right, hStar]
  have h := congrArg Complex.im he
  rw [Complex.conj_im] at h
  exact neg_eq_self.mp h

theorem integral_vectorSpectralMeasure_complexify (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    ∫ z, complexify f z ∂vectorSpectralMeasure U x =
      ⟪x, spectralCalculus U (complexify f) x⟫_ℂ := by
  have h := integral_ofReal (𝕜 := ℂ) (f := ⇑f) (μ := vectorSpectralMeasure U x)
  rw [integral_vectorSpectralMeasure_real U x f] at h
  change (∫ z, Complex.ofReal (f z) ∂vectorSpectralMeasure U x) = _
  refine h.trans ?_
  exact Complex.ext (by simp) (by
    change 0 = (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).im
    exact (inner_spectralCalculus_complexify_im U x f).symm)

set_option maxHeartbeats 1200000 in
/-- Riesz representation of the complex vector state. -/
theorem integral_vectorSpectralMeasure (x : H) (f : C(RepresentationSpectrum U, ℂ)) :
    ∫ z, f z ∂vectorSpectralMeasure U x = ⟪x, spectralCalculus U f x⟫_ℂ := by
  let re : C(RepresentationSpectrum U, ℝ) := ⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩
  let im : C(RepresentationSpectrum U, ℝ) := ⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩
  have hf : f = complexify re + Complex.I • complexify im := by
    ext z
    change f z = Complex.ofReal (f z).re + Complex.I * Complex.ofReal (f z).im
    exact (Complex.re_add_im (f z)).symm.trans (by rw [mul_comm Complex.I])
  rw [hf, map_add, map_smul, add_apply, smul_apply, inner_add_right, inner_smul_right]
  have hRe := (complexify re).continuous.integrable_of_hasCompactSupport
    (μ := vectorSpectralMeasure U x) (HasCompactSupport.of_compactSpace _)
  have hIm := (complexify im).continuous.integrable_of_hasCompactSupport
    (μ := vectorSpectralMeasure U x) (HasCompactSupport.of_compactSpace _)
  refine (integral_add hRe (hIm.smul Complex.I)).trans ?_
  exact congrArg₂ (· + ·) (integral_vectorSpectralMeasure_complexify U x re)
    ((integral_smul (μ := vectorSpectralMeasure U x) Complex.I (⇑(complexify im))).trans
      (congrArg (Complex.I • ·) (integral_vectorSpectralMeasure_complexify U x im)))

theorem vectorSpectralMeasure_mass (x : H) :
    (vectorSpectralMeasure U x Set.univ).toReal = ‖x‖ ^ 2 := by
  have h := integral_vectorSpectralMeasure_real U x (1 : C(RepresentationSpectrum U, ℝ))
  have hRe : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  change (vectorSpectralMeasure U x).real Set.univ = _
  simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, complexify_one,
    map_one, one_apply_eq_self, hRe] using h

/-- The matrix coefficient of a trigonometric polynomial is integrated against
the vector's spectral measure. -/
theorem integral_spectralPolynomial (x : H) (a : G →₀ ℂ) :
    ∫ z, trigonometricPolynomial a (spectralPointCharacter U z) ∂vectorSpectralMeasure U x =
      ⟪x, trigonometricOperator U a x⟫_ℂ := by
  simpa only [spectralPolynomial_apply, spectralCalculus_spectralPolynomial] using
    integral_vectorSpectralMeasure U x (spectralPolynomial U a)

end

end Mixing
