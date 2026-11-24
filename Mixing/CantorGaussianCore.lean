/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorGenerated
public import Mixing.SupportingGaussianPath

/-! # The stationary Gaussian law associated to the annihilated Cantor fibre mode -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter WithLp
open scoped ProbabilityTheory InnerProductSpace Topology NNReal

namespace Mixing

local notation "𝕋" => UnitAddCircle

/-- The spectral input for the Gaussian realization. Its mass is two, corresponding
to the sum of the two opposite fibre characters. -/
noncomputable def example5GaussianSpectralInput : Measure 𝕋 :=
  (2 : ℝ≥0) • cantorCircleMeasure.map (fun x : 𝕋 ↦ (-2 : ℤ) • x)

instance : IsFiniteMeasure example5GaussianSpectralInput := by
  unfold example5GaussianSpectralInput
  infer_instance

/-- The real stationary covariance associated to the two opposite fibre frequencies. -/
noncomputable def example5GaussianCovariance (n : ℤ) : ℝ :=
  GaussianPath.spectralCovariance example5GaussianSpectralInput n

theorem example5GaussianCovariance_fourier (n : ℤ) :
    example5GaussianCovariance n = 2 * (cantorFourier ((-2 * n : ℤ) : ℝ)).re := by
  have hm : Measurable (fun x : 𝕋 ↦ (-2 : ℤ) • x) := by fun_prop
  unfold example5GaussianCovariance GaussianPath.spectralCovariance example5GaussianSpectralInput
  rw [integral_smul_nnreal_measure, integral_map hm.aemeasurable
    (fourier (T := 1) (-n)).continuous.aestronglyMeasurable]
  simp_rw [fourier_circle_zsmul]
  rw [show (-n) * (-2 : ℤ) = 2 * n by ring, cantorCircleMeasure_integral_fourier]
  norm_num [RCLike.smul_re]
  exact RCLike.smul_re (K := ℂ) (2 : ℝ) _

theorem example5GaussianCovariance_zero : example5GaussianCovariance 0 = 2 := by
  rw [example5GaussianCovariance_fourier]
  simp

theorem example5GaussianCovariance_even (n : ℤ) :
    example5GaussianCovariance (-n) = example5GaussianCovariance n :=
  GaussianPath.spectralCovariance_even example5GaussianSpectralInput n

theorem example5GaussianCovariance_psd (I : Finset ℤ) :
    (Matrix.of fun i j : I ↦ example5GaussianCovariance ((i : ℤ) - (j : ℤ))).PosSemidef :=
  GaussianPath.fourier_covariance_posSemidef example5GaussianSpectralInput I

theorem example5GaussianCovariance_tendsto_zero (a : ℤ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    Tendsto (fun g : Multiplicative ℤ ↦ example5GaussianCovariance (g.toAdd + a))
      (p : Filter (Multiplicative ℤ)) (𝓝 0) := by
  have hf := example5_fibreTwo_fourier_tendsto_zero (-2 * a) p hp hsupp
  have hr := (Complex.continuous_re.tendsto (0 : ℂ)).comp hf
  have h := (tendsto_const_nhds (x := (2 : ℝ))).mul hr
  change Tendsto (fun g : Multiplicative ℤ ↦
    2 * (cantorFourier ((-2 * g.toAdd + -2 * a : ℤ) : ℝ)).re) (p : Filter (Multiplicative ℤ))
      (𝓝 (2 * (0 : ℂ).re)) at h
  simp only [Complex.zero_re, mul_zero] at h
  simpa only [example5GaussianCovariance_fourier, mul_add] using h

/-- The probability law of the stationary Gaussian path with the Cantor covariance. -/
noncomputable def example5GaussianMeasure : Measure (ℤ → ℝ) :=
  Classical.choose (GaussianPath.exists_real_projective_limit
    (GaussianPath.finiteGaussianFamily example5GaussianCovariance)
      (GaussianPath.finiteGaussianFamily_projective _ example5GaussianCovariance_psd))

theorem example5GaussianMeasure_projective :
    IsProjectiveLimit (α := fun _ : ℤ ↦ ℝ) example5GaussianMeasure
      (GaussianPath.finiteGaussianFamily example5GaussianCovariance) :=
  Classical.choose_spec (GaussianPath.exists_real_projective_limit
    (GaussianPath.finiteGaussianFamily example5GaussianCovariance)
      (GaussianPath.finiteGaussianFamily_projective _ example5GaussianCovariance_psd))

instance : IsProbabilityMeasure example5GaussianMeasure := example5GaussianMeasure_projective.isProbabilityMeasure

/-- The Gaussian path shift by an arbitrary integer number of time steps. -/
def gaussianPathTimeShift (j : ℤ) (x : ℤ → ℝ) (i : ℤ) : ℝ := x (i + j)

theorem example5GaussianTimeShift_preserving (j : ℤ) :
    MeasurePreserving (gaussianPathTimeShift j) example5GaussianMeasure example5GaussianMeasure where
  measurable := Measurable.of_eval fun i ↦ measurable_pi_apply (i + j)
  map_eq := by
    apply IsProjectiveLimit.unique
      (P := GaussianPath.finiteGaussianFamily example5GaussianCovariance) _
      example5GaussianMeasure_projective
    intro I
    let J := I.image (fun i : ℤ ↦ i + j)
    let k : I → J := fun i ↦ ⟨(i : ℤ) + j, Finset.mem_image_of_mem _ i.2⟩
    have hK := GaussianPath.finiteGaussianFamily_reindex example5GaussianCovariance
      example5GaussianCovariance_psd k (fun i l ↦ by
        change example5GaussianCovariance (((i : ℤ) + j) - ((l : ℤ) + j)) = _
        congr 1
        omega)
    have hm : Measurable (gaussianPathTimeShift j) :=
      Measurable.of_eval fun i ↦ measurable_pi_apply (i + j)
    rw [Measure.map_map I.measurable_restrict hm,
      show I.restrict (π := fun _ ↦ ℝ) ∘ gaussianPathTimeShift j =
        (fun x : J → ℝ ↦ fun i : I ↦ x (k i)) ∘ J.restrict from rfl,
      ← Measure.map_map hK.measurable J.measurable_restrict, example5GaussianMeasure_projective J,
      hK.map_eq]

/-- The concrete stationary Gaussian system associated to the Cantor covariance. -/
noncomputable def example5GaussianSystem : System (Multiplicative ℤ) (ℤ → ℝ) where
  measure := example5GaussianMeasure
  probability := inferInstance
  act g := gaussianPathTimeShift g.toAdd
  act_one := by funext x i; change x (i + 0) = x i; rw [add_zero]
  act_mul g h := by
    funext x i
    change x (i + (g.toAdd + h.toAdd)) = x ((i + g.toAdd) + h.toAdd)
    rw [add_assoc]
  preserves g := example5GaussianTimeShift_preserving g.toAdd

theorem example5Gaussian_euclidean_marginal (I : Finset ℤ) :
    MeasurePreserving (fun x : ℤ → ℝ ↦ toLp 2 (I.restrict x)) example5GaussianMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ example5GaussianCovariance ((i : ℤ) - (j : ℤ)))) :=
  (GaussianPath.preserving_toLp example5GaussianCovariance I).comp
    ⟨I.measurable_restrict, example5GaussianMeasure_projective I⟩

theorem example5Gaussian_coordinate_law (i : ℤ) :
    MeasurePreserving (fun x : ℤ → ℝ ↦ x i) example5GaussianMeasure (gaussianReal 0 2) := by
  let I : Finset ℤ := {i}
  let k : I := ⟨i, by simp [I]⟩
  have h := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ I))
    (example5GaussianCovariance_psd I) (i := k)).comp (example5Gaussian_euclidean_marginal I)
  simpa [k, Function.comp_def, Finset.restrict, example5GaussianCovariance_zero] using h

theorem example5Gaussian_coordinate_memLp (i : ℤ) :
    MemLp (fun x : ℤ → ℝ ↦ x i) 2 example5GaussianMeasure :=
  (IsGaussian.memLp_two_id (μ := gaussianReal 0 2)).comp_measurePreserving
    (example5Gaussian_coordinate_law i)

theorem example5Gaussian_coordinate_integral (i : ℤ) :
    (∫ x, x i ∂example5GaussianMeasure) = 0 := by
  have h := example5Gaussian_coordinate_law i
  rw [← integral_id_gaussianReal (μ := 0) (v := 2), ← h.map_eq]
  have hId : AEStronglyMeasurable (fun x : ℝ ↦ x)
      (example5GaussianMeasure.map (fun x ↦ x i)) := aestronglyMeasurable_id
  exact (integral_map h.measurable.aemeasurable hId).symm

theorem example5Gaussian_coordinate_covariance (i j : ℤ) :
    cov[fun x ↦ x i, fun x ↦ x j; example5GaussianMeasure] = example5GaussianCovariance (i - j) := by
  let I : Finset ℤ := {i, j}
  let l : I := ⟨i, by simp [I]⟩
  let m : I := ⟨j, by simp [I]⟩
  have hI := example5Gaussian_euclidean_marginal I
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ I))
    (example5GaussianCovariance_psd I) l m
  rw [← hI.map_eq, covariance_map] at hc
  · exact hc
  all_goals fun_prop

theorem example5Gaussian_coordinate_pair_integral (i j : ℤ) :
    (∫ x, x i * x j ∂example5GaussianMeasure) = example5GaussianCovariance (i - j) := by
  have h := example5Gaussian_coordinate_covariance i j
  rw [covariance_eq_sub (example5Gaussian_coordinate_memLp i) (example5Gaussian_coordinate_memLp j),
    example5Gaussian_coordinate_integral, zero_mul, sub_zero] at h
  exact h

/-- The Gaussian coordinate at time zero as a Koopman L² vector. -/
noncomputable def example5GaussianVector : Lp ℂ 2 example5GaussianSystem.measure :=
  (example5Gaussian_coordinate_memLp 0).ofReal.toLp (fun x ↦ ((x 0 : ℝ) : ℂ))

theorem example5GaussianVector_ae :
    example5GaussianVector =ᵐ[example5GaussianSystem.measure] fun x ↦ ((x 0 : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

theorem example5GaussianVector_autocorrelation (j : ℤ) :
    ⟪example5GaussianVector,
      example5GaussianSystem.koopmanRep (Multiplicative.ofAdd j) example5GaussianVector⟫_ℂ =
        (example5GaussianCovariance j : ℂ) := by
  let g := Multiplicative.ofAdd j
  have hShift := (Lp.coeFn_compMeasurePreserving example5GaussianVector
    (example5GaussianSystem.preserves g)).trans
      ((example5GaussianSystem.preserves g).quasiMeasurePreserving.ae_eq_comp example5GaussianVector_ae)
  rw [MeasureTheory.L2.inner_def]
  have h : (∫ x, ⟪example5GaussianVector x,
      example5GaussianSystem.koopmanRep g example5GaussianVector x⟫_ℂ
      ∂example5GaussianSystem.measure) =
      ∫ x, ((x 0 * x j : ℝ) : ℂ) ∂example5GaussianMeasure := by
    apply integral_congr_ae
    change (fun x ↦ ⟪example5GaussianVector x,
      example5GaussianSystem.koopmanRep g example5GaussianVector x⟫_ℂ) =ᵐ[example5GaussianMeasure] _
    filter_upwards [example5GaussianVector_ae, hShift] with x h₀ h₁
    change example5GaussianSystem.koopmanRep g example5GaussianVector x =
      ((x (0 + j) : ℝ) : ℂ) at h₁
    rw [zero_add] at h₁
    rw [h₀, h₁, RCLike.inner_apply']
    simp [Complex.ofReal_mul]
  change (∫ x, ⟪example5GaussianVector x, example5GaussianSystem.koopmanRep g
    example5GaussianVector x⟫_ℂ ∂example5GaussianSystem.measure) = _
  rw [h]
  rw [integral_complex_ofReal, example5Gaussian_coordinate_pair_integral, zero_sub,
    example5GaussianCovariance_even]

end Mixing
