/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Koopman
public import SixProblems.OperatorialRecurrenceGaussian
public import Mixing.SpectralDual
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

namespace SixProblems

noncomputable section

open MeasureTheory Mixing Set
open scoped Classical ENNReal InnerProductSpace ComplexConjugate Matrix

variable {G : Type} [Group G]

/-- The Fourier condition of Theorem 2.2(f), expressed with a positive error. -/
def NiceFCPlus (R : Set G) : Prop :=
  ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ], ∀ ε > 0,
    ∃ r ∈ R, τ.real {1} - ε ≤ ‖spectralFourier τ r‖

private def χeval (g : G) (χ : DiscreteDual G) : ℂ := dualEvaluation g χ

private theorem χeval_continuous (g : G) : Continuous (χeval g) :=
  continuous_subtype_val.comp (dualEvaluation g).continuous

@[simp] private theorem χeval_norm (g : G) (χ : DiscreteDual G) : ‖χeval g χ‖ = 1 :=
  Circle.norm_coe _

@[simp] private theorem χeval_trivial (g : G) : χeval g (1 : DiscreteDual G) = 1 := by
  rfl

private theorem χeval_mul_inv (g h : G) (χ : DiscreteDual G) :
    χeval (g*h⁻¹) χ = χeval g χ * conj (χeval h χ) := by
  change ((χ (g*h⁻¹) : Circle) : ℂ) = (χ g : ℂ) * conj (χ h : ℂ)
  rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]

private theorem χeval_inv (g : G) (χ : DiscreteDual G) :
    χeval g⁻¹ χ = conj (χeval g χ) := by
  change ((χ g⁻¹ : Circle) : ℂ) = conj (χ g : ℂ)
  rw [map_inv, Circle.coe_inv_eq_conj]

private theorem χeval_integrable (τ : Measure (DiscreteDual G)) [IsFiniteMeasure τ] (g : G) :
    Integrable (χeval g) τ :=
  Integrable.of_bound (χeval_continuous g).aestronglyMeasurable 1
    (.of_forall fun χ ↦ (χeval_norm g χ).le)

private theorem spectralFourier_re (τ : Measure (DiscreteDual G)) [IsFiniteMeasure τ] (g : G) :
    (spectralFourier τ g).re = ∫ χ, (χeval g χ).re ∂τ :=
  (integral_re (χeval_integrable τ g)).symm

private theorem spectralFourier_inv (τ : Measure (DiscreteDual G)) (g : G) :
    spectralFourier τ g⁻¹ = conj (spectralFourier τ g) := by
  change (∫ χ, χeval g⁻¹ χ ∂τ) = conj (∫ χ, χeval g χ ∂τ)
  simp_rw [χeval_inv]
  exact integral_conj

theorem norm_spectralFourier_le (τ : Measure (DiscreteDual G)) (g : G) :
    ‖spectralFourier τ g‖ ≤ τ.real univ := by
  change ‖∫ χ, χeval g χ ∂τ‖ ≤ _
  exact (norm_integral_le_integral_norm _).trans_eq (by simp [measureReal_def])

/-- Real parts of Fourier coefficients of finite positive measures are positive definite. -/
theorem spectralFourier_realPositiveDefinite (τ : Measure (DiscreteDual G)) [IsFiniteMeasure τ] :
    RealPositiveDefinite (fun g ↦ (spectralFourier τ g).re) := by
  intro I
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    refine Matrix.IsSymm.ext fun i j ↦ ?_
    change (spectralFourier τ ((j : G)*(i : G)⁻¹)).re =
      (spectralFourier τ ((i : G)*(j : G)⁻¹)).re
    rw [show (j : G)*(i : G)⁻¹ = ((i : G)*(j : G)⁻¹)⁻¹ by group,
      spectralFourier_inv, Complex.conj_re]
  intro a
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  let v (i j : I) (χ : DiscreteDual G) := a i * ((χeval ((i : G)*(j : G)⁻¹) χ).re * a j)
  have hv i j : Integrable (v i j) τ := ((χeval_integrable τ _).re.mul_const _).const_mul _
  have hFin :
      (∫ χ, ∑ i, ∑ j, v i j χ ∂τ) =
        ∑ i : I, ∑ j : I, a i * ((spectralFourier τ ((i : G)*(j : G)⁻¹)).re * a j) := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hv i j))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ (fun j _ ↦ hv i j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show v i j = fun χ ↦ a i * ((χeval ((i : G)*(j : G)⁻¹) χ).re * a j) from rfl,
      integral_const_mul, integral_mul_const, ← spectralFourier_re]
  rw [← hFin]
  apply integral_nonneg
  intro χ
  change 0 ≤ ∑ i, ∑ j, v i j χ
  let : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal
  let u (i : I) := χeval (i : G) χ
  have hMat : (Matrix.of fun i j : I ↦ (χeval ((i : G)*(j : G)⁻¹) χ).re) = (Matrix.gram ℝ u)ᵀ := by
    ext i j
    change (χeval ((i : G)*(j : G)⁻¹) χ).re = (⟪u j, u i⟫_ℂ).re
    rw [χeval_mul_inv, RCLike.inner_apply', mul_comm]
  have hPos : (Matrix.gram ℝ u).PosSemidef := Matrix.posSemidef_gram ℝ u
  have h := hPos.transpose.dotProduct_mulVec_nonneg a
  rw [← hMat] at h
  simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, v, star_trivial] using h

/-- The supremum formulation of Theorem 2.2(f) on a nonempty testing set. -/
theorem niceFCPlus_iff_sSup {R : Set G} (hR : R.Nonempty) : NiceFCPlus R ↔
    ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ],
      τ.real {1} ≤ sSup ((fun g ↦ ‖spectralFourier τ g‖) '' R) := by
  constructor
  · intro h τ hτ
    by_contra! hn
    have hB : BddAbove ((fun g ↦ ‖spectralFourier τ g‖) '' R) :=
      ⟨τ.real univ, fun _ ⟨g, _, hg⟩ ↦ hg ▸ norm_spectralFourier_le τ g⟩
    obtain ⟨g, hg, hge⟩ := h τ _ (half_pos (sub_pos.mpr hn))
    have hle := le_csSup hB (Set.mem_image_of_mem _ hg)
    linarith
  · intro h τ hτ ε hε
    by_contra! hn
    have hle : sSup ((fun g ↦ ‖spectralFourier τ g‖) '' R) ≤ τ.real {1} - ε :=
      csSup_le (hR.image _) (by rintro _ ⟨g, hg, rfl⟩; exact (hn g hg).le)
    linarith [h τ]

private theorem spectralFourier_add_measures (τ σ : Measure (DiscreteDual G))
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] (g : G) :
    spectralFourier (τ + σ) g = spectralFourier τ g + spectralFourier σ g :=
  integral_add_measure (χeval_integrable τ g) (χeval_integrable σ g)

private theorem spectralFourier_smul_measure (τ : Measure (DiscreteDual G)) (c : ℝ≥0∞) (g : G) :
    spectralFourier (c • τ) g = c.toReal • spectralFourier τ g :=
  integral_smul_measure _ _

@[simp] private theorem spectralFourier_dirac_trivial (g : G) :
    spectralFourier (Measure.dirac (1 : DiscreteDual G)) g = 1 := by
  change ∫ χ, χeval g χ ∂Measure.dirac (1 : DiscreteDual G) = 1
  rw [integral_dirac' _ _ (χeval_continuous g).stronglyMeasurable, χeval_trivial]

theorem niceFCPlus_of_nonnegativePD {R : Set G} (h : NonnegativeOnPositiveDefinite R) :
    NiceFCPlus R := by
  intro τ hτ ε hε
  let A := ({1} : Set (DiscreteDual G))
  let ν := τ.restrict Aᶜ
  obtain ⟨r, hr, hneg⟩ := h _ (spectralFourier_realPositiveDefinite ν) ε hε
  refine ⟨r, hr, ?_⟩
  have hn := Complex.re_le_norm (spectralFourier τ r)
  have heq : spectralFourier τ r = spectralFourier ν r + (τ.real A : ℂ) := by
    have hm : MeasurableSet A := measurableSet_singleton _
    rw [← Measure.restrict_compl_add_restrict (μ := τ) hm, spectralFourier_add_measures]
    congr 1
    change spectralFourier (τ.restrict ({1} : Set (DiscreteDual G))) r = _
    rw [Measure.restrict_singleton, spectralFourier_smul_measure, spectralFourier_dirac_trivial]
    simp [measureReal_def, A]
  rw [heq, Complex.add_re, Complex.ofReal_re] at hn
  rw [← heq] at hn
  change τ.real A - ε ≤ _
  linarith

private theorem niceFCPlus_finite {R : Set G} (h : NiceFCPlus R)
    (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ r ∈ R, μ.real {1} - ε ≤ ‖spectralFourier μ r‖ := by
  let ν : FiniteMeasure (DiscreteDual G) := ⟨μ, inferInstance⟩
  let τ : Measure (DiscreteDual G) := ν.normalize
  have hμ : μ = (ν.mass : ℝ≥0∞) • τ :=
    congrArg (fun v : FiniteMeasure (DiscreteDual G) ↦ (v : Measure (DiscreteDual G)))
      ν.self_eq_mass_smul_normalize
  let c : ℝ := ν.mass
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have hε' : 0 < ε / (c + 1) := div_pos hε (by linarith)
  have : IsProbabilityMeasure τ := inferInstanceAs
    (IsProbabilityMeasure (ν.normalize : Measure (DiscreteDual G)))
  obtain ⟨r, hr, hb⟩ := h τ _ hε'
  refine ⟨r, hr, ?_⟩
  have hAtom : μ.real {1} = c * τ.real {1} := by
    rw [hμ]
    change (((ν.mass : ℝ≥0∞) • τ) {1}).toReal = _
    rw [smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rfl
  have hFourier : ‖spectralFourier μ r‖ = c * ‖spectralFourier τ r‖ := by
    rw [hμ, spectralFourier_smul_measure, norm_smul, ENNReal.coe_toReal, Real.norm_eq_abs,
      abs_of_nonneg hc]
  have hδ : c * (ε / (c+1)) ≤ ε := calc
    _ ≤ (c+1) * (ε / (c+1)) := mul_le_mul_of_nonneg_right (by linarith) hε'.le
    _ = ε := by field_simp
  rw [hAtom, hFourier]
  linarith [mul_le_mul_of_nonneg_left hb hc]

variable [Countable G] [IsMulCommutative G]

private theorem exists_spectralFourier_eq_realPD (φ : G → ℝ) (hφ : RealPositiveDefinite φ) :
    ∃ μ : Measure (DiscreteDual G), IsFiniteMeasure μ ∧ ∀ g, spectralFourier μ g = (φ g : ℂ) := by
  let S := gaussianPathSystem φ hφ
  let f : (G → ℝ) → ℂ := fun x ↦ (x 1 : ℂ)
  have hf : MemLp f 2 S.measure := (gaussianPath_coordinate_memLp φ hφ 1).ofReal
  let v := hf.toLp f
  let μ := dualVectorSpectralMeasure (systemKoopman S) v
  refine ⟨μ, inferInstance, fun g ↦ ?_⟩
  rw [show spectralFourier μ g = _ from spectralFourier_dualVectorSpectralMeasure
    (systemKoopman S) v g]
  rw [show ⟪v, systemKoopman S g v⟫_ℂ = _ from inner_systemKoopman_of_memLp S hf g]
  change (∫ x, (x ((g⁻¹)⁻¹ * 1) : ℂ) * conj (x 1 : ℂ) ∂S.measure) = _
  simp only [inv_inv, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal]
  exact congrArg Complex.ofReal ((gaussianPath_covariance φ hφ g 1).trans
    (by rw [mul_one, hφ.inv_eq]))

theorem nonnegativePD_of_niceFCPlus {R : Set G} (h : NiceFCPlus R) :
    NonnegativeOnPositiveDefinite R := by
  intro φ hφ ε hε
  obtain ⟨μ, hμ, hμFourier⟩ := exists_spectralFourier_eq_realPD φ hφ
  let c := (φ 1 + 1).toNNReal
  let δ : Measure (DiscreteDual G) := Measure.dirac 1
  let ν := μ + c • δ
  have hc : (c : ℝ) = φ 1 + 1 := Real.coe_toNNReal _ (by linarith [hφ.one_nonneg])
  have hc' : 0 ≤ (c : ℝ) := NNReal.coe_nonneg _
  have : IsFiniteMeasure δ := inferInstanceAs (IsFiniteMeasure (Measure.dirac (1 : DiscreteDual G)))
  have : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (μ + c • δ))
  have hAtom : (c : ℝ) ≤ ν.real {1} := by
    have hmn : (c • δ) {1} ≤ ν {1} := by
      change (c • δ) {1} ≤ (μ + c • δ) {1}
      rw [add_apply]
      exact le_add_self
    have ht := (ENNReal.toReal_le_toReal (measure_ne_top (c • δ) {1})
      (measure_ne_top ν {1})).mpr hmn
    have hδ : δ {1} = 1 := Measure.dirac_apply_of_mem (Set.mem_singleton _)
    simpa only [← Measure.coe_nnreal_smul, smul_apply, smul_eq_mul, hδ, mul_one,
      ENNReal.coe_toReal, measureReal_def] using ht
  obtain ⟨r, hr, hν⟩ := niceFCPlus_finite h ν ε hε
  refine ⟨r, hr, ?_⟩
  have hCalc : spectralFourier ν r = ((φ r + c : ℝ) : ℂ) := by
    change spectralFourier (μ + c • δ) r = _
    rw [spectralFourier_add_measures, hμFourier, ← Measure.coe_nnreal_smul,
      spectralFourier_smul_measure, ENNReal.coe_toReal, Complex.ofReal_add]
    change (φ r : ℂ) + (c : ℝ) • spectralFourier (Measure.dirac (1 : DiscreteDual G)) r = _
    rw [spectralFourier_dirac_trivial]
    simp
  have hpos : 0 ≤ φ r + c := by
    rw [hc]
    linarith [(abs_le.mp (hφ.abs_le_one r)).1]
  rw [hCalc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at hν
  linarith

/-- The abelian clause of Theorem 2.2 is equivalent to the real
    positive-definite condition. -/
theorem niceFCPlus_iff_nonnegativePD {R : Set G} :
    NiceFCPlus R ↔ NonnegativeOnPositiveDefinite R :=
  ⟨nonnegativePD_of_niceFCPlus, niceFCPlus_of_nonnegativePD⟩

/-- Theorem 2.2(d) and (f), both in the supremum form printed in the paper. -/
theorem theorem2_2_d_iff_f {R : Set G} (hR : R.Nonempty) :
    (∀ φ : G → ℝ, RealPositiveDefinite φ → 0 ≤ sSup (φ '' R)) ↔
      ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ],
        τ.real {1} ≤ sSup ((fun r ↦ ‖spectralFourier τ r‖) '' R) :=
  (nonnegativeOnPositiveDefinite_iff_sSup hR).symm.trans
    (niceFCPlus_iff_nonnegativePD.symm.trans (niceFCPlus_iff_sSup hR))

end

end SixProblems
