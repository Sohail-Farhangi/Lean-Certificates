/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Stationary Gaussian path laws. Adapted from the Apache-2.0 formalization in SharpRecurrence/GaussianProcess.lean. -/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set WithLp

open scoped ENNReal NNReal ProbabilityTheory RealInnerProductSpace ComplexConjugate

namespace Mixing.GaussianPath

noncomputable section

private theorem measurable_ereal_toReal : Measurable EReal.toReal := by
  classical
  let s : Set EReal := {⊥, ⊤}ᶜ
  have hs : MeasurableSet s := (measurableSet_singleton _ |>.insert _).compl
  have h := EReal.continuousOn_toReal.measurable_piecewise
    (continuousOn_const (c := (0 : ℝ))) hs
  convert h using 1
  funext x
  change x.toReal = s.piecewise EReal.toReal (fun _ ↦ 0) x
  by_cases hx : x ∈ s
  · rw [Set.piecewise_eq_of_mem s _ _ hx]
  · rw [Set.piecewise_eq_of_notMem s _ _ hx]
    have hbad : x = ⊥ ∨ x = ⊤ := by
      simpa only [s, mem_compl_iff, not_not, mem_insert_iff, mem_singleton_iff] using hx
    rcases hbad with rfl | rfl <;> simp

private def pad (J : Finset ℤ) (x : J → ℝ) (i : ℤ) : EReal :=
  if hi : i ∈ J then (x ⟨i, hi⟩ : EReal) else 0

private theorem measurable_pad (J : Finset ℤ) : Measurable (pad J) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ J
  · simp only [pad, dite_eq_left hi]
    exact continuous_coe_real_ereal.measurable.comp (measurable_pi_apply (⟨i, hi⟩ : J))
  · simp [pad, hi]

private def compactify (I : Finset ℤ) (x : I → ℝ) (i : I) : EReal := (x i : EReal)

private theorem measurable_compactify (I : Finset ℤ) : Measurable (compactify I) :=
  Measurable.of_eval fun i ↦ continuous_coe_real_ereal.measurable.comp (measurable_pi_apply i)

private theorem continuous_project (I : Finset ℤ) :
    Continuous (I.restrict (π := fun _ : ℤ ↦ EReal)) :=
  continuous_pi fun i ↦ continuous_apply (i : ℤ)

/-- Countable real projective extension, by compactifying each coordinate and applying the
finite intersection property to the closed conditions prescribing the finite marginals. -/
theorem exists_real_projective_limit (P : (I : Finset ℤ) → Measure (I → ℝ))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ ℝ) P) :
    ∃ μ : Measure (ℤ → ℝ), IsProjectiveLimit (α := fun _ : ℤ ↦ ℝ) μ P := by
  classical
  let prob (I : Finset ℤ) : ProbabilityMeasure (I → ℝ) := ⟨P I, inferInstance⟩
  let fiber (I : Finset ℤ) : Set (ProbabilityMeasure (ℤ → EReal)) :=
    {μ | μ.map (I.restrict (π := fun _ ↦ EReal)) = (prob I).map (compactify I)}
  have hclosed (I : Finset ℤ) : IsClosed (fiber I) :=
    isClosed_eq (ProbabilityMeasure.continuous_map (continuous_project I)) continuous_const
  have hfinite (D : Finset (Finset ℤ)) : (⋂ I ∈ D, fiber I).Nonempty := by
    let J := D.biUnion id
    refine ⟨(prob J).map (pad J), ?_⟩
    simp only [mem_iInter]
    intro I hI
    have hsub : I ⊆ J := Finset.subset_biUnion_of_mem id hI
    change ((prob J).map (pad J)).map (I.restrict (π := fun _ ↦ EReal)) =
      (prob I).map (compactify I)
    apply ProbabilityMeasure.toMeasure_injective
    change ((P J).map (pad J)).map (I.restrict (π := fun _ ↦ EReal)) = (P I).map (compactify I)
    rw [Measure.map_map (continuous_project I).measurable (measurable_pad J)]
    have heq : I.restrict (π := fun _ ↦ EReal) ∘ pad J =
        compactify I ∘ Finset.restrict₂ (π := fun _ ↦ ℝ) hsub := by
      funext x i
      simp [pad, compactify, hsub i.2]
    rw [heq, ← Measure.map_map (measurable_compactify I) (Finset.measurable_restrict₂ hsub),
      ← hP J I hsub]
  obtain ⟨ν, hν⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  let recover (x : ℤ → EReal) (i : ℤ) : ℝ := (x i).toReal
  have hrecover : Measurable recover :=
    Measurable.of_eval fun i ↦ measurable_ereal_toReal.comp (measurable_pi_apply i)
  refine ⟨(ν : Measure (ℤ → EReal)).map recover, ?_⟩
  intro I
  let recoverI (x : I → EReal) (i : I) : ℝ := (x i).toReal
  have hrecoverI : Measurable recoverI :=
    Measurable.of_eval fun i ↦ measurable_ereal_toReal.comp (measurable_pi_apply i)
  have hνI := mem_iInter.mp hν I
  have hνI' := congrArg (fun p : ProbabilityMeasure (I → EReal) ↦ (p : Measure (I → EReal))) hνI
  change (ν : Measure (ℤ → EReal)).map (I.restrict (π := fun _ ↦ EReal)) =
    (P I).map (compactify I) at hνI'
  rw [Measure.map_map I.measurable_restrict hrecover,
    show I.restrict (π := fun _ ↦ ℝ) ∘ recover =
      recoverI ∘ I.restrict (π := fun _ ↦ EReal) from rfl,
    ← Measure.map_map hrecoverI (continuous_project I).measurable, hνI',
    Measure.map_map hrecoverI (measurable_compactify I)]
  rw [show recoverI ∘ compactify I = id by funext x i; simp [recoverI, compactify], Measure.map_id]

/-- The centered Gaussian law on a finite set of times, in product coordinates. -/
def finiteGaussianFamily (c : ℤ → ℝ) (I : Finset ℤ) : Measure (I → ℝ) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ I)
    (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ)))).map
      (MeasurableEquiv.toLp 2 (I → ℝ)).symm

instance finiteGaussianFamily_isProbability (c : ℤ → ℝ) (I : Finset ℤ) :
    IsProbabilityMeasure (finiteGaussianFamily c I) := by
  unfold finiteGaussianFamily
  infer_instance

private theorem preserving_ofLp (c : ℤ → ℝ) (I : Finset ℤ) :
    MeasurePreserving ofLp
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ)))) (finiteGaussianFamily c I) where
  measurable := by fun_prop
  map_eq := rfl

theorem preserving_toLp (c : ℤ → ℝ) (I : Finset ℤ) :
    MeasurePreserving (toLp 2) (finiteGaussianFamily c I)
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ)))) where
  measurable := by fun_prop
  map_eq := by
    rw [finiteGaussianFamily, Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

theorem finiteGaussianFamily_projective (c : ℤ → ℝ)
    (hc : ∀ I : Finset ℤ, (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ))).PosSemidef) :
    IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ ℝ) (finiteGaussianFamily c) := by
  intro I J hJI
  nth_rw 2 [finiteGaussianFamily]
  rw [Measure.map_map]
  · have h : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ EuclideanSpace.restrict₂ hJI := by ext; simp
    rw [h]
    symm
    have hr := measurePreserving_restrict₂_multivariateGaussian (μ := (0 : EuclideanSpace ℝ I))
      (hc I) hJI
    change MeasurePreserving _ _ (multivariateGaussian (0 : EuclideanSpace ℝ J)
      (Matrix.of fun i j : J ↦ c ((i : ℤ) - (j : ℤ)))) at hr
    exact ((preserving_ofLp c J).comp hr).map_eq
  · exact Finset.measurable_restrict₂ _
  · fun_prop

/-- The law of the finite vector is preserved under any reindexing that preserves
all of its covariance entries. -/
theorem finiteGaussianFamily_reindex (c : ℤ → ℝ)
    (hc : ∀ I : Finset ℤ, (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ))).PosSemidef)
    {I J : Finset ℤ} (k : I → J)
    (hk : ∀ i j : I, c ((k i : ℤ) - (k j : ℤ)) = c ((i : ℤ) - (j : ℤ))) :
    MeasurePreserving (fun x : J → ℝ ↦ fun i : I ↦ x (k i))
      (finiteGaussianFamily c J) (finiteGaussianFamily c I) := by
  let g : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ I :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I ↦ ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i ↦ EuclideanSpace.proj (k i))
  have hgi (x : EuclideanSpace ℝ J) (i : I) : (g x) i = x (k i) := rfl
  have hg : MeasurePreserving g
      (multivariateGaussian (0 : EuclideanSpace ℝ J)
        (Matrix.of fun i j : J ↦ c ((i : ℤ) - (j : ℤ))))
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ)))) := by
    refine ⟨g.continuous.measurable, ?_⟩
    ·
      apply IsGaussian.ext
      · simp only [id_eq, integral_id_multivariateGaussian]
        rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian, map_zero]
        exact IsGaussian.integrable_id
      rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun I ℝ).toBasis fun i j ↦ ?_
      rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
        covarianceBilin_apply_eq_cov, covariance_map]
      · have heval (i : I) : (fun u ↦ ⟪(EuclideanSpace.basisFun I ℝ).toBasis i, u⟫) ∘ g =
            fun u ↦ u (k i) := by ext; simp [PiLp.inner_apply, hgi]
        simp_rw [heval, covariance_eval_multivariateGaussian (hc J),
          covarianceBilin_multivariateGaussian (hc I)]
        simpa using hk i j
      any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
      · exact g.continuous.measurable.aemeasurable
      · exact IsGaussian.memLp_two_id
  exact ((preserving_ofLp c I).comp (hg.comp (preserving_toLp c J)))

def shift : (ℤ → ℝ) ≃ᵐ (ℤ → ℝ) :=
  (MeasurableEquiv.piCongrLeft (π := fun _ : ℤ ↦ ℝ) (Equiv.addRight (1 : ℤ))).symm

theorem shift_apply (x : ℤ → ℝ) (i : ℤ) : shift x i = x (i + 1) := rfl

theorem shift_iterate_apply (r : ℕ) (x : ℤ → ℝ) (i : ℤ) :
    ((shift : (ℤ → ℝ) → ℤ → ℝ)^[r] x) i = x (i + (r : ℤ)) := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', shift_apply, ih]
    congr 1
    omega

theorem shift_preserving_of_projective_limit (c : ℤ → ℝ)
    (hc : ∀ I : Finset ℤ, (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ))).PosSemidef)
    {μ : Measure (ℤ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℤ ↦ ℝ) μ (finiteGaussianFamily c)) :
    MeasurePreserving shift μ μ where
  measurable := shift.measurable
  map_eq := by
    apply IsProjectiveLimit.unique (P := finiteGaussianFamily c) _ hμ
    intro I
    let J := I.image (fun i : ℤ ↦ i + 1)
    let k : I → J := fun i ↦ ⟨(i : ℤ) + 1, Finset.mem_image_of_mem _ i.2⟩
    have hK := finiteGaussianFamily_reindex c hc k (fun i j ↦ by
      change c (((i : ℤ) + 1) - ((j : ℤ) + 1)) = _
      congr 1
      omega)
    rw [Measure.map_map I.measurable_restrict shift.measurable,
      show I.restrict (π := fun _ ↦ ℝ) ∘ shift = (fun x : J → ℝ ↦ fun i : I ↦ x (k i)) ∘ J.restrict
        from rfl,
      ← Measure.map_map hK.measurable J.measurable_restrict, hμ J, hK.map_eq]

private theorem euclideanEvalAddLaw (c : ℤ → ℝ) (h0 : c 0 = 1) (I : Finset ℤ)
    (hc : (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ))).PosSemidef) (i j : I) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I ↦ x i + x j)
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ))))
      (gaussianReal 0 (Real.toNNReal (2 + 2 * c ((i : ℤ) - (j : ℤ))))) := by
  let S : Matrix I I ℝ := Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ))
  let ρ := multivariateGaussian (0 : EuclideanSpace ℝ I) S
  let L : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj i + EuclideanSpace.proj j
  change MeasurePreserving L ρ _
  refine ⟨L.continuous.measurable, ?_⟩
  have : IsGaussian ρ := by unfold ρ; infer_instance
  have hL0 : (∫ x, L x ∂ρ) = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id L]
    unfold ρ
    rw [integral_id_multivariateGaussian, map_zero]
  rw [IsGaussian.map_eq_gaussianReal, hL0]
  congr 2
  change Var[fun x : EuclideanSpace ℝ I ↦ x i + x j; ρ] = _
  have hmem (k : I) : MemLp (fun x : EuclideanSpace ℝ I ↦ x k) 2 ρ :=
    (IsGaussian.hasGaussianLaw_id.map_fun (EuclideanSpace.proj k)).memLp_two
  rw [variance_fun_add (hmem i) (hmem j)]
  unfold ρ
  rw [variance_eval_multivariateGaussian hc, variance_eval_multivariateGaussian hc,
    covariance_eval_multivariateGaussian hc]
  simp only [Matrix.of_apply, sub_self, h0]
  ring

/-- Section 4.1's Gaussian path law and the prescribed one-point and pair-sum
distributions. The integer shift is measure preserving for this law. -/
theorem exists_stationary_gaussian_path (c : ℤ → ℝ) (h0 : c 0 = 1) (heven : Function.Even c)
    (hc : ∀ I : Finset ℤ, (Matrix.of fun i j : I ↦ c ((i : ℤ) - (j : ℤ))).PosSemidef) :
    ∃ μ : Measure (ℤ → ℝ), IsProbabilityMeasure μ ∧ MeasurePreserving shift μ μ ∧
      MeasurePreserving (fun x : ℤ → ℝ ↦ x 0) μ (gaussianReal 0 1) ∧
      ∀ r : ℕ, MeasurePreserving (fun x : ℤ → ℝ ↦ x 0 + x (r : ℤ)) μ
        (gaussianReal 0 (Real.toNNReal (2 + 2 * c r))) := by
  obtain ⟨μ, hμ⟩ := exists_real_projective_limit (finiteGaussianFamily c)
    (finiteGaussianFamily_projective c hc)
  have hlimit (I : Finset ℤ) : MeasurePreserving (I.restrict (π := fun _ ↦ ℝ)) μ
      (finiteGaussianFamily c I) := ⟨I.measurable_restrict, hμ I⟩
  refine ⟨μ, hμ.isProbabilityMeasure, shift_preserving_of_projective_limit c hc hμ, ?_, ?_⟩
  · let I : Finset ℤ := {0}
    let i : I := ⟨0, by simp [I]⟩
    have h := (measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ I)) (hc I) (i := i)).comp
      ((preserving_toLp c I).comp (hlimit I))
    simpa [i, h0, Function.comp_def, Finset.restrict] using h
  intro r
  let I : Finset ℤ := {0, (r : ℤ)}
  let i : I := ⟨0, by simp [I]⟩
  let j : I := ⟨(r : ℤ), by simp [I]⟩
  have h := (euclideanEvalAddLaw c h0 I (hc I) i j).comp
    ((preserving_toLp c I).comp (hlimit I))
  simpa [i, j, heven (r : ℤ), Function.comp_def, Finset.restrict] using h

def spectralCovariance (τ : Measure UnitAddCircle) (n : ℤ) : ℝ :=
  (∫ x, fourier (-n) x ∂τ).re

private theorem fourier_re_integrable (τ : Measure UnitAddCircle) [IsFiniteMeasure τ] (n : ℤ) :
    Integrable (fun x ↦ (fourier (-n) x).re) τ :=
  (Complex.continuous_re.comp (fourier (-n)).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem spectralCovariance_eq_integral (τ : Measure UnitAddCircle) [IsFiniteMeasure τ] (n : ℤ) :
    spectralCovariance τ n = ∫ x, (fourier (-n) x).re ∂τ := by
  unfold spectralCovariance
  symm
  exact integral_re (𝕜 := ℂ) ((fourier (-n)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

theorem spectralCovariance_zero (τ : Measure UnitAddCircle) [IsProbabilityMeasure τ] :
    spectralCovariance τ 0 = 1 := by
  rw [spectralCovariance_eq_integral]
  simp [measureReal_def]

theorem spectralCovariance_even (τ : Measure UnitAddCircle) [IsFiniteMeasure τ] (n : ℤ) :
    spectralCovariance τ (-n) = spectralCovariance τ n := by
  rw [spectralCovariance_eq_integral, spectralCovariance_eq_integral]
  simp only [neg_neg, fourier_neg, Complex.conj_re]

/-- Real Fourier coefficients give a positive-definite covariance sequence. Each
quadratic form is the integral of a sum of two real squares. -/
theorem fourier_covariance_posSemidef (τ : Measure UnitAddCircle) [IsFiniteMeasure τ]
    (I : Finset ℤ) :
    (Matrix.of fun i j : I ↦ spectralCovariance τ ((i : ℤ) - (j : ℤ))).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    intro i j
    change spectralCovariance τ ((j : ℤ) - (i : ℤ)) =
      spectralCovariance τ ((i : ℤ) - (j : ℤ))
    rw [show (j : ℤ) - (i : ℤ) = -((i : ℤ) - (j : ℤ)) by omega,
      spectralCovariance_even]
  intro a
  let f : I → I → UnitAddCircle → ℝ := fun i j x ↦
    a i * ((fourier (-((i : ℤ) - (j : ℤ))) x).re * a j)
  have hf (i j : I) : Integrable (f i j) τ :=
    ((fourier_re_integrable τ ((i : ℤ) - (j : ℤ))).mul_const (a j)).const_mul (a i)
  have hpoint (x : UnitAddCircle) (i j : I) :
      (fourier (-((i : ℤ) - (j : ℤ))) x).re =
        (fourier (-(i : ℤ)) x).re * (fourier (-(j : ℤ)) x).re +
        (fourier (-(i : ℤ)) x).im * (fourier (-(j : ℤ)) x).im := by
    have hj : fourier (j : ℤ) x = conj (fourier (-(j : ℤ)) x) := by
      simpa only [neg_neg] using (fourier_neg (n := -(j : ℤ)) (x := x))
    rw [show -((i : ℤ) - (j : ℤ)) = -(i : ℤ) + (j : ℤ) by omega,
      fourier_add, hj, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hnonneg (x : UnitAddCircle) : 0 ≤ ∑ i : I, ∑ j : I, f i j x := by
    have hexpand :
        (∑ i : I, a i * (fourier (-(i : ℤ)) x).re) ^ 2 +
          (∑ i : I, a i * (fourier (-(i : ℤ)) x).im) ^ 2 = ∑ i : I, ∑ j : I, f i j x := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [f]
      rw [hpoint]
      ring
    rw [← hexpand]
    positivity
  have hint : (∫ x, ∑ i : I, ∑ j : I, f i j x ∂τ) =
      ∑ i : I, ∑ j : I, a i * (spectralCovariance τ ((i : ℤ) - (j : ℤ)) * a j) := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ ↦ hf i j)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [f, integral_const_mul, integral_mul_const, spectralCovariance_eq_integral]
    · exact fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hf i j
  have h := integral_nonneg (μ := τ) (f := fun x ↦ ∑ i : I, ∑ j : I, f i j x) hnonneg
  rw [hint] at h
  simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum] using h


end

end Mixing.GaussianPath
