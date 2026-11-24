/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorGaussianDensity
public import Mixing.RigidRepresentations

/-! # Stationary Gaussian systems and their covariance -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter WithLp Set
open scoped ProbabilityTheory InnerProductSpace Topology NNReal BigOperators ComplexConjugate

namespace Mixing.StationaryGaussian

variable (τ : Measure UnitAddCircle) [IsProbabilityMeasure τ]

/-- The real covariance prescribed by a spectral probability measure. -/
noncomputable def covariance : ℤ → ℝ := GaussianPath.spectralCovariance τ

theorem covariance_zero : covariance τ 0 = 1 := GaussianPath.spectralCovariance_zero τ

theorem covariance_even (n : ℤ) : covariance τ (-n) = covariance τ n :=
  GaussianPath.spectralCovariance_even τ n

theorem covariance_psd (I : Finset ℤ) :
    (Matrix.of fun i j : I ↦ covariance τ ((i : ℤ) - (j : ℤ))).PosSemidef :=
  GaussianPath.fourier_covariance_posSemidef τ I

/-- The probability law of the stationary Gaussian path with the prescribed covariance. -/
noncomputable def measure : Measure (ℤ → ℝ) :=
  Classical.choose (GaussianPath.exists_real_projective_limit
    (GaussianPath.finiteGaussianFamily (covariance τ))
      (GaussianPath.finiteGaussianFamily_projective _ (covariance_psd τ)))

theorem measure_projective :
    IsProjectiveLimit (α := fun _ : ℤ ↦ ℝ) (measure τ)
      (GaussianPath.finiteGaussianFamily (covariance τ)) :=
  Classical.choose_spec (GaussianPath.exists_real_projective_limit
    (GaussianPath.finiteGaussianFamily (covariance τ))
      (GaussianPath.finiteGaussianFamily_projective _ (covariance_psd τ)))

instance : IsProbabilityMeasure (measure τ) := (measure_projective τ).isProbabilityMeasure

theorem timeShift_preserving (j : ℤ) :
    MeasurePreserving (gaussianPathTimeShift j) (measure τ) (measure τ) where
  measurable := Measurable.of_eval fun i ↦ measurable_pi_apply (i + j)
  map_eq := by
    apply IsProjectiveLimit.unique
      (P := GaussianPath.finiteGaussianFamily (covariance τ)) _
      (measure_projective τ)
    intro I
    let J := I.image (fun i : ℤ ↦ i + j)
    let k : I → J := fun i ↦ ⟨(i : ℤ) + j, Finset.mem_image_of_mem _ i.2⟩
    have hK := GaussianPath.finiteGaussianFamily_reindex (covariance τ)
      (covariance_psd τ) k (fun i l ↦ by
        change (covariance τ) (((i : ℤ) + j) - ((l : ℤ) + j)) = _
        congr 1
        omega)
    have hm : Measurable (gaussianPathTimeShift j) :=
      Measurable.of_eval fun i ↦ measurable_pi_apply (i + j)
    rw [Measure.map_map I.measurable_restrict hm,
      show I.restrict (π := fun _ ↦ ℝ) ∘ gaussianPathTimeShift j =
        (fun x : J → ℝ ↦ fun i : I ↦ x (k i)) ∘ J.restrict from rfl,
      ← Measure.map_map hK.measurable J.measurable_restrict, (measure_projective τ) J,
      hK.map_eq]

/-- The concrete stationary Gaussian system associated to a spectral probability measure. -/
noncomputable abbrev system : System (Multiplicative ℤ) (ℤ → ℝ) where
  measure := (measure τ)
  probability := inferInstance
  act g := gaussianPathTimeShift g.toAdd
  act_one := by funext x i; change x (i + 0) = x i; rw [add_zero]
  act_mul g h := by
    funext x i
    change x (i + (g.toAdd + h.toAdd)) = x ((i + g.toAdd) + h.toAdd)
    rw [add_assoc]
  preserves g := (timeShift_preserving τ) g.toAdd

theorem euclidean_marginal (I : Finset ℤ) :
    MeasurePreserving (fun x : ℤ → ℝ ↦ toLp 2 (I.restrict x)) (measure τ)
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ (covariance τ) ((i : ℤ) - (j : ℤ)))) :=
  (GaussianPath.preserving_toLp (covariance τ) I).comp
    ⟨I.measurable_restrict, (measure_projective τ) I⟩

theorem coordinate_law (i : ℤ) :
    MeasurePreserving (fun x : ℤ → ℝ ↦ x i) (measure τ) (gaussianReal 0 1) := by
  let I : Finset ℤ := {i}
  let k : I := ⟨i, by simp [I]⟩
  have h := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ I))
    ((covariance_psd τ) I) (i := k)).comp ((euclidean_marginal τ) I)
  simpa [k, Function.comp_def, Finset.restrict, (covariance_zero τ)] using h

theorem coordinate_memLp (i : ℤ) :
    MemLp (fun x : ℤ → ℝ ↦ x i) 2 (measure τ) :=
  (IsGaussian.memLp_two_id (μ := gaussianReal 0 1)).comp_measurePreserving
    ((coordinate_law τ) i)

theorem coordinate_integral (i : ℤ) :
    (∫ x, x i ∂(measure τ)) = 0 := by
  have h := (coordinate_law τ) i
  rw [← integral_id_gaussianReal (μ := 0) (v := 1), ← h.map_eq]
  have hId : AEStronglyMeasurable (fun x : ℝ ↦ x)
      ((measure τ).map (fun x ↦ x i)) := aestronglyMeasurable_id
  exact (integral_map h.measurable.aemeasurable hId).symm

theorem coordinate_covariance (i j : ℤ) :
    cov[fun x ↦ x i, fun x ↦ x j; (measure τ)] = (covariance τ) (i - j) := by
  let I : Finset ℤ := {i, j}
  let l : I := ⟨i, by simp [I]⟩
  let m : I := ⟨j, by simp [I]⟩
  have hI := (euclidean_marginal τ) I
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ I))
    ((covariance_psd τ) I) l m
  rw [← hI.map_eq, covariance_map] at hc
  · exact hc
  all_goals fun_prop

theorem coordinate_pair_integral (i j : ℤ) :
    (∫ x, x i * x j ∂(measure τ)) = (covariance τ) (i - j) := by
  have h := (coordinate_covariance τ) i j
  rw [covariance_eq_sub ((coordinate_memLp τ) i) ((coordinate_memLp τ) j),
    (coordinate_integral τ), zero_mul, sub_zero] at h
  exact h

/-- Coordinate covariance of the cylindrical linear functional. -/
noncomputable def quadratic {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ k, a i * a k * (covariance τ) (j i - j k)

/-- Every finite-coordinate character has the characteristic expectation prescribed by the
Gaussian covariance, allowing repeated time indices. -/
theorem cylChar_integral {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (a : ι → ℝ) :
    (∫ x, gaussianCylChar j a x ∂(measure τ)) =
      Complex.exp (-(((quadratic τ) j a : ℝ) : ℂ) / 2) := by
  classical
  let I := Finset.univ.image j
  let k : ι → I := fun i ↦ ⟨j i, Finset.mem_image_of_mem j (Finset.mem_univ i)⟩
  let S : Matrix I I ℝ := Matrix.of fun m n : I ↦ (covariance τ) ((m : ℤ) - (n : ℤ))
  let ρ := multivariateGaussian (0 : EuclideanSpace ℝ I) S
  let R : EuclideanSpace ℝ I →L[ℝ] ℝ := ∑ i, a i • EuclideanSpace.proj (k i)
  have hR (w : EuclideanSpace ℝ I) : R w = ∑ i, a i * w (k i) := by
    simp [R, smul_eq_mul]
  have hI : MeasurePreserving (fun x : ℤ → ℝ ↦ toLp 2 (I.restrict x)) (measure τ) ρ :=
    (euclidean_marginal τ) I
  have hM : MemLp id 2 ρ := IsGaussian.memLp_two_id
  have ha (i : ι) : MemLp (fun x : EuclideanSpace ℝ I ↦ a i * x (k i)) 2 ρ :=
    ((IsGaussian.hasGaussianLaw_id.map_fun (EuclideanSpace.proj (k i))).memLp_two).const_mul (a i)
  have hCov : covarianceBilinDual ρ R R = (quadratic τ) j a := by
    rw [covarianceBilinDual_eq_covariance hM]
    have hFun : (R : EuclideanSpace ℝ I → ℝ) = fun w ↦ ∑ i, a i * w (k i) := funext hR
    rw [hFun, covariance_fun_sum_fun_sum ha ha]
    unfold quadratic
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right]
    change a i * (a l * cov[fun w ↦ w (k i), fun w ↦ w (k l);
      multivariateGaussian (0 : EuclideanSpace ℝ I) S]) = _
    rw [covariance_eval_multivariateGaussian ((covariance_psd τ) I)]
    change a i * (a l * (covariance τ) (j i - j l)) = _
    ring
  have hMean : R (∫ x, x ∂ρ) = 0 := by
    unfold ρ
    rw [integral_id_multivariateGaussian, map_zero]
  have hChar := IsGaussian.charFunDual_eq' (μ := ρ) R
  change charFunDual ρ R =
    Complex.exp (((R (∫ x, x ∂ρ) : ℝ) : ℂ) * Complex.I -
      ((covarianceBilinDual ρ R R : ℝ) : ℂ) / 2) at hChar
  rw [hMean, hCov, Complex.ofReal_zero, zero_mul, zero_sub, ← neg_div] at hChar
  rw [← hChar, charFunDual_apply, ← hI.map_eq,
    integral_map hI.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  change gaussianCylChar j a x = Complex.exp ((R (toLp 2 (I.restrict x)) : ℂ) * Complex.I)
  rw [gaussianCylChar, hR]
  rfl

private theorem gaussianCylChar_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ) (x : ℤ → ℝ) :
    gaussianCylChar j a x * gaussianCylChar k b x =
      gaussianCylChar (Sum.elim j k) (Sum.elim a b) x := by
  simp [gaussianCylChar, Fintype.sum_sum_type, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem quadratic_join {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ) (n : ℤ) :
    (quadratic τ) (Sum.elim j (fun l ↦ k l + n)) (Sum.elim a b) =
      (quadratic τ) j a + (quadratic τ) k b +
        (∑ i, ∑ l, a i * b l * (covariance τ) (n + (k l - j i))) +
        ∑ l, ∑ i, b l * a i * (covariance τ) (n + (k l - j i)) := by
  simp only [quadratic, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib, add_sub_add_right_eq_sub]
  have hf (i : ι) (l : κ) :
      (covariance τ) (j i - (k l + n)) =
        (covariance τ) (n + (k l - j i)) := by
    rw [show j i - (k l + n) = -(n + (k l - j i)) by omega, (covariance_even τ)]
  have hr (i : ι) (l : κ) : k l + n - j i = n + (k l - j i) := by omega
  simp_rw [hf, hr]
  ac_rfl

private noncomputable def jointQuadratic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ) (c : ℤ → ℝ) : ℝ :=
  quadratic τ j a + quadratic τ k b +
    (∑ i, ∑ l, a i * b l * c (k l - j i)) +
    ∑ l, ∑ i, b l * a i * c (k l - j i)

private theorem correlation_cylChar_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ) (g : Multiplicative ℤ) :
    (∫ x, gaussianCylChar j a x * gaussianCylChar k b ((system τ).act g x) ∂(measure τ)) =
      Complex.exp (-(jointQuadratic τ j a k b (fun s => covariance τ (g.toAdd + s)) : ℂ) / 2) := by
  change (∫ x, gaussianCylChar j a x *
    gaussianCylChar (fun l => k l + g.toAdd) b x ∂(measure τ)) = _
  simp_rw [gaussianCylChar_mul, cylChar_integral, quadratic_join]
  rfl

private theorem correlation_cylChar_tendsto {ι κ J : Type*} [Fintype ι] [Fintype κ]
    (j : ι → ℤ) (a : ι → ℝ) (k : κ → ℤ) (b : κ → ℝ) (g : J → Multiplicative ℤ)
    (L : Filter J) (c : ℤ → ℝ)
    (hCov : ∀ s : ℤ, Tendsto (fun z => covariance τ ((g z).toAdd + s)) L (𝓝 (c s))) :
    Tendsto (fun z => ∫ x, gaussianCylChar j a x *
        gaussianCylChar k b ((system τ).act (g z) x) ∂(measure τ)) L
      (𝓝 (Complex.exp (-(jointQuadratic τ j a k b c : ℂ) / 2))) := by
  simp_rw [correlation_cylChar_eq]
  refine ((show Continuous (fun s : ℝ => Complex.exp (-(s : ℂ) / 2)) by fun_prop).tendsto _).comp ?_
  unfold jointQuadratic
  have h₁ : Tendsto (fun z => ∑ i, ∑ l, a i * b l * covariance τ ((g z).toAdd + (k l - j i)))
      L (𝓝 (∑ i, ∑ l, a i * b l * c (k l - j i))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun l _ =>
      (tendsto_const_nhds (x := a i * b l)).mul (hCov (k l - j i))
  have h₂ : Tendsto (fun z => ∑ l, ∑ i, b l * a i * covariance τ ((g z).toAdd + (k l - j i)))
      L (𝓝 (∑ l, ∑ i, b l * a i * c (k l - j i))) :=
    tendsto_finsetSum _ fun l _ => tendsto_finsetSum _ fun i _ =>
      (tendsto_const_nhds (x := b l * a i)).mul (hCov (k l - j i))
  exact (tendsto_const_nhds.add h₁).add h₂

private theorem conj_cylChar {ι : Type*} [Fintype ι] (j : ι → ℤ) (a : ι → ℝ) (x : ℤ → ℝ) :
    conj (gaussianCylChar j a x) = gaussianCylChar j (fun i => -a i) x := by
  simp only [gaussianCylChar, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_neg, mul_neg]

private theorem testVector_inner (a b : GaussianTest) (g : Multiplicative ℤ) :
    ⟪a.toVector (measure τ), (system τ).koopmanRep g (b.toVector (measure τ))⟫_ℂ =
      ∫ x, gaussianCylChar a.times (fun i => -a.frequencies i) x *
        gaussianCylChar b.times b.frequencies ((system τ).act g x) ∂(measure τ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have ha : a.toVector (measure τ) =ᵐ[measure τ] a.observable := a.observable.coe_l2 _
  have hb := (Lp.coeFn_compMeasurePreserving (b.toVector (measure τ)) ((system τ).preserves g)).trans
    (((system τ).preserves g).quasiMeasurePreserving.ae_eq_comp (b.observable.coe_l2 _))
  filter_upwards [ha, hb] with x hA hB
  change a.toVector (measure τ) x = gaussianCylChar a.times a.frequencies x at hA
  change (system τ).koopmanRep g (b.toVector (measure τ)) x =
    gaussianCylChar b.times b.frequencies ((system τ).act g x) at hB
  rw [hA, hB, RCLike.inner_apply', conj_cylChar]

private theorem testOperator_eq_of_inner_eq (D E : Lp ℂ 2 (measure τ) →L[ℂ] Lp ℂ 2 (measure τ))
    (hDE : ∀ a b : GaussianTest,
      ⟪a.toVector (measure τ), D (b.toVector (measure τ))⟫_ℂ =
        ⟪a.toVector (measure τ), E (b.toVector (measure τ))⟫_ℂ) : D = E := by
  let W := Set.range fun a : GaussianTest => a.toVector (measure τ)
  let U := D - E
  have hDense : (Submodule.span ℂ W).topologicalClosure = ⊤ := gaussianTestVectors_dense (measure τ)
  have hZero (L : Lp ℂ 2 (measure τ) →L[ℂ] ℂ) (hL : W ⊆ L.ker) (z : Lp ℂ 2 (measure τ)) :
      L z = 0 := by
    have h := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hL) L.isClosed_ker
    rw [hDense] at h
    exact h Submodule.mem_top
  have hU : W ⊆ U.ker := by
    rintro _ ⟨b, rfl⟩
    let z := U (b.toVector (measure τ))
    have h := hZero (innerSL ℂ z) (by
      rintro _ ⟨a, rfl⟩
      change ⟪z, a.toVector (measure τ)⟫_ℂ = 0
      rw [← inner_conj_symm]
      change conj ⟪a.toVector (measure τ), (D - E) (b.toVector (measure τ))⟫_ℂ = 0
      rw [sub_apply, inner_sub_right, hDE, sub_self, map_zero]) z
    exact inner_self_eq_zero.mp h
  have h := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hU) U.isClosed_ker
  rw [hDense] at h
  apply ContinuousLinearMap.ext
  intro z
  exact sub_eq_zero.mp (h (Submodule.mem_top (x := z)))

/-- Gaussian ultrafilter mixing follows from vanishing of the covariance at each shifted time. -/
theorem isUMixing_singleton_of_covariance_tendsto (p : Ultrafilter (Multiplicative ℤ))
    (hCov : ∀ s : ℤ, Tendsto (fun g : Multiplicative ℤ => covariance τ (g.toAdd + s))
      (p : Filter (Multiplicative ℤ)) (𝓝 0)) : (system τ).IsUMixing {p} := by
  let S := system τ
  let c := constantOne (measure τ)
  let Q := InnerProductSpace.rankOne ℂ c c
  let A := ultrafilterOperator S.koopmanRep p
  have hQ (f k : Lp ℂ 2 (measure τ)) :
      ⟪f, Q k⟫_ℂ = star (∫ x, f x ∂(measure τ)) * (∫ x, k x ∂(measure τ)) := by
    simp only [Q, InnerProductSpace.rankOne_apply, inner_smul_right]
    rw [mul_comm, ← inner_conj_symm]
    exact congrArg₂ (· * ·) (congrArg star (inner_constantOne_left _ f)) (inner_constantOne_left _ k)
  have hAQ : A = Q := by
    apply testOperator_eq_of_inner_eq τ
    intro a b
    have hlim := correlation_cylChar_tendsto τ a.times (fun i => -a.frequencies i)
      b.times b.frequencies id (p : Filter (Multiplicative ℤ)) 0 hCov
    change Tendsto (fun g => ∫ x, gaussianCylChar a.times (fun i => -a.frequencies i) x *
      gaussianCylChar b.times b.frequencies (S.act g x) ∂(measure τ)) _ _ at hlim
    have hlim := hlim.congr fun g => (testVector_inner τ a b g).symm
    have hMeanA : star (∫ x, a.toVector (measure τ) x ∂(measure τ)) =
        ∫ x, gaussianCylChar a.times (fun i => -a.frequencies i) x ∂(measure τ) := by
      rw [GaussianTest.toVector, integral_congr_ae (a.observable.coe_l2 _), Complex.star_def, ← integral_conj]
      change (∫ x, conj (gaussianCylChar a.times a.frequencies x) ∂(measure τ)) = _
      simp_rw [conj_cylChar]
    have hMeanB : (∫ x, b.toVector (measure τ) x ∂(measure τ)) =
        ∫ x, gaussianCylChar b.times b.frequencies x ∂(measure τ) :=
      integral_congr_ae (b.observable.coe_l2 _)
    rw [hQ, hMeanA, hMeanB, cylChar_integral, cylChar_integral]
    have hFactor (d e : ℝ) : Complex.exp (-((d + e : ℝ) : ℂ) / 2) =
        Complex.exp (-(d : ℂ) / 2) * Complex.exp (-(e : ℂ) / 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [jointQuadratic, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hFactor] at hlim
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff S.koopmanRep p _ _) hlim
  rw [System.isUMixing_iff_lp_correlations]
  intro q hq f k
  have he : q = p := Set.mem_singleton_iff.mp hq
  subst q
  have hlim := tendsto_ultrafilterOperator_coeff S.koopmanRep p f k
  change Tendsto _ _ (𝓝 ⟪f, A k⟫_ℂ) at hlim
  rw [hAQ, hQ] at hlim
  exact hlim

/-- One sequence on which the shifted covariance returns to its original
values is a rigidity sequence for the stationary Gaussian system. -/
theorem isRigidRepresentation_of_covariance_tendsto (g : ℕ → Multiplicative ℤ)
    (hg : Tendsto g atTop cofinite)
    (hCov : ∀ s : ℤ, Tendsto (fun n => covariance τ ((g n).toAdd + s)) atTop (𝓝 (covariance τ s))) :
    IsRigidRepresentation (system τ).koopmanRep := by
  let U := (system τ).koopmanRep
  refine ⟨g, hg, fun x y => ?_⟩
  apply (Filter.tendsto_iff_ultrafilter _ _ _).mpr
  intro p hp
  let q := p.map g
  let A := ultrafilterOperator U q
  have hA (x y : Lp ℂ 2 (measure τ)) :
      Tendsto (fun n => ⟪x, U (g n) y⟫_ℂ) (p : Filter ℕ) (𝓝 ⟪x, A y⟫_ℂ) :=
    (tendsto_ultrafilterOperator_coeff U q x y).comp tendsto_map
  have hId : A = 1 := by
    apply testOperator_eq_of_inner_eq τ
    intro a b
    have hlim := (correlation_cylChar_tendsto τ a.times (fun i => -a.frequencies i)
      b.times b.frequencies g atTop (covariance τ) hCov).mono_left hp
    have hlim := hlim.congr fun n => (testVector_inner τ a b (g n)).symm
    have he : (1 : Multiplicative ℤ).toAdd = 0 := rfl
    have hAt0 : ⟪a.toVector (measure τ), (1 : Lp ℂ 2 (measure τ) →L[ℂ] Lp ℂ 2 (measure τ))
        (b.toVector (measure τ))⟫_ℂ = Complex.exp
          (-(jointQuadratic τ a.times (fun i => -a.frequencies i) b.times b.frequencies (covariance τ) : ℂ) / 2) := by
      have hf := (testVector_inner τ a b 1).trans
        (correlation_cylChar_eq τ a.times (fun i => -a.frequencies i) b.times b.frequencies 1)
      have hCov0 : (fun s => covariance τ ((1 : Multiplicative ℤ).toAdd + s)) = covariance τ :=
        funext fun s => by rw [he, zero_add]
      rw [hCov0, map_one] at hf
      exact hf
    rw [← hAt0] at hlim
    exact tendsto_nhds_unique (hA _ _) hlim
  change Tendsto (fun n => ⟪y, U (g n) x⟫_ℂ) (p : Filter ℕ) (𝓝 ⟪y, x⟫_ℂ)
  simpa only [hId, one_apply_eq_self] using hA y x

/-- The stationary Gaussian model is nontrivial since one marginal is a
standard normal law. -/
theorem exists_event_intermediate_probability :
    ∃ A : Set (ℤ → ℝ), MeasurableSet A ∧ 0 < (system τ).measure A ∧ (system τ).measure A < 1 := by
  let e : (ℤ → ℝ) → ℝ := fun x => x 0
  let B : Set ℝ := Ioi 0
  let C : Set ℝ := Iio 0
  let ρ := gaussianReal 0 1
  have hL : MeasurePreserving e (measure τ) ρ := coordinate_law τ 0
  have hAc : volume ≪ ρ := gaussianReal_absolutelyContinuous' 0 one_ne_zero
  have hB : MeasurableSet B := measurableSet_Ioi
  have hC : MeasurableSet C := measurableSet_Iio
  have hB₀ : 0 < ρ B := by
    refine pos_iff_ne_zero.mpr fun h0 => ?_
    exact (by simp [B] : volume B ≠ 0) (hAc h0)
  have hC₀ : 0 < ρ C := by
    refine pos_iff_ne_zero.mpr fun h0 => ?_
    exact (by simp [C] : volume C ≠ 0) (hAc h0)
  have hB₁ : ρ B < 1 := by
    by_contra! h
    have hNull : ρ Bᶜ = 0 := by rw [measure_compl hB (measure_ne_top _ _), measure_univ, tsub_eq_zero_of_le h]
    have hsub : C ⊆ Bᶜ := fun _ hx hx' => lt_asymm hx hx'
    exact hC₀.ne' (measure_mono_null hsub hNull)
  refine ⟨e ⁻¹' B, hL.measurable hB, ?_⟩
  change 0 < measure τ (e ⁻¹' B) ∧ measure τ (e ⁻¹' B) < 1
  rw [hL.measure_preimage hB.nullMeasurableSet]
  exact ⟨hB₀, hB₁⟩

end Mixing.StationaryGaussian
