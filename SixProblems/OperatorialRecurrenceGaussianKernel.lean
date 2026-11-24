/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Finite-coordinate Gaussian laws and countable projective limits. Adapted from the Apache-2.0 formalization in SharpRecurrence/GaussianProcess.lean. -/

@[expose] public section

open Function MeasureTheory ProbabilityTheory Set WithLp

open scoped Classical ENNReal NNReal ProbabilityTheory RealInnerProductSpace ComplexConjugate

namespace SixProblems.Gaussian

noncomputable section

variable {Γ : Type*}

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

private def pad (J : Finset Γ) (x : J → ℝ) (i : Γ) : EReal :=
  if hi : i ∈ J then (x ⟨i, hi⟩ : EReal) else 0

private theorem measurable_pad (J : Finset Γ) : Measurable (pad J) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ J
  · simp only [pad, dite_eq_left hi]
    exact continuous_coe_real_ereal.measurable.comp (measurable_pi_apply (⟨i, hi⟩ : J))
  · simp [pad, hi]

private def compactify (I : Finset Γ) (x : I → ℝ) (i : I) : EReal := (x i : EReal)

private theorem measurable_compactify (I : Finset Γ) : Measurable (compactify I) :=
  Measurable.of_eval fun i ↦ continuous_coe_real_ereal.measurable.comp (measurable_pi_apply i)

private theorem continuous_project (I : Finset Γ) :
    Continuous (I.restrict (π := fun _ : Γ ↦ EReal)) :=
  continuous_pi fun i ↦ continuous_apply (i : Γ)

/-- Countable real projective extension, by compactifying each coordinate and applying the
finite intersection property to the closed conditions prescribing the finite marginals. -/
theorem exists_real_projective_limit [Countable Γ] (P : (I : Finset Γ) → Measure (I → ℝ))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : Γ ↦ ℝ) P) :
    ∃ μ : Measure (Γ → ℝ), IsProjectiveLimit (α := fun _ : Γ ↦ ℝ) μ P := by
  classical
  let prob (I : Finset Γ) : ProbabilityMeasure (I → ℝ) := ⟨P I, inferInstance⟩
  let fiber (I : Finset Γ) : Set (ProbabilityMeasure (Γ → EReal)) :=
    {μ | μ.map (I.restrict (π := fun _ ↦ EReal)) = (prob I).map (compactify I)}
  have hclosed (I : Finset Γ) : IsClosed (fiber I) :=
    isClosed_eq (ProbabilityMeasure.continuous_map (continuous_project I)) continuous_const
  have hfinite (D : Finset (Finset Γ)) : (⋂ I ∈ D, fiber I).Nonempty := by
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
  let recover (x : Γ → EReal) (i : Γ) : ℝ := (x i).toReal
  have hrecover : Measurable recover :=
    Measurable.of_eval fun i ↦ measurable_ereal_toReal.comp (measurable_pi_apply i)
  refine ⟨(ν : Measure (Γ → EReal)).map recover, ?_⟩
  intro I
  let recoverI (x : I → EReal) (i : I) : ℝ := (x i).toReal
  have hrecoverI : Measurable recoverI :=
    Measurable.of_eval fun i ↦ measurable_ereal_toReal.comp (measurable_pi_apply i)
  have hνI := mem_iInter.mp hν I
  have hνI' := congrArg (fun p : ProbabilityMeasure (I → EReal) ↦ (p : Measure (I → EReal))) hνI
  change (ν : Measure (Γ → EReal)).map (I.restrict (π := fun _ ↦ EReal)) =
    (P I).map (compactify I) at hνI'
  rw [Measure.map_map I.measurable_restrict hrecover,
    show I.restrict (π := fun _ ↦ ℝ) ∘ recover =
      recoverI ∘ I.restrict (π := fun _ ↦ EReal) from rfl,
    ← Measure.map_map hrecoverI (continuous_project I).measurable, hνI',
    Measure.map_map hrecoverI (measurable_compactify I)]
  rw [show recoverI ∘ compactify I = id by funext x i; simp [recoverI, compactify], Measure.map_id]

/-- The centered Gaussian law on a finite set of times, in product coordinates. -/
def finiteGaussianFamily (c : Γ → Γ → ℝ) (I : Finset Γ) : Measure (I → ℝ) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ I)
    (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))).map
      (MeasurableEquiv.toLp 2 (I → ℝ)).symm

instance finiteGaussianFamily_isProbability (c : Γ → Γ → ℝ) (I : Finset Γ) :
    IsProbabilityMeasure (finiteGaussianFamily c I) := by
  unfold finiteGaussianFamily
  infer_instance

private theorem preserving_ofLp (c : Γ → Γ → ℝ) (I : Finset Γ) :
    MeasurePreserving ofLp
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))) (finiteGaussianFamily c I) where
  measurable := by fun_prop
  map_eq := rfl

theorem preserving_toLp (c : Γ → Γ → ℝ) (I : Finset Γ) :
    MeasurePreserving (toLp 2) (finiteGaussianFamily c I)
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))) where
  measurable := by fun_prop
  map_eq := by
    rw [finiteGaussianFamily, Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

theorem finiteGaussianFamily_projective (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    IsProjectiveMeasureFamily (α := fun _ : Γ ↦ ℝ) (finiteGaussianFamily c) := by
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
      (Matrix.of fun i j : J ↦ c (i : Γ) (j : Γ))) at hr
    exact ((preserving_ofLp c J).comp hr).map_eq
  · exact Finset.measurable_restrict₂ _
  · fun_prop


/-- Taking any list of coordinates preserves Gaussianity and reindexes the covariance.
    The coordinate map need not be injective. -/
theorem euclideanGaussian_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (k : ι → κ)
    (hk : ∀ i j, B (k i) (k j) = A i j) :
    MeasurePreserving (fun x : EuclideanSpace ℝ κ ↦ toLp 2 (fun i ↦ x (k i)))
      (multivariateGaussian (0 : EuclideanSpace ℝ κ) B)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) := by
  let g : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i ↦ EuclideanSpace.proj (k i))
  change MeasurePreserving g _ _
  refine ⟨g.continuous.measurable, ?_⟩
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian, map_zero]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have heval (i : ι) : (fun u ↦ ⟪(EuclideanSpace.basisFun ι ℝ).toBasis i, u⟫) ∘ g =
        fun u ↦ u (k i) := by ext; simp [PiLp.inner_apply, show ∀ x i, g x i = x (k i) from fun _ _ ↦ rfl]
    simp_rw [heval, covariance_eval_multivariateGaussian hB,
      covarianceBilin_multivariateGaussian hA]
    simpa using hk i j
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact g.continuous.measurable.aemeasurable
  · exact IsGaussian.memLp_two_id

/-- The unique countable path law with the prescribed finite centered Gaussian marginals. -/
def pathLaw [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    Measure (Γ → ℝ) :=
  Classical.choose (exists_real_projective_limit (finiteGaussianFamily c)
    (finiteGaussianFamily_projective c hc))

theorem pathLaw_projective [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    IsProjectiveLimit (α := fun _ : Γ ↦ ℝ) (pathLaw c hc) (finiteGaussianFamily c) :=
  Classical.choose_spec (exists_real_projective_limit (finiteGaussianFamily c)
    (finiteGaussianFamily_projective c hc))

instance pathLaw_isProbability [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    IsProbabilityMeasure (pathLaw c hc) := (pathLaw_projective c hc).isProbabilityMeasure

theorem kernel_posSemidef_tuple (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    {ι : Type*} [Fintype ι] (v : ι → Γ) :
    (Matrix.of fun i j ↦ c (v i) (v j)).PosSemidef := by
  classical
  let I := Finset.univ.image v
  let k : ι → I := fun i ↦ ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  exact (hc I).submatrix k

/-- Every finite list of evaluations has its centered Gaussian law, with repetitions allowed. -/
theorem pathLaw_tuple [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Γ) :
    MeasurePreserving (fun x : Γ → ℝ ↦ toLp 2 (fun i ↦ x (v i))) (pathLaw c hc)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (Matrix.of fun i j ↦ c (v i) (v j))) := by
  classical
  let I := Finset.univ.image v
  let k : ι → I := fun i ↦ ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  have hI : MeasurePreserving (I.restrict (π := fun _ : Γ ↦ ℝ)) (pathLaw c hc)
      (finiteGaussianFamily c I) := ⟨I.measurable_restrict, pathLaw_projective c hc I⟩
  let hr := euclideanGaussian_reindex (kernel_posSemidef_tuple c hc v) (hc I) k (fun _ _ ↦ rfl)
  exact hr.comp ((preserving_toLp c I).comp hI)

/-- A path law is determined by all its finite Gaussian marginals. -/
theorem pathLaw_unique [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (μ : Measure (Γ → ℝ)) (hμ : ∀ (I : Finset Γ),
      μ.map (fun x : Γ → ℝ ↦ toLp 2 (I.restrict x)) =
        multivariateGaussian (0 : EuclideanSpace ℝ I) (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))) :
    μ = pathLaw c hc := by
  apply IsProjectiveLimit.unique _ (pathLaw_projective c hc)
  intro I
  change μ.map (I.restrict (π := fun _ : Γ ↦ ℝ)) = finiteGaussianFamily c I
  rw [← (preserving_ofLp c I).map_eq, ← hμ I, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Every coordinate change preserving the covariance preserves the whole path law. -/
theorem pathLaw_invariant [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (q : Γ → Γ) (hq : ∀ i j, c (q i) (q j) = c i j) :
    MeasurePreserving (fun x : Γ → ℝ ↦ x ∘ q) (pathLaw c hc) (pathLaw c hc) := by
  have hm : Measurable (fun x : Γ → ℝ ↦ x ∘ q) :=
    Measurable.of_eval fun i ↦ measurable_pi_apply (q i)
  refine ⟨hm, pathLaw_unique c hc _ fun I ↦ ?_⟩
  have h := pathLaw_tuple c hc (fun i : I ↦ q i)
  rw [Measure.map_map (by fun_prop) hm]
  change (pathLaw c hc).map (fun x ↦ toLp 2 (fun i : I ↦ x (q i))) = _
  have hmat : (Matrix.of fun i j : I ↦ c (q i) (q j)) =
      (Matrix.of fun i j : I ↦ c i j) := Matrix.ext fun i j ↦ hq i j
  exact h.map_eq.trans (congrArg (multivariateGaussian (0 : EuclideanSpace ℝ I)) hmat)

/-- A coordinate has the usual real Gaussian law, even when its variance is zero. -/
theorem pathLaw_coordinate [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i : Γ) : MeasurePreserving (fun x : Γ → ℝ ↦ x i) (pathLaw c hc)
      (gaussianReal 0 (c i i).toNNReal) := by
  let a : Unit → Γ := fun _ ↦ i
  have h := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ Unit))
    (kernel_posSemidef_tuple c hc a) (i := ())).comp (pathLaw_tuple c hc a)
  simpa only [a, Function.comp_def, Matrix.of_apply, PiLp.zero_apply] using h

theorem pathLaw_coordinate_memLp [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i : Γ) : MemLp (fun x : Γ → ℝ ↦ x i) 2 (pathLaw c hc) :=
  (IsGaussian.memLp_two_id (μ := gaussianReal 0 (c i i).toNNReal)).comp_measurePreserving
    (pathLaw_coordinate c hc i)

theorem pathLaw_coordinate_mean [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i : Γ) : (∫ x, x i ∂(pathLaw c hc)) = 0 := by
  have h := pathLaw_coordinate c hc i
  rw [← integral_id_gaussianReal (μ := 0) (v := (c i i).toNNReal), ← h.map_eq]
  have hId : AEStronglyMeasurable (fun x : ℝ ↦ x)
      ((pathLaw c hc).map (fun x ↦ x i)) := aestronglyMeasurable_id
  exact (integral_map h.measurable.aemeasurable hId).symm

theorem pathLaw_covariance [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i j : Γ) : (∫ x, x i * x j ∂(pathLaw c hc)) = c i j := by
  let a : Bool → Γ := fun b ↦ if b then i else j
  have hI := pathLaw_tuple c hc a
  have he := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ Bool))
    (kernel_posSemidef_tuple c hc a) true false
  rw [← hI.map_eq, covariance_map] at he
  · simp only [Function.comp_def, a, Bool.false_eq_true, ite_false, ite_true, Matrix.of_apply] at he
    rw [covariance_eq_sub (pathLaw_coordinate_memLp c hc i) (pathLaw_coordinate_memLp c hc j),
      pathLaw_coordinate_mean c hc i, zero_mul, sub_zero] at he
    exact he
  on_goal 3 => exact hI.measurable.aemeasurable
  all_goals fun_prop

end

end SixProblems.Gaussian
