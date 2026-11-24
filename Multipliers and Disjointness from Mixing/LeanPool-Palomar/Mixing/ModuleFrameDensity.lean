/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.InvariantModuleFrames
public import Mixing.RelativeFrameMultiplierTowers

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate InnerProductSpace ProbabilityTheory

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable {E : System G X} {B : System G Y}

private theorem nonempty_factor_source (_ : FactorMap E B) : Nonempty X :=
  nonempty_of_isProbabilityMeasure E.measure

set_option maxHeartbeats 1600000 in
/-- A global L² vector lying in the span of an orthonormal relative frame
on almost every fibre belongs to the closed global span of its bounded
base multipliers. -/
theorem FactorMap.mem_relativeFrameClosure_of_fibre_span
    {π : FactorMap E B} {n : ℕ} (A : RelativeFiniteFrame π n) {κ : Kernel Y X}
    (hκ : κ ∘ₘ B.measure = E.measure)
    (hFibre : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    (hOrtho : FibreOrthonormal κ B.measure A.vector)
    (v : Lp ℂ 2 E.measure)
    (hSpan : ∀ᵐ y ∂B.measure, ∃ (hA : ∀ j, MemLp (A.vector j) 2 (κ y)) (hv : MemLp v 2 (κ y)),
      hv.toLp v ∈ Submodule.span ℂ (range fun j => (hA j).toLp (A.vector j))) :
    v ∈ (Submodule.span ℂ π.relativeFrameGenerators).topologicalClosure := by
  let c (j : Fin n) (y : Y) := ∫ x, conj (A.vector j x) * v x ∂κ y
  have hC (j : Fin n) : Measurable (c j) := by
    have hm : Measurable (fun x : X => conj (A.vector j x) * v x) :=
      (Complex.continuous_conj.measurable.comp (Lp.stronglyMeasurable (A.vector j)).measurable).mul
        (Lp.stronglyMeasurable v).measurable
    exact (hm.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  let w (j : Fin n) (x : X) := c j (π.toFun x) * A.vector j x
  have hW (j : Fin n) : Measurable (w j) :=
    ((hC j).comp π.preserves.measurable).mul (Lp.stronglyMeasurable (A.vector j)).measurable
  have hLocal : ∀ᵐ y ∂B.measure,
      (∀ j, Integrable (fun x => ‖w j x‖ ^ 2) (κ y) ∧
        (∫ x, ‖w j x‖ ^ 2 ∂κ y) ≤ ∫ x, ‖v x‖ ^ 2 ∂κ y) ∧
      ∀ᵐ x ∂κ y, v x = ∑ j, w j x := by
    filter_upwards [hOrtho, hSpan, hFibre] with y hy hS hF
    obtain ⟨h, hNorm, hOrth⟩ := hy
    obtain ⟨_, hv, hIn⟩ := hS
    let u j := (h j).toLp (A.vector j)
    let z := hv.toLp v
    have hCeq (j : Fin n) : inner ℂ (u j) z = c j y := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(h j).coeFn_toLp, hv.coeFn_toLp] with x hx hx'
      change u j x = A.vector j x at hx
      change z x = v x at hx'
      rw [hx, hx', RCLike.inner_apply']
    refine ⟨?_, ?_⟩
    · intro j
      let p := c j y • u j
      have hp : p =ᵐ[κ y] w j := by
        filter_upwards [Lp.coeFn_smul (c j y) (u j), (h j).coeFn_toLp, hF] with x hx hu hπ
        change p x = _ at hx
        change u j x = A.vector j x at hu
        rw [hx, Pi.smul_apply, hu, smul_eq_mul]
        simp only [w, hπ]
      have hMem := MemLp.ae_eq hp (Lp.memLp p)
      refine ⟨(memLp_two_iff_integrable_sq_norm (hW j).aestronglyMeasurable).mp hMem, ?_⟩
      have hNormLe : ‖u j‖ ≤ 1 := by
        rcases hNorm j with hZero | hOne
        · rw [show u j = 0 from hZero, norm_zero]
          exact zero_le_one
        · exact hOne.le
      have hpNorm : ‖p‖ ≤ ‖z‖ := by
        change ‖c j y • u j‖ ≤ ‖z‖
        rw [norm_smul, ← hCeq]
        calc
          _ ≤ (‖u j‖ * ‖z‖) * ‖u j‖ :=
            mul_le_mul_of_nonneg_right (norm_inner_le_norm (u j) z) (norm_nonneg _)
          _ ≤ ‖z‖ := by
            exact (mul_le_mul (mul_le_mul_of_nonneg_right hNormLe (norm_nonneg _)) hNormLe
              (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg _))).trans_eq (by simp)
      calc
        _ = ‖p‖ ^ 2 :=
          (integral_congr_ae (hp.symm.mono fun x hx => by rw [hx])).trans
            (lp_two_norm_sq_eq_integral p).symm
        _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpNorm _
        _ = _ := (lp_two_norm_sq_eq_integral z).trans
          (integral_congr_ae (hv.coeFn_toLp.mono fun x hx => by
            change z x = v x at hx
            change ‖z x‖ ^ 2 = ‖v x‖ ^ 2
            rw [hx]))
    · have hExp : (∑ j, c j y • u j) = z := by
        simpa only [hCeq] using sum_inner_smul_eq_of_mem_span u hNorm hOrth (w := z) hIn
      have he := ae_coe_toLp_sum_smul h (fun j => c j y)
      change (∑ j, c j y • u j) =ᵐ[κ y] _ at he
      rw [hExp] at he
      filter_upwards [he, hv.coeFn_toLp, hF] with x hx hvx hπ
      change z x = (∑ j, c j y * A.vector j x) at hx
      change z x = v x at hvx
      rw [← hvx, hx]
      simp only [w, hπ]
  have hMem (j : Fin n) : MemLp (w j) 2 E.measure := by
    have hvInt : Integrable (fun x => ‖v x‖ ^ 2) E.measure :=
      (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable v).aestronglyMeasurable).mp (Lp.memLp v)
    have hvK : Integrable (fun x => ‖v x‖ ^ 2) (κ ∘ₘ B.measure) :=
      (congrArg (fun μ => Integrable (fun x => ‖v x‖ ^ 2) μ) hκ).mpr hvInt
    have hI : Integrable (fun x => ‖w j x‖ ^ 2) (κ ∘ₘ B.measure) := by
      apply (Measure.integrable_comp_iff ((hW j).norm.pow_const _).aestronglyMeasurable).mpr
      refine ⟨hLocal.mono (fun _ hy => (hy.1 j).1), ?_⟩
      apply ((Measure.integrable_comp_iff hvK.1).mp hvK).2.mono
        (((hW j).norm.pow_const _).norm.stronglyMeasurable.integral_kernel (κ := κ)).aestronglyMeasurable
      filter_upwards [hLocal] with y hy
      have hVnonneg : 0 ≤ ∫ x, ‖‖v x‖ ^ 2‖ ∂κ y := integral_nonneg fun _ => norm_nonneg _
      have hWnonneg : 0 ≤ ∫ x, ‖‖w j x‖ ^ 2‖ ∂κ y := integral_nonneg fun _ => norm_nonneg _
      have hSqNorm (r : ℝ) : ‖r ^ 2‖ = r ^ 2 := Real.norm_of_nonneg (sq_nonneg r)
      rw [Real.norm_of_nonneg hVnonneg, Real.norm_of_nonneg hWnonneg]
      simpa only [hSqNorm] using (hy.1 j).2
    exact (memLp_two_iff_integrable_sq_norm (hW j).aestronglyMeasurable).mpr
      ((congrArg (fun μ => Integrable (fun x => ‖w j x‖ ^ 2) μ) hκ).mp hI)
  let W (j : Fin n) := (hMem j).toLp (w j)
  have hSum : (∑ j, W j) = v := by
    have he : v =ᵐ[E.measure] fun x => ∑ j, w j x := by
      rw [← congrArg ae hκ]
      exact Measure.ae_comp_of_ae_ae
        (measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable
          (Finset.measurable_fun_sum _ fun j _ => hW j)) (hLocal.mono fun _ hy => hy.2)
    apply Lp.ext
    refine (Lp.coeFn_finsetSum _ W).trans ?_
    filter_upwards [ae_all_iff.mpr (fun j => (hMem j).coeFn_toLp), he] with x hx hvx
    rw [Finset.sum_apply, hvx]
    exact Finset.sum_congr rfl (fun j _ => hx j)
  rw [← hSum]
  exact Submodule.sum_mem _ (fun j _ => FactorMap.mem_relativeFrameClosure_of_measurable_coefficient
    A j (c j) (hC j) (W j) (hMem j).coeFn_toLp)

/-- The generators of the finite invariant modules over the bounded base
observables, including their products with bounded base observables. -/
def FactorMap.finiteModuleGenerators (π : FactorMap E B) : Set (Lp ℂ 2 E.measure) :=
  {v | ∃ (n : ℕ) (M : FiniteInvariantBaseModule π n) (i : Fin n) (b : BoundedObservable Y),
    v = (b.comp π.toFun π.preserves.measurable).mulL2 E.measure (M.vector i)}

set_option maxHeartbeats 1400000 in
/-- The dense invariant finite-module condition implies the concrete dense
relative-frame condition. The bridge uses the canonical factor kernel,
conditional Gram–Schmidt, and truncation of measurable coefficients. -/
theorem FactorMap.hasDenseRelativeFrames_of_finiteModuleGenerators
    [StandardBorelSpace X] [Nonempty X] [MeasurableEq Y]
    (π : FactorMap E B)
    (hDensity : Dense (Submodule.span ℂ π.finiteModuleGenerators : Set (Lp ℂ 2 E.measure))) :
    π.HasDenseRelativeFrames := by
  let C := (Submodule.span ℂ π.relativeFrameGenerators).topologicalClosure
  have hC : IsClosed (C : Set (Lp ℂ 2 E.measure)) :=
    (Submodule.span ℂ _).isClosed_topologicalClosure
  have hSpan : Submodule.span ℂ π.finiteModuleGenerators ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, M, i, b, rfl⟩
    let κ := π.conditionalKernel
    have hEq (g : G) : ∀ᵐ y ∂B.measure, MeasurePreserving (E.act g) (κ y) (κ (B.act g y)) := by
      filter_upwards [π.ae_conditionalKernel_equivariant g] with y hy
      exact ⟨(E.preserves g).measurable, hy⟩
    obtain ⟨Q, hQSpan⟩ := M.exists_conditionalOrthogonalFrame κ π.comp_conditionalKernel
      π.ae_conditionalKernel_fibre hEq
    obtain ⟨A, hA⟩ := Q.exists_relativeFiniteFrame_of_factor
    have hOrtho : FibreOrthonormal κ B.measure A.vector := hA.symm ▸ Q.fibre
    have hASpan : FibreSpanEq κ B.measure A.vector M.vector := hA.symm ▸ hQSpan
    let v := (b.comp π.toFun π.preserves.measurable).mulL2 E.measure (M.vector i)
    have hvAE := (b.comp π.toFun π.preserves.measurable).ae_mulL2 (M.vector i)
    rw [← congrArg ae π.comp_conditionalKernel] at hvAE
    have hLocal : ∀ᵐ y ∂B.measure, ∃ (hU : ∀ j, MemLp (A.vector j) 2 (κ y))
        (hv : MemLp v 2 (κ y)),
        hv.toLp v ∈ Submodule.span ℂ (range fun j => (hU j).toLp (A.vector j)) := by
      filter_upwards [hASpan, ae_memLp_two_of_kernel_average π.comp_conditionalKernel v,
        Measure.ae_ae_of_ae_comp hvAE, π.ae_conditionalKernel_fibre] with y hy hv hEqv hF
      obtain ⟨hU, hM, hSpanEq⟩ := hy
      have he : hv.toLp v = b y • (hM i).toLp (M.vector i) := by
        apply Lp.ext
        filter_upwards [hv.coeFn_toLp, (hM i).coeFn_toLp, hEqv, hF,
          Lp.coeFn_smul (b y) ((hM i).toLp (M.vector i))] with x hx hvx hEx hFx hSm
        change v x = b (π.toFun x) * M.vector i x at hEx
        rw [hx, hSm, Pi.smul_apply, hvx, hEx, hFx, smul_eq_mul]
      refine ⟨hU, hv, ?_⟩
      rw [he, hSpanEq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact FactorMap.mem_relativeFrameClosure_of_fibre_span A π.comp_conditionalKernel
      π.ae_conditionalKernel_fibre hOrtho v hLocal
  have hIncl := closure_minimal hSpan hC
  rw [hDensity.closure_eq] at hIncl
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (top_unique (fun v _ => hIncl (mem_univ v)))

section IsometricExtension

variable {Z : Type*} [MeasurableSpace Z] [Countable G]

/-- Lemma 2 in the invariant finite L∞ module formulation of an isometric
extension. No ergodicity assumption on the base or extension is needed. -/
theorem lemma2_of_dense_finiteModules [StandardBorelSpace X] [MeasurableEq Y]
    {R : System G Z} (π : FactorMap E B)
    (hDense : Dense (Submodule.span ℂ π.finiteModuleGenerators : Set (Lp ℂ 2 E.measure)))
    (hWeak : IsWeaklyMixing R.koopmanZeroRep) (hDisjoint : Disjoint R B) : Disjoint R E := by
  let := nonempty_of_isProbabilityMeasure E.measure
  exact π.disjoint_of_weakMixing_of_dense_relativeFrames
    (π.hasDenseRelativeFrames_of_finiteModuleGenerators hDense) hDisjoint hWeak

/-- Theorem 2.1 in the invariant finite L∞ module formulation of an
isometric extension of the second ergodic system. -/
theorem theorem2_1_of_dense_finiteModules [StandardBorelSpace X] [MeasurableEq Y]
    {R : System G Z} (π : FactorMap E B) (_hR : R.IsErgodic) (_hB : B.IsErgodic)
    (hDense : Dense (Submodule.span ℂ π.finiteModuleGenerators : Set (Lp ℂ 2 E.measure)))
    (hWeak : IsWeaklyMixing R.koopmanZeroRep) (hDisjoint : Disjoint R B) : Disjoint R E :=
  lemma2_of_dense_finiteModules π hDense hWeak hDisjoint

/-- Corollary 2(i) for isometric extensions given by dense finite invariant
base modules. -/
theorem corollary2_i_of_dense_finiteModules [StandardBorelSpace X] [MeasurableEq Y]
    (C : Set (System G Z)) (π : FactorMap E B)
    (hDense : Dense (Submodule.span ℂ π.finiteModuleGenerators : Set (Lp ℂ 2 E.measure)))
    (hWeak : ∀ R ∈ C, IsWeaklyMixing R.koopmanZeroRep)
    (hDis : ∀ R ∈ C, Disjoint B R) : ∀ R ∈ C, Disjoint E R :=
  fun R hR => (lemma2_of_dense_finiteModules π hDense (hWeak R hR) (hDis R hR).symm).symm

end IsometricExtension

section Multipliers

universe u

variable {U V W : Type u} [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace W]
variable [Countable G]

/-- A simultaneous individual multiplier conclusion for a class of weakly
mixing systems. -/
theorem corollary2_ii_pointwise_of_dense_finiteModules [StandardBorelSpace U] [MeasurableEq V]
    {T : System G U} {S : System G V} (C : Set (System G W)) (π : FactorMap T S)
    (hDense : Dense (Submodule.span ℂ π.finiteModuleGenerators : Set (Lp ℂ 2 T.measure)))
    (hWeak : ∀ R ∈ C, IsWeaklyMixing R.koopmanZeroRep)
    (hMul : ∀ R ∈ C, S.IsMultiplierAgainst R) : ∀ R ∈ C, T.IsMultiplierAgainst R := by
  let := nonempty_of_isProbabilityMeasure T.measure
  intro R hR
  exact π.isMultiplierAgainst_of_dense_relativeFrames
    (π.hasDenseRelativeFrames_of_finiteModuleGenerators hDense) (hMul R hR) (hWeak R hR)

/-- Membership in the multiplier class of the disjoint complement of C. -/
def System.IsMultiplierForDisjointClass (T : System G U) (C : Set (System G W)) : Prop :=
  ∀ (Y : Type u) [MeasurableSpace Y] (S : System G Y), (∀ R ∈ C, Disjoint S R) →
    ∀ (σ : Measure (U × Y)) (hσ : IsJoining T S σ), ∀ R ∈ C, Disjoint hσ.system R

/-- Corollary 2(ii) in its class-level formulation. A single projected
joining is disjoint from every element of the class, so the relative
finite-frame disjointness theorem applies to each element. -/
theorem corollary2_ii_of_dense_finiteModules [StandardBorelSpace U] [MeasurableEq V]
    {T : System G U} {S : System G V} (C : Set (System G W)) (π : FactorMap T S)
    (hDense : Dense (Submodule.span ℂ π.finiteModuleGenerators : Set (Lp ℂ 2 T.measure)))
    (hWeak : ∀ R ∈ C, IsWeaklyMixing R.koopmanZeroRep)
    (hMul : S.IsMultiplierForDisjointClass C) : T.IsMultiplierForDisjointClass C := by
  let := nonempty_of_isProbabilityMeasure T.measure
  intro Y _ Ysys hDis σ hσ R hR
  let π' := π.joiningLeft hσ
  let σ' := hσ.map π (FactorMap.identity Ysys)
  have hB : Disjoint σ'.system R := hMul Y Ysys hDis _ σ' R hR
  have hFrames := π.hasDenseRelativeFrames_joiningLeft
    (π.hasDenseRelativeFrames_of_finiteModuleGenerators hDense) hσ
  exact (π'.disjoint_of_weakMixing_of_dense_relativeFrames hFrames hB.symm (hWeak R hR)).symm

/-- A distal tower given by one-point, finite-module successor, and
L²-spanning factor limit data. -/
inductive InvariantModuleTower (G : Type*) [CommGroup G] :
    {X : Type u} → [m : MeasurableSpace X] → @System G X _ m → Prop
  | point {X : Type u} [MeasurableSpace X] (T : System G X) (hX : Subsingleton X) :
      InvariantModuleTower G T
  | step {X X' : Type u} [MeasurableSpace X] [MeasurableSpace X']
      [StandardBorelSpace X] [MeasurableEq X']
      {T : System G X} {S : System G X'} (π : FactorMap T S)
      (hBase : InvariantModuleTower G S)
      (hModules : Dense (Submodule.span ℂ π.finiteModuleGenerators : Set (Lp ℂ 2 T.measure))) :
      InvariantModuleTower G T
  | limit {I : Type u} {X : Type u} [MeasurableSpace X]
      {V : I → Type u} [∀ i, MeasurableSpace (V i)]
      {T : System G X} {S : ∀ i, System G (V i)} (π : ∀ i, FactorMap T (S i))
      (hDense : DenseFactorPullbacks π) (hFactors : ∀ i, InvariantModuleTower G (S i)) :
      InvariantModuleTower G T

omit [Countable G] in
/-- Convert a tower in the invariant finite-module formulation to the
relative frame formulation. -/
theorem InvariantModuleTower.toRelativeFrameTower {T : System G U}
    (h : InvariantModuleTower G T) : RelativeFrameTower G T := by
  induction h with
  | point T hX => exact .point T hX
  | step π _ hModules ih =>
    let := nonempty_factor_source π
    exact .step π ih (π.hasDenseRelativeFrames_of_finiteModuleGenerators hModules)
  | limit π hDense _ ih => exact .limit π hDense ih

/-- The simultaneous individual multiplier conclusion for a distal tower. -/
theorem corollary2_iii_pointwise_of_invariantModuleTower
    {T : System G U} (h : InvariantModuleTower G T) (C : Set (System G W))
    (hWeak : ∀ R ∈ C, IsWeaklyMixing R.koopmanZeroRep) :
    ∀ R ∈ C, T.IsMultiplierAgainst R :=
  fun R hR => h.toRelativeFrameTower.isMultiplierAgainst R (hWeak R hR)

/-- Corollary 2(iii) for distal towers given by their invariant finite-module
successor and spanning inverse-limit data. -/
theorem corollary2_iii_of_invariantModuleTower
    {T : System G U} (h : InvariantModuleTower G T) (C : Set (System G W))
    (hWeak : ∀ R ∈ C, IsWeaklyMixing R.koopmanZeroRep) :
    T.IsMultiplierForDisjointClass C :=
  fun Y _ S hDis σ hσ R hR =>
    corollary2_iii_pointwise_of_invariantModuleTower h C hWeak R hR Y S (hDis R hR) σ hσ

end Multipliers

end Mixing
