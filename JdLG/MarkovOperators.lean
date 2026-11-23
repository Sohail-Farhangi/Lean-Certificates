/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MarkovSimple

/-! # Markov semigroups on probability L¹ -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace JdLG

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The inclusion acts on simple functions by keeping the same representative. -/
theorem probabilityLpInclusion_simpleFunctionLp
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (f : SimpleFunc X ℂ) :
    probabilityLpInclusion (𝕜 := ℂ) μ hpq (simpleFunctionLp μ q f) = simpleFunctionLp μ p f := by
  apply Lp.ext
  rw [probabilityLpInclusion_coeFn]
  exact (simpleFunctionLp_coeFn μ q f).trans (simpleFunctionLp_coeFn μ p f).symm

variable {μ}

/-- A Markov operator on probability L¹ is contractive. -/
theorem IsProbabilityMarkovOperator.norm_le_one
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T) :
    ‖T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  refine (Lp.simpleFunc.denseRange (E := ℂ) (μ := μ) (p := 1) (by simp)).induction_on
    (p := fun y ↦ ‖T y‖ ≤ ‖y‖) x (isClosed_le T.continuous.norm continuous_norm) ?_
  intro g
  let f := Lp.simpleFunc.toSimpleFunc g
  have hg : simpleFunctionLp μ 1 f = (g : Lp ℂ 1 μ) := by
    apply Lp.ext
    exact (simpleFunctionLp_coeFn μ 1 f).trans (Lp.simpleFunc.toSimpleFunc_eq_toFun g)
  change ‖T (g : Lp ℂ 1 μ)‖ ≤ ‖(g : Lp ℂ 1 μ)‖
  rw [← hg, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  have h := (hT.integral_norm_pow_le f 1).2
  simp only [pow_one] at h
  exact h.trans_eq (integral_congr_ae ((simpleFunctionLp_coeFn μ 1 f).mono
    fun _ hx ↦ congrArg norm hx)).symm

omit [IsProbabilityMeasure μ] in
private theorem lpTwo_norm_sq_eq_integral (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = RCLike.re (∫ x, inner ℂ (f x) (f x) ∂μ) :=
      congrArg RCLike.re (L2.inner_def f f)
    _ = ∫ x, RCLike.re (inner ℂ (f x) (f x)) ∂μ :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
      simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

private theorem IsProbabilityMarkovOperator.simpleFunction_liftLpTwo
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T)
    (f : Lp.simpleFunc ℂ 2 μ) :
    ∃ y : Lp ℂ 2 μ, probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) y =
        T (probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (f : Lp ℂ 2 μ)) ∧
      ‖y‖ ≤ ‖(f : Lp ℂ 2 μ)‖ := by
  let j := probabilityLpInclusion (𝕜 := ℂ) (E := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let g := Lp.simpleFunc.toSimpleFunc f
  have hf : simpleFunctionLp μ 2 g = (f : Lp ℂ 2 μ) := by
    apply Lp.ext
    exact (simpleFunctionLp_coeFn μ 2 g).trans (Lp.simpleFunc.toSimpleFunc_eq_toFun f)
  have hg1 : j (f : Lp ℂ 2 μ) = simpleFunctionLp μ 1 g := by
    rw [← hf]
    exact probabilityLpInclusion_simpleFunctionLp μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) g
  let u := T (simpleFunctionLp μ 1 g)
  have h := hT.integral_norm_pow_le g 2
  have hu : MemLp (⇑u : X → ℂ) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).2 h.1
  let y := hu.toLp (⇑u : X → ℂ)
  have hcoe : (y : X → ℂ) =ᵐ[μ] u := hu.coeFn_toLp
  have hjy : j y = u := by
    apply Lp.ext
    exact hcoe
  refine ⟨y, ?_, ?_⟩
  · change j y = T (j (f : Lp ℂ 2 μ))
    rw [hjy, hg1]
  · apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
    rw [lpTwo_norm_sq_eq_integral, lpTwo_norm_sq_eq_integral]
    calc
      _ = ∫ x, ‖u x‖ ^ 2 ∂μ :=
        integral_congr_ae (hcoe.mono fun x hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx)
      _ ≤ ∫ x, ‖g x‖ ^ 2 ∂μ := h.2
      _ = _ := integral_congr_ae ((Lp.simpleFunc.toSimpleFunc_eq_toFun f).mono
        fun x hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx)

attribute [local instance] Lp.simpleFunc.module Lp.simpleFunc.isBoundedSMul
  Lp.simpleFunc.normedSpace

/-- The L² restriction of a Markov operator is a Hilbert-space contraction.
It is constructed from the bounded lift on the dense subspace of simple functions. -/
theorem IsProbabilityMarkovOperator.exists_lpTwoLift
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T) :
    ∃ A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, ‖A‖ ≤ 1 ∧
      ∀ x, probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (A x) =
        T (probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) x) := by
  let j := probabilityLpInclusion (𝕜 := ℂ) (E := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hji := probabilityLpInclusion_injective (E := ℂ) (𝕜 := ℂ) μ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let e : Lp.simpleFunc ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have he : DenseRange e := Lp.simpleFunc.denseRange (by simp)
  choose a ha hanorm using hT.simpleFunction_liftLpTwo
  have ha' (x : Lp.simpleFunc ℂ 2 μ) : j (a x) = T (j (e x)) := ha x
  let B : Lp.simpleFunc ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := a
      map_add' := fun x y ↦ hji (by
        change j (a (x + y)) = j (a x + a y)
        rw [ha', map_add j, ha' x, ha' y, map_add e, map_add j, map_add T])
      map_smul' := fun c x ↦ hji (by
        change j (a (c • x)) = j (c • a x)
        rw [ha', map_smul j, ha' x, map_smul e, map_smul j, map_smul T]) }
  have hB (x : Lp.simpleFunc ℂ 2 μ) : ‖B x‖ ≤ 1 * ‖e x‖ := by
    change ‖a x‖ ≤ 1 * ‖(x : Lp ℂ 2 μ)‖
    simpa only [one_mul] using hanorm x
  let A := B.extendOfNorm e
  have hA : ‖A‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le he zero_le_one hB
  refine ⟨A, hA, fun x ↦ ?_⟩
  have hEq : (fun z ↦ j (A z)) = fun z ↦ T (j z) :=
    he.equalizer (j.continuous.comp A.continuous) (T.continuous.comp j.continuous) (by
      funext z
      change j (A (e z)) = T (j (e z))
      rw [LinearMap.extendOfNorm_eq he ⟨1, hB⟩]
      exact ha' z)
  exact congrFun hEq x

/-- The bounded L² restriction of a Markov operator. -/
noncomputable def IsProbabilityMarkovOperator.lpTwoLift
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := hT.exists_lpTwoLift.choose

theorem IsProbabilityMarkovOperator.norm_lpTwoLift_le_one
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T) :
    ‖hT.lpTwoLift‖ ≤ 1 := hT.exists_lpTwoLift.choose_spec.1

theorem IsProbabilityMarkovOperator.lpTwoLift_intertwines
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T) (x : Lp ℂ 2 μ) :
    probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hT.lpTwoLift x) =
      T (probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) x) :=
  hT.exists_lpTwoLift.choose_spec.2 x

/-- Theorem 1.2(iii). A nonempty semigroup of Markov operators on complex L¹
of a probability space is JdLG-admissible for the weak operator topology. -/
theorem admissible_probabilityMarkov {S : Type*} [Semigroup S] [Nonempty S]
    (π : S →ₙ* (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ))
    (hπ : ∀ s, IsProbabilityMarkovOperator μ (π s)) :
    IsJdLGAdmissible π := by
  let j := probabilityLpInclusion (𝕜 := ℂ) (E := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hji := probabilityLpInclusion_injective (E := ℂ) (𝕜 := ℂ) μ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let σ : S →ₙ* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
    { toFun := fun s ↦ (hπ s).lpTwoLift
      map_mul' := fun a b ↦ by
        apply ContinuousLinearMap.ext
        intro x
        apply hji
        change j ((hπ (a * b)).lpTwoLift x) = j ((hπ a).lpTwoLift ((hπ b).lpTwoLift x))
        simp only [IsProbabilityMarkovOperator.lpTwoLift_intertwines, j, map_mul,
          mul_apply_eq_comp] }
  exact admissible_probabilityLpOne_of_lpTwo_contractions π σ
    (fun s x ↦ ((hπ s).lpTwoLift_intertwines x).symm) zero_le_one
    (fun s ↦ (hπ s).norm_le_one) (fun s ↦ (hπ s).norm_lpTwoLift_le_one)

end JdLG
