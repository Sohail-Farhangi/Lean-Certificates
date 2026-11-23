/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.HilbertCompactness
public import JdLG.PaperExamplesWapClosed
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Monothetic Dunford–Schwartz actions on finite-measure L¹ -/

@[expose] public section

namespace JdLG

open Filter MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The inclusion of complex L² into complex L¹ on a finite measure space. -/
noncomputable def finiteLpTwoToOne (μ : Measure X) [IsFiniteMeasure μ] :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ⟨f.1, Lp.antitone (by norm_num : (1 : ℝ≥0∞) ≤ 2) f.2⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
    (μ univ ^ (1 / 2 : ℝ)).toReal (fun f ↦ by
      let r : ℝ≥0∞ := μ univ ^ (1 / 2 : ℝ)
      have hr : r ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
      have hf := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.aestronglyMeasurable f)
      have hb : eLpNorm (⇑f) 1 μ ≤ eLpNorm (⇑f) 2 μ * r := by
        convert hf using 2
        norm_num [r]
      change (eLpNorm (⇑f) 1 μ).toReal ≤ r.toReal * (eLpNorm (⇑f) 2 μ).toReal
      simpa only [ENNReal.toReal_mul, mul_comm] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hr) hb)

theorem finiteLpTwoToOne_coeFn (f : Lp ℂ 2 μ) :
    (finiteLpTwoToOne μ f : X → ℂ) = f := rfl

/-- The weak closure of the essentially bounded L¹ ball is compact. -/
theorem isCompact_weakClosure_essBound (C : ℝ) :
    IsCompact (closure (toWeakSpace ℂ (Lp ℂ 1 μ) ''
      {f : Lp ℂ 1 μ | ∀ᵐ x ∂μ, ‖f x‖ ≤ C})) := by
  let I := finiteLpTwoToOne μ
  let weakI := fun w : WeakSpace ℂ (Lp ℂ 2 μ) ↦
    toWeakSpace ℂ (Lp ℂ 1 μ) (I ((toWeakSpace ℂ (Lp ℂ 2 μ)).symm w))
  have hcont : Continuous weakI := by
    apply WeakBilin.continuous_of_continuous_eval
    intro φ
    exact WeakBilin.eval_continuous (topDualPairing ℂ (Lp ℂ 2 μ)).flip (φ.comp I)
  let R : ℝ≥0∞ := μ univ ^ (1 / 2 : ℝ) * ENNReal.ofReal C
  have hR : R ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _))
      ENNReal.ofReal_ne_top
  have hc := (isCompact_weakHilbert_ball (E := Lp ℂ 2 μ) R.toReal).image hcont
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨f, hf, rfl⟩
  let hmem : MemLp (⇑f) 2 μ := MemLp.of_bound (Lp.aestronglyMeasurable f) C hf
  let g := hmem.toLp (⇑f)
  refine ⟨toWeakSpace ℂ (Lp ℂ 2 μ) g, ?_, ?_⟩
  · change ‖(toWeakSpace ℂ (Lp ℂ 2 μ)).symm (toWeakSpace ℂ (Lp ℂ 2 μ) g)‖ ≤ R.toReal
    rw [LinearEquiv.symm_apply_apply, Lp.norm_def, eLpNorm_congr_ae hmem.coeFn_toLp]
    apply ENNReal.toReal_mono hR
    simpa only [R, ENNReal.toReal_ofNat, one_div] using
      eLpNorm_le_of_ae_bound (p := 2) (Lp.aestronglyMeasurable f) hf
  · change toWeakSpace ℂ (Lp ℂ 1 μ)
      (I ((toWeakSpace ℂ (Lp ℂ 2 μ)).symm (toWeakSpace ℂ (Lp ℂ 2 μ) g))) = _
    rw [LinearEquiv.symm_apply_apply]
    congr 1
    apply Lp.ext
    rw [finiteLpTwoToOne_coeFn]
    exact hmem.coeFn_toLp

/-- The semigroup representation given by all nonnegative powers of one operator. -/
noncomputable def monotheticLpOne (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) :
    Multiplicative ℕ →ₙ* (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) where
  toFun n := T ^ n.toAdd
  map_mul' m n := pow_add _ m.toAdd n.toAdd

omit [IsFiniteMeasure μ] in
theorem norm_monotheticLpOne_le_one (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (hT : ‖T‖ ≤ 1)
    (n : Multiplicative ℕ) : ‖monotheticLpOne T n‖ ≤ 1 := by
  change ‖T ^ n.toAdd‖ ≤ 1
  let m := n.toAdd
  change ‖T ^ m‖ ≤ 1
  induction m with
  | zero =>
    rw [pow_zero]
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Lp ℂ 1 μ)
  | succ m ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_right ih (norm_nonneg T)).trans (by simpa using hT))

/-- The Dunford–Schwartz branch of the monothetic L¹ example following Theorem 1.2.
The L∞ contraction hypothesis is stated using preservation of every essential bound. -/
theorem admissible_monotheticLpOne_of_dunfordSchwartz
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (hT : ‖T‖ ≤ 1)
    (hbound : ∀ (f : Lp ℂ 1 μ) (C : ℝ), (∀ᵐ x ∂μ, ‖f x‖ ≤ C) →
      ∀ᵐ x ∂μ, ‖T f x‖ ≤ C) : IsJdLGAdmissible (monotheticLpOne T) := by
  let π := monotheticLpOne T
  have hb : ∀ n, ‖π n‖ ≤ 1 := norm_monotheticLpOne_le_one T hT
  have hwap : ∀ f : Lp ℂ 1 μ, IsWapVector π f := by
    have hw : IsClosed (wapVectorSubmodule π : Set (Lp ℂ 1 μ)) :=
      isClosed_wapVectorSubmodule π hb
    have hd := Lp.simpleFunc.dense (E := ℂ) (μ := μ) (by simp : (1 : ℝ≥0∞) ≠ ∞)
    intro f
    apply closure_minimal _ hw (hd f)
    intro y hy
    let ys : Lp.simpleFunc ℂ 1 μ := ⟨y, hy⟩
    let g := Lp.simpleFunc.toSimpleFunc ys
    let C := ∑ v ∈ g.range, ‖v‖
    have hC : ∀ᵐ x ∂μ, ‖y x‖ ≤ C := by
      filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun ys] with x hx
      rw [← hx]
      exact Finset.single_le_sum (f := fun v : ℂ ↦ ‖v‖)
        (fun _ _ ↦ norm_nonneg _) (SimpleFunc.mem_range_self g x)
    change IsWapVector π y
    have hc := isCompact_weakClosure_essBound (μ := μ) C
    refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
    rintro _ ⟨n, rfl⟩
    apply subset_closure
    refine ⟨π n y, ?_, rfl⟩
    let m := n.toAdd
    change ∀ᵐ x ∂μ, ‖(T ^ m) y x‖ ≤ C
    induction m with
    | zero => simpa using hC
    | succ m ih =>
      rw [pow_succ']
      change ∀ᵐ x ∂μ, ‖T ((T ^ m) y) x‖ ≤ C
      exact hbound _ C ih
  apply admissible_of_commutative (compact_weakOperatorClosure_of_wap π hb hwap)
  intro m n
  rw [← map_mul, ← map_mul, mul_comm]

end JdLG
