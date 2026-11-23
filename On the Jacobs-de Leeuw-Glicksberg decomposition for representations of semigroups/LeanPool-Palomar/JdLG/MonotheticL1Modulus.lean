/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MonotheticL1Mean
public import JdLG.WeakCompactApproximation

/-! # Monothetic L¹ actions with a mean-ergodic linear modulus -/

@[expose] public section

namespace JdLG

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The finite-measure complex L¹ order interval dominated by an integrable
function has compact weak closure. -/
theorem isCompact_weakClosure_lpOne_orderInterval (h : Lp ℝ 1 μ) {C : ℝ} (hC : 0 ≤ C) :
    IsCompact (closure (toWeakSpace ℂ (Lp ℂ 1 μ) ''
      {f : Lp ℂ 1 μ | ∀ᵐ x ∂μ, ‖f x‖ ≤ C * h x})) := by
  apply isCompact_closure_weak_of_approx
  intro ε hε
  let A (n : ℕ) : Set X := {x | h x ≤ (n : ℝ)}
  let hA (n : ℕ) : MeasurableSet (A n) :=
    measurableSet_le (Lp.stronglyMeasurable h).measurable measurable_const
  have hv : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ (A n)ᶜ := Eventually.of_forall fun x ↦ by
    obtain ⟨N, hN⟩ := exists_nat_ge (h x)
    refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    exact not_not.2 (hN.trans (by exact_mod_cast hn))
  have hn := tendsto_norm_lpOneRestrict_zero (𝕜 := ℝ) h (fun n ↦ (hA n).compl) hv
  have hCp : 0 < C + 1 := by positivity
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.1 hn (ε / (C + 1)) (div_pos hε hCp)).exists
  have hnb : ‖lpOneRestrict (𝕜 := ℝ) (hA n).compl h‖ ≤ ε / (C + 1) := by
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  let K := closure (toWeakSpace ℂ (Lp ℂ 1 μ) ''
    {f : Lp ℂ 1 μ | ∀ᵐ x ∂μ, ‖f x‖ ≤ C * (n : ℝ)})
  refine ⟨K, isCompact_weakClosure_essBound _, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  let g := lpOneRestrict (𝕜 := ℂ) (hA n) f
  let r := lpOneRestrict (𝕜 := ℂ) (hA n).compl f
  have hgs : f - g = r := sub_eq_iff_eq_add.2
    ((lpOneRestrict_add_compl (𝕜 := ℂ) (hA n) f).symm.trans (add_comm _ _))
  refine ⟨toWeakSpace ℂ (Lp ℂ 1 μ) g, subset_closure ⟨g, ?_, rfl⟩, ?_⟩
  · change ∀ᵐ x ∂μ, ‖g x‖ ≤ C * (n : ℝ)
    filter_upwards [hf, lpOneRestrict_ae (𝕜 := ℂ) (hA n) f] with x hfx hg
    change g x = (A n).indicator (⇑f) x at hg
    rw [hg]
    by_cases hx : x ∈ A n
    · rw [indicator_of_mem hx]
      exact hfx.trans (mul_le_mul_of_nonneg_left hx hC)
    · rw [indicator_of_notMem hx, norm_zero]
      positivity
  · rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hgs]
    have he := Lp.norm_le_mul_norm_of_ae_le_mul (f := r)
      (g := lpOneRestrict (𝕜 := ℝ) (hA n).compl h) (c := C) (by
        filter_upwards [hf, lpOneRestrict_ae (𝕜 := ℂ) (hA n).compl f,
          lpOneRestrict_ae (𝕜 := ℝ) (hA n).compl h] with x hfx hf' hh'
        change r x = (A n)ᶜ.indicator (⇑f) x at hf'
        rw [hf', hh']
        by_cases hx : x ∈ (A n)ᶜ
        · rw [indicator_of_mem hx, indicator_of_mem hx]
          exact hfx.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
        · simp [indicator_of_notMem hx])
    exact he.trans ((mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_left hnb (by positivity)).trans_eq
        (by field_simp)))

omit [IsFiniteMeasure μ] in
/-- Pointwise domination by a positive operator propagates to every power. -/
theorem lpOneModulus_pow_le (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (pPos : ∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ P f)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ)
    (hdom : ∀ f, lpOneModulus (T f) ≤ P (lpOneModulus f))
    (n : ℕ) (f : Lp ℂ 1 μ) :
    lpOneModulus ((T ^ n) f) ≤ (P ^ n) (lpOneModulus f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change lpOneModulus (T ((T ^ n) f)) ≤ P ((P ^ n) (lpOneModulus f))
    exact (hdom _).trans (lpOne_positive_monotone P pPos ih)

/-- Every vector supported on the positive region of a fixed point for
the dominating operator has a relatively weakly compact orbit. -/
theorem isWapVector_monotheticLpOne_of_fixed_support
    (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (pPos : ∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ P f)
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (hT : ‖T‖ ≤ 1)
    (hdom : ∀ f, lpOneModulus (T f) ≤ P (lpOneModulus f))
    (h : Lp ℝ 1 μ) (hh : 0 ≤ h) (hfix : P h = h)
    (f : Lp ℂ 1 μ) (hf : ∀ᵐ x ∂μ, ¬ 0 < h x → f x = 0) :
    IsWapVector (monotheticLpOne T) f := by
  let π := monotheticLpOne T
  let V := wapVectorSubmodule π
  let g (n : ℕ) := lpOneRestrict (𝕜 := ℂ) (measurableSet_lpOneFixedPointCut h f n) f
  have hc : IsClosed (V : Set (Lp ℂ 1 μ)) :=
    isClosed_wapVectorSubmodule π (norm_monotheticLpOne_le_one T hT)
  have hlim : Tendsto g atTop (𝓝 f) := tendsto_lpOneFixedPointCut (𝕜 := ℂ) h f hh hf
  apply hc.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  change IsWapVector π (g n)
  have hgn : lpOneModulus (g n) ≤ (n : ℝ) • h := by
    apply (Lp.coeFn_le _ _).1
    filter_upwards [lpOneModulus_ae (g n), lpOneFixedPointCut_domination (𝕜 := ℂ) h f hh n,
      Lp.coeFn_smul (n : ℝ) h] with x he hb hs
    change ((n : ℝ) • h) x = (n : ℝ) * h x at hs
    exact he.trans_le (hb.trans_eq hs.symm)
  have hPfix (k : ℕ) : (P ^ k) h = h := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ']
      change P ((P ^ k) h) = h
      rw [ih, hfix]
  have hK := isCompact_weakClosure_lpOne_orderInterval h (Nat.cast_nonneg n)
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  apply subset_closure
  refine ⟨π k (g n), ?_, rfl⟩
  have he := (lpOneModulus_pow_le P pPos T hdom k.toAdd (g n)).trans
    (lpOne_positive_pow_monotone P pPos k.toAdd hgn)
  rw [map_smul, hPfix] at he
  filter_upwards [(Lp.coeFn_le _ _).2 he, lpOneModulus_ae (π k (g n)), Lp.coeFn_smul (n : ℝ) h]
    with x hb hm hs
  change ((n : ℝ) • h) x = (n : ℝ) * h x at hs
  exact hm.symm.trans_le (hb.trans_eq hs)

/-- Convergence of the positive dominating operator's Cesàro averages at
the constant one suffices for admissibility of the complex power action. -/
theorem admissible_monotheticLpOne_of_meanErgodicModulus
    (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) (hT : ‖T‖ ≤ 1)
    (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (hP : ‖P‖ ≤ 1)
    (pPos : ∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ P f)
    (hdom : ∀ f, lpOneModulus (T f) ≤ P (lpOneModulus f))
    (hmean : ∀ f, ∃ h, Tendsto (lpOneCesaro P f) atTop (𝓝 h)) :
    IsJdLGAdmissible (monotheticLpOne T) := by
  let π := monotheticLpOne T
  let u : Lp ℝ 1 μ := (memLp_const 1).toLp (fun _ ↦ 1)
  have hu : (⇑u : X → ℝ) =ᵐ[μ] fun _ ↦ 1 := (memLp_const 1).coeFn_toLp
  have hu0 : 0 ≤ u := (Lp.coeFn_nonneg u).1 (hu.mono fun x hx ↦ by
    change 0 ≤ u x
    rw [hx]
    exact zero_le_one)
  obtain ⟨h, hlim⟩ := hmean u
  have hclosed : IsClosed (Ici (0 : Lp ℝ 1 μ)) := isClosed_Ici
  have hh : 0 ≤ h := hclosed.mem_of_tendsto hlim
    (Eventually.of_forall fun n ↦ lpOneCesaro_nonneg P pPos hu0 n)
  have hfix := lpOneCesaro_fixed_limit P hP hlim
  let A : Set X := {x | 0 < h x}
  let hA : MeasurableSet A :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable h).measurable
  let R := lpOneRestrict (μ := μ) (E := ℝ) (𝕜 := ℝ) hA.compl
  let Q := lpOneRestrict (μ := μ) (E := ℂ) (𝕜 := ℂ) hA
  let D := lpOneRestrict (μ := μ) (E := ℂ) (𝕜 := ℂ) hA.compl
  have hzero : Tendsto (fun n ↦ ‖R ((P ^ n) u)‖) atTop (𝓝 0) :=
    tendsto_lpOne_away_from_fixed_support P hP pPos hu0 hlim
  have hpow := norm_monotheticLpOne_le_one T hT
  suffices hw : ∀ f, IsWapVector π f by
    apply admissible_of_commutative (compact_weakOperatorClosure_of_wap π hpow hw)
    intro m n
    rw [← map_mul, ← map_mul, mul_comm]
  apply isWapVector_of_dense π
    (Lp.simpleFunc.dense (E := ℂ) (μ := μ) (by simp : (1 : ℝ≥0∞) ≠ ∞)) _ hpow
  intro f hf
  let fs : Lp.simpleFunc ℂ 1 μ := ⟨f, hf⟩
  let v := Lp.simpleFunc.toSimpleFunc fs
  let C := ∑ z ∈ v.range, ‖z‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hfu : lpOneModulus f ≤ C • u := by
    apply (Lp.coeFn_le _ _).1
    filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun fs, hu, lpOneModulus_ae f,
      Lp.coeFn_smul C u] with x hv hx hm hc
    change (C • u) x = C * u x at hc
    rw [hm, hc, hx, mul_one, ← hv]
    exact Finset.single_le_sum (f := fun z : ℂ ↦ ‖z‖)
      (fun _ _ ↦ norm_nonneg _) (SimpleFunc.mem_range_self v x)
  have hd (n : ℕ) : ‖D ((T ^ n) f)‖ ≤ C * ‖R ((P ^ n) u)‖ := by
    have he := (lpOneModulus_pow_le P pPos T hdom n f).trans
      (lpOne_positive_pow_monotone P pPos n hfu)
    rw [map_smul] at he
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(Lp.coeFn_le _ _).2 he, Lp.coeFn_smul C ((P ^ n) u),
      lpOneModulus_ae ((T ^ n) f), lpOneRestrict_ae (𝕜 := ℝ) hA.compl ((P ^ n) u),
      lpOneRestrict_ae (𝕜 := ℂ) hA.compl ((T ^ n) f)] with x hb hc hm hr hd'
    change (C • (P ^ n) u) x = C * ((P ^ n) u) x at hc
    rw [hm, hc] at hb
    change ‖D ((T ^ n) f) x‖ ≤ C * ‖R ((P ^ n) u) x‖
    rw [hd', hr]
    by_cases hx : x ∈ Aᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      exact hb.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
    · simp [indicator_of_notMem hx]
  have hdLim : Tendsto (fun n ↦ ‖D ((T ^ n) f)‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hd ?_
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hzero
  apply isWapVector_of_approx
  intro ε hε
  obtain ⟨m, hm⟩ := (Metric.tendsto_nhds.1 hdLim ε hε).exists
  have hm' : ‖D ((T ^ m) f)‖ ≤ ε := by
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hm.le
  let g := Q ((T ^ m) f)
  have hg : ∀ᵐ x ∂μ, ¬ 0 < h x → g x = 0 := by
    filter_upwards [lpOneRestrict_ae (𝕜 := ℂ) hA ((T ^ m) f)] with x hx hnon
    exact hx.trans (indicator_of_notMem hnon _)
  have hKg := isWapVector_monotheticLpOne_of_fixed_support P pPos T hT hdom h hh hfix g hg
  let F := (fun n : ℕ ↦ toWeakSpace ℂ (Lp ℂ 1 μ) ((T ^ n) f)) '' (Finset.range m : Set ℕ)
  have hF : IsCompact F := ((Finset.range m).finite_toSet.image _).isCompact
  refine ⟨F ∪ weakVectorOrbit π g, hF.union hKg, fun s ↦ ?_⟩
  by_cases hs : s.toAdd < m
  · exact ⟨toWeakSpace ℂ (Lp ℂ 1 μ) (π s f), Or.inl ⟨s.toAdd, Finset.mem_range.2 hs, rfl⟩,
      by rw [LinearEquiv.symm_apply_apply, sub_self, norm_zero]; exact hε.le⟩
  · let k := Multiplicative.ofAdd (s.toAdd - m)
    refine ⟨toWeakSpace ℂ (Lp ℂ 1 μ) (π k g), Or.inr (subset_closure (mem_range_self k)), ?_⟩
    rw [LinearEquiv.symm_apply_apply]
    have hs' : s.toAdd - m + m = s.toAdd := Nat.sub_add_cancel (le_of_not_gt hs)
    change ‖(T ^ s.toAdd) f - (T ^ (s.toAdd - m)) g‖ ≤ ε
    have hsEq : (T ^ s.toAdd) f = (T ^ (s.toAdd - m)) ((T ^ m) f) := by
      change (T ^ s.toAdd) f = ((T ^ (s.toAdd - m)) * (T ^ m)) f
      rw [← pow_add, hs']
    rw [hsEq]
    rw [← map_sub]
    have he : (T ^ m) f - g = D ((T ^ m) f) :=
      sub_eq_iff_eq_add.2 ((lpOneRestrict_add_compl (𝕜 := ℂ) hA ((T ^ m) f)).symm.trans
        (add_comm _ _))
    rw [he]
    exact (((π k).le_of_opNorm_le (hpow k)) _).trans (by simpa only [one_mul] using hm')

end JdLG

