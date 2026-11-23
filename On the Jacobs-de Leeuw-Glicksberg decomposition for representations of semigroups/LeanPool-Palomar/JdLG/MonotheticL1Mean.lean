/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MonotheticL1Support

/-! # A positive mean-ergodic contraction loses all mass off its fixed support -/

@[expose] public section

namespace JdLG

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

noncomputable def lpOneCesaro (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (f : Lp ℝ 1 μ) (N : ℕ) :
    Lp ℝ 1 μ :=
  (N : ℝ)⁻¹ • ∑ j ∈ Finset.range N, (P ^ j) f

theorem lpOne_positive_apply_pow_norm_le (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hP : ‖P‖ ≤ 1) (n : ℕ) (f : Lp ℝ 1 μ) : ‖(P ^ n) f‖ ≤ ‖f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ‖P ((P ^ n) f)‖ ≤ ‖f‖
    refine ((P.le_of_opNorm_le hP) _).trans ?_
    simpa only [one_mul] using ih

theorem lpOneCesaro_nonneg (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hP : ∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ P f) {f : Lp ℝ 1 μ} (hf : 0 ≤ f) (n : ℕ) :
    0 ≤ lpOneCesaro P f n := by
  let g := ∑ j ∈ Finset.range n, (P ^ j) f
  have hg : 0 ≤ g := Finset.sum_nonneg fun j _ ↦ lpOne_positive_pow_nonneg P hP j hf
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [(Lp.coeFn_nonneg g).2 hg, Lp.coeFn_smul (n : ℝ)⁻¹ g] with x hp hs
  change 0 ≤ g x at hp
  change ((n : ℝ)⁻¹ • g) x = (n : ℝ)⁻¹ * g x at hs
  change 0 ≤ ((n : ℝ)⁻¹ • g) x
  rw [hs]
  positivity

theorem lpOneCesaro_fixed_limit (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
    (hP : ‖P‖ ≤ 1) {f h : Lp ℝ 1 μ} (hlim : Tendsto (lpOneCesaro P f) atTop (𝓝 h)) :
    P h = h := by
  have heq (n : ℕ) : P (lpOneCesaro P f n) - lpOneCesaro P f n =
      (n : ℝ)⁻¹ • ((P ^ n) f - f) := by
    simp only [lpOneCesaro, map_smul, map_sum, ← smul_sub]
    congr 1
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        add_sub_add_comm, ih, pow_succ']
      change (P ^ n) f - f + (P ((P ^ n) f) - (P ^ n) f) = P ((P ^ n) f) - f
      abel
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hv := hi.mul (tendsto_const_nhds (x := ‖f‖ + ‖f‖))
  have hv0 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * (‖f‖ + ‖f‖)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hv
  have hz : Tendsto (fun n ↦ P (lpOneCesaro P f n) - lpOneCesaro P f n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hv0
    rw [heq, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (add_le_add_left (lpOne_positive_apply_pow_norm_le P hP n f) _))
      (by positivity)
  have hfinal := tendsto_nhds_unique (((P.continuous.tendsto h).comp hlim).sub hlim) hz
  exact sub_eq_zero.mp hfinal

/-- The norm on nonnegative real L¹ vectors is the integral. -/
theorem norm_realLpOne_eq_integral_of_nonneg {f : Lp ℝ 1 μ} (hf : 0 ≤ f) :
    ‖f‖ = L1.integralCLM f := by
  rw [lpOne_norm_eq_integral_norm, ← L1.integral_eq]
  have hi := memLp_one_iff_integrable.mp (Lp.memLp f)
  have hIntegral : (∫ x, f x ∂μ) = L1.integral f := by
    rw [MeasureTheory.integral_eq (⇑f) hi, Integrable.toL1_coeFn]
  rw [← hIntegral]
  refine integral_congr_ae ?_
  filter_upwards [(Lp.coeFn_nonneg f).2 hf] with x hp
  change 0 ≤ f x at hp
  exact Real.norm_of_nonneg hp

/-- A nonnegative input whose Cesàro averages converge loses all its
off-support mass under the powers of the positive contraction. -/
theorem tendsto_lpOne_away_from_fixed_support
    (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ) (hP : ‖P‖ ≤ 1)
    (hp : ∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ P f)
    {f h : Lp ℝ 1 μ} (hf : 0 ≤ f) (hlim : Tendsto (lpOneCesaro P f) atTop (𝓝 h)) :
    let A : Set X := {x | 0 < h x}
    let hA : MeasurableSet A :=
      measurableSet_lt measurable_const (Lp.stronglyMeasurable h).measurable
    Tendsto (fun n ↦ ‖lpOneRestrict (𝕜 := ℝ) hA.compl ((P ^ n) f)‖) atTop (𝓝 0) := by
  let A : Set X := {x | 0 < h x}
  let hA : MeasurableSet A :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable h).measurable
  let R := lpOneRestrict (μ := μ) (E := ℝ) (𝕜 := ℝ) hA.compl
  let m (n : ℕ) := ‖R ((P ^ n) f)‖
  have hclosed : IsClosed (Ici (0 : Lp ℝ 1 μ)) := isClosed_Ici
  have hh : 0 ≤ h := hclosed.mem_of_tendsto hlim
    (Eventually.of_forall fun n ↦ lpOneCesaro_nonneg P hp hf n)
  have hfix := lpOneCesaro_fixed_limit P hP hlim
  have hRh : R h = 0 := by
    apply Lp.ext
    filter_upwards [lpOneRestrict_ae (𝕜 := ℝ) hA.compl h, Lp.coeFn_zero ℝ 1 μ,
      (Lp.coeFn_nonneg h).2 hh] with x he hz hhx
    change R h x = (0 : Lp ℝ 1 μ) x
    rw [he, hz]
    by_cases hx : x ∈ A
    · exact indicator_of_notMem (by simpa using hx) _
    · rw [indicator_of_mem (mem_compl hx)]
      exact le_antisymm (le_of_not_gt hx) hhx
  have hm : Antitone m := by
    apply antitone_nat_of_succ_le
    intro n
    let g := (P ^ n) f
    let Q := lpOneRestrict (μ := μ) (E := ℝ) (𝕜 := ℝ) hA
    have hg : 0 ≤ g := lpOne_positive_pow_nonneg P hp n hf
    have hs : Q g + R g = g := lpOneRestrict_add_compl hA g
    have hvanish : R (P (Q g)) = 0 := lpOneRestrict_compl_positive_fixed_support P hp h hh hfix g hg
    have hsplit : R (P g) = R (P (R g)) := by
      calc
        R (P g) = R (P (Q g + R g)) := congrArg (fun z ↦ R (P z)) hs.symm
        _ = R (P (R g)) := by rw [map_add, map_add, hvanish, zero_add]
    change ‖R ((P ^ (n + 1)) f)‖ ≤ ‖R g‖
    rw [pow_succ']
    change ‖R (P g)‖ ≤ ‖R g‖
    rw [hsplit]
    exact (norm_lpOneRestrict_le hA.compl (P (R g))).trans
      (by simpa only [one_mul] using P.le_of_opNorm_le hP (R g))
  let φ := (L1.integralCLM (μ := μ) (E := ℝ)).comp R
  have hφ (n : ℕ) : m n = φ ((P ^ n) f) :=
    norm_realLpOne_eq_integral_of_nonneg
      (lpOneRestrict_nonneg hA.compl (lpOne_positive_pow_nonneg P hp n hf))
  have hz : φ h = 0 := by
    change L1.integralCLM (R h) = 0
    rw [hRh, map_zero]
  have hl : Tendsto (fun n ↦ φ (lpOneCesaro P f n)) atTop (𝓝 0) := by
    rw [← hz]
    exact (φ.continuous.tendsto h).comp hlim
  change Tendsto m atTop (𝓝 0)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hl
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_le_iff.mp hn)
  change m n ≤ φ (lpOneCesaro P f n)
  rw [lpOneCesaro, map_smul, map_sum, smul_eq_mul, inv_mul_eq_div]
  rw [le_div_iff₀ hn0, mul_comm]
  calc
    (n : ℝ) * m n = ∑ j ∈ Finset.range n, m n := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun j hj ↦
      (hm (Finset.mem_range.1 hj).le).trans_eq (hφ j)

end JdLG
