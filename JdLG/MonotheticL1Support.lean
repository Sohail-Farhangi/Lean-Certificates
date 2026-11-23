/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MonotheticL1Order

/-! # The support of a positive fixed point on L¹ -/

@[expose] public section

namespace JdLG

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {X 𝕜 E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The region on which the magnitude of f is bounded by an integer multiple of h. -/
def lpOneFixedPointCut (h : Lp ℝ 1 μ) (f : Lp E 1 μ) (n : ℕ) : Set X :=
  {x | ‖f x‖ ≤ (n : ℝ) * h x}

theorem measurableSet_lpOneFixedPointCut (h : Lp ℝ 1 μ) (f : Lp E 1 μ) (n : ℕ) :
    MeasurableSet (lpOneFixedPointCut h f n) :=
  measurableSet_le (Lp.stronglyMeasurable f).norm.measurable
    ((Lp.stronglyMeasurable h).measurable.const_mul _)

/-- A vector supported on the positive region of h is the norm limit of
its restrictions to regions where it is dominated by multiples of h. -/
theorem tendsto_lpOneFixedPointCut (h : Lp ℝ 1 μ) (f : Lp E 1 μ) (hh : 0 ≤ h)
    (hf : ∀ᵐ x ∂μ, ¬ 0 < h x → f x = 0) :
    Tendsto (fun n ↦ lpOneRestrict (𝕜 := 𝕜) (measurableSet_lpOneFixedPointCut h f n) f)
      atTop (𝓝 f) := by
  let A : ℕ → Set X := fun n ↦ lpOneFixedPointCut h f n
  let hA : ∀ n, MeasurableSet (A n) := measurableSet_lpOneFixedPointCut h f
  have hv : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ (A n)ᶜ := by
    filter_upwards [hf, (Lp.coeFn_nonneg h).2 hh] with x hfx hhx
    change 0 ≤ h x at hhx
    simp only [mem_compl_iff, not_not]
    by_cases hpos : 0 < h x
    · obtain ⟨N, hN⟩ := exists_nat_ge (‖f x‖ / h x)
      exact eventually_atTop.2 ⟨N, fun n hn ↦
        (div_le_iff₀ hpos).1 (hN.trans (by exact_mod_cast hn))⟩
    · have hx := hfx hpos
      exact Eventually.of_forall fun n ↦
        (by rw [hx, norm_zero]; positivity : ‖f x‖ ≤ (n : ℝ) * h x)
  have hnorm := tendsto_norm_lpOneRestrict_zero (𝕜 := 𝕜) f (fun n ↦ (hA n).compl) hv
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := (Metric.tendsto_nhds.1 hnorm ε hε)
  refine he.mono fun n hn ↦ ?_
  have hm : f - lpOneRestrict (𝕜 := 𝕜) (hA n) f =
      lpOneRestrict (𝕜 := 𝕜) (hA n).compl f :=
    sub_eq_iff_eq_add.2 ((lpOneRestrict_add_compl (𝕜 := 𝕜) (hA n) f).symm.trans
      (add_comm _ _))
  rw [dist_eq_norm, norm_sub_rev, hm]
  simpa only [Real.dist_eq, sub_zero, abs_norm] using hn

theorem lpOneFixedPointCut_domination (h : Lp ℝ 1 μ) (f : Lp E 1 μ) (hh : 0 ≤ h)
    (n : ℕ) :
    ∀ᵐ x ∂μ, ‖lpOneRestrict (𝕜 := 𝕜) (measurableSet_lpOneFixedPointCut h f n) f x‖
      ≤ (n : ℝ) * h x := by
  filter_upwards [(Lp.coeFn_nonneg h).2 hh,
    lpOneRestrict_ae (𝕜 := 𝕜) (measurableSet_lpOneFixedPointCut h f n) f] with x hhn hx
  rw [hx]
  by_cases hc : x ∈ lpOneFixedPointCut h f n
  · rw [indicator_of_mem hc]
    exact hc
  · rw [indicator_of_notMem hc, norm_zero]
    change 0 ≤ h x at hhn
    exact mul_nonneg (by positivity) hhn

omit [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] in
theorem lpOneRestrict_nonneg {A : Set X} (hA : MeasurableSet A) {f : Lp ℝ 1 μ}
    (hf : 0 ≤ f) : 0 ≤ lpOneRestrict (𝕜 := ℝ) hA f := by
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [(Lp.coeFn_nonneg f).2 hf,
    lpOneRestrict_ae (𝕜 := ℝ) hA f] with x hfx hx
  rw [hx]
  by_cases ha : x ∈ A
  · rw [indicator_of_mem ha]
    exact hfx
  · rw [indicator_of_notMem ha]
    exact le_rfl

section PositiveOperator

variable (P : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ)
  (hP : ∀ f : Lp ℝ 1 μ, 0 ≤ f → 0 ≤ P f)

include hP

theorem lpOne_positive_monotone : Monotone P := by
  intro f g h
  have he := hP (g - f) (sub_nonneg.2 h)
  rw [map_sub] at he
  exact sub_nonneg.1 he

theorem lpOne_positive_pow_monotone (n : ℕ) : Monotone (P ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact monotone_id
  | succ n ih =>
    rw [pow_succ']
    exact (lpOne_positive_monotone P hP).comp ih

theorem lpOne_positive_pow_nonneg (n : ℕ) {f : Lp ℝ 1 μ} (hf : 0 ≤ f) : 0 ≤ (P ^ n) f := by
  simpa only [map_zero] using lpOne_positive_pow_monotone P hP n hf

/-- A positive operator preserves the subspace supported by a nonnegative
fixed point, here stated on its positive cone. -/
theorem lpOneRestrict_compl_positive_fixed_support (h : Lp ℝ 1 μ) (hh : 0 ≤ h)
    (hfix : P h = h) (f : Lp ℝ 1 μ) (hf : 0 ≤ f) :
    let A : Set X := {x | 0 < h x}
    let hA : MeasurableSet A :=
      measurableSet_lt measurable_const (Lp.stronglyMeasurable h).measurable
    lpOneRestrict (𝕜 := ℝ) hA.compl (P (lpOneRestrict (𝕜 := ℝ) hA f)) = 0 := by
  dsimp only
  let A : Set X := {x | 0 < h x}
  let hA : MeasurableSet A :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable h).measurable
  let g := lpOneRestrict (𝕜 := ℝ) hA f
  have hg : 0 ≤ g := lpOneRestrict_nonneg hA hf
  have hz : ∀ᵐ x ∂μ, ¬ 0 < h x → g x = 0 := by
    filter_upwards [lpOneRestrict_ae (𝕜 := ℝ) hA f] with x hx hc
    exact hx.trans (indicator_of_notMem hc _)
  let e (n : ℕ) := lpOneRestrict (𝕜 := ℝ) (measurableSet_lpOneFixedPointCut h g n) g
  have hlim : Tendsto e atTop (𝓝 g) := tendsto_lpOneFixedPointCut h g hh hz
  let Q := (lpOneRestrict (𝕜 := ℝ) hA.compl).comp P
  change Q g = 0
  have hQ (n : ℕ) : Q (e n) = 0 := by
    have hen : 0 ≤ e n := lpOneRestrict_nonneg (measurableSet_lpOneFixedPointCut h g n) hg
    have hge : e n ≤ (n : ℝ) • h := by
      apply (Lp.coeFn_le _ _).1
      filter_upwards [lpOneFixedPointCut_domination (𝕜 := ℝ) h g hh n,
        Lp.coeFn_smul (n : ℝ) h] with x hbound hs
      exact (le_abs_self ((e n) x)).trans (hbound.trans_eq hs.symm)
    have hpBound := lpOne_positive_monotone P hP hge
    rw [map_smul, hfix] at hpBound
    apply Lp.ext
    filter_upwards [(Lp.coeFn_nonneg (P (e n))).2 (hP (e n) hen),
      (Lp.coeFn_le _ _).2 hpBound, Lp.coeFn_smul (n : ℝ) h, Lp.coeFn_zero ℝ 1 μ,
      lpOneRestrict_ae (𝕜 := ℝ) hA.compl (P (e n))] with x hp0 hp hs hz' hq
    change 0 ≤ P (e n) x at hp0
    change P (e n) x ≤ ((n : ℝ) • h) x at hp
    change ((n : ℝ) • h) x = (n : ℝ) * h x at hs
    change lpOneRestrict (𝕜 := ℝ) hA.compl (P (e n)) x = (0 : Lp ℝ 1 μ) x
    rw [hq, hz']
    by_cases hx : x ∈ A
    · exact indicator_of_notMem (by simpa using hx) _
    · rw [indicator_of_mem (mem_compl hx)]
      have hn : h x ≤ 0 := le_of_not_gt hx
      rw [hs] at hp
      exact le_antisymm (hp.trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hn)) hp0
  have hzero : Tendsto (fun n : ℕ ↦ Q (e n)) atTop (𝓝 (0 : Lp ℝ 1 μ)) :=
    tendsto_const_nhds.congr (fun n ↦ (hQ n).symm)
  exact tendsto_nhds_unique ((Q.continuous.tendsto g).comp hlim) hzero

end PositiveOperator

end JdLG
