/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Permissible
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Bounded PET -/

@[expose] public section

open Filter Finset Function MeasureTheory Set
open scoped Topology BigOperators

namespace VdC

section

variable {X : Type*} [MeasurableSpace X]

private def orbitMax (T : X → X) (g : X → ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | n+1, x => max 0 (g x + orbitMax T g n (T x))

omit [MeasurableSpace X] in
private theorem orbitMax_nonneg (T : X → X) (g : X → ℝ) (n : ℕ) (x : X) :
    0 ≤ orbitMax T g n x := by cases n <;> simp [orbitMax]

omit [MeasurableSpace X] in
private theorem orbitMax_monotone (T : X → X) (g : X → ℝ) (x : X) :
    Monotone (fun n => orbitMax T g n x) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing x with
  | zero => exact orbitMax_nonneg T g _ _
  | succ n ih =>
    simp only [orbitMax]
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

private theorem orbitMax_measurable {T : X → X} {g : X → ℝ} (hT : Measurable T)
    (hg : Measurable g) (n : ℕ) : Measurable (orbitMax T g n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hg.add (ih.comp hT))

omit [MeasurableSpace X] in
private theorem orbitMax_le {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, |g x| ≤ C) (n : ℕ) (x : X) : orbitMax T g n x ≤ (n : ℝ)*C := by
  induction n generalizing x with
  | zero => simp [orbitMax]
  | succ n ih =>
    rw [orbitMax, Nat.cast_succ]
    refine max_le (by positivity) ?_
    have hb := (abs_le.mp (hg x)).2
    have hi := ih (T x)
    linarith only [hb, hi]

omit [MeasurableSpace X] in
private theorem orbit_sum_le_max (T : X → X) (g : X → ℝ) (n : ℕ) (x : X) :
    ∑ i ∈ range n, g (T^[i] x) ≤ orbitMax T g n x := by
  induction n generalizing x with
  | zero => simp [orbitMax]
  | succ n ih =>
    rw [Finset.sum_range_succ', orbitMax]
    simp only [iterate_zero_apply, iterate_succ_apply]
    refine le_trans ?_ (le_max_right _ _)
    linarith only [ih (T x)]

private theorem integrable_real_bounded {μ : Measure X} [IsFiniteMeasure μ] {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) : Integrable g μ := by
  refine Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => ?_)
  simpa only [Real.norm_eq_abs] using hb x

/-- The maximal ergodic inequality for a bounded real observable. The set in
the integral consists of the points where a running maximum of partial sums is positive. -/
private theorem maximal_orbit_integral_nonneg {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) :
    0 ≤ ∫ x, (⋃ n : ℕ, {x | 0 < orbitMax T g n x}).indicator g x ∂μ := by
  classical
  let E (n : ℕ) : Set X := {x | 0 < orbitMax T g n x}
  have hEm (n : ℕ) : MeasurableSet (E n) := measurableSet_lt measurable_const (orbitMax_measurable hT.measurable hg n)
  have hEmono : Monotone E := fun a b hab x hx => hx.trans_le (orbitMax_monotone T g x hab)
  have hpoint (n : ℕ) (x : X) : orbitMax T g n x - orbitMax T g n (T x) ≤ (E n).indicator g x := by
    by_cases hx : x ∈ E n
    · rw [Set.indicator_of_mem hx]
      cases n with
      | zero => simp [E, orbitMax] at hx
      | succ n =>
        have hp : 0 < max 0 (g x + orbitMax T g n (T x)) := hx
        have hp' : 0 ≤ g x + orbitMax T g n (T x) := by
          by_contra! hn
          simp only [max_eq_left hn.le, lt_self_iff_false] at hp
        rw [orbitMax, max_eq_right hp']
        have hh := orbitMax_monotone T g (T x) (Nat.le_succ n)
        linarith only [hh]
    · rw [Set.indicator_of_notMem hx]
      have hn : orbitMax T g n x = 0 := le_antisymm (le_of_not_gt hx) (orbitMax_nonneg T g n x)
      rw [hn, zero_sub]
      exact neg_nonpos.mpr (orbitMax_nonneg T g n (T x))
  have hfinite (n : ℕ) : 0 ≤ ∫ x, (E n).indicator g x ∂μ := by
    have hMax : Integrable (orbitMax T g n) μ := by
      apply integrable_real_bounded (orbitMax_measurable hT.measurable hg n)
      intro x
      rw [abs_of_nonneg (orbitMax_nonneg T g n x)]
      exact orbitMax_le hC hb n x
    have hMaxT : Integrable (fun x => orbitMax T g n (T x)) μ := by
      apply integrable_real_bounded ((orbitMax_measurable hT.measurable hg n).comp hT.measurable)
      intro x
      change |orbitMax T g n (T x)| ≤ _
      rw [abs_of_nonneg (orbitMax_nonneg T g n (T x))]
      exact orbitMax_le hC hb n (T x)
    have hsame : (∫ x, orbitMax T g n (T x) ∂μ) = ∫ x, orbitMax T g n x ∂μ := by
      rw [← integral_map_of_stronglyMeasurable hT.measurable (orbitMax_measurable hT.measurable hg n).stronglyMeasurable,
        hT.map_eq]
    have h := integral_mono (hMax.sub hMaxT) ((integrable_real_bounded hg hb).indicator (hEm n)) (hpoint n)
    change (∫ x, orbitMax T g n x - orbitMax T g n (T x) ∂μ) ≤ ∫ x, (E n).indicator g x ∂μ at h
    rwa [integral_sub hMax hMaxT, hsame, sub_self] at h
  let U := ⋃ n, E n
  have hU : MeasurableSet U := MeasurableSet.iUnion hEm
  have ht : Tendsto (fun n => ∫ x, (E n).indicator g x ∂μ) atTop (𝓝 (∫ x, U.indicator g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hg.indicator (hEm n)).aestronglyMeasurable)
      (integrable_const _) ?_ ?_
    · intro n
      exact ae_of_all _ fun x => by
        by_cases hx : x ∈ E n
        · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs] using hb x
        · simpa only [Set.indicator_of_notMem hx, norm_zero] using hC
    · apply ae_of_all
      intro x
      have H : (fun n => (E n).indicator g x) =ᶠ[atTop] (fun _ => U.indicator g x) := by
        by_cases hx : x ∈ U
        · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
          filter_upwards [eventually_ge_atTop n] with k hk
          rw [Set.indicator_of_mem (hEmono hk hn), Set.indicator_of_mem hx]
        · exact Eventually.of_forall fun n => by
            have hn : x ∉ E n := fun h => hx (Set.mem_iUnion.mpr ⟨n,h⟩)
            simp only [Set.indicator_of_notMem hn, Set.indicator_of_notMem hx]
      exact tendsto_const_nhds.congr' H.symm
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hfinite)

private noncomputable def orbitRealAvg (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  realCesaro (fun n => g (T^[n] x)) N

omit [MeasurableSpace X] in
private theorem orbitRealAvg_abs_le {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |g x| ≤ C) (x : X) (N : ℕ) : |orbitRealAvg T g N x| ≤ C := by
  by_cases hN : N = 0
  · simpa [orbitRealAvg, realCesaro, hN] using hC
  apply abs_le.mpr
  have hN' : 0 < N := Nat.pos_of_ne_zero hN
  exact ⟨(realCesaro_const_pos (-C) hN').symm.le.trans
      (realCesaro_mono (fun n => (abs_le.mp (hb (T^[n] x))).1) N),
    (realCesaro_mono (fun n => (abs_le.mp (hb (T^[n] x))).2) N).trans_eq (realCesaro_const_pos C hN')⟩

omit [MeasurableSpace X] in
private theorem orbitRealAvg_bddAbove {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |g x| ≤ C) (x : X) : atTop.IsBoundedUnder (· ≤ ·) (fun N => orbitRealAvg T g N x) :=
  isBoundedUnder_of_eventually_le (a := C) (Eventually.of_forall fun N => (abs_le.mp (orbitRealAvg_abs_le hC hb x N)).2)

omit [MeasurableSpace X] in
private theorem orbitRealAvg_cobdd {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |g x| ≤ C) (x : X) : atTop.IsCoboundedUnder (· ≤ ·) (fun N => orbitRealAvg T g N x) :=
  isCoboundedUnder_le_of_le _ (fun N => (abs_le.mp (orbitRealAvg_abs_le hC hb x N)).1)

private theorem limsup_le_of_tendsto_sub_zero {u v : ℕ → ℝ}
    (hu : atTop.IsCoboundedUnder (· ≤ ·) u) (hv : atTop.IsBoundedUnder (· ≤ ·) v)
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) : limsup u atTop ≤ limsup v atTop := by
  by_contra! hbad
  let δ := (limsup u atTop - limsup v atTop) / 3
  have hd : 0 < δ := by dsimp [δ]; linarith only [hbad]
  have he1 := h.eventually (gt_mem_nhds hd)
  have he2 := eventually_lt_add_pos_of_limsup_le hv (le_refl (limsup v atTop)) hd
  have hle : limsup u atTop ≤ limsup v atTop + 2*δ := by
    apply limsup_le_of_le hu
    filter_upwards [he1, he2] with n hn hn'
    linarith only [hn, hn']
  dsimp [δ] at hle
  linarith only [hbad, hle]

omit [MeasurableSpace X] in
private theorem limsup_orbitRealAvg_invariant {T : X → X} {g : X → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) (x : X) :
    limsup (fun N => orbitRealAvg T g N (T x)) atTop = limsup (fun N => orbitRealAvg T g N x) atTop := by
  have h := tendsto_realCesaro_shift_sub_zero hC (fun n => hb (T^[n] x)) 1
  have hshift : Tendsto (fun N => orbitRealAvg T g N (T x) - orbitRealAvg T g N x) atTop (𝓝 0) := by
    simpa only [orbitRealAvg, Nat.succ_eq_add_one, iterate_succ_apply] using h
  have hshift' : Tendsto (fun N => orbitRealAvg T g N x - orbitRealAvg T g N (T x)) atTop (𝓝 0) := by
    simpa only [neg_sub, neg_zero] using hshift.neg
  exact le_antisymm (limsup_le_of_tendsto_sub_zero (orbitRealAvg_cobdd hC hb (T x))
    (orbitRealAvg_bddAbove hC hb x) hshift) (limsup_le_of_tendsto_sub_zero
      (orbitRealAvg_cobdd hC hb x) (orbitRealAvg_bddAbove hC hb (T x)) hshift')

private theorem ae_limsup_orbitRealAvg_le {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, limsup (fun N => orbitRealAvg T g N x) atTop ≤ ∫ y, g y ∂μ := by
  classical
  let m := ∫ y, g y ∂μ
  let U (x : X) := limsup (fun N => orbitRealAvg T g N x) atTop
  have hm (N : ℕ) : Measurable (orbitRealAvg T g N) := by
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun n _ => hg.comp (hT.measurable.iterate n))
  have hU : Measurable U := Measurable.limsup hm
  have hUpper (q : ℚ) : ∀ᵐ x ∂μ, m < (q : ℝ) → U x ≤ q := by
    by_cases hq : m < (q : ℝ)
    · let B : Set X := {x | (q : ℝ) < U x}
      have hBm : MeasurableSet B := measurableSet_lt measurable_const hU
      have hBInv : T ⁻¹' B = B := by
        ext x
        change (q : ℝ) < U (T x) ↔ (q : ℝ) < U x
        rw [show U (T x) = U x from limsup_orbitRealAvg_invariant hC hb x]
      rcases hT.toPreErgodic.ae_mem_or_ae_notMem hBm.nullMeasurableSet
        (Eventually.of_forall fun x => by simp only [hBInv]) with hFull | hFail
      · exfalso
        let g' (x : X) := g x - (q : ℝ)
        have hg' : Measurable g' := hg.sub_const _
        have hb' (x : X) : |g' x| ≤ C + |(q : ℝ)| := (abs_sub _ _).trans (add_le_add (hb x) le_rfl)
        let E : Set X := ⋃ n : ℕ, {x | 0 < orbitMax T g' n x}
        have hSub : ∀ᵐ x ∂μ, x ∈ E := by
          filter_upwards [hFull] with x hx
          have hx' : (q : ℝ) < limsup (fun N => orbitRealAvg T g N x) atTop := hx
          have hv : ∃ᶠ N : ℕ in atTop, (q : ℝ) < orbitRealAvg T g N x := by
            by_contra h
            have he : ∀ᶠ N : ℕ in atTop, orbitRealAvg T g N x ≤ q := by
              simpa only [Filter.not_frequently, not_lt] using h
            exact hx'.not_ge (limsup_le_of_le (orbitRealAvg_cobdd hC hb x) he)
          obtain ⟨N, hn, hn'⟩ := ((eventually_gt_atTop (0 : ℕ)).and_frequently hv).exists
          have hN : 0 < (N : ℝ) := by exact_mod_cast hn
          have hsum : (q : ℝ) * N < ∑ n ∈ range N, g (T^[n] x) := (lt_div_iff₀ hN).mp hn'
          have hsum' : 0 < ∑ n ∈ range N, g' (T^[n] x) := by
            simp only [g', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            linarith only [hsum]
          exact Set.mem_iUnion.mpr ⟨N, hsum'.trans_le (orbit_sum_le_max T g' N x)⟩
        have ha : 0 ≤ ∫ x, E.indicator g' x ∂μ := maximal_orbit_integral_nonneg hT.toMeasurePreserving hg' (by positivity) hb'
        have hEq : (∫ x, E.indicator g' x ∂μ) = m - q := by
          rw [integral_congr_ae (hSub.mono fun x hx => Set.indicator_of_mem hx g')]
          exact integral_sub (integrable_real_bounded hg hb) (integrable_const _) |>.trans (by simp [m])
        rw [hEq] at ha
        linarith only [ha, hq]
      · exact hFail.mono fun x h => fun _ => le_of_not_gt h
    · exact Eventually.of_forall fun _ hm => False.elim (hq hm)
  filter_upwards [ae_all_iff.mpr hUpper] with x hx
  change U x ≤ m
  by_contra! H
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn H
  exact hq'.not_ge (hx q hq)

/-- Bounded-observable pointwise ergodic theorem, real form. -/
theorem ae_tendsto_orbitCesaro_real {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun N => realCesaro (fun n => g (T^[n] x)) N) atTop (𝓝 (∫ y, g y ∂μ)) := by
  have hb' : ∀ x, |(-g) x| ≤ C := fun x => by simpa only [Pi.neg_apply, abs_neg] using hb x
  filter_upwards [ae_limsup_orbitRealAvg_le hT hg hC hb, ae_limsup_orbitRealAvg_le hT hg.neg hC hb'] with x h1 h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_lt_add_pos_of_limsup_le (orbitRealAvg_bddAbove hC hb x) h1 hε,
    eventually_lt_add_pos_of_limsup_le (orbitRealAvg_bddAbove hC hb' x) h2 hε] with N hn hn'
  have he : orbitRealAvg T (-g) N x = -(orbitRealAvg T g N x) := by
    simp only [orbitRealAvg, realCesaro, Pi.neg_apply, sum_neg_distrib, neg_div]
  rw [he] at hn'
  simp only [Pi.neg_apply, integral_neg] at hn'
  rw [Real.dist_eq, abs_lt]
  change -ε < orbitRealAvg T g N x - (∫ y, g y ∂μ) ∧ orbitRealAvg T g N x - (∫ y, g y ∂μ) < ε
  constructor <;> linarith only [hn, hn']

/-- Bounded-observable pointwise ergodic theorem, complex form. -/
theorem ae_tendsto_orbitCesaro {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (cesaro (fun n => g (T^[n] x))) atTop (𝓝 (∫ y, g y ∂μ)) := by
  have hi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hb)
  have hRe := ae_tendsto_orbitCesaro_real hT (Complex.continuous_re.measurable.comp hg) hC
    (fun x => (Complex.abs_re_le_norm (g x)).trans (hb x))
  have hIm := ae_tendsto_orbitCesaro_real hT (Complex.continuous_im.measurable.comp hg) hC
    (fun x => (Complex.abs_im_le_norm (g x)).trans (hb x))
  filter_upwards [hRe, hIm] with x hre him
  change Tendsto (fun N => realCesaro (fun n => (g (T^[n] x)).re) N) atTop
    (𝓝 (∫ y, (g y).re ∂μ)) at hre
  change Tendsto (fun N => realCesaro (fun n => (g (T^[n] x)).im) N) atTop
    (𝓝 (∫ y, (g y).im ∂μ)) at him
  have hIR : (∫ y, (g y).re ∂μ) = (∫ y, g y ∂μ).re := integral_re hi
  have hII : (∫ y, (g y).im ∂μ) = (∫ y, g y ∂μ).im := integral_im hi
  simp only [realCesaro_re, hIR] at hre
  have hm (u : ℕ → ℂ) (N : ℕ) : realCesaro (fun n => (u n).im) N = (cesaro u N).im := by
    unfold cesaro realCesaro
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.im_sum]
  simp only [hm, hII] at him
  have hr' := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have hi' := (Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul_const Complex.I
  simpa only [Function.comp_def, Complex.re_add_im] using hr'.add hi'

end
end VdC
