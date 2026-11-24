/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.PartialMixingDefinitions
public import Mixing.RigidInjectivity
public import Mixing.WeakMixingBridge
public import Mathlib.Topology.Compactification.StoneCech

/-! # Positive partial mixing implies weak mixing -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology Mixing

namespace Mixing

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- Weak Koopman limits preserve real-valued L² classes. -/
theorem System.ae_im_ultrafilterOperator_zero_of_real (S : System G X) (p : Ultrafilter G)
    (f : Lp ℂ 2 S.measure) (hf : ∀ᵐ x ∂S.measure, (f x).im = 0) :
    ∀ᵐ x ∂S.measure, (ultrafilterOperator S.koopmanRep p f x).im = 0 := by
  let Q := ultrafilterOperator S.koopmanRep p
  have hInt : Integrable (fun x => Q f x) S.measure := (Lp.memLp (Q f)).integrable (by norm_num)
  apply ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun _ _ _ => hInt.im.integrableOn)
  intro A hA _
  let v := Q.adjoint (eventVector S hA)
  have hReal := S.ae_im_zero_event_ultrafilterOperator (inverseUltrafilter p) hA
  rw [ultrafilterOperator_inverse] at hReal
  change (∫ x in A, RCLike.im (Q f x) ∂S.measure) = 0
  rw [integral_im hInt.integrableOn, ← L2.inner_indicatorConstLp_one hA (measure_ne_top _ _)]
  change RCLike.im (inner ℂ (eventVector S hA) (Q f)) = 0
  rw [← ContinuousLinearMap.adjoint_inner_left, L2.inner_def,
    ← integral_im (L2.integrable_inner (𝕜 := ℂ) v f)]
  have hPoint : (fun x => RCLike.im (inner ℂ (v x) (f x))) =ᵐ[S.measure]
      fun _ => (0 : ℝ) := by
    filter_upwards [hf, hReal] with x hfx hvx
    change (inner ℂ (v x) (f x)).im = 0
    change (v x).im = 0 at hvx
    rw [RCLike.inner_apply', Complex.mul_im, Complex.conj_re, Complex.conj_im,
      hfx, hvx, neg_zero, mul_zero, zero_mul, add_zero]
  rw [integral_congr_ae hPoint, integral_zero]

private theorem constantOne_ae (S : System G X) :
    constantOne S.measure =ᵐ[S.measure] fun _ => (1 : ℂ) :=
  Lp.coeFn_const (p := 2) (μ := S.measure) 1

private theorem scaled_constantOne_ae (S : System G X) (C : ℝ) :
    ((C : ℂ) • constantOne S.measure : Lp ℂ 2 S.measure) =ᵐ[S.measure] fun _ => (C : ℂ) := by
  filter_upwards [Lp.coeFn_smul (C : ℂ) (constantOne S.measure), constantOne_ae S]
    with x h₁ h₂
  rw [h₁, Pi.smul_apply, h₂, smul_eq_mul, mul_one]

/-- For a real-valued centered L² function, partial mixing contracts its essential
uniform bound by the factor 1−β. -/
theorem System.ae_norm_ultrafilterOperator_le_of_partialMixing_centered (S : System G X)
    (p : Ultrafilter G) {β : ℝ} (h : S.IsPartiallyMixingAlong p β)
    (f : Lp ℂ 2 S.measure) (hfReal : ∀ᵐ x ∂S.measure, (f x).im = 0)
    (hMean : ∫ x, f x ∂S.measure = 0)
    {C : ℝ} (hC : ∀ᵐ x ∂S.measure, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂S.measure, ‖ultrafilterOperator S.koopmanRep p f x‖ ≤ (1 - β) * C := by
  let Q := ultrafilterOperator S.koopmanRep p
  let c := constantOne S.measure
  let u := (C : ℂ) • c
  let fp := u + f
  let fm := u - f
  have hu : u =ᵐ[S.measure] fun _ => (C : ℂ) := scaled_constantOne_ae S C
  have huMean : inner ℂ c u = (C : ℂ) := by
    simp only [u, inner_smul_right, c, inner_constantOne_self, mul_one]
  have hfMean : inner ℂ c f = 0 := (inner_constantOne_left _ _).trans hMean
  have hpMean : (∫ x, fp x ∂S.measure) = (C : ℂ) := by
    rw [← inner_constantOne_left]
    change inner ℂ c (u + f) = _
    rw [inner_add_right, huMean, hfMean, add_zero]
  have hmMean : (∫ x, fm x ∂S.measure) = (C : ℂ) := by
    rw [← inner_constantOne_left]
    change inner ℂ c (u - f) = _
    rw [inner_sub_right, huMean, hfMean, sub_zero]
  have hpae : fp =ᵐ[S.measure] fun x => (C : ℂ) + f x := by
    filter_upwards [Lp.coeFn_add u f, hu] with x hx hux
    change fp x = _ at hx
    rw [hx, Pi.add_apply, hux]
  have hmae : fm =ᵐ[S.measure] fun x => (C : ℂ) - f x := by
    filter_upwards [Lp.coeFn_sub u f, hu] with x hx hux
    change fm x = _ at hx
    rw [hx, Pi.sub_apply, hux]
  have hpr : ∀ᵐ x ∂S.measure, (fp x).im = 0 := by
    filter_upwards [hpae, hfReal] with x hx hr
    simp only [hx, Complex.add_im, Complex.ofReal_im, hr, add_zero]
  have hmr : ∀ᵐ x ∂S.measure, (fm x).im = 0 := by
    filter_upwards [hmae, hfReal] with x hx hr
    simp only [hx, Complex.sub_im, Complex.ofReal_im, hr, sub_zero]
  have hPos : ∀ᵐ x ∂S.measure, 0 ≤ (fp x).re := by
    filter_upwards [hpae, hC] with x hx hB
    rw [hx, Complex.add_re, Complex.ofReal_re]
    linarith [(abs_le.mp ((Complex.abs_re_le_norm (f x)).trans hB)).1]
  have hNeg : ∀ᵐ x ∂S.measure, 0 ≤ (fm x).re := by
    filter_upwards [hmae, hC] with x hx hB
    rw [hx, Complex.sub_re, Complex.ofReal_re]
    linarith [(abs_le.mp ((Complex.abs_re_le_norm (f x)).trans hB)).2]
  have hQLow := S.ae_re_dominated_of_partialMixing p β h fp hpr hPos
  have hQUp := S.ae_re_dominated_of_partialMixing p β h fm hmr hNeg
  have hQfp : Q fp = u + Q f := by
    simp only [fp, u, Q, map_add, map_smul, c, S.ultrafilterOperator_constantOne]
  have hQfm : Q fm = u - Q f := by
    simp only [fm, u, Q, map_sub, map_smul, c, S.ultrafilterOperator_constantOne]
  change ∀ᵐ x ∂S.measure, β * (∫ y, fp y ∂S.measure).re ≤ (Q fp x).re at hQLow
  change ∀ᵐ x ∂S.measure, β * (∫ y, fm y ∂S.measure).re ≤ (Q fm x).re at hQUp
  rw [hpMean, hQfp] at hQLow
  rw [hmMean, hQfm] at hQUp
  filter_upwards [hQLow, hQUp, Lp.coeFn_add u (Q f), Lp.coeFn_sub u (Q f), hu,
    S.ae_im_ultrafilterOperator_zero_of_real p f hfReal] with x hL hU hAdd hSub hux hReal
  simp only [hAdd, Pi.add_apply, hux, Complex.add_re, Complex.ofReal_re] at hL
  simp only [hSub, Pi.sub_apply, hux, Complex.sub_re, Complex.ofReal_re] at hU
  have hR : ((Q f x).re : ℂ) = Q f x :=
    Complex.ext (Complex.ofReal_re _) (by simpa only [Complex.ofReal_im, eq_comm] using hReal)
  change ‖Q f x‖ ≤ _
  rw [← hR, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

private theorem System.tendsto_power_apply_zero_of_partialMixing_centered (S : System G X)
    (p : Ultrafilter G) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (h : S.IsPartiallyMixingAlong p β) (f : Lp ℂ 2 S.measure)
    (hf : ∀ᵐ x ∂S.measure, (f x).im = 0) (hMean : ∫ x, f x ∂S.measure = 0)
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ᵐ x ∂S.measure, ‖f x‖ ≤ C) :
    Tendsto (fun n : ℕ => (ultrafilterOperator S.koopmanRep p ^ n) f) atTop (𝓝 0) := by
  let Q := ultrafilterOperator S.koopmanRep p
  have hPow (n : ℕ) :
      (∀ᵐ x ∂S.measure, ((Q ^ n) f x).im = 0) ∧
        (∫ x, (Q ^ n) f x ∂S.measure = 0) ∧
        ∀ᵐ x ∂S.measure, ‖(Q ^ n) f x‖ ≤ (1 - β) ^ n * C := by
    induction n with
    | zero => simpa only [pow_zero, one_apply_eq_self, one_mul] using And.intro hf ⟨hMean, hBound⟩
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_assoc]
      exact ⟨S.ae_im_ultrafilterOperator_zero_of_real p _ ih.1,
        (S.integral_ultrafilterOperator_apply p _).trans ih.2.1,
        S.ae_norm_ultrafilterOperator_le_of_partialMixing_centered p h _ ih.1 ih.2.1 ih.2.2⟩
  have hNorm (n : ℕ) : ‖(Q ^ n) f‖ ≤ (1 - β) ^ n * C := by
    have hh := Lp.norm_le_of_ae_bound (mul_nonneg (pow_nonneg (sub_nonneg.mpr hβ₁) _) hC)
      (hPow n).2.2
    simpa [measureUnivNNReal, measure_univ] using hh
  have hQ : Tendsto (fun n : ℕ => (1 - β) ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hβ₁)
      (sub_lt_self 1 hβ₀)).mul_const C
  have hn := squeeze_zero (fun n => norm_nonneg ((Q ^ n) f)) hNorm hQ
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)

private theorem System.tendsto_event_coeff_power_of_partialMixing (S : System G X)
    (p : Ultrafilter G) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (h : S.IsPartiallyMixingAlong p β)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => inner ℂ (eventVector S hA)
      ((ultrafilterOperator S.koopmanRep p ^ n) (eventVector S hB))) atTop
      (𝓝 ((S.measure.real A * S.measure.real B : ℝ) : ℂ)) := by
  let Q := ultrafilterOperator S.koopmanRep p
  let c := constantOne S.measure
  let e := eventVector S hB
  let b := S.measure.real B
  let f := e - (b : ℂ) • c
  have hZero : (∫ x, f x ∂S.measure) = 0 := by
    rw [← inner_constantOne_left]
    change inner ℂ c (e - (b : ℂ) • c) = _
    rw [inner_sub_right, inner_smul_right, show inner ℂ c c = 1 from inner_constantOne_self _,
      mul_one]
    change inner ℂ (constantOne S.measure) (eventVector S hB) - (b : ℂ) = _
    rw [inner_constantOne_left, integral_eventVector, show b = S.measure.real B from rfl, sub_self]
  have hEv : f =ᵐ[S.measure] fun x => B.indicator (fun _ => (1 : ℂ)) x - (b : ℂ) := by
    filter_upwards [Lp.coeFn_sub e ((b : ℂ) • c), scaled_constantOne_ae S b,
      indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top S.measure B) (c := (1 : ℂ))]
      with x hx hc he
    change f x = _ at hx
    change e x = _ at he
    rw [hx, Pi.sub_apply, hc, he]
  have hReal : ∀ᵐ x ∂S.measure, (f x).im = 0 := by
    filter_upwards [hEv] with x hx
    rw [hx]
    classical
    by_cases hmem : x ∈ B <;> simp [hmem]
  have hBound : ∀ᵐ x ∂S.measure, ‖f x‖ ≤ 1 := by
    have hB0 : 0 ≤ b := ENNReal.toReal_nonneg
    have hB1 : b ≤ 1 := by
      simpa only [b, measureReal_def, ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := S.measure) (s := B))
    filter_upwards [hEv] with x hx
    rw [hx]
    classical
    by_cases hmem : x ∈ B
    · rw [indicator_of_mem hmem, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hB1)]
      linarith
    · rw [indicator_of_notMem hmem, zero_sub, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hB0]
      exact hB1
  have hLim := S.tendsto_power_apply_zero_of_partialMixing_centered p hβ₀ hβ₁ h f
    hReal hZero (by norm_num : 0 ≤ (1 : ℝ)) hBound
  have hFix (n : ℕ) : (Q ^ n) c = c := by
    induction n with
    | zero => simp only [pow_zero, one_apply_eq_self]
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih]
      exact S.ultrafilterOperator_constantOne p
  have hSplit (n : ℕ) :
      inner ℂ (eventVector S hA) ((Q ^ n) e) =
        inner ℂ (eventVector S hA) ((Q ^ n) f) +
          ((S.measure.real A * S.measure.real B : ℝ) : ℂ) := by
    have he : e = f + (b : ℂ) • c := by rw [show f = e - (b : ℂ) • c from rfl, sub_add_cancel]
    conv_lhs => rw [he]
    rw [map_add, map_smul, hFix, inner_add_right, inner_smul_right,
      ← inner_conj_symm (𝕜 := ℂ) (eventVector S hA) c]
    simp only [c, inner_constantOne_left, integral_eventVector, Complex.conj_ofReal,
      Complex.ofReal_mul, b, mul_comm (S.measure.real B : ℂ)]
  have hInner := ((InnerProductSpace.toDual ℂ _ (eventVector S hA)).continuous.tendsto _).comp hLim
  have hAdd := hInner.add (tendsto_const_nhds (x :=
    ((S.measure.real A * S.measure.real B : ℝ) : ℂ)))
  change Tendsto (fun n => inner ℂ (eventVector S hA) ((Q ^ n) e)) atTop _
  simpa only [hSplit, Function.comp_def, InnerProductSpace.toDual_apply_apply,
    inner_zero_right, zero_add] using hAdd

/-- Positive partial mixing along one ultrafilter yields mixing along an ultrafilter
obtained from iterates of the given one. -/
theorem System.exists_isUMixing_singleton_of_partiallyMixingAlong (S : System G X)
    (p : Ultrafilter G) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (h : S.IsPartiallyMixingAlong p β) :
    ∃ q : Ultrafilter G, S.IsUMixing {q} := by
  let s : ℕ → Ultrafilter G := Nat.rec p (fun _ q => p * q)
  have hPow (n : ℕ) : ultrafilterOperator S.koopmanRep (s n) =
      ultrafilterOperator S.koopmanRep p ^ (n + 1) := by
    induction n with
    | zero => simp only [s, Nat.rec_zero, Nat.zero_add, pow_one]
    | succ n ih =>
      change ultrafilterOperator S.koopmanRep (p * s n) = _
      rw [ultrafilterOperator_mul, ih]
      exact (pow_succ' _ _).symm
  obtain ⟨r, hr⟩ := exists_ultrafilter_le (atTop : Filter ℕ)
  obtain ⟨q, _, hq⟩ := isCompact_univ.ultrafilter_le_nhds' (r.map s)
    (Ultrafilter.mem_map.mpr (Eventually.of_forall fun _ => mem_univ _))
  have hQ : Tendsto s (r : Filter ℕ) (𝓝 q) := hq
  have hContinuous :
      Continuous (fun q => ContinuousLinearMapWOT.ofCLM (ultrafilterOperator S.koopmanRep q)) :=
    continuous_subtype_val.comp (continuous_ultrafilter_extend (weakClosureInclusion S.koopmanRep))
  refine ⟨q, (S.isUMixing_iff_events {q}).mpr ?_⟩
  intro q' hq' A B hA hB
  have heq : q' = q := mem_singleton_iff.mp hq'
  subst q'
  have hCoeff := ((ContinuousLinearMapWOT.continuous_dual_apply (eventVector S hB)
    (InnerProductSpace.toDual ℂ _ (eventVector S hA))).tendsto _).comp
      ((hContinuous.tendsto q).comp hQ)
  change Tendsto (fun n => inner ℂ (eventVector S hA)
    (ultrafilterOperator S.koopmanRep (s n) (eventVector S hB))) (r : Filter ℕ)
      (𝓝 (inner ℂ (eventVector S hA) (ultrafilterOperator S.koopmanRep q (eventVector S hB)))) at hCoeff
  simp only [hPow] at hCoeff
  have hEv := ((S.tendsto_event_coeff_power_of_partialMixing p hβ₀ hβ₁ h hA hB).comp
    (tendsto_add_atTop_nat 1)).mono_left hr
  have hLimit := tendsto_nhds_unique hCoeff hEv
  simpa only [hLimit, Complex.ofReal_re] using S.tendsto_event_correlation q hA hB

/-- The weak-mixing implication used in the proof of Theorem 5.1. -/
theorem System.isWeaklyMixing_of_partiallyMixingAlong (S : System G X)
    (p : Ultrafilter G) {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (h : S.IsPartiallyMixingAlong p β) : IsWeaklyMixing S.koopmanZeroRep := by
  obtain ⟨q, hq⟩ := S.exists_isUMixing_singleton_of_partiallyMixingAlong p hβ₀ hβ₁ h
  exact isWeaklyMixing_of_isUMixing S.koopmanZeroRep (singleton_nonempty q) hq

end Mixing
