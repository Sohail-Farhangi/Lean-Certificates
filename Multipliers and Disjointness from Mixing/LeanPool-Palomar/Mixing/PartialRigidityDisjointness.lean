/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.JoiningExtreme
public import Mixing.JoiningSpectrum
public import Mixing.PartialMixingDecay
public import Mixing.MeasureDomination

/-! # Disjointness of partial rigidity from partial mixing -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Mixing

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]

namespace IsJoining

variable {T : System G X} {S : System G Y} {τ : Measure (X × Y)}

/-- The correlation operator of a joining on full L², from the second coordinate
to the first. -/
noncomputable def firstOperator (h : IsJoining T S τ) :
    Lp ℂ 2 S.measure →L[ℂ] Lp ℂ 2 T.measure :=
  h.fstFactor.pullback.toContinuousLinearMap.adjoint.comp h.sndFactor.pullback.toContinuousLinearMap

theorem firstOperator_intertwines (h : IsJoining T S τ) :
    Intertwines S.koopmanRep T.koopmanRep h.firstOperator :=
  h.fstFactor.intertwines_pullback.adjoint.comp h.sndFactor.intertwines_pullback

theorem firstOperator_one (h : IsJoining T S τ) :
    h.firstOperator (constantOne S.measure) = constantOne T.measure := by
  apply ext_inner_left ℂ
  intro z
  change inner ℂ z (h.fstFactor.pullback.toContinuousLinearMap.adjoint
    (h.sndFactor.pullback (constantOne S.measure))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, h.sndFactor.pullback_one,
    ← h.fstFactor.pullback_one]
  exact h.fstFactor.pullback.inner_map_map _ _

theorem setIntegral_firstOperator (h : IsJoining T S τ)
    (f : Lp ℂ 2 S.measure) {A : Set X} (hA : MeasurableSet A) :
    (∫ x in A, h.firstOperator f x ∂T.measure) = ∫ w in Prod.fst ⁻¹' A, f w.2 ∂τ := by
  rw [← L2.inner_indicatorConstLp_one hA (measure_ne_top _ _)]
  change inner ℂ (eventVector T hA) (h.fstFactor.pullback.toContinuousLinearMap.adjoint
    (h.sndFactor.pullback f)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (Lp.compMeasurePreserving Prod.fst h.fst (eventVector T hA))
    (Lp.compMeasurePreserving Prod.snd h.snd f) = _
  rw [eventVector, Lp.indicatorConstLp_compMeasurePreserving, L2.inner_indicatorConstLp_one]
  exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_compMeasurePreserving f h.snd))

theorem integral_firstOperator (h : IsJoining T S τ) (f : Lp ℂ 2 S.measure) :
    (∫ x, h.firstOperator f x ∂T.measure) = ∫ y, f y ∂S.measure := by
  have hInt := h.setIntegral_firstOperator f MeasurableSet.univ
  rw [setIntegral_univ, preimage_univ, setIntegral_univ] at hInt
  have hMap := integral_map (μ := τ) (φ := Prod.snd) (f := fun y => f y)
    h.snd.measurable.aemeasurable (Lp.stronglyMeasurable f).aestronglyMeasurable
  rw [h.snd.map_eq] at hMap
  exact hInt.trans hMap.symm

theorem event_firstOperator_coeff (h : IsJoining T S τ)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℂ (eventVector T hA) (h.firstOperator (eventVector S hB)) = (τ.real (A ×ˢ B) : ℂ) := by
  let := h.probability
  change inner ℂ (eventVector T hA) (h.fstFactor.pullback.toContinuousLinearMap.adjoint
    (h.sndFactor.pullback (eventVector S hB))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (Lp.compMeasurePreserving Prod.fst h.fst (eventVector T hA))
    (Lp.compMeasurePreserving Prod.snd h.snd (eventVector S hB)) = _
  rw [eventVector, eventVector, Lp.indicatorConstLp_compMeasurePreserving,
    Lp.indicatorConstLp_compMeasurePreserving, L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  rfl

theorem ae_im_firstOperator_zero_of_real (h : IsJoining T S τ)
    (f : Lp ℂ 2 S.measure) (hf : ∀ᵐ y ∂S.measure, (f y).im = 0) :
    ∀ᵐ x ∂T.measure, (h.firstOperator f x).im = 0 := by
  have hJInt : Integrable (fun x => h.firstOperator f x) T.measure :=
    (Lp.memLp (h.firstOperator f)).integrable (by norm_num)
  have hFInt : Integrable (fun w : X × Y => f w.2) τ :=
    h.snd.integrable_comp_of_integrable ((Lp.memLp f).integrable (by norm_num))
  apply ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun _ _ _ => hJInt.im.integrableOn)
  intro A hA _
  change (∫ x in A, RCLike.im (h.firstOperator f x) ∂T.measure) = 0
  rw [integral_im hJInt.integrableOn, h.setIntegral_firstOperator f hA,
    ← integral_im hFInt.integrableOn]
  exact integral_eq_zero_of_ae (ae_restrict_of_ae (h.snd.quasiMeasurePreserving.ae hf))

theorem ae_re_firstOperator_nonneg (h : IsJoining T S τ)
    (f : Lp ℂ 2 S.measure) (hf : ∀ᵐ y ∂S.measure, 0 ≤ (f y).re) :
    ∀ᵐ x ∂T.measure, 0 ≤ (h.firstOperator f x).re := by
  have hJInt : Integrable (fun x => h.firstOperator f x) T.measure :=
    (Lp.memLp (h.firstOperator f)).integrable (by norm_num)
  have hFInt : Integrable (fun w : X × Y => f w.2) τ :=
    h.snd.integrable_comp_of_integrable ((Lp.memLp f).integrable (by norm_num))
  apply ae_nonneg_of_forall_setIntegral_nonneg hJInt.re
  intro A hA _
  rw [integral_re hJInt.integrableOn, h.setIntegral_firstOperator f hA,
    ← integral_re hFInt.integrableOn]
  exact setIntegral_nonneg_of_ae (h.snd.quasiMeasurePreserving.ae hf)

theorem ae_re_firstOperator_mono (h : IsJoining T S τ)
    (f g : Lp ℂ 2 S.measure) (hfg : ∀ᵐ y ∂S.measure, (f y).re ≤ (g y).re) :
    ∀ᵐ x ∂T.measure, (h.firstOperator f x).re ≤ (h.firstOperator g x).re := by
  have hPos : ∀ᵐ y ∂S.measure, 0 ≤ ((g - f : Lp ℂ 2 S.measure) y).re := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with y hy hsub
    rw [hsub, Pi.sub_apply, Complex.sub_re]
    exact sub_nonneg.mpr hy
  have hJ := h.ae_re_firstOperator_nonneg (g - f) hPos
  rw [map_sub] at hJ
  filter_upwards [hJ, Lp.coeFn_sub (h.firstOperator g) (h.firstOperator f)] with x hx hsub
  rw [hsub, Pi.sub_apply, Complex.sub_re] at hx
  exact sub_nonneg.mp hx

end IsJoining

private theorem System.ae_re_ultrafilterOperator_upper (T : System G X)
    (p : Ultrafilter G) (β : ℝ) (h : T.IsPartiallyMixingAlong p β)
    (f : Lp ℂ 2 T.measure) (hf : ∀ᵐ x ∂T.measure, (f x).im = 0)
    {C : ℝ} (hC : ∀ᵐ x ∂T.measure, (f x).re ≤ C) :
    ∀ᵐ x ∂T.measure, (ultrafilterOperator T.koopmanRep p f x).re ≤
      β * (∫ y, f y ∂T.measure).re + (1 - β) * C := by
  let Q := ultrafilterOperator T.koopmanRep p
  let c := constantOne T.measure
  let u := (C : ℂ) • c
  let g := u - f
  have hu : u =ᵐ[T.measure] fun _ => (C : ℂ) := by
    filter_upwards [Lp.coeFn_smul (C : ℂ) c, Lp.coeFn_const (p := 2) (μ := T.measure) (1 : ℂ)]
      with x hs hc
    change c x = 1 at hc
    rw [hs, Pi.smul_apply, hc, smul_eq_mul, mul_one]
  have hg : g =ᵐ[T.measure] fun x => (C : ℂ) - f x := by
    filter_upwards [Lp.coeFn_sub u f, hu] with x hx hux
    change g x = _ at hx
    rw [hx, Pi.sub_apply, hux]
  have hgReal : ∀ᵐ x ∂T.measure, (g x).im = 0 := by
    filter_upwards [hg, hf] with x hx hReal
    simp only [hx, Complex.sub_im, Complex.ofReal_im, hReal, sub_zero]
  have hgPos : ∀ᵐ x ∂T.measure, 0 ≤ (g x).re := by
    filter_upwards [hg, hC] with x hx hBound
    rw [hx, Complex.sub_re, Complex.ofReal_re]
    exact sub_nonneg.mpr hBound
  have hgMean : (∫ x, g x ∂T.measure) = (C : ℂ) - ∫ x, f x ∂T.measure := by
    rw [← inner_constantOne_left]
    change inner ℂ c ((C : ℂ) • c - f) = _
    rw [inner_sub_right, inner_smul_right, show inner ℂ c c = 1 from inner_constantOne_self _,
      mul_one, inner_constantOne_left]
  have hQ : Q g = u - Q f := by
    simp only [g, u, Q, map_sub, map_smul, c, T.ultrafilterOperator_constantOne]
  have hgDom := T.ae_re_dominated_of_partialMixing p β h g hgReal hgPos
  change ∀ᵐ x ∂T.measure, β * (∫ y, g y ∂T.measure).re ≤ (Q g x).re at hgDom
  rw [hgMean, hQ] at hgDom
  filter_upwards [hgDom, Lp.coeFn_sub u (Q f), hu] with x hx hSub hux
  simp only [hSub, Pi.sub_apply, hux, Complex.sub_re, Complex.ofReal_re] at hx
  change (Q f x).re ≤ _
  nlinarith

/-- Theorem 5.1, in the order with the partly mixing system first. -/
theorem disjoint_partiallyMixing_partiallyRigid
    {T : System G X} {S : System G Y} (p : Ultrafilter G) {α β : ℝ}
    (hα : α ≤ 1) (hβ : β ≤ 1) (hSum : 1 < α + β)
    (hMix : T.IsPartiallyMixingAlong p β) (hRigid : S.IsPartiallyRigidAlong p α) :
    Disjoint T S := by
  have hα₀ : 0 < α := by linarith
  have hβ₀ : 0 < β := by linarith
  let D := β / (α + β - 1)
  have hD0 : 0 ≤ D := div_nonneg hβ₀.le (by linarith)
  obtain ⟨qMix, hqMix⟩ :=
    T.exists_isUMixing_singleton_of_partiallyMixingAlong p hβ₀ hβ hMix
  intro τ hτ
  let := hτ.probability
  let : IsFiniteMeasure (ENNReal.ofReal D • (T.measure.prod S.measure)) := ⟨by
    change ENNReal.ofReal D * (T.measure.prod S.measure) univ < ∞
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  apply dominated_joining_eq_prod hτ (C := ENNReal.ofReal D) ENNReal.ofReal_ne_top _ qMix hqMix
  apply measure_le_of_rectangles
  intro A B hA hB
  let J := hτ.firstOperator
  let a := J (eventVector S hB)
  let b := S.measure.real B
  let Q := ultrafilterOperator T.koopmanRep p
  let r := (1 - β) / α
  have hr₀ : 0 ≤ r := div_nonneg (by linarith) hα₀.le
  have hr₁ : r < 1 := (div_lt_one hα₀).mpr (by linarith)
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hMean : (∫ x, a x ∂T.measure) = (b : ℂ) := by
    change (∫ x, hτ.firstOperator (eventVector S hB) x ∂T.measure) = _
    rw [hτ.integral_firstOperator, integral_eventVector]
  have hEvt := indicatorConstLp_coeFn (p := 2) (hs := hB)
    (hμs := measure_ne_top S.measure B) (c := (1 : ℂ))
  have hEvtReal : ∀ᵐ y ∂S.measure, (eventVector S hB y).im = 0 := by
    filter_upwards [hEvt] with y hy
    change eventVector S hB y = _ at hy
    rw [hy]
    classical
    by_cases hmem : y ∈ B <;> simp [hmem]
  have haReal := hτ.ae_im_firstOperator_zero_of_real (eventVector S hB) hEvtReal
  have ha₁ : ∀ᵐ x ∂T.measure, (a x).re ≤ 1 := by
    have hInput : ∀ᵐ y ∂S.measure,
        (eventVector S hB y).re ≤ (constantOne S.measure y).re := by
      filter_upwards [hEvt, Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)] with y hy hOne
      change eventVector S hB y = _ at hy
      change constantOne S.measure y = 1 at hOne
      rw [hy, hOne]
      classical
      by_cases hmem : y ∈ B <;> simp [hmem]
    have hUp := hτ.ae_re_firstOperator_mono (eventVector S hB) (constantOne S.measure) hInput
    rw [hτ.firstOperator_one] at hUp
    filter_upwards [hUp, Lp.coeFn_const (p := 2) (μ := T.measure) (1 : ℂ)] with x hx hOne
    change constantOne T.measure x = 1 at hOne
    rw [hOne, Complex.one_re] at hx
    exact hx
  have hLower : ∀ᵐ x ∂T.measure, α * (a x).re ≤ (Q a x).re := by
    have hInput : ∀ᵐ y ∂S.measure,
        (((α : ℂ) • eventVector S hB : Lp ℂ 2 S.measure) y).re ≤
          ((ultrafilterOperator S.koopmanRep p (eventVector S hB)) y).re := by
      filter_upwards [hEvt, Lp.coeFn_smul (α : ℂ) (eventVector S hB),
        S.ae_event_dominated_of_partialRigidity p α hRigid hB] with y hy hs hDom
      change eventVector S hB y = _ at hy
      rw [hs, Pi.smul_apply, hy, smul_eq_mul]
      classical
      by_cases hmem : y ∈ B <;> simpa [hmem] using hDom
    have hJ := hτ.ae_re_firstOperator_mono ((α : ℂ) • eventVector S hB)
      (ultrafilterOperator S.koopmanRep p (eventVector S hB)) hInput
    rw [map_smul, hτ.firstOperator_intertwines.ultrafilter p (eventVector S hB)] at hJ
    filter_upwards [hJ, Lp.coeFn_smul (α : ℂ) a] with x hx hs
    change (((α : ℂ) • a : Lp ℂ 2 T.measure) x).re ≤ (Q a x).re at hx
    rw [hs, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hx
    exact hx
  have hStepEq (n : ℕ) :
      β * b + (1 - β) * (D * b + r ^ n) = α * (D * b + r ^ (n + 1)) := by
    have hFix : β + (1 - β) * D = α * D := by
      dsimp [D]
      field_simp [show α + β - 1 ≠ 0 by linarith]
      ring
    have hR : α * r = 1 - β := by
      dsimp [r]
      field_simp [hα₀.ne']
    rw [pow_succ']
    calc
      _ = (β + (1 - β) * D) * b + (1 - β) * r ^ n := by ring
      _ = _ := by rw [hFix, ← hR]; ring
  have hBound (n : ℕ) : ∀ᵐ x ∂T.measure, (a x).re ≤ D * b + r ^ n := by
    induction n with
    | zero =>
      filter_upwards [ha₁] with x hx
      rw [pow_zero]
      linarith [mul_nonneg hD0 hb]
    | succ n ih =>
      have hUp := T.ae_re_ultrafilterOperator_upper p β hMix a haReal ih
      rw [hMean] at hUp
      filter_upwards [hLower, hUp] with x hxL hxU
      change (Q a x).re ≤ _ at hxU
      rw [Complex.ofReal_re, hStepEq n] at hxU
      exact (mul_le_mul_iff_right₀ hα₀).mp (hxL.trans hxU)
  have hLim : Tendsto (fun n : ℕ => D * b + r ^ n) atTop (𝓝 (D * b)) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁)
  have hDom : ∀ᵐ x ∂T.measure, (a x).re ≤ D * b := by
    filter_upwards [ae_all_iff.mpr hBound] with x hx
    exact ge_of_tendsto' hLim hx
  have hInt : Integrable (fun x => a x) T.measure := (Lp.memLp a).integrable (by norm_num)
  have hIntComp := setIntegral_mono_ae (s := A) hInt.re.integrableOn
    (integrable_const (D * b)).integrableOn
    hDom
  change (∫ x in A, RCLike.re (a x) ∂T.measure) ≤ _ at hIntComp
  rw [integral_re hInt.integrableOn, setIntegral_const, smul_eq_mul,
    ← L2.inner_indicatorConstLp_one hA (measure_ne_top _ _)] at hIntComp
  change (inner ℂ (eventVector T hA) (hτ.firstOperator (eventVector S hB))).re ≤ _ at hIntComp
  rw [hτ.event_firstOperator_coeff hA hB, Complex.ofReal_re] at hIntComp
  have hRhsTop : (ENNReal.ofReal D • T.measure.prod S.measure) (A ×ˢ B) ≠ ∞ := measure_ne_top _ _
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) hRhsTop).mp
  change (τ.real (A ×ˢ B)) ≤ (ENNReal.ofReal D * T.measure.prod S.measure (A ×ˢ B)).toReal
  rw [Measure.prod_prod, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0]
  change τ.real (A ×ˢ B) ≤ D * (T.measure.real A * b)
  linarith only [hIntComp]

/-- Theorem 5.1, with partial rigidity and partial mixing defined by the
ultrafilter limits of the paper's event correlations. -/
theorem theorem5_1
    {T : System G X} {S : System G Y} (p : Ultrafilter G) {α β : ℝ}
    (hα : α ≤ 1) (hβ : β ≤ 1) (hSum : 1 < α + β)
    (hRigid : T.IsPartiallyRigidAlong p α) (hMix : S.IsPartiallyMixingAlong p β) :
    Disjoint T S :=
  (disjoint_partiallyMixing_partiallyRigid p hα hβ hSum hMix hRigid).symm

/-- Theorem 5.1 directly in the event-correlation formulation. -/
theorem theorem5_1_events
    {T : System G X} {S : System G Y} (p : Ultrafilter G) {α β : ℝ}
    (hα : α ≤ 1) (hβ : β ≤ 1) (hSum : 1 < α + β)
    (hRigid : ∀ A : Set X, MeasurableSet A → α * T.measure.real A ≤
      scalarUltralimit p (fun g ↦ T.measure.real (A ∩ T.act g ⁻¹' A)))
    (hMix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      β * S.measure.real A * S.measure.real B ≤
        scalarUltralimit p (fun g ↦ S.measure.real (A ∩ S.act g ⁻¹' B))) :
    Disjoint T S := by
  refine theorem5_1 p hα hβ hSum ?_ ((S.isPartiallyMixingAlong_iff_scalarUltralimit p β).2 hMix)
  intro A hA
  simpa only [scalarUltralimit, (T.tendsto_event_correlation p hA hA).limUnder_eq] using hRigid A hA

end Mixing
