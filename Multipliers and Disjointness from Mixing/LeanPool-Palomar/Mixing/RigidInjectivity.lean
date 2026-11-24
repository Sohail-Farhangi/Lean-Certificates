/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RigidEventBounds
public import Mixing.InjectiveLimits

/-! # Injectivity of partially rigid weak Koopman limits -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Mixing

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

private theorem eventVector_compl (S : System G X) {A : Set X} (hA : MeasurableSet A) :
    eventVector S hA.compl = constantOne S.measure - eventVector S hA := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top S.measure A)
      (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hA.compl) (hμs := measure_ne_top S.measure Aᶜ)
      (c := (1 : ℂ)),
    Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ),
    Lp.coeFn_sub (constantOne S.measure) (eventVector S hA)] with x h₁ h₂ hC hSub
  change constantOne S.measure x = 1 at hC
  rw [hSub, Pi.sub_apply, hC]
  change _ = 1 - (indicatorConstLp 2 hA (measure_ne_top _ _) 1 : Lp ℂ 2 S.measure) x
  rw [h₁]
  change (indicatorConstLp 2 hA.compl (measure_ne_top _ _) 1 : Lp ℂ 2 S.measure) x = _
  rw [h₂]
  classical
  by_cases hx : x ∈ A <;> simp [hx]

/-- Every weak Koopman limit preserves the integral. -/
theorem System.integral_ultrafilterOperator_apply (S : System G X)
    (p : Ultrafilter G) (f : Lp ℂ 2 S.measure) :
    (∫ x, ultrafilterOperator S.koopmanRep p f x ∂S.measure) = ∫ x, f x ∂S.measure := by
  rw [← inner_constantOne_left, ← inner_constantOne_left,
    ← ContinuousLinearMap.adjoint_inner_left, ← ultrafilterOperator_inverse,
    S.ultrafilterOperator_constantOne]

private theorem System.isPartiallyRigidAlong_inverse (S : System G X)
    (p : Ultrafilter G) (α : ℝ) (h : S.IsPartiallyRigidAlong p α) :
    S.IsPartiallyRigidAlong (inverseUltrafilter p) α := by
  intro A hA
  rw [ultrafilterOperator_inverse, ContinuousLinearMap.adjoint_inner_right]
  have he : (inner ℂ (ultrafilterOperator S.koopmanRep p (eventVector S hA))
        (eventVector S hA)).re =
      (inner ℂ (eventVector S hA) (ultrafilterOperator S.koopmanRep p (eventVector S hA))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  exact h A hA

/-- The image of an event under a weak Koopman limit is a.e. real-valued. -/
theorem System.ae_im_zero_event_ultrafilterOperator (S : System G X)
    (p : Ultrafilter G) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ x ∂S.measure, (ultrafilterOperator S.koopmanRep p (eventVector S hA) x).im = 0 := by
  let v := ultrafilterOperator S.koopmanRep p (eventVector S hA)
  have hInt : Integrable (fun x => v x) S.measure := (Lp.memLp v).integrable (by norm_num)
  apply ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun _ _ _ => hInt.im.integrableOn)
  intro B hB _
  change (∫ x in B, RCLike.im (v x) ∂S.measure) = 0
  rw [integral_im hInt.integrableOn, ← L2.inner_indicatorConstLp_one hB (measure_ne_top _ _)]
  have hLim := (Complex.continuous_im.tendsto _).comp
    (tendsto_ultrafilterOperator_coeff S.koopmanRep p (eventVector S hB) (eventVector S hA))
  simp only [Function.comp_def, koopman_event_coeff, Complex.ofReal_im] at hLim
  exact tendsto_nhds_unique hLim tendsto_const_nhds

private theorem System.ae_re_zero_of_rigid_kernel (S : System G X)
    (p : Ultrafilter G) {α : ℝ} (hα : 1 / 2 < α) (h : S.IsPartiallyRigidAlong p α)
    (f : Lp ℂ 2 S.measure) (hQ : ultrafilterOperator S.koopmanRep p f = 0) :
    ∀ᵐ x ∂S.measure, (f x).re = 0 := by
  classical
  let A := {x : X | 0 < (f x).re}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const
      (Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable f).measurable)
  let pInv := inverseUltrafilter p
  let Q := ultrafilterOperator S.koopmanRep p
  let QInv := ultrafilterOperator S.koopmanRep pInv
  let v := QInv (eventVector S hA)
  have hInv := S.isPartiallyRigidAlong_inverse p α h
  have hIm : ∀ᵐ x ∂S.measure, (v x).im = 0 := S.ae_im_zero_event_ultrafilterOperator pInv hA
  have hOne : QInv (eventVector S hA.compl) = constantOne S.measure - v := by
    rw [eventVector_compl, map_sub]
    change QInv (constantOne S.measure) - v = _
    rw [S.ultrafilterOperator_constantOne pInv]
  have hPos : ∀ᵐ x ∂S.measure, x ∈ A → α ≤ (v x).re := by
    filter_upwards [S.ae_event_dominated_of_partialRigidity pInv α hInv hA] with x hx hxA
    exact (indicator_of_mem hxA (fun _ => α)) ▸ hx
  have hNeg : ∀ᵐ x ∂S.measure, x ∉ A → (v x).re ≤ 1 - α := by
    have hUpper := S.ae_event_dominated_of_partialRigidity pInv α hInv hA.compl
    change ∀ᵐ x ∂S.measure, Aᶜ.indicator (fun _ => α) x ≤
      (QInv (eventVector S hA.compl) x).re at hUpper
    rw [hOne] at hUpper
    filter_upwards [hUpper, Lp.coeFn_sub (constantOne S.measure) v,
      Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)] with x hUp hSub hC hx
    change constantOne S.measure x = 1 at hC
    rw [indicator_of_mem (show x ∈ Aᶜ from hx), hSub, Pi.sub_apply, hC,
      Complex.sub_re, Complex.one_re] at hUp
    linarith
  have hInner : inner ℂ v f = 0 := by
    change inner ℂ (ultrafilterOperator S.koopmanRep (inverseUltrafilter p)
      (eventVector S hA)) f = 0
    rw [ultrafilterOperator_inverse, ContinuousLinearMap.adjoint_inner_left, hQ, inner_zero_right]
  have hProdAe : (fun x => RCLike.re (inner ℂ (v x) (f x))) =ᵐ[S.measure]
      fun x => (v x).re * (f x).re := by
    filter_upwards [hIm] with x hx
    change (inner ℂ (v x) (f x)).re = _
    rw [RCLike.inner_apply', Complex.mul_re, Complex.conj_re, Complex.conj_im, hx, neg_zero,
      zero_mul, sub_zero]
  have hProdInt : Integrable (fun x => (v x).re * (f x).re) S.measure :=
    (L2.integrable_inner (𝕜 := ℂ) v f).re.congr hProdAe
  have hProd : (∫ x, (v x).re * (f x).re ∂S.measure) = 0 := by
    rw [← integral_congr_ae hProdAe, integral_re (L2.integrable_inner (𝕜 := ℂ) v f),
      ← L2.inner_def, hInner, map_zero]
  let Fp := A.indicator (fun x => (f x).re)
  let Fn := Aᶜ.indicator (fun x => (f x).re)
  have hFInt : Integrable (fun x => f x) S.measure := (Lp.memLp f).integrable (by norm_num)
  have hFp : Integrable Fp S.measure := hFInt.re.indicator hA
  have hFn : Integrable Fn S.measure := hFInt.re.indicator hA.compl
  have hSplit : (fun x => Fp x + Fn x) = fun x => (f x).re := by
    funext x
    by_cases hx : x ∈ A <;> simp [Fp, Fn, hx]
  have hMean := S.integral_ultrafilterOperator_apply p f
  rw [hQ] at hMean
  have hMeanZero : (∫ x, f x ∂S.measure) = 0 :=
    hMean.symm.trans (by simpa only [Pi.zero_apply, integral_zero] using
      (integral_congr_ae (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := S.measure))))
  have hSum : (∫ x, Fp x ∂S.measure) + (∫ x, Fn x ∂S.measure) = 0 := by
    rw [← integral_add hFp hFn, hSplit]
    change (∫ x, RCLike.re (f x) ∂S.measure) = 0
    rw [integral_re hFInt, hMeanZero, map_zero]
  have hPoint : ∀ᵐ x ∂S.measure,
      α * Fp x + (1 - α) * Fn x ≤ (v x).re * (f x).re := by
    filter_upwards [hPos, hNeg] with x hxP hxN
    by_cases hx : x ∈ A
    · simpa [Fp, Fn, hx] using mul_le_mul_of_nonneg_right (hxP hx)
        (le_of_lt (show 0 < (f x).re from hx))
    · simpa [Fp, Fn, hx] using mul_le_mul_of_nonpos_right (hxN hx)
        (le_of_not_gt (show ¬ 0 < (f x).re from hx))
  have hIneq := integral_mono_ae ((hFp.const_mul α).add (hFn.const_mul (1 - α))) hProdInt hPoint
  change (∫ x, α * Fp x + (1 - α) * Fn x ∂S.measure) ≤
    (∫ x, (v x).re * (f x).re ∂S.measure) at hIneq
  rw [integral_add (hFp.const_mul α) (hFn.const_mul (1 - α)),
    integral_const_mul, integral_const_mul, hProd] at hIneq
  have hpNonneg (x : X) : 0 ≤ Fp x := by
    by_cases hx : x ∈ A
    · simpa [Fp, hx] using (show 0 ≤ (f x).re from (show 0 < (f x).re from hx).le)
    · simp [Fp, hx]
  have hnNonneg (x : X) : 0 ≤ -Fn x := by
    by_cases hx : x ∈ A
    · simp [Fn, hx]
    · simpa [Fn, hx] using (neg_nonneg.mpr (le_of_not_gt (show ¬ 0 < (f x).re from hx)))
  have hNonpos : (2 * α - 1) * (∫ x, Fp x ∂S.measure) ≤ 0 := by
    nlinarith
  have hFpZero : (∫ x, Fp x ∂S.measure) = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right hNonpos (by linarith)) (integral_nonneg hpNonneg)
  have hFnZero : (∫ x, -Fn x ∂S.measure) = 0 := by
    rw [integral_neg]
    linarith
  have hAEp := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hpNonneg) hFp).mp hFpZero
  have hAEn := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hnNonneg) hFn.neg).mp hFnZero
  filter_upwards [hAEp, hAEn] with x hpx hnx
  have hx := congrFun hSplit x
  linarith

/-- Proposition 7(i), from the event correlation definition of α-rigidity. -/
theorem proposition7_i (S : System G X) (p : Ultrafilter G)
    {α : ℝ} (hα : 1 / 2 < α) (h : S.IsPartiallyRigidAlong p α) :
    Function.Injective (ultrafilterOperator S.koopmanRep p) := by
  intro f g hfg
  let v := f - g
  have hQv : ultrafilterOperator S.koopmanRep p v = 0 := by
    rw [show v = f - g from rfl, map_sub, hfg, sub_self]
  have hQR := S.ae_re_zero_of_rigid_kernel p hα h v hQv
  have hQI : ultrafilterOperator S.koopmanRep p ((-Complex.I) • v) = 0 := by
    rw [map_smul, hQv, smul_zero]
  have hi := S.ae_re_zero_of_rigid_kernel p hα h ((-Complex.I) • v) hQI
  have hv : v = 0 := by
    apply Lp.ext
    filter_upwards [hQR, hi, Lp.coeFn_smul (-Complex.I) v,
      Lp.coeFn_zero (p := 2) (μ := S.measure) (E := ℂ)] with x hR hI hS hZero
    rw [hS, Pi.smul_apply, smul_eq_mul] at hI
    have hIm : (v x).im = 0 := by
      simpa [Complex.mul_re] using hI
    rw [hZero]
    exact Complex.ext (by simpa using hR) (by simpa using hIm)
  exact sub_eq_zero.mp hv

/-- Injectivity on full L² restricts to the mean-zero weak Koopman limit. -/
theorem System.injective_meanZero_limit_of_injective_full (S : System G X) (p : Ultrafilter G)
    (h : Function.Injective (ultrafilterOperator S.koopmanRep p)) :
    Function.Injective (ultrafilterOperator S.koopmanZeroRep p) := by
  have hSub : Intertwines S.koopmanZeroRep S.koopmanRep (meanZero S.measure).subtypeL :=
    fun _ _ => rfl
  intro f g he
  apply Subtype.ext
  apply h
  exact (hSub.ultrafilter p f).symm.trans
    ((congrArg (meanZero S.measure).subtypeL he).trans (hSub.ultrafilter p g))

/-- The generation and spectral-disjointness conclusions of Proposition 7(i). -/
theorem proposition7_i_consequences (S : System G X) (p : Ultrafilter G)
    {α : ℝ} (hα : 1 / 2 < α) (h : S.IsPartiallyRigidAlong p α) :
    S.generatedSigma {p} = (inferInstance : MeasurableSpace X) ∧
      ∀ {Y : Type*} [MeasurableSpace Y] (T : System G Y), T.IsUMixing {p} →
        SpectrallyDisjoint S.koopmanZeroRep T.koopmanZeroRep :=
  S.generated_and_spectrallyDisjoint_of_injective_limit p
    (S.injective_meanZero_limit_of_injective_full p (proposition7_i S p hα h))

end Mixing
