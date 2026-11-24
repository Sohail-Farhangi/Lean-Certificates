/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EventMixing
public import Mixing.InjectiveLimits
public import Mixing.PartialRigidity
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Partial mixing of event correlations -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Mixing

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- The α-weak-mixing equality in Definition 2, with Koopman pullback on events. -/
def System.IsAlphaWeaklyMixingAlong (S : System G X) (p : Ultrafilter G) (α : ℝ) : Prop :=
  ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun g => S.measure.real (A ∩ S.act g ⁻¹' B)) (p : Filter G)
      (𝓝 (α * S.measure.real A * S.measure.real B + (1 - α) * S.measure.real (A ∩ B)))

/-- The β-partial-mixing inequality in Definition 2. The real coefficient on the
right is the ultrafilter limit of the event correlations. -/
def System.IsPartiallyMixingAlong (S : System G X) (p : Ultrafilter G) (β : ℝ) : Prop :=
  ∀ (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B),
    β * S.measure.real A * S.measure.real B ≤
      (inner ℂ (eventVector S hA) (ultrafilterOperator S.koopmanRep p (eventVector S hB))).re

/-- The global liminf version of partial mixing in Definition 2. -/
def System.IsPartiallyMixing (S : System G X) (β : ℝ) : Prop :=
  ∀ (A B : Set X), MeasurableSet A → MeasurableSet B →
    β * S.measure.real A * S.measure.real B ≤
      liminf (fun g => S.measure.real (A ∩ S.act g ⁻¹' B)) cofinite

/-- The ultrafilter limit of the real event correlation is its real matrix coefficient. -/
theorem System.tendsto_event_correlation (S : System G X) (p : Ultrafilter G)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun g => S.measure.real (A ∩ S.act g ⁻¹' B)) (p : Filter G)
      (𝓝 (inner ℂ (eventVector S hA) (ultrafilterOperator S.koopmanRep p
        (eventVector S hB))).re) := by
  simpa only [Function.comp_def, koopman_event_coeff, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto _).comp
      (tendsto_ultrafilterOperator_coeff S.koopmanRep p (eventVector S hA) (eventVector S hB))

/-- A direct comparison with the scalar ultrafilter limit in Definition 2. -/
theorem System.isPartiallyMixingAlong_iff_scalarUltralimit (S : System G X)
    (p : Ultrafilter G) (β : ℝ) :
    S.IsPartiallyMixingAlong p β ↔
      ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
        β * S.measure.real A * S.measure.real B ≤
          scalarUltralimit p (fun g => S.measure.real (A ∩ S.act g ⁻¹' B)) := by
  unfold System.IsPartiallyMixingAlong
  constructor
  · intro h A B hA hB
    rw [scalarUltralimit, (S.tendsto_event_correlation p hA hB).limUnder_eq]
    exact h A B hA hB
  · intro h A B hA hB
    have hAB := h A B hA hB
    simpa only [scalarUltralimit, (S.tendsto_event_correlation p hA hB).limUnder_eq] using hAB

/-- Partial mixing bounds the image of each event below by the corresponding
constant multiple of its probability. -/
theorem System.ae_event_dominated_of_partialMixing (S : System G X)
    (p : Ultrafilter G) (β : ℝ) (h : S.IsPartiallyMixingAlong p β)
    {B : Set X} (hB : MeasurableSet B) :
    ∀ᵐ x ∂S.measure, β * S.measure.real B ≤
      ((ultrafilterOperator S.koopmanRep p (eventVector S hB)) x).re := by
  let v := ultrafilterOperator S.koopmanRep p (eventVector S hB)
  have hIntegrable : Integrable (fun x => v x) S.measure :=
    (Lp.memLp v).integrable (by norm_num)
  apply ae_le_of_forall_setIntegral_le (integrable_const _) hIntegrable.re
  intro A hA _
  have hAB := h A B hA hB
  change β * S.measure.real A * S.measure.real B ≤ (inner ℂ (eventVector S hA) v).re at hAB
  rw [eventVector, L2.inner_indicatorConstLp_one] at hAB
  change _ ≤ RCLike.re (∫ x in A, v x ∂S.measure) at hAB
  rw [← integral_re (hIntegrable.integrableOn)] at hAB
  rw [setIntegral_const, smul_eq_mul]
  convert hAB using 1
  ring

/-- Reversing the group elements exchanges the two events in partial mixing. -/
theorem System.isPartiallyMixingAlong_inverse (S : System G X)
    (p : Ultrafilter G) (β : ℝ) (h : S.IsPartiallyMixingAlong p β) :
    S.IsPartiallyMixingAlong (inverseUltrafilter p) β := by
  intro A B hA hB
  rw [ultrafilterOperator_inverse, ContinuousLinearMap.adjoint_inner_right]
  have he : (inner ℂ (ultrafilterOperator S.koopmanRep p (eventVector S hA))
        (eventVector S hB)).re =
      (inner ℂ (eventVector S hB) (ultrafilterOperator S.koopmanRep p (eventVector S hA))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  rw [mul_assoc, mul_comm (S.measure.real A), ← mul_assoc]
  exact h B A hB hA

/-- The partial-mixing lower bound extends from indicators to every nonnegative
real-valued vector in complex L². -/
theorem System.ae_re_dominated_of_partialMixing (S : System G X)
    (p : Ultrafilter G) (β : ℝ) (h : S.IsPartiallyMixingAlong p β)
    (f : Lp ℂ 2 S.measure) (hfReal : ∀ᵐ x ∂S.measure, (f x).im = 0)
    (hfNonneg : ∀ᵐ x ∂S.measure, 0 ≤ (f x).re) :
    ∀ᵐ x ∂S.measure, β * (∫ y, f y ∂S.measure).re ≤
      ((ultrafilterOperator S.koopmanRep p f) x).re := by
  let Q := ultrafilterOperator S.koopmanRep p
  have hFInt : Integrable (fun x => f x) S.measure := (Lp.memLp f).integrable (by norm_num)
  have hQInt : Integrable (fun x => Q f x) S.measure := (Lp.memLp (Q f)).integrable (by norm_num)
  apply ae_le_of_forall_setIntegral_le (integrable_const _) hQInt.re
  intro A hA _
  have hAdj := S.ae_event_dominated_of_partialMixing (inverseUltrafilter p) β
    (S.isPartiallyMixingAlong_inverse p β h) hA
  rw [ultrafilterOperator_inverse] at hAdj
  let v := Q.adjoint (eventVector S hA)
  have hBoth := L2.integrable_inner (𝕜 := ℂ) v f
  have hIntegral :
      (∫ x, β * S.measure.real A * (f x).re ∂S.measure) ≤
        ∫ x, RCLike.re (inner ℂ (v x) (f x)) ∂S.measure := by
    apply integral_mono_ae (hFInt.re.const_mul _) hBoth.re
    filter_upwards [hAdj, hfReal, hfNonneg] with x hAx hIm hRe
    change β * S.measure.real A ≤ (v x).re at hAx
    change _ ≤ (inner ℂ (v x) (f x)).re
    rw [RCLike.inner_apply', Complex.mul_re, Complex.conj_re, hIm, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_right hAx hRe
  have hFReal : (∫ x, (f x).re ∂S.measure) = (∫ x, f x ∂S.measure).re := integral_re hFInt
  rw [integral_const_mul, hFReal, integral_re hBoth, ← L2.inner_def] at hIntegral
  change _ ≤ RCLike.re (inner ℂ (Q.adjoint (eventVector S hA)) f) at hIntegral
  rw [ContinuousLinearMap.adjoint_inner_left, eventVector, L2.inner_indicatorConstLp_one,
    ← integral_re hQInt.integrableOn] at hIntegral
  rw [setIntegral_const, smul_eq_mul]
  convert hIntegral using 1
  ring

/-- The scalar correlation identity determines the full Koopman operator. -/
theorem System.ultrafilterOperator_eq_of_alphaWeaklyMixing (S : System G X)
    (p : Ultrafilter G) (α : ℝ) (h : S.IsAlphaWeaklyMixingAlong p α) :
    ultrafilterOperator S.koopmanRep p =
      (α : ℂ) • InnerProductSpace.rankOne ℂ (constantOne S.measure) (constantOne S.measure) +
        ((1 - α : ℝ) : ℂ) • (1 : Lp ℂ 2 S.measure →L[ℂ] Lp ℂ 2 S.measure) := by
  apply sub_eq_zero.mp
  apply zero_of_event_coefficients S
  intro A B hA hB
  let c := constantOne S.measure
  let Q := ultrafilterOperator S.koopmanRep p
  let a := eventVector S hA
  let b := eventVector S hB
  have hCoeff :
      inner ℂ a (Q b) =
        ((α * S.measure.real A * S.measure.real B + (1 - α) * S.measure.real (A ∩ B) : ℝ) : ℂ) := by
    have hLim := tendsto_ultrafilterOperator_coeff S.koopmanRep p a b
    simp only [a, b, koopman_event_coeff] at hLim
    exact tendsto_nhds_unique hLim ((Complex.continuous_ofReal.tendsto _).comp (h A B hA hB))
  have hLeft : inner ℂ a c = (S.measure.real A : ℂ) := by
    rw [← inner_conj_symm, inner_constantOne_left, integral_eventVector, Complex.conj_ofReal]
  have hRight : inner ℂ c b = (S.measure.real B : ℂ) := by
    rw [inner_constantOne_left, integral_eventVector]
  have hInter : inner ℂ a b = (S.measure.real (A ∩ B) : ℂ) :=
    L2.inner_indicatorConstLp_one_indicatorConstLp_one _ _
  change inner ℂ a ((Q - ((α : ℂ) • InnerProductSpace.rankOne ℂ c c +
    ((1 - α : ℝ) : ℂ) • 1)) b) = 0
  simp only [sub_apply, add_apply, smul_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply,
    inner_sub_right, inner_add_right, inner_smul_right,
    hCoeff, hLeft, hRight, hInter]
  push_cast
  ring

/-- The α-weak-mixing limit on mean-zero L² is scalar multiplication. -/
theorem System.ultrafilterOperator_zero_eq_of_alphaWeaklyMixing (S : System G X)
    (p : Ultrafilter G) (α : ℝ) (h : S.IsAlphaWeaklyMixingAlong p α) :
    ultrafilterOperator S.koopmanZeroRep p =
      ((1 - α : ℝ) : ℂ) • (1 : meanZero S.measure →L[ℂ] meanZero S.measure) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  have hlim := tendsto_ultrafilterOperator_coeff S.koopmanZeroRep p g f
  have hFull := tendsto_ultrafilterOperator_coeff S.koopmanRep p (g : Lp ℂ 2 S.measure)
    (f : Lp ℂ 2 S.measure)
  have hf : inner ℂ (constantOne S.measure) (f : Lp ℂ 2 S.measure) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp f.property
  rw [S.ultrafilterOperator_eq_of_alphaWeaklyMixing p α h] at hFull
  simp only [add_apply, smul_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply, hf, zero_smul,
    smul_zero, zero_add] at hFull
  exact tendsto_nhds_unique hlim hFull

/-- Proposition 7(ii), for the α-weak-mixing range 0 ≤ α < 1. -/
theorem proposition7_ii (S : System G X) (p : Ultrafilter G) {α : ℝ}
    (hα : α < 1) (h : S.IsAlphaWeaklyMixingAlong p α) :
    Function.Injective (ultrafilterOperator S.koopmanZeroRep p) :=
  injective_of_partialWeakMixing hα (S.ultrafilterOperator_zero_eq_of_alphaWeaklyMixing p α h)

/-- The generation and spectral-disjointness conclusions of Proposition 7(ii). -/
theorem proposition7_ii_consequences (S : System G X) (p : Ultrafilter G)
    {α : ℝ} (hα : α < 1) (h : S.IsAlphaWeaklyMixingAlong p α) :
    S.generatedSigma {p} = (inferInstance : MeasurableSpace X) ∧
      ∀ {Y : Type*} [MeasurableSpace Y] (T : System G Y), T.IsUMixing {p} →
        SpectrallyDisjoint S.koopmanZeroRep T.koopmanZeroRep :=
  S.generated_and_spectrallyDisjoint_of_injective_limit p (proposition7_ii S p hα h)

end Mixing
