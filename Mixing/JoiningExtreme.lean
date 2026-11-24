/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.BoundedKoopman
public import Mixing.SystemMixing
public import Mixing.WeakMixingBridge

/-! # The product joining of a weakly mixing system is extreme -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

namespace Mixing

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]

/-- An extreme point of the convex set of joinings of the two fixed systems. -/
def IsExtremeJoining (T : System G X) (S : System G Y) (τ : Measure (X × Y)) : Prop :=
  IsJoining T S τ ∧
    ∀ μ₁ μ₂, IsJoining T S μ₁ → IsJoining T S μ₂ →
      ∀ (a : ℝ≥0∞), 0 < a → a < 1 → a • μ₁ + (1 - a) • μ₂ = τ → μ₁ = τ ∧ μ₂ = τ

private noncomputable def changeMeasureCLM {W : Type*} [MeasurableSpace W]
    {μ ν : Measure W} {C : ℝ≥0∞} (hC : C ≠ ∞) (hμν : μ ≤ C • ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ where
  toFun := Lp.LpToLpOfMeasureLeSMul hC hμν
  map_add' := map_add (Lp.LpToLpOfMeasureLeSMul hC hμν)
  map_smul' k v := by
    apply Lp.ext
    have hn := Measure.absolutelyContinuous_of_le_smul hμν
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hC hμν (k • v),
      Lp.coeFn_LpToLpOfMeasureLeSMul hC hμν v,
      Lp.coeFn_smul k (Lp.LpToLpOfMeasureLeSMul hC hμν v),
      hn.ae_eq (Lp.coeFn_smul k v)] with x hv₁ hv₂ h₁ h₂
    simp only [RingHom.id_apply]
    rw [hv₁, h₁, h₂, Pi.smul_apply, Pi.smul_apply, hv₂]
  cont := (Lp.LpToLpOfMeasureLeSMul hC hμν).continuous

private theorem changeMeasureCLM_ae {W : Type*} [MeasurableSpace W]
    {μ ν : Measure W} {C : ℝ≥0∞} (hC : C ≠ ∞) (hμν : μ ≤ C • ν) (v : Lp ℂ 2 ν) :
    changeMeasureCLM hC hμν v =ᵐ[μ] v :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hC hμν v

private def observableTensor (f : BoundedObservable X) (F : BoundedObservable Y) :
    BoundedObservable (X × Y) :=
  (f.comp Prod.fst measurable_fst).mul (F.comp Prod.snd measurable_snd)

private theorem dominated_joining_centered_integral
    {T : System G X} {S : System G Y} {τ : Measure (X × Y)}
    (hτ : IsJoining T S τ) {ν : Measure Y} [IsProbabilityMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hDom : τ ≤ C • T.measure.prod ν)
    (p : Ultrafilter G) (hMix : T.IsUMixing {p})
    (f : BoundedObservable X) (F : BoundedObservable Y)
    (hMean : ∫ x, f x ∂T.measure = 0) :
    (∫ w, f w.1 * F w.2 ∂τ) = 0 := by
  let := hτ.probability
  let ρ := T.measure.prod ν
  let B (g : G) := observableTensor (T.translated g f) (S.translated g F)
  let x (g : G) := (B g).l2 ρ
  have hNorm (g : G) : ‖x g‖ ≤ f.bound * F.bound := (B g).norm_l2_le ρ
  have hCorr : Tendsto (fun v : G × G => inner ℂ (x v.1) (x v.2))
      (fubiniUltrafilter p p : Filter _) (𝓝 0) := by
    apply tendsto_fubiniUltrafilter (g := fun _ => 0) _ tendsto_const_nhds
    intro r
    have hT := (System.hasMixingCorrelations hMix) p (by simp) (T.translated r f) f
    have hT' : Tendsto (fun g => ∫ a, conj (f (T.act r a)) * f (T.act g a) ∂T.measure)
        (p : Filter G) (𝓝 0) := by
      simpa only [System.translated_apply, hMean, mul_zero] using hT
    have hSBound (g : G) :
        ‖∫ b, conj (F (S.act r b)) * F (S.act g b) ∂ν‖ ≤ F.bound * F.bound :=
      (((S.translated r F).conjugate).mul (S.translated g F)).norm_integral_le ν
    have hLim := hT'.zero_mul_isBoundedUnder_le
      ⟨_, eventually_map.mpr (Eventually.of_forall hSBound)⟩
    have hEq (g : G) :
        inner ℂ (x r) (x g) =
          (∫ a, conj (f (T.act r a)) * f (T.act g a) ∂T.measure) *
          ∫ b, conj (F (S.act r b)) * F (S.act g b) ∂ν := by
      rw [show x r = (B r).l2 ρ from rfl, show x g = (B g).l2 ρ from rfl,
        BoundedObservable.inner_l2, ← integral_prod_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun w => by
        simp only [B, observableTensor, BoundedObservable.mul_apply, BoundedObservable.comp_apply,
          System.translated_apply, map_mul]
        ring
    simpa only [hEq] using hLim
  let L := changeMeasureCLM hC hDom
  let e := (BoundedObservable.const (1 : ℂ) : BoundedObservable (X × Y)).l2 τ
  have hL := tendsto_inner_zero_of_fubini_correlations_single p x hNorm hCorr (L.adjoint e)
  have hEq (g : G) : inner ℂ (L.adjoint e) (x g) = ∫ w, B g w ∂τ := by
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
    apply integral_congr_ae
    have hx : x g =ᵐ[τ] B g :=
      (Measure.absolutelyContinuous_of_le_smul hDom).ae_eq ((B g).coe_l2 ρ)
    filter_upwards [(BoundedObservable.const (1 : ℂ) : BoundedObservable (X × Y)).coe_l2 τ,
      changeMeasureCLM_ae hC hDom (x g), hx] with w he hLx hxx
    change e w = _ at he
    change (L (x g)) w = _ at hLx
    rw [he, hLx, hxx, RCLike.inner_apply']
    simp
  have hInv (g : G) : (∫ w, B g w ∂τ) = ∫ w, f w.1 * F w.2 ∂τ :=
    (observableTensor f F).integral_comp_of_preserving (hτ.invariant g)
  have hConstant : Tendsto (fun _ : G => ∫ w, f w.1 * F w.2 ∂τ) (p : Filter G) (𝓝 0) := by
    simpa only [hEq, hInv] using hL
  exact tendsto_nhds_unique tendsto_const_nhds hConstant

private theorem dominated_joining_integral_mul
    {T : System G X} {S : System G Y} {τ : Measure (X × Y)}
    (hτ : IsJoining T S τ) {ν : Measure Y} [IsProbabilityMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hDom : τ ≤ C • T.measure.prod ν)
    (p : Ultrafilter G) (hMix : T.IsUMixing {p})
    (f : BoundedObservable X) (F : BoundedObservable Y) :
    (∫ w, f w.1 * F w.2 ∂τ) =
      (∫ x, f x ∂T.measure) * ∫ y, F y ∂S.measure := by
  let := hτ.probability
  let c := ∫ x, f x ∂T.measure
  let d := f.sub (BoundedObservable.const c)
  have hMean : ∫ x, d x ∂T.measure = 0 := by
    change (∫ x : X, f x - c ∂T.measure) = 0
    have hf : Integrable (fun x => f x) T.measure := f.integrable _
    rw [integral_sub hf (integrable_const c)]
    simp [c]
  have h0 := dominated_joining_centered_integral hτ hC hDom p hMix d F hMean
  change (∫ w : X × Y, (f w.1 - c) * F w.2 ∂τ) = 0 at h0
  simp_rw [sub_mul] at h0
  have h₁ : Integrable (fun w : X × Y => f w.1 * F w.2) τ :=
    (observableTensor f F).integrable τ
  have h₂ : Integrable (fun w : X × Y => c * F w.2) τ :=
    (observableTensor (BoundedObservable.const c) F).integrable τ
  rw [integral_sub h₁ h₂, integral_const_mul, F.integral_comp_of_preserving hτ.snd] at h0
  exact sub_eq_zero.mp h0

private noncomputable def rectangleIndicator {W : Type*} [MeasurableSpace W]
    (s : Set W) (hs : MeasurableSet s) : BoundedObservable W where
  toFun := s.indicator (fun _ => 1)
  measurable := measurable_const.indicator hs
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    classical
    by_cases h : x ∈ s <;> simp [h]

/-- Domination by a product with the mixing system's marginal forces independence.
The second probability in the dominating product may be any probability on the
second coordinate space. -/
theorem dominated_joining_eq_prod_of_reference
    {T : System G X} {S : System G Y} {τ : Measure (X × Y)}
    (hτ : IsJoining T S τ) {ν : Measure Y} [IsProbabilityMeasure ν]
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hDom : τ ≤ C • T.measure.prod ν)
    (p : Ultrafilter G) (hMix : T.IsUMixing {p}) : τ = T.measure.prod S.measure := by
  let := hτ.probability
  apply Measure.ext_prod
  intro a b ha hb
  classical
  have h := dominated_joining_integral_mul hτ hC hDom p hMix
    (rectangleIndicator a ha) (rectangleIndicator b hb)
  have he : (fun w : X × Y => rectangleIndicator a ha w.1 * rectangleIndicator b hb w.2) =
      (a ×ˢ b).indicator (fun _ => (1 : ℂ)) := by
    funext w
    by_cases h₁ : w.1 ∈ a <;> by_cases h₂ : w.2 ∈ b <;>
      simp [rectangleIndicator, h₁, h₂]
  rw [he] at h
  change (∫ w : X × Y, (a ×ˢ b).indicator (fun _ => (1 : ℂ)) w ∂τ) =
    (∫ x, a.indicator (fun _ => (1 : ℂ)) x ∂T.measure) *
      ∫ y, b.indicator (fun _ => (1 : ℂ)) y ∂S.measure at h
  rw [integral_indicator_const _ (ha.prod hb), integral_indicator_const _ ha,
    integral_indicator_const _ hb] at h
  have hRe := congrArg Complex.re h
  simp only [Complex.real_smul, mul_one, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hRe
  have hReal : (τ (a ×ˢ b)).toReal = ((T.measure.prod S.measure) (a ×ˢ b)).toReal := by
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    exact hRe
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using congrArg ENNReal.ofReal hReal

/-- A joining dominated by a finite multiple of the product is the product when
one coordinate is mixing along an ultrafilter. -/
theorem dominated_joining_eq_prod
    {T : System G X} {S : System G Y} {τ : Measure (X × Y)}
    (hτ : IsJoining T S τ) {C : ℝ≥0∞} (hC : C ≠ ∞) (hDom : τ ≤ C • T.measure.prod S.measure)
    (p : Ultrafilter G) (hMix : T.IsUMixing {p}) : τ = T.measure.prod S.measure :=
  dominated_joining_eq_prod_of_reference hτ hC hDom p hMix

/-- An upper bound on a measure scaled by a finite positive constant. -/
theorem le_inv_smul_of_smul_le {W : Type*} [MeasurableSpace W]
    {a : ℝ≥0∞} (ha₀ : a ≠ 0) (haTop : a ≠ ∞) {μ ν : Measure W} (h : a • μ ≤ ν) :
    μ ≤ a⁻¹ • ν := by
  calc
    μ = a⁻¹ • (a • μ) := by rw [smul_smul, ENNReal.inv_mul_cancel ha₀ haTop, one_smul]
    _ ≤ _ := by gcongr

/-- A weakly mixing system is mixing along some ultrafilter. -/
theorem System.exists_isUMixing_singleton [Countable G] {T : System G X}
    (hWeak : IsWeaklyMixing T.koopmanZeroRep) : ∃ p : Ultrafilter G, T.IsUMixing {p} := by
  obtain ⟨F, hF⟩ := exists_isFolnerSequence (G := G)
  have hPos : HasPositiveFolnerDensity (univ : Set G) := by
    refine ⟨F, hF, 1, zero_lt_one, Eventually.frequently (Eventually.of_forall fun n => ?_)⟩
    have hCard : (F n).card ≠ 0 := (hF.1 n).card_ne_zero
    simp [finsetDensity, hCard]
  obtain ⟨p, hp, _⟩ := exists_essentialUltrafilter_mem_of_hasPositiveFolnerDensity hPos
  refine ⟨p, fun q hq => ?_⟩
  have hqp : q = p := Set.mem_singleton_iff.mp hq
  subst q
  exact isUMixing_essential_of_isWeaklyMixing T.koopmanZeroRep hWeak p hp

/-- Lemma 3. A weakly mixing system and an arbitrary second system have an extreme
product joining. The proof uses domination of the measures in a convex decomposition. -/
theorem lemma3 [Countable G] {T : System G X} (S : System G Y)
    (hWeak : IsWeaklyMixing T.koopmanZeroRep) :
    IsExtremeJoining T S (T.measure.prod S.measure) := by
  obtain ⟨p, hMix⟩ := System.exists_isUMixing_singleton hWeak
  refine ⟨product_isJoining T S, fun μ₁ μ₂ h₁ h₂ a ha₀ ha₁ he => ?_⟩
  have h₁le : a • μ₁ ≤ T.measure.prod S.measure := by
    rw [← he]
    apply Measure.le_iff'.mpr
    intro A
    rw [add_apply]
    exact le_self_add
  have h₂le : (1 - a) • μ₂ ≤ T.measure.prod S.measure := by
    rw [← he]
    apply Measure.le_iff'.mpr
    intro A
    rw [add_apply]
    exact le_add_self
  have hb₀ : 1 - a ≠ 0 := (tsub_pos_of_lt ha₁).ne'
  have hbTop : 1 - a ≠ ∞ := (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
  refine ⟨dominated_joining_eq_prod h₁ (ENNReal.inv_ne_top.mpr ha₀.ne')
    (le_inv_smul_of_smul_le ha₀.ne' (ha₁.trans ENNReal.one_lt_top).ne h₁le) p hMix,
    dominated_joining_eq_prod h₂ (ENNReal.inv_ne_top.mpr hb₀)
      (le_inv_smul_of_smul_le hb₀ hbTop h₂le) p hMix⟩

end Mixing
