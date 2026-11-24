/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.GeneratedClosure
public import Mixing.JoiningExtreme
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology

variable {G X Y Z : Type*} [CommGroup G]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- A finite family of L² vectors whose translates are linear combinations
of the family, with uniformly bounded measurable coefficients on the base.
In particular, the coordinates of a measurable unitary cocycle have this
uniform bound. -/
structure RelativeFiniteFrame {E : System G Z} {B : System G Y}
    (π : FactorMap E B) (n : ℕ) where
  vector : Fin n → Lp ℂ 2 E.measure
  coefficient : G → Fin n → Fin n → BoundedObservable Y
  bound : ℝ
  norm_bound : ∀ g i j, (coefficient g i j).bound ≤ bound
  translate : ∀ g i, ∀ᵐ z ∂E.measure, vector i (E.act g z) =
    ∑ j, coefficient g i j (π.toFun z) * vector j z

/-- A measurable unitary coefficient matrix provides a relative frame with
entry bound one. -/
def RelativeFiniteFrame.ofUnitaryCoefficients {E : System G Z} {B : System G Y}
    {π : FactorMap E B} {n : ℕ}
    (v : Fin n → Lp ℂ 2 E.measure) (C : G → Y → Matrix (Fin n) (Fin n) ℂ)
    (hMeas : ∀ g i j, Measurable (fun y => C g y i j))
    (hUnitary : ∀ g y, C g y ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hTranslate : ∀ g i, ∀ᵐ z ∂E.measure, v i (E.act g z) =
      ∑ j, C g (π.toFun z) i j * v j z) :
    RelativeFiniteFrame π n where
  vector := v
  coefficient g i j :=
    ⟨fun y => C g y i j, hMeas g i j, 1, zero_le_one,
      fun y => entry_norm_bound_of_unitary (hUnitary g y) i j⟩
  bound := 1
  norm_bound _ _ _ := le_rfl
  translate := hTranslate

/-- Multiplication by a bounded observable acts pointwise almost everywhere. -/
theorem BoundedObservable.ae_mulL2 (b : BoundedObservable Z) {μ : Measure Z} [IsFiniteMeasure μ]
    (v : Lp ℂ 2 μ) : b.mulL2 μ v =ᵐ[μ] fun z => b z * v z := by
  have hMul := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((b.memLp μ ⊤).toLp b) v
  change b.mulL2 μ v =ᵐ[μ] _ at hMul
  filter_upwards [hMul, (b.memLp μ ⊤).coeFn_toLp] with z hz hb
  rw [hz, hb]
  rfl

private def frameTensor (f : BoundedObservable X) (b : BoundedObservable Y) :
    BoundedObservable (X × Y) :=
  (f.comp Prod.fst measurable_fst).mul (b.comp Prod.snd measurable_snd)

/-- A centered translate multiplied by an arbitrary uniformly bounded
observable of the independent second coordinate tends weakly to zero. -/
private theorem tendsto_centered_tensor {R : System G X} {B : System G Y}
    (p : Ultrafilter G) (hMix : R.IsUMixing {p}) (f : BoundedObservable X)
    (hMean : ∫ x, f x ∂R.measure = 0) (b : G → BoundedObservable Y)
    {C : ℝ} (hC : ∀ g, (b g).bound ≤ C) (v : Lp ℂ 2 (R.prod B).measure) :
    Tendsto (fun g => inner ℂ v ((frameTensor (R.translated g f) (b g)).l2 (R.prod B).measure))
      (p : Filter G) (𝓝 0) := by
  let ν := (R.prod B).measure
  let x (g : G) := (frameTensor (R.translated g f) (b g)).l2 ν
  have hNorm (g : G) : ‖x g‖ ≤ f.bound * C :=
    ((frameTensor (R.translated g f) (b g)).norm_l2_le ν).trans
      (mul_le_mul_of_nonneg_left (hC g) f.bound_nonneg)
  apply tendsto_inner_zero_of_fubini_correlations_single p x hNorm _ v
  apply tendsto_fubiniUltrafilter (g := fun _ => 0) _ tendsto_const_nhds
  intro r
  have hR := (System.hasMixingCorrelations hMix) p (by simp) (R.translated r f) f
  have hR' : Tendsto (fun g => ∫ a, conj (f (R.act r a)) * f (R.act g a) ∂R.measure)
      (p : Filter G) (𝓝 0) := by
    simpa only [System.translated_apply, hMean, mul_zero] using hR
  have hBound (g : G) : ‖∫ y, conj (b r y) * b g y ∂B.measure‖ ≤ (b r).bound * C :=
    (((b r).conjugate.mul (b g)).norm_integral_le B.measure).trans
      (mul_le_mul_of_nonneg_left (hC g) (b r).bound_nonneg)
  have hLim := hR'.zero_mul_isBoundedUnder_le
    ⟨_, eventually_map.mpr (Eventually.of_forall hBound)⟩
  have hEq (g : G) :
      inner ℂ (x r) (x g) =
        (∫ a, conj (f (R.act r a)) * f (R.act g a) ∂R.measure) *
          ∫ y, conj (b r y) * b g y ∂B.measure := by
    rw [show x r = (frameTensor (R.translated r f) (b r)).l2 ν from rfl,
      show x g = (frameTensor (R.translated g f) (b g)).l2 ν from rfl,
      BoundedObservable.inner_l2, ← integral_prod_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by
      simp only [frameTensor, BoundedObservable.mul_apply, BoundedObservable.comp_apply,
        System.translated_apply, map_mul]
      ring
  simpa only [hEq] using hLim

/-- A relative frame slot, multiplied by a bounded base observable, has zero
correlation in every joining with a centered observable of a mixing system
that is disjoint from the base. -/
theorem integral_centered_relativeFiniteFrame
    {R : System G X} {B : System G Y} {E : System G Z} {π : FactorMap E B}
    {n : ℕ} (A : RelativeFiniteFrame π n) (i : Fin n) {τ : Measure (X × Z)}
    (hτ : IsJoining R E τ) (hDisjoint : Disjoint R B)
    (p : Ultrafilter G) (hMix : R.IsUMixing {p}) (f : BoundedObservable X)
    (hMean : ∫ x, f x ∂R.measure = 0) (b : BoundedObservable Y) :
    (∫ w, conj (f w.1) * b (π.toFun w.2) * A.vector i w.2 ∂τ) = 0 := by
  let := hτ.probability
  let ρ := (R.prod B).measure
  let F := Prod.map (id : X → X) π.toFun
  let idR : FactorMap R R := ⟨id, MeasurePreserving.id _, fun _ => rfl⟩
  have hF : MeasurePreserving F τ ρ := ⟨measurable_id.prodMap π.preserves.measurable,
    hDisjoint _ (hτ.map idR π)⟩
  let L : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 τ :=
    (Lp.compMeasurePreservingₗᵢ ℂ F hF).toContinuousLinearMap
  let V (j : Fin n) := Lp.compMeasurePreserving Prod.snd hτ.snd (A.vector j)
  let c (j : Fin n) (g : G) := ((B.translated g b).mul (A.coefficient g i j)).conjugate
  let x (j : Fin n) (g : G) := frameTensor (R.translated g f) (c j g)
  have hLim (j : Fin n) : Tendsto (fun g => inner ℂ (L ((x j g).l2 ρ)) (V j))
      (p : Filter G) (𝓝 0) := by
    have hc (g : G) : (c j g).bound ≤ b.bound * A.bound :=
      mul_le_mul_of_nonneg_left (A.norm_bound g i j) b.bound_nonneg
    have h := tendsto_centered_tensor p hMix f hMean (c j) hc (L.adjoint (V j))
    have h' := (Complex.continuous_conj.tendsto (0 : ℂ)).comp h
    simpa only [Function.comp_def, map_zero, ContinuousLinearMap.adjoint_inner_left,
      inner_conj_symm] using h'
  have hFinite : Tendsto (fun g => ∑ j, inner ℂ (L ((x j g).l2 ρ)) (V j))
      (p : Filter G) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hLim j)
  let term (g : G) (j : Fin n) (w : X × Z) : ℂ :=
    conj (f (R.act g w.1)) * b (B.act g (π.toFun w.2)) *
      (A.coefficient g i j (π.toFun w.2) * A.vector j w.2)
  have hTerm (g : G) (j : Fin n) :
      (fun w => inner ℂ (L ((x j g).l2 ρ) w) (V j w)) =ᵐ[τ] term g j := by
    have hx := (Lp.coeFn_compMeasurePreserving ((x j g).l2 ρ) hF).trans
      (hF.quasiMeasurePreserving.ae_eq_comp ((x j g).coe_l2 ρ))
    have hv := Lp.coeFn_compMeasurePreserving (A.vector j) hτ.snd
    filter_upwards [hx, hv] with w hw hz
    change L ((x j g).l2 ρ) w = x j g (F w) at hw
    change V j w = A.vector j w.2 at hz
    rw [hw, hz, RCLike.inner_apply']
    simp only [x, c, term, frameTensor, F, BoundedObservable.mul_apply,
      BoundedObservable.comp_apply, BoundedObservable.conjugate_apply, System.translated_apply,
      Prod.map_fst, Prod.map_snd, id_eq, map_mul, starRingEnd_self_apply]
    ring
  have hTermsInt (g : G) (j : Fin n) : Integrable (term g j) τ :=
    (L2.integrable_inner (𝕜 := ℂ) (L ((x j g).l2 ρ)) (V j)).congr (hTerm g j)
  let I (w : X × Z) : ℂ := conj (f w.1) * b (π.toFun w.2) * A.vector i w.2
  have hI : Measurable I :=
    (((f.conjugate.measurable.comp measurable_fst).mul
      (b.measurable.comp (π.preserves.measurable.comp measurable_snd))).mul
      ((Lp.stronglyMeasurable (A.vector i)).measurable.comp measurable_snd))
  have hEval (g : G) : (∫ w, I w ∂τ) = ∑ j, inner ℂ (L ((x j g).l2 ρ)) (V j) := by
    have hShift := integral_map (μ := τ)
      (hτ.invariant g).measurable.aemeasurable hI.aestronglyMeasurable
    rw [(hτ.invariant g).map_eq] at hShift
    calc
      _ = ∫ w, I (R.prodAct E g w) ∂τ := hShift
      _ = ∫ w, ∑ j, term g j w ∂τ := by
        apply integral_congr_ae
        filter_upwards [hτ.snd.quasiMeasurePreserving.ae (A.translate g i)] with w hw
        have he : π.toFun (E.act g w.2) = B.act g (π.toFun w.2) := congrFun (π.equivariant g) w.2
        change conj (f (R.act g w.1)) * b (π.toFun (E.act g w.2)) * A.vector i (E.act g w.2) =
          ∑ j, term g j w
        rw [he, hw, Finset.mul_sum]
      _ = ∑ j, ∫ w, term g j w ∂τ := integral_finsetSum _ (fun j _ => hTermsInt g j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [L2.inner_def]
        exact (integral_congr_ae (hTerm g j)).symm
  have hConst : Tendsto (fun _ : G => ∫ w, I w ∂τ) (p : Filter G) (𝓝 0) := by
    simpa only [← hEval] using hFinite
  exact tendsto_nhds_unique tendsto_const_nhds hConst

/-- Products of slots in bounded-coefficient relative frames with arbitrary
bounded functions of the base. -/
def FactorMap.relativeFrameGenerators {E : System G Z} {B : System G Y} (π : FactorMap E B) :
    Set (Lp ℂ 2 E.measure) :=
  {v | ∃ (n : ℕ) (A : RelativeFiniteFrame π n) (i : Fin n) (b : BoundedObservable Y),
    v = (b.comp π.toFun π.preserves.measurable).mulL2 E.measure (A.vector i)}

/-- The relative finite-frame spanning condition on an extension. -/
def FactorMap.HasDenseRelativeFrames {E : System G Z} {B : System G Y} (π : FactorMap E B) :
    Prop :=
  Dense (Submodule.span ℂ π.relativeFrameGenerators : Set (Lp ℂ 2 E.measure))

private theorem integral_centered_of_dense_relativeFrames
    {R : System G X} {B : System G Y} {E : System G Z} {π : FactorMap E B}
    (hDense : π.HasDenseRelativeFrames) {τ : Measure (X × Z)}
    (hτ : IsJoining R E τ) (hDisjoint : Disjoint R B)
    (p : Ultrafilter G) (hMix : R.IsUMixing {p})
    (f : BoundedObservable X) (hMean : ∫ x, f x ∂R.measure = 0) (v : Lp ℂ 2 E.measure) :
    (∫ w, conj (f w.1) * v w.2 ∂τ) = 0 := by
  let := hτ.probability
  let u := hτ.fstFactor.pullback (f.l2 R.measure)
  let Ψ : Lp ℂ 2 E.measure →L[ℂ] ℂ :=
    (InnerProductSpace.toDual ℂ _ u).comp hτ.sndFactor.pullback.toContinuousLinearMap
  have hEval (w : Lp ℂ 2 E.measure) :
      Ψ w = ∫ z, conj (f z.1) * w z.2 ∂τ := by
    change inner ℂ u (hτ.sndFactor.pullback w) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    have hu := (Lp.coeFn_compMeasurePreserving (f.l2 R.measure) hτ.fst).trans
      (hτ.fst.quasiMeasurePreserving.ae_eq_comp (f.coe_l2 R.measure))
    have hw := Lp.coeFn_compMeasurePreserving w hτ.snd
    filter_upwards [hu, hw] with z hz hwz
    change u z = f z.1 at hz
    change hτ.sndFactor.pullback w z = w z.2 at hwz
    rw [hz, hwz, RCLike.inner_apply']
  have hGen : Submodule.span ℂ π.relativeFrameGenerators ≤ Ψ.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, A, i, b, rfl⟩
    change Ψ ((b.comp π.toFun π.preserves.measurable).mulL2 E.measure (A.vector i)) = 0
    rw [hEval]
    have he := hτ.snd.quasiMeasurePreserving.ae_eq_comp
      ((b.comp π.toFun π.preserves.measurable).ae_mulL2 (A.vector i))
    refine (integral_congr_ae ?_).trans (integral_centered_relativeFiniteFrame A i hτ hDisjoint
      p hMix f hMean b)
    filter_upwards [he] with w hw
    rw [show ((b.comp π.toFun π.preserves.measurable).mulL2 E.measure (A.vector i)) w.2 =
      b (π.toFun w.2) * A.vector i w.2 from hw, mul_assoc]
  have hClosed := closure_minimal hGen Ψ.isClosed_ker
  rw [hDense.closure_eq] at hClosed
  have hv : Ψ v = 0 := hClosed (mem_univ v)
  rwa [hEval] at hv

private def frameEventIndicator {W : Type*} [MeasurableSpace W]
    (D : Set W) (hD : MeasurableSet D) : BoundedObservable W where
  toFun := D.indicator (fun _ => 1)
  measurable := measurable_const.indicator hD
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    classical
    by_cases h : x ∈ D <;> simp [h]

/-- Disjointness from a system mixing along an ultrafilter lifts through an
extension with the relative finite-frame spanning condition. -/
theorem FactorMap.disjoint_of_isUMixing_of_dense_relativeFrames
    {R : System G X} {B : System G Y} {E : System G Z} (π : FactorMap E B)
    (hDense : π.HasDenseRelativeFrames) (hDisjoint : Disjoint R B)
    (p : Ultrafilter G) (hMix : R.IsUMixing {p}) : Disjoint R E := by
  intro η hη
  let := hη.probability
  have hPair (f : BoundedObservable X) (b : BoundedObservable Z) :
      (∫ w, f w.1 * b w.2 ∂η) =
        (∫ x, f x ∂R.measure) * ∫ z, b z ∂E.measure := by
    let c := ∫ x, f x ∂R.measure
    let a := f.sub (BoundedObservable.const c)
    have ha : (∫ x, a x ∂R.measure) = 0 := by
      change (∫ x, f x - c ∂R.measure) = 0
      rw [integral_sub (f.integrable _) (integrable_const _)]
      simp [c]
    have ha' : (∫ x, a.conjugate x ∂R.measure) = 0 := by
      change (∫ x, conj (a x) ∂R.measure) = 0
      rw [integral_conj, ha, map_zero]
    have hz := integral_centered_of_dense_relativeFrames hDense hη hDisjoint p hMix
      a.conjugate ha' (b.l2 E.measure)
    have hZero : (∫ w, (f w.1 - c) * b w.2 ∂η) = 0 := by
      refine (integral_congr_ae ?_).trans hz
      filter_upwards [hη.snd.quasiMeasurePreserving.ae_eq_comp (b.coe_l2 E.measure)] with w hw
      simp only [a, BoundedObservable.conjugate_apply, starRingEnd_self_apply,
        BoundedObservable.sub_apply, BoundedObservable.const_apply]
      rw [show b.l2 E.measure w.2 = b w.2 from hw]
    simp_rw [sub_mul] at hZero
    have hf : Integrable (fun w : X × Z => f w.1 * b w.2) η := (frameTensor f b).integrable _
    have hb : Integrable (fun w : X × Z => c * b w.2) η :=
      (frameTensor (BoundedObservable.const c) b).integrable _
    rw [integral_sub hf hb, integral_const_mul, b.integral_comp_of_preserving hη.snd] at hZero
    exact sub_eq_zero.mp hZero
  apply Measure.ext_prod
  intro D C hD hC
  let f := frameEventIndicator D hD
  let b := frameEventIndicator C hC
  have h := hPair f b
  have he : (fun w : X × Z => f w.1 * b w.2) = (D ×ˢ C).indicator (fun _ => (1 : ℂ)) := by
    classical
    funext w
    by_cases h₁ : w.1 ∈ D <;> by_cases h₂ : w.2 ∈ C <;>
      simp [f, b, frameEventIndicator, h₁, h₂]
  change (∫ w, f w.1 * b w.2 ∂η) =
    (∫ x, D.indicator (fun _ => (1 : ℂ)) x ∂R.measure) *
      ∫ z, C.indicator (fun _ => (1 : ℂ)) z ∂E.measure at h
  rw [he, integral_indicator_const _ (hD.prod hC), integral_indicator_const _ hD,
    integral_indicator_const _ hC] at h
  have hReal : (η (D ×ˢ C)).toReal = ((R.measure.prod E.measure) (D ×ˢ C)).toReal := by
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    simpa only [Complex.real_smul, mul_one, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, measureReal_def] using congrArg Complex.re h
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using congrArg ENNReal.ofReal hReal

/-- The weak-mixing version of the relative finite-frame disjointness lift. -/
theorem FactorMap.disjoint_of_weakMixing_of_dense_relativeFrames [Countable G]
    {R : System G X} {B : System G Y} {E : System G Z} (π : FactorMap E B)
    (hDense : π.HasDenseRelativeFrames) (hDisjoint : Disjoint R B)
    (hMix : IsWeaklyMixing R.koopmanZeroRep) : Disjoint R E := by
  obtain ⟨p, hp⟩ := System.exists_isUMixing_singleton hMix
  exact π.disjoint_of_isUMixing_of_dense_relativeFrames hDense hDisjoint p hp

end Mixing
