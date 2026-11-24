/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RelativeFrameJoiningLift

@[expose] public section
noncomputable section

namespace Mixing

open MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace

universe u

variable {G ι : Type*} [CommGroup G]
variable {X Y Z : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {W : ι → Type u} [∀ i, MeasurableSpace (W i)]

/-- An inverse-limit spanning condition expressed using the pullbacks in L². -/
def DenseFactorPullbacks {T : System G X} {S : ∀ i, System G (W i)}
    (π : ∀ i, FactorMap T (S i)) : Prop :=
  Dense (Submodule.span ℂ (⋃ i, Set.range (π i).pullback) : Set (Lp ℂ 2 T.measure))

/-- Directed factor σ-algebras generating the ambient σ-algebra give the
L² spanning condition of the inverse-limit argument. -/
theorem denseFactorPullbacks_of_iSup_comap [Nonempty ι]
    {T : System G X} {S : ∀ i, System G (W i)} (π : ∀ i, FactorMap T (S i))
    (hDirected : Directed (· ≤ ·) (fun i =>
      MeasurableSpace.comap (π i).toFun (inferInstance : MeasurableSpace (W i))))
    (hTotal : (⨆ i, MeasurableSpace.comap (π i).toFun
      (inferInstance : MeasurableSpace (W i))) = ‹MeasurableSpace X›) :
    DenseFactorPullbacks π := by
  classical
  let m (i : ι) := MeasurableSpace.comap (π i).toFun (inferInstance : MeasurableSpace (W i))
  let C := ⋃ i, {D : Set X | MeasurableSet[m i] D}
  let V := Submodule.span ℂ (⋃ i, Set.range (π i).pullback)
  have hPi : IsPiSystem C := by
    intro D hD E hE _
    obtain ⟨i, hi⟩ := mem_iUnion.mp hD
    obtain ⟨j, hj⟩ := mem_iUnion.mp hE
    obtain ⟨k, hk₁, hk₂⟩ := hDirected i j
    exact mem_iUnion.mpr ⟨k, (hk₁ _ hi).inter (hk₂ _ hj)⟩
  have hGen : MeasurableSpace.generateFrom C = ‹MeasurableSpace X› :=
    (MeasurableSpace.generateFrom_iUnion_measurableSet m).trans hTotal
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_bot]
  have hi : Integrable v T.measure := (Lp.memLp v).integrable (by norm_num)
  have hC (D : Set X) (hD : D ∈ C) : (∫ x in D, v x ∂T.measure) = 0 := by
    obtain ⟨i, hiD⟩ := mem_iUnion.mp hD
    obtain ⟨E, hE, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hiD
    let e : BoundedObservable (W i) :=
      ⟨E.indicator (fun _ => 1), measurable_const.indicator hE, 1, zero_le_one, by
        intro y
        by_cases h : y ∈ E <;> simp [h]⟩
    let q := (π i).pullback (e.l2 (S i).measure)
    have hq : q ∈ V := Submodule.subset_span (mem_iUnion.mpr ⟨i, e.l2 (S i).measure, rfl⟩)
    have he := hv q hq
    rw [L2.inner_def] at he
    rw [← integral_indicator ((π i).preserves.measurable hE)]
    refine (integral_congr_ae ?_).trans he
    have hq' := (Lp.coeFn_compMeasurePreserving (e.l2 (S i).measure) (π i).preserves).trans
      ((π i).preserves.quasiMeasurePreserving.ae_eq_comp (e.coe_l2 (S i).measure))
    filter_upwards [hq'] with x hx
    change q x = e ((π i).toFun x) at hx
    rw [hx, RCLike.inner_apply']
    by_cases h : (π i).toFun x ∈ E <;> simp [e, h]
  have hUniv : (∫ x, v x ∂T.measure) = 0 := by
    let i := Classical.choice (inferInstance : Nonempty ι)
    simpa only [Measure.restrict_univ] using hC univ (mem_iUnion.mpr
      ⟨i, @MeasurableSet.univ X (m i)⟩)
  have hAll (D : Set X) (hD : MeasurableSet D) : (∫ x in D, v x ∂T.measure) = 0 := by
    refine MeasurableSpace.induction_on_inter hGen.symm hPi (by simp) hC ?_ ?_ D hD
    · intro D hhD hD0
      rw [setIntegral_compl hhD hi, hUniv, hD0, sub_zero]
    · intro D hDis hD hD0
      rw [integral_iUnion hD hDis hi.integrableOn]
      simp only [hD0, tsum_zero]
  apply Lp.ext
  exact (ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hi.integrableOn) (fun D hD _ => hAll D hD)).trans
    (Lp.coeFn_zero ℂ 2 T.measure).symm

set_option maxHeartbeats 1200000 in
private theorem integral_centered_of_dense_factorPullbacks
    {T : System G X} {S : ∀ i, System G (W i)} {A : System G Y} {R : System G Z}
    {π : ∀ i, FactorMap T (S i)} (hDense : DenseFactorPullbacks π)
    (hMultiplier : ∀ i, (S i).IsMultiplierAgainst R) (hAR : Disjoint A R)
    {σ : Measure (X × Y)} {hσ : IsJoining T A σ} {τ : Measure ((X × Y) × Z)}
    (hτ : IsJoining hσ.system R τ) (F : BoundedObservable Y) (H : BoundedObservable Z)
    (hMean : ∫ z, H z ∂R.measure = 0) (v : Lp ℂ 2 T.measure) :
    (∫ w, H w.2 * F w.1.2 * v w.1.1 ∂τ) = 0 := by
  let := hτ.probability
  let B := (H.comp Prod.snd measurable_snd).mul
    (F.comp (fun w : (X × Y) × Z => w.1.2) (measurable_snd.comp measurable_fst))
  let L : Lp ℂ 2 T.measure →L[ℂ] Lp ℂ 2 τ :=
    (Lp.compMeasurePreservingₗᵢ ℂ _ (hσ.fst.comp hτ.fst)).toContinuousLinearMap
  let Ψ : Lp ℂ 2 T.measure →L[ℂ] ℂ :=
    (InnerProductSpace.toDual ℂ _ (B.conjugate.l2 τ)).comp L
  have hEval (w : Lp ℂ 2 T.measure) :
      Ψ w = ∫ z, H z.2 * F z.1.2 * w z.1.1 ∂τ := by
    change inner ℂ (B.conjugate.l2 τ) (L w) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [B.conjugate.coe_l2 τ, Lp.coeFn_compMeasurePreserving w (hσ.fst.comp hτ.fst)]
      with z hz hw
    change L w z = w z.1.1 at hw
    rw [hz, hw, RCLike.inner_apply']
    simp [B]
  have hSpan : Submodule.span ℂ (⋃ i, Set.range (π i).pullback) ≤ Ψ.ker := by
    apply Submodule.span_le.mpr
    intro w hw
    obtain ⟨i, u, rfl⟩ := mem_iUnion.mp hw
    change Ψ ((π i).pullback u) = 0
    rw [hEval]
    let P := (π i).joiningLeft hσ
    let Qi := hσ.map (π i) (FactorMap.identity A)
    have hd := hMultiplier i Y A hAR _ Qi
    let p := Prod.map P.toFun (id : Z → Z)
    have hp : MeasurePreserving p τ (Qi.system.measure.prod R.measure) :=
      ⟨P.preserves.measurable.prodMap measurable_id, hd _ (hτ.map P (FactorMap.identity R))⟩
    let J (w : (W i × Y) × Z) : ℂ := (F w.1.2 * u w.1.1) * H w.2
    have hJ : Measurable J := ((F.measurable.comp (measurable_snd.comp measurable_fst)).mul
      ((Lp.stronglyMeasurable u).measurable.comp (measurable_fst.comp measurable_fst))).mul
      (H.measurable.comp measurable_snd)
    calc
      _ = ∫ w, J (p w) ∂τ := by
        apply integral_congr_ae
        filter_upwards [(hσ.fst.comp hτ.fst).quasiMeasurePreserving.ae_eq_comp
          (Lp.coeFn_compMeasurePreserving u (π i).preserves)] with w hw
        change (π i).pullback u w.1.1 = u ((π i).toFun w.1.1) at hw
        rw [hw]
        change H w.2 * F w.1.2 * u ((π i).toFun w.1.1) =
          (F w.1.2 * u ((π i).toFun w.1.1)) * H w.2
        rw [mul_assoc, mul_comm (H w.2)]
      _ = ∫ w, J w ∂(Qi.system.measure.prod R.measure) := by
        rw [← hp.map_eq]
        exact (integral_map hp.aemeasurable hJ.aestronglyMeasurable).symm
      _ = 0 := by
        change (∫ w : (W i × Y) × Z, (F w.1.2 * u w.1.1) * H w.2
          ∂(Qi.system.measure.prod R.measure)) = _
        rw [integral_prod_mul (fun w : W i × Y => F w.2 * u w.1) (fun z => H z),
          hMean, mul_zero]
  have hClosed := closure_minimal hSpan Ψ.isClosed_ker
  have hDense' : Dense (Submodule.span ℂ (⋃ i, Set.range (π i).pullback) :
      Set (Lp ℂ 2 T.measure)) := hDense
  rw [hDense'.closure_eq] at hClosed
  have hv : Ψ v = 0 := hClosed (mem_univ _)
  rwa [hEval] at hv

/-- The multiplier property passes to a system spanned in L² by pullbacks
from factor multipliers. This is the inverse-limit step used for distal towers. -/
theorem System.isMultiplierAgainst_of_denseFactorPullbacks
    {T : System G X} {S : ∀ i, System G (W i)} {R : System G Z}
    {π : ∀ i, FactorMap T (S i)} (hDense : DenseFactorPullbacks π)
    (hMultiplier : ∀ i, (S i).IsMultiplierAgainst R) : T.IsMultiplierAgainst R := by
  intro Y _ A hAR σ hσ τ hτ
  let := hσ.probability
  let := hτ.probability
  apply joining_eq_prod_of_integrals
  intro f F H
  let c := ∫ z, H z ∂R.measure
  let H₀ := H.sub (BoundedObservable.const c)
  have hMean : (∫ z, H₀ z ∂R.measure) = 0 := by
    change (∫ z, H z - c ∂R.measure) = 0
    rw [integral_sub (H.integrable _) (integrable_const _)]
    simp [c]
  have h0 := integral_centered_of_dense_factorPullbacks hDense hMultiplier hAR hτ F H₀ hMean
    (f.l2 T.measure)
  have hz : (∫ w, (H w.2 - c) * F w.1.2 * f w.1.1 ∂τ) = 0 := by
    refine (integral_congr_ae ?_).trans h0
    filter_upwards [(hσ.fst.comp hτ.fst).quasiMeasurePreserving.ae_eq_comp (f.coe_l2 T.measure)]
      with w hw
    rw [show f.l2 T.measure w.1.1 = f w.1.1 from hw]
    rfl
  let v := (F.comp Prod.snd measurable_snd).mul (f.comp Prod.fst measurable_fst)
  let w := ((H.comp Prod.snd measurable_snd).mul
    (F.comp (fun z : (X × Y) × Z => z.1.2) (measurable_snd.comp measurable_fst))).mul
    (f.comp (fun z : (X × Y) × Z => z.1.1) (measurable_fst.comp measurable_fst))
  have he (z : (X × Y) × Z) : (H z.2 - c) * F z.1.2 * f z.1.1 =
      w z - c * v z.1 := by
    simp only [w, v, BoundedObservable.mul_apply, BoundedObservable.comp_apply]
    ring
  have hC : Integrable (fun z : (X × Y) × Z => c * v z.1) τ :=
    (v.comp Prod.fst measurable_fst |>.integrable τ).const_mul c
  simp_rw [he] at hz
  rw [integral_sub (w.integrable _) hC, integral_const_mul, v.integral_comp_of_preserving hτ.fst,
    sub_eq_zero] at hz
  rw [mul_comm c] at hz
  exact hz

/-- A one-point system is a multiplier against every system. -/
theorem System.isMultiplierAgainst_of_subsingleton [Subsingleton X]
    (T : System G X) (R : System G Z) : T.IsMultiplierAgainst R := by
  intro Y _ A hAR σ hσ τ hτ
  let := hσ.probability
  let := hτ.probability
  let x₀ := (nonempty_of_isProbabilityMeasure T.measure).some
  let p := Prod.map (Prod.snd : X × Y → Y) (id : Z → Z)
  have hp : MeasurePreserving p τ (A.measure.prod R.measure) :=
    ⟨measurable_snd.prodMap measurable_id, hAR _ (hτ.map hσ.sndFactor (FactorMap.identity R))⟩
  apply joining_eq_prod_of_integrals
  intro f F H
  have hf (x : X) : f x = f x₀ := congrArg f (Subsingleton.elim x x₀)
  have hLeft : (∫ w, H w.2 * F w.1.2 ∂τ) =
      (∫ y, F y ∂A.measure) * ∫ z, H z ∂R.measure := by
    let J := (H.comp Prod.snd measurable_snd).mul (F.comp Prod.fst measurable_fst)
    calc
      _ = ∫ w, J w ∂(A.measure.prod R.measure) := J.integral_comp_of_preserving hp
      _ = ∫ w : Y × Z, F w.1 * H w.2 ∂(A.measure.prod R.measure) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => mul_comm _ _
      _ = _ := integral_prod_mul _ _
  have hRight : (∫ a : X × Y, F a.2 ∂hσ.system.measure) = ∫ y, F y ∂A.measure :=
    F.integral_comp_of_preserving hσ.snd
  simp_rw [hf]
  rw [integral_mul_const, integral_mul_const, hLeft, hRight]
  ring

/-- A tower starting at a one-point system, with dense relative-frame
successors and limits having dense spans of factor pullbacks. -/
inductive RelativeFrameTower (G : Type*) [CommGroup G] :
    {X : Type u} → [m : MeasurableSpace X] → @System G X _ m → Prop
  | point {X : Type u} [MeasurableSpace X] (T : System G X) (hX : Subsingleton X) :
      RelativeFrameTower G T
  | step {X X' : Type u} [MeasurableSpace X] [MeasurableSpace X']
      {T : System G X} {B : System G X'} (π : FactorMap T B)
      (hBase : RelativeFrameTower G B) (hFrames : π.HasDenseRelativeFrames) :
      RelativeFrameTower G T
  | limit {I : Type u} {X : Type u} [MeasurableSpace X]
      {V : I → Type u} [∀ i, MeasurableSpace (V i)]
      {T : System G X} {B : ∀ i, System G (V i)} (π : ∀ i, FactorMap T (B i))
      (hDense : DenseFactorPullbacks π) (hFactors : ∀ i, RelativeFrameTower G (B i)) :
      RelativeFrameTower G T

/-- The finite-frame tower form of Corollary 2(iii). Each such tower is a
multiplier for every weakly mixing system. -/
theorem RelativeFrameTower.isMultiplierAgainst [Countable G]
    {T : System G X} (hT : RelativeFrameTower G T) (R : System G Z)
    (hWeak : IsWeaklyMixing R.koopmanZeroRep) : T.IsMultiplierAgainst R := by
  induction hT with
  | point T hX =>
    let := hX
    exact T.isMultiplierAgainst_of_subsingleton R
  | step π _ hFrames ih => exact π.isMultiplierAgainst_of_dense_relativeFrames hFrames ih hWeak
  | limit _ hDense _ ih => exact System.isMultiplierAgainst_of_denseFactorPullbacks hDense ih

end Mixing
