/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ComplementaryMixingProduct
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Strong mixing on the complementary product subspace in Example 4 -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable (S : System G X) (T : System G Y)

set_option maxHeartbeats 1200000 in
/-- Bounded product observables test every vector in the product L² space. -/
theorem eq_zero_of_pairObservable_inner_eq_zero (v : Lp ℂ 2 (S.prod T).measure)
    (hv : ∀ f : BoundedObservable X, ∀ h : BoundedObservable Y,
      ⟪(pairObservable f h).l2 (S.prod T).measure, v⟫_ℂ = 0) : v = 0 := by
  let μ := (S.prod T).measure
  let _ : IsProbabilityMeasure μ := (S.prod T).probability
  have hint : Integrable v μ := (Lp.memLp v).integrable (by norm_num)
  have hRect (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      (∫ z in A ×ˢ B, v z ∂μ) = 0 := by
    let f := BoundedObservable.eventIndicator A hA
    let h := BoundedObservable.eventIndicator B hB
    have he := hv f h
    rw [L2.inner_def] at he
    rw [← integral_indicator (hA.prod hB)]
    refine (integral_congr_ae ?_).trans he
    filter_upwards [(pairObservable f h).coe_l2 μ] with z hz
    rw [hz, RCLike.inner_apply']
    change (A ×ˢ B).indicator (fun z => v z) z =
      conj (A.indicator (fun _ => (1 : ℂ)) z.1 * B.indicator (fun _ => (1 : ℂ)) z.2) * v z
    classical
    by_cases ha : z.1 ∈ A <;> by_cases hb : z.2 ∈ B <;> simp [ha, hb, Set.mem_prod]
  have hAll (D : Set (X × Y)) (hD : MeasurableSet D) : (∫ z in D, v z ∂μ) = 0 := by
    have hUniv : (∫ z, v z ∂μ) = 0 := by
      simpa only [univ_prod_univ, Measure.restrict_univ] using
        hRect univ univ MeasurableSet.univ MeasurableSet.univ
    refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod
      (by simp) ?_ ?_ ?_ D hD
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      exact hRect A B hA hB
    · intro E hE hE0
      rw [setIntegral_compl hE hint, hUniv, hE0, sub_zero]
    · intro F hDis hF hF0
      rw [integral_iUnion hF hDis hint.integrableOn]
      simp only [hF0, tsum_zero]
  apply Lp.ext
  exact (ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hint.integrableOn) (fun D hD _ => hAll D hD)).trans
    (Lp.coeFn_zero ℂ 2 μ).symm

noncomputable def fstPullback : Lp ℂ 2 S.measure →L[ℂ] Lp ℂ 2 (S.prod T).measure :=
  (product_isJoining S T).fstFactor.pullback.toContinuousLinearMap

noncomputable def sndPullback : Lp ℂ 2 T.measure →L[ℂ] Lp ℂ 2 (S.prod T).measure :=
  (product_isJoining S T).sndFactor.pullback.toContinuousLinearMap

/-- The closed sum of the two coordinate Hilbert spaces in the product system. -/
noncomputable def System.productCoordinateSubmodule : ClosedSubmodule ℂ (Lp ℂ 2 (S.prod T).measure) :=
  ((fstPullback S T).range ⊔ (sndPullback S T).range).closure

theorem System.productCoordinateSubmodule_invariant :
    IsInvariantSubmodule (S.prod T).koopmanRep (S.productCoordinateSubmodule T) := by
  change IsInvariantSubmodule (S.prod T).koopmanRep
    ((fstPullback S T).range ⊔ (sndPullback S T).range).topologicalClosure
  apply IsInvariantSubmodule.closure
  intro g x hx
  obtain ⟨a, ⟨f, rfl⟩, b, ⟨h, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  apply Submodule.mem_sup.mpr
  refine ⟨_, ⟨S.koopmanRep g f, ?_⟩, _, ⟨T.koopmanRep g h, ?_⟩, rfl⟩
  · exact (product_isJoining S T).fstFactor.intertwines_pullback g f
  · exact (product_isJoining S T).sndFactor.intertwines_pullback g h

private theorem ultrafilterOperator_apply_zero_of_cofinite_diag {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (U : G →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hDiag : Tendsto (fun g => ⟪x, U g x⟫_ℂ) cofinite (𝓝 0))
    (p : Ultrafilter G) (hp : p ∈ freeUltrafilters G) : ultrafilterOperator U p x = 0 := by
  let W := cyclicClosedSubmodule U x
  let V := unitarySubmoduleAction U W.toSubmodule (cyclicClosedSubmodule_invariant U x)
  let _ : CompleteSpace W.toSubmodule := W.isClosed.completeSpace_coe
  let v : W.toSubmodule := ⟨x, mem_cyclicClosedSubmodule U x⟩
  have h := (isStronglyMixing_iff_isUMixing_free V).mp
    (isStronglyMixing_cyclicClosedSubmodule U x hDiag) p hp
  have he := (intertwines_unitarySubmoduleAction U W.toSubmodule
    (cyclicClosedSubmodule_invariant U x)).ultrafilter p v
  rw [h, zero_apply, map_zero] at he
  exact he.symm

set_option maxHeartbeats 1200000 in
private theorem ultrafilterOperator_apply_zero_of_mem_productComplement [Countable G]
    (hCover : ∀ r ∈ freeUltrafilters G, S.IsUMixing {r} ∨ T.IsUMixing {r})
    (p : Ultrafilter G) (hp : p ∈ freeUltrafilters G)
    (v : Lp ℂ 2 (S.prod T).measure) (hv : v ∈ (S.productCoordinateSubmodule T).orthogonal) :
    ultrafilterOperator (S.prod T).koopmanRep p v = 0 := by
  let U := (S.prod T).koopmanRep
  let Q := ultrafilterOperator U p
  let r := inverseUltrafilter p
  let μ := (S.prod T).measure
  let J := product_isJoining S T
  have hr : r ∈ freeUltrafilters G :=
    (Filter.map_mono hp).trans (inv_injective : Function.Injective (Inv.inv : G → G)).tendsto_cofinite
  have hAdj : Q.adjoint = ultrafilterOperator U r := (ultrafilterOperator_inverse U p).symm
  apply eq_zero_of_pairObservable_inner_eq_zero S T
  intro f h
  let cf := ∫ x, f x ∂S.measure
  let ch := ∫ y, h y ∂T.measure
  let f₀ := f.sub (BoundedObservable.const cf)
  let h₀ := h.sub (BoundedObservable.const ch)
  have hf₀ : ∫ x, f₀ x ∂S.measure = 0 := by
    simp [f₀, cf, integral_sub (f.integrable _) (integrable_const _), measureReal_def]
  have hh₀ : ∫ y, h₀ y ∂T.measure = 0 := by
    simp [h₀, ch, integral_sub (h.integrable _) (integrable_const _), measureReal_def]
  let w := (pairObservable f₀ h₀).l2 μ
  have hWlim : Tendsto (fun g => ⟪w, U g w⟫_ℂ) cofinite (𝓝 0) := by
    have he := example4_pairObservable_rajchman S T hCover f₀ h₀ hf₀ hh₀
    rw [funext (spectralFourier_dualVectorSpectralMeasure _ _)] at he
    exact he
  have hw : Q.adjoint w = 0 := by
    rw [hAdj]
    exact ultrafilterOperator_apply_zero_of_cofinite_diag U w hWlim r hr
  let a := fstPullback S T (f₀.l2 S.measure)
  let b := sndPullback S T (h.l2 T.measure)
  have hpair : (pairObservable f h).l2 μ = w + ch • a + cf • b := by
    apply Lp.ext
    have ha := (Lp.coeFn_compMeasurePreserving (f₀.l2 S.measure) J.fstFactor.preserves).trans
      (J.fstFactor.preserves.quasiMeasurePreserving.ae_eq_comp (f₀.coe_l2 S.measure))
    have hb := (Lp.coeFn_compMeasurePreserving (h.l2 T.measure) J.sndFactor.preserves).trans
      (J.sndFactor.preserves.quasiMeasurePreserving.ae_eq_comp (h.coe_l2 T.measure))
    filter_upwards [(pairObservable f h).coe_l2 μ, (pairObservable f₀ h₀).coe_l2 μ,
      ha, hb, Lp.coeFn_smul ch a, Lp.coeFn_smul cf b,
      Lp.coeFn_add w (ch • a), Lp.coeFn_add (w + ch • a) (cf • b)] with z hz h₁ h₂ h₃ h₄ h₅ h₆ h₇
    change a z = f₀ z.1 at h₂
    change b z = h z.2 at h₃
    rw [hz, h₇, Pi.add_apply, h₆, Pi.add_apply, h₄, h₅, Pi.smul_apply, Pi.smul_apply, h₂, h₃]
    change w z = (pairObservable f₀ h₀) z at h₁
    rw [h₁]
    change f z.1 * h z.2 =
      (f z.1 - cf) * (h z.2 - ch) + ch * (f z.1 - cf) + cf * h z.2
    ring
  have hA : Q.adjoint a ∈ S.productCoordinateSubmodule T := by
    change Q.adjoint a ∈ ((fstPullback S T).range ⊔ (sndPullback S T).range).topologicalClosure
    apply Submodule.le_topologicalClosure
    apply (le_sup_left : (fstPullback S T).range ≤ _)
    refine ⟨ultrafilterOperator S.koopmanRep r (f₀.l2 S.measure), ?_⟩
    rw [hAdj]
    exact J.fstFactor.intertwines_pullback.ultrafilter r _
  have hB : Q.adjoint b ∈ S.productCoordinateSubmodule T := by
    change Q.adjoint b ∈ ((fstPullback S T).range ⊔ (sndPullback S T).range).topologicalClosure
    apply Submodule.le_topologicalClosure
    apply (le_sup_right : (sndPullback S T).range ≤ _)
    refine ⟨ultrafilterOperator T.koopmanRep r (h.l2 T.measure), ?_⟩
    rw [hAdj]
    exact J.sndFactor.intertwines_pullback.ultrafilter r _
  change ⟪(pairObservable f h).l2 μ, Q v⟫_ℂ = 0
  rw [← Q.adjoint_inner_left, hpair, map_add, map_add, map_smul, map_smul, hw, zero_add]
  exact hv _ ((S.productCoordinateSubmodule T).add_mem
    ((S.productCoordinateSubmodule T).smul_mem ch hA) ((S.productCoordinateSubmodule T).smul_mem cf hB))

/-- The whole orthocomplement of the two coordinate spaces is strongly mixing
under the complementary mixing hypothesis in Example 4. -/
theorem example4_product_complement_stronglyMixing [Countable G]
    (hCover : ∀ r ∈ freeUltrafilters G, S.IsUMixing {r} ∨ T.IsUMixing {r}) :
    IsStronglyMixing (unitarySubmoduleAction (S.prod T).koopmanRep
      (S.productCoordinateSubmodule T).orthogonal.toSubmodule
      (S.productCoordinateSubmodule_invariant T).orthogonal) := by
  let U := (S.prod T).koopmanRep
  let W := (S.productCoordinateSubmodule T).orthogonal
  let hi := (S.productCoordinateSubmodule_invariant T).orthogonal
  let V := unitarySubmoduleAction U W.toSubmodule hi
  let _ : CompleteSpace W.toSubmodule := W.isClosed.completeSpace_coe
  apply (isStronglyMixing_iff_isUMixing_free V).mpr
  intro p hp
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  have he := (intertwines_unitarySubmoduleAction U W.toSubmodule hi).ultrafilter p v
  change (↑(ultrafilterOperator V p v) : Lp ℂ 2 (S.prod T).measure) = 0
  exact he.trans (ultrafilterOperator_apply_zero_of_mem_productComplement S T hCover p hp v v.property)

set_option maxHeartbeats 1200000 in
/-- Centered tensors belong to the complement of the two coordinate spaces. -/
theorem pairObservable_mem_productCoordinateSubmodule_orthogonal
    (f : BoundedObservable X) (h : BoundedObservable Y)
    (hf : ∫ x, f x ∂S.measure = 0) (hh : ∫ y, h y ∂T.measure = 0) :
    (pairObservable f h).l2 (S.prod T).measure ∈ (S.productCoordinateSubmodule T).orthogonal := by
  let μ := (S.prod T).measure
  let J := product_isJoining S T
  let w := (pairObservable f h).l2 μ
  let L := innerSL ℂ w
  have hSub : (fstPullback S T).range ⊔ (sndPullback S T).range ≤ L.ker := by
    apply sup_le
    · rintro _ ⟨a, rfl⟩
      change ⟪w, fstPullback S T a⟫_ℂ = 0
      rw [L2.inner_def]
      calc
        _ = ∫ z, (conj (f z.1) * a z.1) * conj (h z.2) ∂μ := by
          apply integral_congr_ae
          filter_upwards [(pairObservable f h).coe_l2 μ,
            Lp.coeFn_compMeasurePreserving a J.fstFactor.preserves] with z hz h₁
          change fstPullback S T a z = a z.1 at h₁
          change w z = (pairObservable f h) z at hz
          rw [hz, h₁, RCLike.inner_apply']
          change conj (f z.1 * h z.2) * a z.1 = _
          rw [map_mul]
          ring
        _ = 0 := by
          change (∫ z : X × Y, (conj (f z.1) * a z.1) * conj (h z.2) ∂S.measure.prod T.measure) = 0
          rw [integral_prod_mul (fun x => conj (f x) * a x) (fun y => conj (h y)),
            integral_conj, hh, map_zero, mul_zero]
    · rintro _ ⟨b, rfl⟩
      change ⟪w, sndPullback S T b⟫_ℂ = 0
      rw [L2.inner_def]
      calc
        _ = ∫ z, conj (f z.1) * (conj (h z.2) * b z.2) ∂μ := by
          apply integral_congr_ae
          filter_upwards [(pairObservable f h).coe_l2 μ,
            Lp.coeFn_compMeasurePreserving b J.sndFactor.preserves] with z hz h₁
          change sndPullback S T b z = b z.2 at h₁
          change w z = (pairObservable f h) z at hz
          rw [hz, h₁, RCLike.inner_apply']
          change conj (f z.1 * h z.2) * b z.2 = _
          rw [map_mul, mul_assoc]
        _ = 0 := by
          change (∫ z : X × Y, conj (f z.1) * (conj (h z.2) * b z.2) ∂S.measure.prod T.measure) = 0
          rw [integral_prod_mul (fun x => conj (f x)) (fun y => conj (h y) * b y),
            integral_conj, hf, map_zero, zero_mul]
  have hClosure := Submodule.topologicalClosure_minimal _ hSub L.isClosed_ker
  intro v hv
  have he : ⟪w, v⟫_ℂ = 0 := hClosure hv
  rw [← inner_conj_symm, he, map_zero]

/-- Nontriviality of both probability spaces makes the complementary product
subspace nonzero. -/
theorem example4_product_complement_nonzero [Countable G]
    {A : Set X} (hA : MeasurableSet A) (hA₀ : 0 < S.measure A) (hA₁ : S.measure A < 1)
    {B : Set Y} (hB : MeasurableSet B) (hB₀ : 0 < T.measure B) (hB₁ : T.measure B < 1) :
    ∃ w ∈ (S.productCoordinateSubmodule T).orthogonal, w ≠ 0 := by
  obtain ⟨f, hf, hf₀⟩ := exists_nonzero_centered_observable S.measure A hA hA₀ hA₁
  obtain ⟨h, hh, hh₀⟩ := exists_nonzero_centered_observable T.measure B hB hB₀ hB₁
  exact ⟨_, pairObservable_mem_productCoordinateSubmodule_orthogonal S T f h hf hh,
    pairObservable_l2_ne_zero S T f h hf₀ hh₀⟩

end Mixing
