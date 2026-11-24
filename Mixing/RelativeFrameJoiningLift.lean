/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RelativeFiniteFrameDisjointness
public import Mixing.SystemSpectralType
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace

variable {G X X' Y : Type*} [CommGroup G]
variable [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]

/-- The identity factor map of a system. -/
def FactorMap.identity (S : System G Y) : FactorMap S S :=
  ⟨id, MeasurePreserving.id _, fun _ => rfl⟩

/-- A factor map in the first coordinate pushes forward any joining, giving
a factor map from the original joining system onto the projected joining. -/
def FactorMap.joiningLeft {E : System G X} {B : System G X'} {S : System G Y}
    (π : FactorMap E B) {σ : Measure (X × Y)} (hσ : IsJoining E S σ) :
    FactorMap hσ.system (hσ.map π (FactorMap.identity S)).system where
  toFun := Prod.map π.toFun id
  preserves := ⟨π.preserves.measurable.prodMap measurable_id, rfl⟩
  equivariant g := by
    funext w
    exact Prod.ext (congrFun (π.equivariant g) w.1) rfl

/-- Relative frames pull back to the joining system with their base
coefficients pulled back from the first coordinate of the projected joining. -/
def RelativeFiniteFrame.joiningLeft {E : System G X} {B : System G X'} {S : System G Y}
    {π : FactorMap E B} {σ : Measure (X × Y)} (hσ : IsJoining E S σ)
    {n : ℕ} (A : RelativeFiniteFrame π n) : RelativeFiniteFrame (π.joiningLeft hσ) n where
  vector j := hσ.fstFactor.pullback (A.vector j)
  coefficient g j k := (A.coefficient g j k).comp Prod.fst measurable_fst
  bound := A.bound
  norm_bound := A.norm_bound
  translate g i := by
    have hv (j : Fin n) :
        hσ.fstFactor.pullback (A.vector j) =ᵐ[σ] fun w => A.vector j w.1 :=
      Lp.coeFn_compMeasurePreserving _ hσ.fst
    filter_upwards [(hσ.invariant g).quasiMeasurePreserving.ae (hv i),
      hσ.fst.quasiMeasurePreserving.ae (A.translate g i), ae_all_iff.mpr hv] with w hw hA hV
    change (hσ.fstFactor.pullback (A.vector i)) (E.prodAct S g w) =
      ∑ j, A.coefficient g i j (π.toFun w.1) * (hσ.fstFactor.pullback (A.vector j)) w
    rw [hw]
    change A.vector i (E.act g w.1) = _
    rw [hA]
    apply Finset.sum_congr rfl
    intro j _
    rw [hV j]

private def pairObs (f : BoundedObservable X) (b : BoundedObservable Y) :
    BoundedObservable (X × Y) :=
  (f.comp Prod.fst measurable_fst).mul (b.comp Prod.snd measurable_snd)

private def pairEvent {W : Type*} [MeasurableSpace W]
    (D : Set W) (hD : MeasurableSet D) : BoundedObservable W where
  toFun := D.indicator (fun _ => 1)
  measurable := measurable_const.indicator hD
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    classical
    by_cases h : x ∈ D <;> simp [h]

private theorem eq_zero_of_pairObs_inner_eq_zero {σ : Measure (X × Y)} [IsFiniteMeasure σ]
    (v : Lp ℂ 2 σ)
    (hv : ∀ f : BoundedObservable X, ∀ b : BoundedObservable Y,
      inner ℂ ((pairObs f b).l2 σ) v = 0) : v = 0 := by
  have hint : Integrable v σ := (Lp.memLp v).integrable (by norm_num)
  have hRect (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      (∫ z in A ×ˢ B, v z ∂σ) = 0 := by
    let f := pairEvent A hA
    let b := pairEvent B hB
    have he := hv f b
    rw [L2.inner_def] at he
    rw [← integral_indicator (hA.prod hB)]
    refine (integral_congr_ae ?_).trans he
    filter_upwards [(pairObs f b).coe_l2 σ] with z hz
    rw [hz, RCLike.inner_apply']
    change (A ×ˢ B).indicator (fun z => v z) z =
      conj (A.indicator (fun _ => (1 : ℂ)) z.1 * B.indicator (fun _ => (1 : ℂ)) z.2) * v z
    classical
    by_cases ha : z.1 ∈ A <;> by_cases hb : z.2 ∈ B <;> simp [ha, hb, Set.mem_prod]
  have hAll (D : Set (X × Y)) (hD : MeasurableSet D) : (∫ z in D, v z ∂σ) = 0 := by
    have hUniv : (∫ z, v z ∂σ) = 0 := by
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
    (Lp.coeFn_zero ℂ 2 σ).symm

set_option maxHeartbeats 1200000 in
/-- Relative finite-frame spanning is preserved by passing to a joining and
projecting the joining in the extension coordinate. -/
theorem FactorMap.hasDenseRelativeFrames_joiningLeft
    {E : System G X} {B : System G X'} {S : System G Y}
    {π : FactorMap E B} (hπ : π.HasDenseRelativeFrames)
    {σ : Measure (X × Y)} (hσ : IsJoining E S σ) :
    (π.joiningLeft hσ).HasDenseRelativeFrames := by
  let := hσ.probability
  let π' := π.joiningLeft hσ
  let U : Set (Lp ℂ 2 σ) := π'.relativeFrameGenerators
  let M := Submodule.span ℂ U
  let C := M.topologicalClosure
  have hC : IsClosed (C : Set (Lp ℂ 2 σ)) := M.isClosed_topologicalClosure
  have hPair (f : BoundedObservable X) (b : BoundedObservable Y) :
      (pairObs f b).l2 σ ∈ C := by
    let L : Lp ℂ 2 E.measure →L[ℂ] Lp ℂ 2 σ :=
      ((b.comp Prod.snd measurable_snd).mulL2 σ).comp
        hσ.fstFactor.pullback.toContinuousLinearMap
    have hL (v : Lp ℂ 2 E.measure) :
        L v =ᵐ[σ] fun w => b w.2 * v w.1 := by
      have hL' := (b.comp Prod.snd measurable_snd).ae_mulL2 (hσ.fstFactor.pullback v)
      have hv := Lp.coeFn_compMeasurePreserving v hσ.fst
      filter_upwards [hL', hv] with w hw hw'
      change L v w = b w.2 * hσ.fstFactor.pullback v w at hw
      change hσ.fstFactor.pullback v w = v w.1 at hw'
      rw [hw, hw']
    have hG : π.relativeFrameGenerators ⊆ L ⁻¹' (C : Set (Lp ℂ 2 σ)) := by
      rintro _ ⟨n, A, i, a, rfl⟩
      let v := (a.comp π.toFun π.preserves.measurable).mulL2 E.measure (A.vector i)
      let a' := pairObs a b
      let W := (A.joiningLeft hσ).vector i
      let u := (a'.comp π'.toFun π'.preserves.measurable).mulL2 σ W
      have hu : u ∈ U := ⟨n, A.joiningLeft hσ, i, a', rfl⟩
      have he : L v = u := by
        apply Lp.ext
        have hv := hσ.fst.quasiMeasurePreserving.ae_eq_comp
          ((a.comp π.toFun π.preserves.measurable).ae_mulL2 (A.vector i))
        have hW := Lp.coeFn_compMeasurePreserving (A.vector i) hσ.fst
        filter_upwards [hL v, hv, hW, (a'.comp π'.toFun π'.preserves.measurable).ae_mulL2 W]
          with w hw hv' hW' hu'
        change L v w = b w.2 * v w.1 at hw
        change v w.1 = a (π.toFun w.1) * A.vector i w.1 at hv'
        change W w = A.vector i w.1 at hW'
        change u w = (a (π.toFun w.1) * b w.2) * W w at hu'
        rw [hw, hv', hu', hW']
        ring
      change L v ∈ C
      rw [he]
      exact M.le_topologicalClosure (Submodule.subset_span hu)
    have hSpan : Submodule.span ℂ π.relativeFrameGenerators ≤ C.comap L.toLinearMap :=
      Submodule.span_le.mpr hG
    have hCL := closure_minimal (show
      (Submodule.span ℂ π.relativeFrameGenerators : Set (Lp ℂ 2 E.measure)) ⊆
        L ⁻¹' (C : Set (Lp ℂ 2 σ)) from hSpan) (hC.preimage L.continuous)
    have hDense : Dense (Submodule.span ℂ π.relativeFrameGenerators : Set (Lp ℂ 2 E.measure)) := hπ
    rw [hDense.closure_eq] at hCL
    have hf : L (f.l2 E.measure) ∈ C := hCL (mem_univ _)
    have he : L (f.l2 E.measure) = (pairObs f b).l2 σ := by
      apply Lp.ext
      filter_upwards [hL (f.l2 E.measure), hσ.fst.quasiMeasurePreserving.ae_eq_comp
        (f.coe_l2 E.measure), (pairObs f b).coe_l2 σ] with w hL' hf' hfb
      change L (f.l2 E.measure) w = b w.2 * f.l2 E.measure w.1 at hL'
      rw [hL', show f.l2 E.measure w.1 = f w.1 from hf', hfb]
      exact mul_comm _ _
    rwa [he] at hf
  have hOrth : Cᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    rw [Submodule.mem_bot]
    exact eq_zero_of_pairObs_inner_eq_zero v (fun f b => hv _ (hPair f b))
  have hTop : C = ⊤ := by
    have he := Submodule.orthogonal_orthogonal_eq_closure C
    rw [hOrth, Submodule.bot_orthogonal_eq_top, hC.submodule_topologicalClosure_eq] at he
    exact he.symm
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hTop

section Multipliers

universe u

variable {W W' V : Type u} [MeasurableSpace W] [MeasurableSpace W'] [MeasurableSpace V]

/-- The multiplier conclusion lifts through extensions satisfying the
relative finite-frame spanning criterion. This is the finite-frame form
of the extension step in Corollary 2(ii). -/
theorem FactorMap.isMultiplierAgainst_of_dense_relativeFrames [Countable G]
    {E : System G W} {B : System G W'} {R : System G V}
    (π : FactorMap E B) (hπ : π.HasDenseRelativeFrames)
    (hBase : B.IsMultiplierAgainst R) (hWeak : IsWeaklyMixing R.koopmanZeroRep) :
    E.IsMultiplierAgainst R := by
  intro Y _ S hRS σ hσ
  let π' := π.joiningLeft hσ
  have hd := hBase Y S hRS _ (hσ.map π (FactorMap.identity S))
  exact (π'.disjoint_of_weakMixing_of_dense_relativeFrames
    (π.hasDenseRelativeFrames_joiningLeft hπ hσ) hd.symm hWeak).symm

end Multipliers

end Mixing
