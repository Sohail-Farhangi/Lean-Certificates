/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationKoopmanAction
public import Mixing.CompactGroupSkew

/-! # The vertical fixed subspace is the pullback of the base -/

@[expose] public section
noncomputable section

namespace Mixing

open MeasureTheory MeasureTheory.Measure Filter

section Product

variable {Y K : Type*} [MeasurableSpace Y] [MeasurableSpace K] [Group K]
  [MeasurableMul₂ K] [MeasurableInv K]

/-- If an L² function on a product with Haar measure is invariant under every fibre
right translation, then it is almost everywhere a function of the first coordinate. -/
theorem exists_fst_pullback_of_ae_rightInvariant
    (ν : Measure Y) [IsFiniteMeasure ν] (m : Measure K) [IsProbabilityMeasure m]
    [IsMulLeftInvariant m] [IsMulRightInvariant m] (F : Lp ℂ 2 (ν.prod m))
    (hInv : ∀ r : K, (fun z : Y × K ↦ F (z.1, z.2 * r)) =ᵐ[ν.prod m] F) :
    ∃ f : Lp ℂ 2 ν, Lp.compMeasurePreserving Prod.fst
      (measurePreserving_fst (μ := ν) (ν := m)) f = F := by
  let f := (Lp.aestronglyMeasurable F).mk F
  have hf : Measurable f := (Lp.aestronglyMeasurable F).stronglyMeasurable_mk.measurable
  have hFf : (F : Y × K → ℂ) =ᵐ[ν.prod m] f := (Lp.aestronglyMeasurable F).ae_eq_mk
  have hInvF (r : K) : ∀ᵐ z ∂ν.prod m, f (z.1, z.2 * r) = f z := by
    have hR : MeasurePreserving (fun z : Y × K ↦ (z.1, z.2 * r)) (ν.prod m) (ν.prod m) :=
      (MeasurePreserving.id ν).prod (measurePreserving_mul_right m r)
    filter_upwards [hInv r, hR.quasiMeasurePreserving.ae hFf, hFf] with z hz₁ hz₂ hz₃
    exact hz₂.symm.trans (hz₁.trans hz₃)
  have hm₁ : MeasurableSet {w : (Y × K) × K | f (w.1.1, w.1.2 * w.2) = f w.1} :=
    measurableSet_eq_fun
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).mul measurable_snd))) (hf.comp measurable_fst)
  have hp₁ : ∀ᵐ w ∂(ν.prod m).prod m, f (w.1.1, w.1.2 * w.2) = f w.1 :=
    (Measure.ae_prod_iff_ae_ae hm₁).2 ((Measure.ae_ae_comm hm₁).2 (ae_of_all _ hInvF))
  have hS : MeasurePreserving (fun w : (Y × K) × K ↦ (w.1, w.1.2⁻¹ * w.2))
      ((ν.prod m).prod m) ((ν.prod m).prod m) :=
    measurePreserving_left_shear (ν.prod m) m (fun z ↦ z.2⁻¹) measurable_snd.inv
  have hp₂ : ∀ᵐ w ∂(ν.prod m).prod m, f (w.1.1, w.2) = f w.1 := by
    filter_upwards [hS.quasiMeasurePreserving.ae hp₁] with w hw
    simpa only [mul_inv_cancel_left] using hw
  have hm₂ : MeasurableSet {w : (Y × K) × K | f (w.1.1, w.2) = f w.1} :=
    measurableSet_eq_fun
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (hf.comp measurable_fst)
  have hp₃ : ∀ᵐ r ∂m, ∀ᵐ z ∂ν.prod m, f (z.1, r) = f z :=
    (Measure.ae_ae_comm hm₂).1 (Measure.ae_ae_of_ae_prod hp₂)
  obtain ⟨r, hr⟩ := hp₃.exists
  let g (y : Y) := f (y, r)
  have hg : Measurable g := hf.comp (measurable_id.prodMk measurable_const)
  have hgF : (g ∘ Prod.fst) =ᵐ[ν.prod m] F := by
    filter_upwards [hr, hFf] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  have hgL : MemLp (g ∘ Prod.fst) 2 (ν.prod m) :=
    (memLp_congr_ae hgF).2 (Lp.memLp F)
  let hp : MeasurePreserving Prod.fst (ν.prod m) ν := measurePreserving_fst
  have hgL' : MemLp g 2 ((ν.prod m).map Prod.fst) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable hp.aemeasurable).2 hgL
  rw [hp.map_eq] at hgL'
  refine ⟨hgL'.toLp g, ?_⟩
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ hp).trans
    ((hp.quasiMeasurePreserving.ae_eq_comp hgL'.coeFn_toLp).trans hgF)

end Product

/-- A principal compact-group extension has no vertical fixed functions beyond
the pullbacks of functions on its base. -/
theorem principalExtension_fixed_iff_pullback
    {G X Y K : Type*} [CommGroup G] [Group K] [MulAction K X]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K]
    [MeasurableMul₂ K] [MeasurableInv K]
    {E : System G X} {B : System G Y} (π : FactorMap E B)
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [IsMulRightInvariant m]
    (e : Y × K ≃ᵐ X) (he : MeasurePreserving e (B.measure.prod m) E.measure)
    (hπ : ∀ y k, π.toFun (e (y, k)) = y)
    (hE : ∀ y k r, e (y, k * r) = r⁻¹ • e (y, k))
    (hPres : ∀ k : K, MeasurePreserving (fun x : X ↦ k • x) E.measure E.measure)
    (v : Lp ℂ 2 E.measure) :
    (∀ k, inverseActionKoopmanRep E.measure hPres k v = v) ↔
      ∃ u : Lp ℂ 2 B.measure, π.pullback u = v := by
  constructor
  · intro hFix
    let F := Lp.compMeasurePreserving e he v
    have hF : (F : Y × K → ℂ) =ᵐ[B.measure.prod m] fun z ↦ v (e z) :=
      Lp.coeFn_compMeasurePreserving v he
    have hFInv (r : K) : (fun z : Y × K ↦ F (z.1, z.2 * r)) =ᵐ[B.measure.prod m] F := by
      have hR : MeasurePreserving (fun z : Y × K ↦ (z.1, z.2 * r))
          (B.measure.prod m) (B.measure.prod m) :=
        (MeasurePreserving.id B.measure).prod (measurePreserving_mul_right m r)
      have hv := ae_inverseActionKoopmanRep_apply E.measure hPres r v
      rw [hFix r] at hv
      filter_upwards [hF, hR.quasiMeasurePreserving.ae hF, he.quasiMeasurePreserving.ae hv]
        with z hz₁ hz₂ hz₃
      change F (z.1, z.2 * r) = v (e (z.1, z.2 * r)) at hz₂
      change v (e z) = v (r⁻¹ • e z) at hz₃
      exact hz₂.trans ((congrArg (fun x : X ↦ v x) (hE z.1 z.2 r)).trans
        (hz₃.symm.trans hz₁.symm))
    obtain ⟨u, hu⟩ := exists_fst_pullback_of_ae_rightInvariant B.measure m F hFInv
    refine ⟨u, (Lp.isometry_compMeasurePreserving (p := 2) (E := ℂ) he).injective ?_⟩
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving π.toFun π.preserves u) = F
    rw [← Lp.compMeasurePreserving_comp_apply, ← hu]
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving u (π.preserves.comp he),
      Lp.coeFn_compMeasurePreserving u (measurePreserving_fst (μ := B.measure) (ν := m))]
      with z hz₁ hz₂
    exact hz₁.trans ((congrArg (fun y : Y ↦ u y) (hπ z.1 z.2)).trans hz₂.symm)
  · rintro ⟨u, rfl⟩ r
    apply (Lp.isometry_compMeasurePreserving (p := 2) (E := ℂ) he).injective
    apply Lp.ext
    have hBase : (π.pullback u : X → ℂ) =ᵐ[E.measure] fun x ↦ u (π.toFun x) :=
      Lp.coeFn_compMeasurePreserving u π.preserves
    have hAct := ae_inverseActionKoopmanRep_apply E.measure hPres r (π.pullback u)
    filter_upwards [
      Lp.coeFn_compMeasurePreserving (inverseActionKoopmanRep E.measure hPres r (π.pullback u)) he,
      Lp.coeFn_compMeasurePreserving (π.pullback u) he,
      he.quasiMeasurePreserving.ae hAct,
      ((hPres r⁻¹).comp he).quasiMeasurePreserving.ae hBase,
      he.quasiMeasurePreserving.ae hBase] with z h₁ h₂ h₃ h₄ h₅
    have hcoord : π.toFun (r⁻¹ • e z) = π.toFun (e z) := by
      rw [← hE z.1 z.2 r, hπ z.1 (z.2 * r), hπ z.1 z.2]
    exact h₁.trans (h₃.trans (h₄.trans ((congrArg (fun y : Y ↦ u y) hcoord).trans
      (h₅.symm.trans h₂.symm))))

end Mixing
