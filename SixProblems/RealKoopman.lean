/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Koopman

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Koopman actions of topological groups on a finite measure space -/

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

private theorem actionPullback_congr {μ : Measure X} {a b : X → X}
    (ha : MeasurePreserving a μ μ) (hb : MeasurePreserving b μ μ) (h : a = b)
    (f : Lp ℝ 2 μ) :
    Lp.compMeasurePreserving a ha f = Lp.compMeasurePreserving b hb f := by
  subst b
  rfl

/-- Pullback by the inverse of a measure-preserving left group action gives
a unitary operator on real L². -/
def realInverseActionKoopman (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) (g : G) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℝ (fun x : X ↦ g⁻¹ • x) (hInv g⁻¹)
  invFun := Lp.compMeasurePreserving (E := ℝ) (p := 2) (fun x : X ↦ g • x) (hInv g)
  left_inv f := by
    change Lp.compMeasurePreserving _ (hInv g)
      (Lp.compMeasurePreserving _ (hInv g⁻¹) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp [Function.comp_apply, ← mul_smul]) f).trans
      (Lp.compMeasurePreserving_id_apply f)
  right_inv f := by
    change Lp.compMeasurePreserving _ (hInv g⁻¹)
      (Lp.compMeasurePreserving _ (hInv g) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp [Function.comp_apply, ← mul_smul]) f).trans
      (Lp.compMeasurePreserving_id_apply f)

/-- The inverse-action Koopman operators form a representation of the acting group. -/
def realInverseActionKoopmanRep (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) :
    G →* (Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ) where
  toFun := realInverseActionKoopman μ hInv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving _ (hInv (1 : G)⁻¹) f = f
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp) f).trans (Lp.compMeasurePreserving_id_apply f)
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving _ (hInv (g * h)⁻¹) f =
      Lp.compMeasurePreserving _ (hInv g⁻¹) (Lp.compMeasurePreserving _ (hInv h⁻¹) f)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact actionPullback_congr _ _
      (funext fun x ↦ by simp only [mul_inv_rev, mul_smul, Function.comp_apply]) f

/-- Representative formula for the inverse-action Koopman representation. -/
theorem ae_realInverseActionKoopmanRep_apply (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (g : G) (f : Lp ℝ 2 μ) :
    (realInverseActionKoopmanRep μ hInv g f : X → ℝ) =ᵐ[μ] fun x ↦ f (g⁻¹ • x) :=
  Lp.coeFn_compMeasurePreserving f (hInv g⁻¹)

/-- For a jointly continuous action, the associated representation is strongly continuous. -/
theorem continuous_realInverseActionKoopmanRep [TopologicalSpace G] [ContinuousInv G]
    [TopologicalSpace X] [R1Space X] [ContinuousSMul G X] [BorelSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) (f : Lp ℝ 2 μ) :
    Continuous (fun g ↦ realInverseActionKoopmanRep μ hInv g f) := by
  let A (g : G) : C(X, X) := ⟨fun x ↦ g⁻¹ • x, continuous_const_smul _⟩
  have hA : Continuous A :=
    ContinuousMap.continuous_of_continuous_uncurry _ (by
      change Continuous (fun z : G × X ↦ z.1⁻¹ • z.2)
      exact continuous_smul.comp (continuous_fst.inv.prodMk continuous_snd))
  exact continuous_const.compMeasurePreservingLp hA (fun g ↦ hInv g⁻¹) (by norm_num)

end SixProblems
