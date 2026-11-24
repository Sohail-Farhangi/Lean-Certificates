/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.JoiningBarycenters
public import Mathlib.MeasureTheory.Group.Prod

/-! # Weak-mixing disjointness lifts to compact-group skew extensions -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace Mixing

variable {G X Y K : Type*} [CommGroup G] [Group K]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K] [MeasurableMul₂ K]

/-- A measurable cocycle taking values in the fibre group. -/
structure MeasurableSkewCocycle (T : System G Y) where
  toFun : G → Y → K
  measurable : ∀ g, Measurable (toFun g)
  one : ∀ y, toFun 1 y = 1
  mul : ∀ g h y, toFun (g * h) y = toFun g (T.act h y) * toFun h y

theorem measurePreserving_left_shear {W : Type*} [MeasurableSpace W]
    (μ : Measure W) [IsFiniteMeasure μ] (mK : Measure K) [IsProbabilityMeasure mK] [IsMulLeftInvariant mK]
    (c : W → K) (hc : Measurable c) :
    MeasurePreserving (fun w : W × K ↦ (w.1, c w.1 * w.2)) (μ.prod mK) (μ.prod mK) := by
  let F : W × K → W × K := fun w ↦ (w.1, c w.1 * w.2)
  have hF : Measurable F := measurable_fst.prodMk ((hc.comp measurable_fst).mul measurable_snd)
  refine ⟨hF, ?_⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hF (hA.prod hB), Measure.prod_apply (hF (hA.prod hB)),
    Measure.prod_apply (hA.prod hB)]
  apply lintegral_congr_ae
  exact .of_forall fun w ↦ by
    change mK (Prod.mk w ⁻¹' (F ⁻¹' (A ×ˢ B))) = mK (Prod.mk w ⁻¹' (A ×ˢ B))
    by_cases hw : w ∈ A
    · have h₁ : Prod.mk w ⁻¹' (F ⁻¹' (A ×ˢ B)) = (fun k ↦ c w * k) ⁻¹' B := by
        ext k
        simp [F, hw]
      have h₂ : Prod.mk w ⁻¹' (A ×ˢ B) = B := by ext k; simp [hw]
      rw [h₁, h₂, (measurePreserving_mul_left mK (c w)).measure_preimage hB.nullMeasurableSet]
    · have h₁ : Prod.mk w ⁻¹' (F ⁻¹' (A ×ˢ B)) = ∅ := by ext k; simp [F, hw]
      have h₂ : Prod.mk w ⁻¹' (A ×ˢ B) = ∅ := by ext k; simp [hw]
      rw [h₁, h₂]

variable (T : System G Y) (c : MeasurableSkewCocycle (K := K) T)
variable (mK : Measure K) [IsProbabilityMeasure mK] [IsMulLeftInvariant mK]

/-- The skew product by a compact-group cocycle, using normalized Haar
probability as the fibre measure. -/
noncomputable def compactGroupSkewSystem : System G (Y × K) where
  measure := T.measure.prod mK
  probability := inferInstance
  act g w := (T.act g w.1, c.toFun g w.1 * w.2)
  act_one := by funext w; simp [T.act_one, c.one]
  act_mul g h := by funext w; simp [T.act_mul, c.mul, mul_assoc]
  preserves g :=
    ((T.preserves g).prod (MeasurePreserving.id mK)).comp
      (measurePreserving_left_shear T.measure mK (c.toFun g) (c.measurable g))

/-- The base factor of the skew product is the first coordinate. -/
noncomputable def compactGroupSkewFactor : FactorMap (compactGroupSkewSystem T c mK) T where
  toFun := Prod.fst
  preserves := measurePreserving_fst
  equivariant _ := rfl

variable [IsMulRightInvariant mK]

private noncomputable def skewRightFactor (r : K) :
    FactorMap (compactGroupSkewSystem T c mK) (compactGroupSkewSystem T c mK) where
  toFun w := (w.1, w.2 * r)
  preserves := (MeasurePreserving.id T.measure).prod (measurePreserving_mul_right mK r)
  equivariant g := by
    funext w
    change (T.act g w.1, (c.toFun g w.1 * w.2) * r) =
      (T.act g w.1, c.toFun g w.1 * (w.2 * r))
    rw [mul_assoc]

private def skewJoiningRight (r : K) (w : X × (Y × K)) : X × (Y × K) :=
  (w.1, (w.2.1, w.2.2 * r))

private theorem measurable_skewJoiningRight (r : K) :
    Measurable (skewJoiningRight (X := X) (Y := Y) r) := by unfold skewJoiningRight; fun_prop

private theorem measurable_uncurry_skewJoiningRight :
    Measurable (Function.uncurry (skewJoiningRight (X := X) (Y := Y) (K := K))) := by
  unfold Function.uncurry skewJoiningRight
  fun_prop

private noncomputable def skewJoiningAverageKernel (τ : Measure (X × (Y × K))) : Kernel K (X × (Y × K)) :=
  (Kernel.id ×ₖ Kernel.const K τ).map (Function.uncurry skewJoiningRight)

private instance (τ : Measure (X × (Y × K))) [IsProbabilityMeasure τ] :
    IsMarkovKernel (skewJoiningAverageKernel τ) :=
  Kernel.IsMarkovKernel.map _ measurable_uncurry_skewJoiningRight

private theorem skewJoiningAverageKernel_apply (τ : Measure (X × (Y × K))) [IsProbabilityMeasure τ]
    (r : K) : skewJoiningAverageKernel τ r = τ.map (skewJoiningRight r) := by
  ext A hA
  rw [skewJoiningAverageKernel, Kernel.map_apply' _ measurable_uncurry_skewJoiningRight _ hA,
    Kernel.id_prod_apply' _ _ (measurable_uncurry_skewJoiningRight hA),
    Kernel.const_apply, Measure.map_apply (measurable_skewJoiningRight r) hA]
  rfl

omit [IsMulRightInvariant mK] in
private theorem skewJoiningAverageKernel_comp (τ : Measure (X × (Y × K))) [IsProbabilityMeasure τ]
    (S : System G X)
    (hBase : τ.map (fun w : X × (Y × K) ↦ (w.1, w.2.1)) = S.measure.prod T.measure) :
    skewJoiningAverageKernel τ ∘ₘ mK = S.measure.prod (T.measure.prod mK) := by
  rw [skewJoiningAverageKernel, ← Measure.map_comp _ _ measurable_uncurry_skewJoiningRight,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  let F : (X × (Y × K)) × K → (X × (Y × K)) × K := fun p ↦ (p.1, p.1.2.2 * p.2)
  have hF : MeasurePreserving F (τ.prod mK) (τ.prod mK) :=
    measurePreserving_left_shear τ mK (fun w ↦ w.2.2) (measurable_snd.comp measurable_snd)
  let P : (X × (Y × K)) × K → (X × Y) × K := Prod.map (fun w ↦ (w.1, w.2.1)) id
  have hp : Measurable (fun w : X × (Y × K) ↦ (w.1, w.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hP : MeasurePreserving P (τ.prod mK) ((S.measure.prod T.measure).prod mK) :=
    (MeasurePreserving.mk hp hBase).prod (MeasurePreserving.id mK)
  have hSwap : MeasurePreserving (Prod.swap : K × (X × (Y × K)) → (X × (Y × K)) × K)
      (mK.prod τ) (τ.prod mK) := measurePreserving_swap
  have h := (measurePreserving_prodAssoc S.measure T.measure mK).comp (hP.comp (hF.comp hSwap))
  exact h.map_eq

/-- A weakly mixing system disjoint from the base is disjoint from a
compact-group skew extension of the base. -/
theorem disjoint_compactGroupSkew_of_weakMixing [Countable G]
    [StandardBorelSpace (X × (Y × K))] [Nonempty (X × (Y × K))]
    (S : System G X) (hWeak : IsWeaklyMixing S.koopmanZeroRep) (hDisj : Disjoint S T) :
    Disjoint S (compactGroupSkewSystem T c mK) := by
  intro τ hτ
  let := hτ.probability
  let E := compactGroupSkewSystem T c mK
  let I : FactorMap S S := ⟨id, MeasurePreserving.id _, fun _ ↦ rfl⟩
  have hBase : τ.map (fun w : X × (Y × K) ↦ (w.1, w.2.1)) = S.measure.prod T.measure :=
    hDisj _ (hτ.map I (compactGroupSkewFactor T c mK))
  have hAvg : skewJoiningAverageKernel τ ∘ₘ mK = S.measure.prod E.measure :=
    skewJoiningAverageKernel_comp T mK τ S hBase
  have hj (r : K) : IsJoining S E (skewJoiningAverageKernel τ r) := by
    rw [skewJoiningAverageKernel_apply]
    exact hτ.map I (skewRightFactor T c mK r)
  have he := ae_kernel_eq_of_extremeJoining_barycenter (lemma3 E hWeak) mK _
    (Eventually.of_forall hj) hAvg
  obtain ⟨r, hr⟩ := he.exists
  rw [skewJoiningAverageKernel_apply] at hr
  have hInv : skewJoiningRight (X := X) (Y := Y) r⁻¹ ∘ skewJoiningRight r = id := by
    funext w
    simp [skewJoiningRight, mul_assoc]
  calc
    τ = (τ.map (skewJoiningRight r)).map (skewJoiningRight r⁻¹) := by
      rw [Measure.map_map (measurable_skewJoiningRight _) (measurable_skewJoiningRight _),
        hInv, Measure.map_id]
    _ = S.measure.prod E.measure := by
      rw [hr]
      exact ((MeasurePreserving.id S.measure).prod (skewRightFactor T c mK r⁻¹).preserves).map_eq

end Mixing
