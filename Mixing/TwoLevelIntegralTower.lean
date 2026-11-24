/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.System
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.GroupTheory.Perm.Basic

/-! # Integral towers with one optional upper level -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Classical

namespace Mixing

variable {X : Type*} [MeasurableSpace X]

def towerBottom (x : X) : X × Bool := (x, false)
def towerTop (x : X) : X × Bool := (x, true)

/-- The unnormalized measure of the two-level tower, with an upper level over `B`.
The unused upper-level points have measure zero. -/
noncomputable def twoLevelTowerRawMeasure (μ : Measure X) (B : Set X) : Measure (X × Bool) :=
  μ.map (fun x ↦ (x, false)) + (μ.restrict B).map (fun x ↦ (x, true))

/-- The measure of the tower divided by its total mass. -/
noncomputable def twoLevelTowerMeasure (μ : Measure X) (B : Set X) : Measure (X × Bool) :=
  (1 + μ B)⁻¹ • twoLevelTowerRawMeasure μ B

instance (μ : Measure X) [IsProbabilityMeasure μ] (B : Set X) :
    IsProbabilityMeasure (twoLevelTowerMeasure μ B) := by
  have hbot : Measurable (towerBottom : X → X × Bool) := measurable_id.prodMk measurable_const
  have htop : Measurable (towerTop : X → X × Bool) := measurable_id.prodMk measurable_const
  have htotal : twoLevelTowerRawMeasure μ B univ = 1 + μ B := by
    change (μ.map towerBottom + (μ.restrict B).map towerTop) univ = _
    rw [add_apply, Measure.map_apply hbot MeasurableSet.univ, Measure.map_apply htop MeasurableSet.univ,
      preimage_univ, preimage_univ, measure_univ, Measure.restrict_apply_univ]
  refine ⟨?_⟩
  rw [twoLevelTowerMeasure, smul_apply, smul_eq_mul, htotal]
  exact ENNReal.inv_mul_cancel (by simp) (ENNReal.add_ne_top.mpr ⟨by simp, measure_ne_top _ _⟩)

/-- The normalized tower measure is concentrated on the two allowed levels. -/
theorem ae_twoLevelTower_supported (μ : Measure X) (B : Set X) (hB : MeasurableSet B) :
    ∀ᵐ w ∂twoLevelTowerMeasure μ B, w.2 = false ∨ w.1 ∈ B := by
  let A : Set (X × Bool) := {w | w.2 = true ∧ w.1 ∉ B}
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun measurable_snd measurable_const).inter (measurable_fst hB).compl
  have he : {w : X × Bool | ¬ (w.2 = false ∨ w.1 ∈ B)} = A := by
    ext w
    rcases w with ⟨x, b⟩
    cases b <;> simp [A]
  have hbot : Measurable (towerBottom : X → X × Bool) := measurable_id.prodMk measurable_const
  have htop : Measurable (towerTop : X → X × Bool) := measurable_id.prodMk measurable_const
  have hpre₀ : towerBottom ⁻¹' A = ∅ := by ext x; simp [towerBottom, A]
  have hpre₁ : towerTop ⁻¹' A = Bᶜ := by ext x; simp [towerTop, A]
  rw [ae_iff, he, twoLevelTowerMeasure, smul_apply, smul_eq_mul]
  change _ * (μ.map towerBottom + (μ.restrict B).map towerTop) A = 0
  rw [add_apply, Measure.map_apply hbot hA, Measure.map_apply htop hA, hpre₀, hpre₁,
    measure_empty, Measure.restrict_apply hB.compl]
  simp

noncomputable def towerNext (e : X ≃ᵐ X) (B : Set X) (x : X × Bool) : X × Bool :=
  if x.2 = true then
    if x.1 ∈ B then towerBottom (e x.1) else x
  else if x.1 ∈ B then towerTop x.1 else towerBottom (e x.1)

noncomputable def towerPrevious (e : X ≃ᵐ X) (B : Set X) (x : X × Bool) : X × Bool :=
  if x.2 = true then
    if x.1 ∈ B then towerBottom x.1 else x
  else if e.symm x.1 ∈ B then towerTop (e.symm x.1) else towerBottom (e.symm x.1)

/-- The integral automorphism with return time two on `B` and one elsewhere. -/
noncomputable def twoLevelTowerEquiv (e : X ≃ᵐ X) (B : Set X) (hB : MeasurableSet B) :
    (X × Bool) ≃ᵐ (X × Bool) where
  toFun := towerNext e B
  invFun := towerPrevious e B
  left_inv := by
    rintro ⟨x, b⟩
    cases b <;> by_cases hx : x ∈ B <;>
      simp [towerNext, towerPrevious, towerBottom, towerTop, hx]
  right_inv := by
    rintro ⟨x, b⟩
    cases b
    · by_cases hx : e.symm x ∈ B <;>
        simp [towerNext, towerPrevious, towerBottom, towerTop, hx]
    · by_cases hx : x ∈ B <;>
        simp [towerNext, towerPrevious, towerBottom, towerTop, hx]
  measurable_toFun := by
    change Measurable (towerNext e B)
    have hm : MeasurableSet {x : X × Bool | x.1 ∈ B} := measurable_fst hB
    have hb : MeasurableSet {x : X × Bool | x.2 = true} :=
      measurableSet_eq_fun measurable_snd measurable_const
    have h0 : Measurable (towerBottom : X → X × Bool) := measurable_id.prodMk measurable_const
    have h1 : Measurable (towerTop : X → X × Bool) := measurable_id.prodMk measurable_const
    have hf : Measurable (fun w : X × Bool ↦ towerBottom (e w.1)) :=
      h0.comp (e.measurable.comp measurable_fst)
    exact (hf.ite hm measurable_id).ite hb ((h1.comp measurable_fst).ite hm hf)
  measurable_invFun := by
    change Measurable (towerPrevious e B)
    have hm : MeasurableSet {x : X × Bool | x.1 ∈ B} := measurable_fst hB
    have hi : MeasurableSet {x : X × Bool | e.symm x.1 ∈ B} := (e.symm.measurable.comp measurable_fst) hB
    have hb : MeasurableSet {x : X × Bool | x.2 = true} :=
      measurableSet_eq_fun measurable_snd measurable_const
    have h0 : Measurable (towerBottom : X → X × Bool) := measurable_id.prodMk measurable_const
    have h1 : Measurable (towerTop : X → X × Bool) := measurable_id.prodMk measurable_const
    have he : Measurable (fun w : X × Bool ↦ e.symm w.1) := e.symm.measurable.comp measurable_fst
    exact ((h0.comp measurable_fst).ite hm measurable_id).ite hb ((h1.comp he).ite hi (h0.comp he))

theorem twoLevelTowerEquiv_measurePreserving (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (B : Set X) (hB : MeasurableSet B) :
    MeasurePreserving (twoLevelTowerEquiv e B hB) (twoLevelTowerMeasure μ B)
      (twoLevelTowerMeasure μ B) := by
  let F := twoLevelTowerEquiv e B hB
  have hF := F.measurable
  have hbot : Measurable (towerBottom : X → X × Bool) := measurable_id.prodMk measurable_const
  have htop : Measurable (towerTop : X → X × Bool) := measurable_id.prodMk measurable_const
  have hb₁ : Measure.map (F ∘ towerBottom) (μ.restrict B) = Measure.map towerTop (μ.restrict B) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hB] with x hx
    change towerNext e B (towerBottom x) = _
    simp [towerNext, towerBottom, hx]
  have hb₀ : Measure.map (F ∘ towerBottom) (μ.restrict Bᶜ) =
      Measure.map (towerBottom ∘ e) (μ.restrict Bᶜ) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hB.compl] with x hx
    change towerNext e B (towerBottom x) = _
    simp [towerNext, towerBottom, show x ∉ B from hx]
  have ht : Measure.map (F ∘ towerTop) (μ.restrict B) =
      Measure.map (towerBottom ∘ e) (μ.restrict B) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hB] with x hx
    change towerNext e B (towerTop x) = _
    simp [towerNext, towerTop, hx]
  have heμ : Measure.map (towerBottom ∘ e) μ = Measure.map towerBottom μ := by
    rw [← Measure.map_map hbot e.measurable, he.map_eq]
  have hsplit : Measure.map (F ∘ towerBottom) μ = Measure.map towerTop (μ.restrict B) +
      Measure.map (towerBottom ∘ e) (μ.restrict Bᶜ) := by
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hB]
    rw [Measure.map_add _ _ (hF.comp hbot), hb₁, hb₀]
  refine ⟨hF, ?_⟩
  change Measure.map F (twoLevelTowerMeasure μ B) = _
  rw [twoLevelTowerMeasure, Measure.map_smul _ hF.aemeasurable]
  congr 1
  change Measure.map F (Measure.map towerBottom μ + Measure.map towerTop (μ.restrict B)) = _
  rw [Measure.map_add _ _ hF, Measure.map_map hF hbot, Measure.map_map hF htop, hsplit, ht]
  calc
    _ = (μ.restrict B + μ.restrict Bᶜ).map (towerBottom ∘ e) + (μ.restrict B).map towerTop := by
      rw [Measure.map_add _ _ (hbot.comp e.measurable)]
      ac_rfl
    _ = _ := by rw [Measure.restrict_add_restrict_compl hB, heμ]; rfl

theorem measurePreserving_perm_zpow (e : X ≃ᵐ X) {μ : Measure X}
    (he : MeasurePreserving e μ μ) (n : ℤ) :
    MeasurePreserving (((e.toEquiv : Equiv.Perm X) ^ n : Equiv.Perm X) : X → X) μ μ := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow]
    exact he.iterate n
  | negSucc n =>
    have hn : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
    rw [hn, zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow]
    exact (he.symm e).iterate _

/-- The probability-preserving integer action of the two-level integral tower. -/
noncomputable def twoLevelTowerSystem (e : X ≃ᵐ X) (μ : Measure X) [IsProbabilityMeasure μ]
    (he : MeasurePreserving e μ μ) (B : Set X) (hB : MeasurableSet B) :
    System (Multiplicative ℤ) (X × Bool) where
  measure := twoLevelTowerMeasure μ B
  probability := inferInstance
  act g := (((twoLevelTowerEquiv e B hB).toEquiv ^ g.toAdd : Equiv.Perm (X × Bool)) : _ → _)
  act_one := by funext x; change ((twoLevelTowerEquiv e B hB).toEquiv ^ (0 : ℤ)) x = x; simp
  act_mul g h := by
    funext x
    let F := (twoLevelTowerEquiv e B hB).toEquiv
    change (F ^ (g.toAdd + h.toAdd)) x = (F ^ g.toAdd) ((F ^ h.toAdd) x)
    rw [zpow_add]
    rfl
  preserves g := measurePreserving_perm_zpow _ (twoLevelTowerEquiv_measurePreserving e he B hB) g.toAdd

end Mixing
