/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.JoiningExtreme
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-! # Barycenters of joinings -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace Mixing

variable {G X Y Z : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private theorem map_joiningBarycenter_eq {V : Type*} [MeasurableSpace V]
    (ν : Measure Z) [IsProbabilityMeasure ν] (κ : Kernel Z (X × Y))
    {f : X × Y → V} {μ : Measure V} (hf : Measurable f)
    (hm : ∀ᵐ z ∂ν, (κ z).map f = μ) : (κ ∘ₘ ν).map f = μ := by
  rw [Measure.map_comp ν κ hf]
  calc
    _ = Kernel.const Z μ ∘ₘ ν := by
      apply Measure.comp_congr
      filter_upwards [hm] with z hz
      rw [Kernel.map_apply _ hf, Kernel.const_apply, hz]
    _ = _ := by rw [Measure.const_comp, measure_univ, one_smul]

/-- Barycenters over a probability measure preserve fixed marginals and invariance. -/
theorem isJoining_comp_of_ae_isJoining {S : System G X} {T : System G Y}
    (ν : Measure Z) [IsProbabilityMeasure ν] (κ : Kernel Z (X × Y)) [IsMarkovKernel κ]
    (hκ : ∀ᵐ z ∂ν, IsJoining S T (κ z)) : IsJoining S T (κ ∘ₘ ν) := by
  refine ⟨inferInstance,
    ⟨measurable_fst, map_joiningBarycenter_eq ν κ measurable_fst (hκ.mono fun _ h ↦ h.fst.map_eq)⟩,
    ⟨measurable_snd, map_joiningBarycenter_eq ν κ measurable_snd (hκ.mono fun _ h ↦ h.snd.map_eq)⟩, ?_⟩
  intro g
  have hf : Measurable (S.prodAct T g) :=
    (S.preserves g).measurable.prodMap (T.preserves g).measurable
  refine ⟨hf, ?_⟩
  rw [Measure.map_comp ν κ hf]
  apply Measure.comp_congr
  filter_upwards [hκ] with z hz
  rw [Kernel.map_apply _ hf, (hz.invariant g).map_eq]

/-- An extreme joining can be the barycenter of a family of joinings only
when that family almost everywhere equals the extreme joining. -/
theorem ae_kernel_eq_of_extremeJoining_barycenter [StandardBorelSpace (X × Y)] [Nonempty (X × Y)]
    {S : System G X} {T : System G Y} {τ : Measure (X × Y)}
    (hτ : IsExtremeJoining S T τ)
    (ν : Measure Z) [IsProbabilityMeasure ν] (κ : Kernel Z (X × Y)) [IsMarkovKernel κ]
    (hJoin : ∀ᵐ z ∂ν, IsJoining S T (κ z)) (hAvg : κ ∘ₘ ν = τ) :
    ∀ᵐ z ∂ν, κ z = τ := by
  let := hτ.1.probability
  have hrestrict (A : Set Z) (hA : MeasurableSet A) :
      κ ∘ₘ (ν.restrict A) = ν A • τ := by
    by_cases h₀ : ν A = 0
    · rw [Measure.restrict_eq_zero.mpr h₀, h₀, zero_smul]
      exact Measure.bind_zero_left κ
    by_cases h₁ : ν A = 1
    · have hAc : ν Aᶜ = 0 := by rw [measure_compl hA (measure_ne_top _ _), measure_univ, h₁, tsub_self]
      have hr := Measure.restrict_add_restrict_compl (μ := ν) hA
      rw [Measure.restrict_eq_zero.mpr hAc, add_zero] at hr
      rw [hr, hAvg, h₁, one_smul]
    let a := ν A
    let b := ν Aᶜ
    have ha : a < 1 := lt_of_le_of_ne (prob_le_one) h₁
    have hb : b = 1 - a := by rw [show b = ν Aᶜ from rfl, measure_compl hA (measure_ne_top _ _), measure_univ]
    have hb₀ : b ≠ 0 := hb ▸ (tsub_pos_of_lt ha).ne'
    let νA := a⁻¹ • ν.restrict A
    let νB := b⁻¹ • ν.restrict Aᶜ
    have hνA : IsProbabilityMeasure νA := ⟨by
      change a⁻¹ • (ν.restrict A) univ = 1
      rw [Measure.restrict_apply_univ]
      exact ENNReal.inv_mul_cancel h₀ (measure_ne_top _ _)⟩
    have hνB : IsProbabilityMeasure νB := ⟨by
      change b⁻¹ • (ν.restrict Aᶜ) univ = 1
      rw [Measure.restrict_apply_univ]
      exact ENNReal.inv_mul_cancel hb₀ (measure_ne_top _ _)⟩
    have hJA := isJoining_comp_of_ae_isJoining νA κ
      (((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _).ae_le hJoin)
    have hJB := isJoining_comp_of_ae_isJoining νB κ
      (((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _).ae_le hJoin)
    have hEA : a • (κ ∘ₘ νA) = κ ∘ₘ (ν.restrict A) := by
      rw [show νA = a⁻¹ • ν.restrict A from rfl, Measure.comp_smul, smul_smul,
        ENNReal.mul_inv_cancel h₀ (measure_ne_top _ _), one_smul]
    have hEB : b • (κ ∘ₘ νB) = κ ∘ₘ (ν.restrict Aᶜ) := by
      rw [show νB = b⁻¹ • ν.restrict Aᶜ from rfl, Measure.comp_smul, smul_smul,
        ENNReal.mul_inv_cancel hb₀ (measure_ne_top _ _), one_smul]
    have hSum : a • (κ ∘ₘ νA) + (1 - a) • (κ ∘ₘ νB) = τ := by
      rw [← hb, hEA, hEB, ← Measure.comp_add, Measure.restrict_add_restrict_compl hA, hAvg]
    have hEq := (hτ.2 _ _ hJA hJB a (pos_iff_ne_zero.mpr h₀) ha hSum).1
    rw [← hEA, hEq]
  have hprod : ν ⊗ₘ κ = ν.prod τ := by
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.compProd_apply_prod hA hB, Measure.prod_prod]
    change (∫⁻ z in A, κ z B ∂ν) = _
    rw [← Measure.bind_apply hB κ.aemeasurable]
    change (κ ∘ₘ (ν.restrict A)) B = _
    rw [hrestrict A hA, smul_apply, smul_eq_mul]
  let ρ := ν ⊗ₘ κ
  have hfst : ρ.fst = ν := Measure.fst_compProd _ _
  have hκ : ρ = ρ.fst ⊗ₘ κ := by rw [hfst]
  have hConst : ρ = ρ.fst ⊗ₘ Kernel.const Z τ := by
    rw [hfst, Measure.compProd_const]
    exact hprod
  have h₁ := eq_condKernel_of_measure_eq_compProd κ hκ
  have h₂ := eq_condKernel_of_measure_eq_compProd (Kernel.const Z τ) hConst
  rw [hfst] at h₁ h₂
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  exact hz₁.trans hz₂.symm

end Mixing
