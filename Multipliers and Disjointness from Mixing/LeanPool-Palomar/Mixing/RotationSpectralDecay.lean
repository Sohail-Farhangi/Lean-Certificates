/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CentralCharacterSpectrum
public import Mixing.SpectralTypeDisjointness
public import Mixing.ComplementaryMixingProduct

/-! # Decay from full circle modulation -/

@[expose] public section
noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace Topology

namespace Mixing

local notation "𝕋" => UnitAddCircle
local notation "haar" => (AddCircle.haarAddCircle : Measure 𝕋)
local notation "ℤₘ" => Multiplicative ℤ

private theorem integer_generator_zpow (n : ℤ) : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
  change n • (1 : ℤ) = n
  simp

theorem integerDualAngle_fourier (χ : DiscreteDual ℤₘ) (n : ℤ) :
    fourier n (integerDualAngle χ) = (dualEvaluation (Multiplicative.ofAdd n) χ : ℂ) := by
  rw [fourier_apply, AddCircle.toCircle_zsmul]
  have he : AddCircle.toCircle (integerDualAngle χ) = dualEvaluation (Multiplicative.ofAdd (1:ℤ)) χ :=
    (AddCircle.homeomorphCircle_apply one_ne_zero _).symm.trans
      ((AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).apply_symm_apply _)
  rw [he]
  change ((χ (Multiplicative.ofAdd (1:ℤ)) ^ n : Circle) : ℂ) = (χ (Multiplicative.ofAdd n) : ℂ)
  rw [← map_zpow, integer_generator_zpow]

theorem integerDualAngle_bijective : Function.Bijective integerDualAngle := by
  constructor
  · intro χ ψ h
    apply ContinuousMonoidHom.ext
    intro g
    apply Subtype.ext
    change (dualEvaluation g χ : ℂ) = (dualEvaluation g ψ : ℂ)
    rw [← ofAdd_toAdd g, ← integerDualAngle_fourier, ← integerDualAngle_fourier, h]
  · intro s
    let _ : TopologicalSpace ℤₘ := ⊥
    let _ : DiscreteTopology ℤₘ := ⟨rfl⟩
    let d : DiscreteDual ℤₘ :=
      { toMonoidHom :=
          { toFun := fun n => (AddCircle.toCircle s) ^ n.toAdd
            map_one' := zpow_zero _
            map_mul' := fun g h => zpow_add _ g.toAdd h.toAdd }
        continuous_toFun := continuous_of_discreteTopology }
    refine ⟨d, ?_⟩
    have he : dualEvaluation (Multiplicative.ofAdd (1:ℤ)) d = AddCircle.toCircle s := by
      change (AddCircle.toCircle s) ^ (1:ℤ) = _
      rw [zpow_one]
    rw [integerDualAngle, he, ← AddCircle.homeomorphCircle_apply one_ne_zero, Homeomorph.symm_apply_apply]

/-- The standard homeomorphism between the dual of the integers and the unit circle. -/
def integerDualHomeomorph : DiscreteDual ℤₘ ≃ₜ 𝕋 :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective integerDualAngle integerDualAngle_bijective)
    integerDualAngle_continuous

def integerDualHaar : Measure (DiscreteDual ℤₘ) := (haar).map integerDualHomeomorph.symm

instance : IsFiniteMeasure integerDualHaar := by
  unfold integerDualHaar
  exact Measure.isFiniteMeasure_map _ _

theorem spectralFourier_integerDualHaar (g : ℤₘ) :
    spectralFourier integerDualHaar g = if g = 1 then 1 else 0 := by
  have hm : Continuous (fun χ : DiscreteDual ℤₘ => (dualEvaluation g χ : ℂ)) :=
    continuous_subtype_val.comp (dualEvaluation g).continuous
  rw [spectralFourier, integerDualHaar, integral_map integerDualHomeomorph.symm.continuous.measurable.aemeasurable
    hm.aestronglyMeasurable]
  have hF (s : 𝕋) : (dualEvaluation g (integerDualHomeomorph.symm s) : ℂ) = fourier g.toAdd s := by
    rw [← ofAdd_toAdd g, ← integerDualAngle_fourier]
    change fourier g.toAdd (integerDualHomeomorph (integerDualHomeomorph.symm s)) = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  simp_rw [hF]
  by_cases hg : g = 1
  · subst g
    simp
  · rw [ite_eq_right hg, integral_haar_fourier_zero _ (fun he => hg (Multiplicative.ext he))]

section Representation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : ℤₘ →* (H ≃ₗᵢ[ℂ] H))

theorem exists_haar_maximal_spectral_vector [SeparableSpace H] [Nontrivial H]
    (hMod : ∀ s : 𝕋, ∃ B : H ≃ₗᵢ[ℂ] H, ∀ (n : ℤ) (x : H),
      U (Multiplicative.ofAdd n) (B x) = fourier n s • B (U (Multiplicative.ofAdd n) x)) :
    ∃ x : H, IsMaximalSpectralVector U x ∧ dualVectorSpectralMeasure U x = integerDualHaar := by
  obtain ⟨x, hx, hHaar, hHaar'⟩ := integer_maximalSpectralType_haar_of_modulations U hMod
  let σ := dualVectorSpectralMeasure U x
  have he : (integerVectorSpectralMeasure U x).map integerDualHomeomorph.symm = σ := by
    rw [integerVectorSpectralMeasure_eq_map_dual, Measure.map_map integerDualHomeomorph.symm.measurable
      integerDualAngle_continuous.measurable]
    change σ.map (integerDualHomeomorph.symm ∘ integerDualHomeomorph) = σ
    rw [Homeomorph.symm_comp_self, Measure.map_id]
  have hν := integerDualHomeomorph.symm.toMeasurableEquiv.measurableEmbedding.absolutelyContinuous_map hHaar'
  have hν' := integerDualHomeomorph.symm.toMeasurableEquiv.measurableEmbedding.absolutelyContinuous_map hHaar
  change integerDualHaar ≪ (integerVectorSpectralMeasure U x).map integerDualHomeomorph.symm at hν
  change (integerVectorSpectralMeasure U x).map integerDualHomeomorph.symm ≪ integerDualHaar at hν'
  rw [he] at hν hν'
  let : Countable ℤₘ := by change Countable ℤ; infer_instance
  obtain ⟨y, hy⟩ := exists_dualVectorSpectralMeasure_eq_of_ac U x integerDualHaar hν
  refine ⟨y, ?_, hy⟩
  intro z
  rw [hy]
  exact (hx z).trans hν'

/-- Full-circle modulation implies cofinite weak-operator decay. -/
theorem isStronglyMixing_of_full_modulations [SeparableSpace H] [Nontrivial H]
    (hMod : ∀ s : 𝕋, ∃ B : H ≃ₗᵢ[ℂ] H, ∀ (n : ℤ) (x : H),
      U (Multiplicative.ofAdd n) (B x) = fourier n s • B (U (Multiplicative.ofAdd n) x)) :
    IsStronglyMixing U := by
  obtain ⟨x, hx, hxH⟩ := exists_haar_maximal_spectral_vector U hMod
  have hDiag : Tendsto (fun g => ⟪x, U g x⟫_ℂ) cofinite (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(Set.finite_singleton (1 : ℤₘ)).compl_mem_cofinite] with g hg
    change g ≠ 1 at hg
    rw [← spectralFourier_dualVectorSpectralMeasure, hxH, spectralFourier_integerDualHaar, ite_eq_right hg]
  have hZero (p : Ultrafilter ℤₘ) (hp : p ∈ freeUltrafilters ℤₘ) : ultrafilterOperator U p x = 0 := by
    let W := cyclicClosedSubmodule U x
    let V := unitarySubmoduleAction U W.toSubmodule (cyclicClosedSubmodule_invariant U x)
    let : CompleteSpace W.toSubmodule := W.isClosed.completeSpace_coe
    let v : W.toSubmodule := ⟨x, mem_cyclicClosedSubmodule U x⟩
    have h := (isStronglyMixing_iff_isUMixing_free V).mp (isStronglyMixing_cyclicClosedSubmodule U x hDiag) p hp
    have he := (intertwines_unitarySubmoduleAction U W.toSubmodule (cyclicClosedSubmodule_invariant U x)).ultrafilter p v
    rw [h, zero_apply, map_zero] at he
    exact he.symm
  apply (isStronglyMixing_iff_isUMixing_free U).2
  apply (theorem6_1_ii_positiveMeasureClass U (freeUltrafilters ℤₘ) x hx).2
  intro ν inst hν p hp q
  have hqp := mul_mem_freeUltrafilters (p := q) hp
  exact tendsto_spectralFourier_zero_of_ac U x (q*p) (hZero (q*p) hqp) ν hν

end Representation

/-- Central-character components with the full phase image have cofinite
weak-operator decay, the conclusion needed for free-ultrafilter generation. -/
theorem centralCharacterTime_stronglyMixing {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))
    {C : Subgroup Γ} (χ : C →* Circle)
    [SeparableSpace (centralCharacterSubmodule ρ χ)] [Nontrivial (centralCharacterSubmodule ρ χ)]
    (hC : C ≤ Subgroup.center Γ) (a : Γ)
    (hComm : ∀ s : 𝕋, ∃ (b : Γ) (u : C), a*b = b*a*(u : Γ) ∧ χ u = AddCircle.toCircle s) :
    IsStronglyMixing (centralCharacterTime ρ χ hC a) := by
  apply isStronglyMixing_of_full_modulations
  intro s
  obtain ⟨b, u, hab, hχ⟩ := hComm s
  exact centralCharacterTime_modulates ρ χ hC a b u hab s hχ

end Mixing
