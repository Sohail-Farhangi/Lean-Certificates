/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroObservationLaw
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Kernel.CompProdEqIff

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical ProbabilityTheory

/-- Conditional law of a Rudin–Shapiro word given its dyadic phase sequence. -/
def rudinShapiroPhaseConditionalLaw (p : Ultrafilter ℕ) : Kernel RudinShapiroPhases SignWords :=
  condDistrib id rudinShapiroPhaseSequence (rudinShapiroOrbitLaw p : Measure SignWords)

instance (p : Ultrafilter ℕ) : IsMarkovKernel (rudinShapiroPhaseConditionalLaw p) :=
  inferInstanceAs (IsMarkovKernel (condDistrib id rudinShapiroPhaseSequence
    (rudinShapiroOrbitLaw p : Measure SignWords)))

theorem rudinShapiroPhaseConditionalLaw_disintegrates (p : Ultrafilter ℕ) :
    rudinShapiroPhaseLaw p ⊗ₘ rudinShapiroPhaseConditionalLaw p =
      (rudinShapiroOrbitLaw p : Measure SignWords).map (fun w ↦ (rudinShapiroPhaseSequence w, w)) :=
  compProd_map_condDistrib measurable_rudinShapiroPhaseSequence.aemeasurable measurable_id.aemeasurable

private theorem ae_rudinShapiro_phaseConditionalLaw_support (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) :
    ∀ᵐ r ∂rudinShapiroPhaseLaw p, ∀ᵐ w ∂rudinShapiroPhaseConditionalLaw p r,
      w ∈ regularRudinShapiroWords ∧ rudinShapiroPhaseSequence w = r := by
  apply Measure.ae_ae_of_ae_compProd (p := fun x ↦
    x.2 ∈ regularRudinShapiroWords ∧ rudinShapiroPhaseSequence x.2 = x.1)
  rw [rudinShapiroPhaseConditionalLaw_disintegrates]
  have hM : MeasurableSet {x : RudinShapiroPhases × SignWords |
      x.2 ∈ regularRudinShapiroWords ∧ rudinShapiroPhaseSequence x.2 = x.1} :=
    (measurable_snd measurableSet_regularRudinShapiroWords).inter
      (measurableSet_eq_fun (measurable_rudinShapiroPhaseSequence.comp measurable_snd) measurable_fst)
  exact (ae_map_iff (measurable_rudinShapiroPhaseSequence.prodMk measurable_id).aemeasurable hM).mpr
    ((ae_mem_regularRudinShapiroWords p hp).mono fun w hw ↦ ⟨hw, rfl⟩)

private theorem ae_rudinShapiro_phaseConditionalLaw_sign (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) :
    ∀ᵐ r ∂rudinShapiroPhaseLaw p,
      (rudinShapiroPhaseConditionalLaw p r).map (fun w ↦ w 0) = rudinShapiroFairSign := by
  let ν := rudinShapiroPhaseLaw p
  let κ := rudinShapiroPhaseConditionalLaw p
  let e (w : SignWords) : Bool := w 0
  have he : Measurable e := measurable_pi_apply 0
  have h : ν ⊗ₘ κ.map e = ν ⊗ₘ Kernel.const _ rudinShapiroFairSign := by
    rw [Measure.compProd_map he, Measure.compProd_const]
    change ((rudinShapiroPhaseLaw p) ⊗ₘ (rudinShapiroPhaseConditionalLaw p)).map (Prod.map id e) = _
    have hm : Measurable (fun w : SignWords ↦ (rudinShapiroPhaseSequence w, w)) :=
      measurable_rudinShapiroPhaseSequence.prodMk measurable_id
    rw [rudinShapiroPhaseConditionalLaw_disintegrates, Measure.map_map (measurable_id.prodMap he) hm]
    exact rudinShapiroObservations_map_eq_prod p hp
  filter_upwards [Kernel.ae_eq_of_compProd_eq h] with r hr
  rw [← Kernel.map_apply κ he r, hr, Kernel.const_apply]

/-- Almost every dyadic phase has exactly two regular lifts, one per central
sign, and its conditional law puts half the mass on each lift. -/
theorem rudinShapiro_phaseConditionalLaw_twoPoint (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) :
    ∀ᵐ r ∂rudinShapiroPhaseLaw p, ∃ u : Bool → SignWords,
      Function.Injective u ∧
      (∀ b, u b ∈ regularRudinShapiroWords ∧ u b 0 = b ∧
        ∀ k, rudinShapiroResidue k (r k) (u b)) ∧
      (∀ w ∈ regularRudinShapiroWords,
        rudinShapiroPhaseSequence w = r ↔ ∃ b, w = u b) ∧
      rudinShapiroPhaseConditionalLaw p r =
        (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (u false) + Measure.dirac (u true)) := by
  filter_upwards [ae_rudinShapiro_phaseConditionalLaw_support p hp,
    ae_rudinShapiro_phaseConditionalLaw_sign p hp] with r hSupport hSign
  let κ := rudinShapiroPhaseConditionalLaw p r
  let A (b : Bool) := {w : SignWords | w ∈ regularRudinShapiroWords ∧
    rudinShapiroPhaseSequence w = r ∧ w 0 = b}
  have hMass (b : Bool) : κ (A b) = (2 : ℝ≥0∞)⁻¹ := by
    have ha : A b =ᵐ[κ] {w | w 0 = b} := hSupport.mono fun w hw ↦ by
      change (w ∈ regularRudinShapiroWords ∧ rudinShapiroPhaseSequence w = r ∧ w 0 = b) ↔ w 0 = b
      simp only [hw.1, hw.2, true_and]
    rw [measure_congr ha]
    have hb := congrArg (fun μ : Measure Bool ↦ μ {b}) hSign
    rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton b),
      rudinShapiroFairSign_apply_singleton] at hb
    exact hb
  have hex (b : Bool) : ∃ w : SignWords, w ∈ A b := by
    by_contra! hn
    have he : A b = ∅ := Set.eq_empty_iff_forall_notMem.mpr hn
    have hz := hMass b
    rw [he, measure_empty] at hz
    exact ENNReal.inv_ne_zero.mpr (by norm_num) hz.symm
  choose u hu using hex
  have hA (b : Bool) : A b = {u b} := by
    ext w
    constructor
    · intro hw
      have hgu : rudinShapiroObservations w = rudinShapiroObservations (u b) := by
        change (rudinShapiroPhaseSequence w, w 0) = (rudinShapiroPhaseSequence (u b), u b 0)
        rw [hw.2.1, hw.2.2, (hu b).2.1, (hu b).2.2]
      have he : (⟨w, hw.1⟩ : regularRudinShapiroWords) = ⟨u b, (hu b).1⟩ :=
        measurableEmbedding_regularRudinShapiroObservations.injective hgu
      exact congrArg Subtype.val he
    · rintro (rfl : w = u b)
      exact hu b
  have huPhase (b : Bool) : rudinShapiroPhaseSequence (u b) = r := (hu b).2.1
  have huSign (b : Bool) : u b 0 = b := (hu b).2.2
  have hInj : Function.Injective u := by
    intro a b h
    rw [← huSign a, ← huSign b, h]
  have hExact (w : SignWords) (hw : w ∈ regularRudinShapiroWords) :
      rudinShapiroPhaseSequence w = r ↔ ∃ b, w = u b := by
    constructor
    · intro h
      have hm : w ∈ A (w 0) := ⟨hw, h, rfl⟩
      rw [hA] at hm
      exact ⟨w 0, hm⟩
    · rintro ⟨b, rfl⟩
      exact huPhase b
  refine ⟨u, hInj, ?_, hExact, ?_⟩
  · intro b
    refine ⟨(hu b).1, huSign b, fun k ↦ ?_⟩
    exact (rudinShapiroPhase_eq_iff (hu b).1.1 k (r k)).mp (congrFun (huPhase b) k)
  · change κ = _
    have hPoint (b : Bool) : κ {u b} = (2 : ℝ≥0∞)⁻¹ := (hA b) ▸ hMass b
    have hSupp : ∀ᵐ w ∂κ, w = u false ∨ w = u true :=
      hSupport.mono fun w hw ↦ by
        obtain ⟨b, h⟩ := (hExact w hw.1).mp hw.2
        cases b with
        | false => exact Or.inl h
        | true => exact Or.inr h
    apply Measure.ext
    intro s hs
    have he : s =ᵐ[κ] ((s ∩ {u false}) ∪ (s ∩ {u true})) :=
      hSupp.mono fun w h ↦ by
        change w ∈ s ↔ (w ∈ s ∧ w = u false) ∨ (w ∈ s ∧ w = u true)
        exact ⟨fun hw ↦ h.elim (fun he' ↦ Or.inl ⟨hw, he'⟩) (fun he' ↦ Or.inr ⟨hw, he'⟩),
          fun h' ↦ h'.elim And.left And.left⟩
    have hd : _root_.Disjoint (s ∩ {u false}) (s ∩ {u true}) := Set.disjoint_left.mpr fun w h₁ h₂ ↦ by
      have hh : u false = u true := (show w = u false from h₁.2).symm.trans h₂.2
      exact Bool.noConfusion (hInj hh)
    have hEval (b : Bool) : κ (s ∩ {u b}) =
        (2 : ℝ≥0∞)⁻¹ * Measure.dirac (u b) s := by
      rw [Measure.dirac_apply' _ hs]
      by_cases h : u b ∈ s
      · have he' : s ∩ {u b} = {u b} := inter_eq_right.mpr (singleton_subset_iff.mpr h)
        rw [he', hPoint, indicator_of_mem h]
        exact (mul_one _).symm
      · have he' : s ∩ {u b} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro w ⟨hw, rfl : w = u b⟩
          exact h hw
        rw [he', measure_empty, indicator_of_notMem h, mul_zero]
    rw [measure_congr he, measure_union hd (hs.inter (measurableSet_singleton _)), hEval, hEval,
      smul_apply, add_apply, smul_eq_mul, mul_add]

end Mixing
