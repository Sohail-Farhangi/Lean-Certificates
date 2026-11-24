/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroAtomDensity
public import Mathlib.Probability.UniformOn

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal Topology

def rudinShapiroPhaseLaw (p : Ultrafilter ℕ) : Measure RudinShapiroPhases :=
  (rudinShapiroOrbitLaw p : Measure SignWords).map rudinShapiroPhaseSequence

instance (p : Ultrafilter ℕ) : IsProbabilityMeasure (rudinShapiroPhaseLaw p) :=
  (Measure.isProbabilityMeasure_map_iff measurable_rudinShapiroPhaseSequence.aemeasurable).mpr inferInstance

def rudinShapiroFairSign : Measure Bool := uniformOn univ

instance : IsProbabilityMeasure rudinShapiroFairSign :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn (univ : Set Bool)))

theorem rudinShapiroFairSign_apply_singleton (b : Bool) : rudinShapiroFairSign {b} = (2 : ℝ≥0∞)⁻¹ := by
  rw [rudinShapiroFairSign, uniformOn_univ]
  norm_num

private theorem measure_rudinShapiro_selectedPhase (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) (k : ℕ) (a : Fin (2 ^ k)) :
    (rudinShapiroOrbitLaw p : Measure SignWords) {w | rudinShapiroPhase k w = a} =
      ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  have ha : {w | rudinShapiroPhase k w = a} =ᵐ[(rudinShapiroOrbitLaw p : Measure SignWords)]
      {w | rudinShapiroResidue k a w} :=
    (ae_mem_rudinShapiroSubshift p hp).mono fun w hw ↦ rudinShapiroPhase_eq_iff hw k a
  rw [measure_congr ha]
  exact measure_rudinShapiro_residue p hp k a

private theorem measure_rudinShapiro_selectedPhase_sign (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) (k : ℕ) (a : Fin (2 ^ k)) (b : Bool) :
    (rudinShapiroOrbitLaw p : Measure SignWords) {w | rudinShapiroPhase k w = a ∧ w 0 = b} =
      ((2 : ℝ≥0∞) ^ k)⁻¹ * (2 : ℝ≥0∞)⁻¹ := by
  have ha : {w | rudinShapiroPhase k w = a ∧ w 0 = b} =ᵐ[(rudinShapiroOrbitLaw p : Measure SignWords)]
      {w | rudinShapiroResidue k a w ∧ w 0 = b} :=
    (ae_mem_rudinShapiroSubshift p hp).mono fun w hw ↦
      and_congr_left' (rudinShapiroPhase_eq_iff hw k a)
  rw [measure_congr ha,
    measure_rudinShapiro_residueSign p hp k a b a.isLt, ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.div_eq_inv_mul, one_div,
    ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

private theorem measure_rudinShapiro_prefix_slice (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) {t : Set RudinShapiroObservations}
    (hPrefix : t ∈ rudinShapiroPrefixEvents) (b : Bool) :
    (rudinShapiroOrbitLaw p : Measure SignWords)
      {w | (rudinShapiroPhaseSequence w, b) ∈ t ∧ w 0 = b} =
    (rudinShapiroOrbitLaw p : Measure SignWords)
      {w | (rudinShapiroPhaseSequence w, b) ∈ t} * (2 : ℝ≥0∞)⁻¹ := by
  obtain ⟨k, hk⟩ := hPrefix
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  let S := {w : SignWords | (rudinShapiroPhaseSequence w, b) ∈ t}
  let D := {w : SignWords | w 0 = b}
  let A (a : Fin (2 ^ k)) := {w : SignWords | rudinShapiroPhase k w = a}
  let I : Finset (Fin (2 ^ k)) := Finset.univ.filter fun a ↦
    ∃ w ∈ rudinShapiroSubshift, w ∈ S ∧ w ∈ A a
  have hI (w : SignWords) (hw : w ∈ rudinShapiroSubshift) :
      w ∈ S ↔ rudinShapiroPhase k w ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h ↦ ⟨w, hw, h, rfl⟩
    · rintro ⟨v, hv, hS, hvA⟩
      exact (hk (rudinShapiroPhaseSequence v, b) (rudinShapiroPhaseSequence w, b)
        (fun j hj ↦ rudinShapiroPhase_eq_of_le hv hw hj hvA) rfl).mp hS
  have hU : S =ᵐ[μ] (⋃ a ∈ I, A a) := (ae_mem_rudinShapiroSubshift p hp).mono fun w hw ↦ by
    rw [hI w hw]
    simp only [mem_iUnion]
    exact ⟨fun h ↦ ⟨_, h, rfl⟩, fun ⟨a, ha, he⟩ ↦ (show rudinShapiroPhase k w = a from he) ▸ ha⟩
  have hUD : S ∩ D =ᵐ[μ] (⋃ a ∈ I, A a ∩ D) := hU.mono fun w hw ↦ by
    change (w ∈ S ∧ w ∈ D) ↔ _
    rw [hw]
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun ⟨⟨a, ha, h⟩, hD⟩ ↦ ⟨a, ha, h, hD⟩,
      fun ⟨a, ha, h, hD⟩ ↦ ⟨⟨a, ha, h⟩, hD⟩⟩
  have hA (a : Fin (2 ^ k)) : MeasurableSet (A a) :=
    measurable_rudinShapiroPhase k (measurableSet_singleton a)
  have hD : MeasurableSet D := by
    have hm : Measurable (fun w : SignWords ↦ w 0) := measurable_pi_apply 0
    exact hm (measurableSet_singleton b)
  have hDisj : PairwiseDisjoint (↑I : Set (Fin (2 ^ k))) A := by
    intro a _ c _ hac
    exact Set.disjoint_left.mpr fun w (ha : rudinShapiroPhase k w = a) (hc : rudinShapiroPhase k w = c) ↦
      hac (ha.symm.trans hc)
  have hDisj' : PairwiseDisjoint (↑I : Set (Fin (2 ^ k))) (fun a ↦ A a ∩ D) := by
    intro a ha c hc hac
    exact (hDisj ha hc hac).mono inter_subset_left inter_subset_left
  change μ (S ∩ D) = μ S * _
  rw [measure_congr hUD, measure_congr hU, measure_biUnion_finset hDisj' (fun a _ ↦ (hA a).inter hD),
    measure_biUnion_finset hDisj (fun a _ ↦ hA a), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  change μ {w | rudinShapiroPhase k w = a ∧ w 0 = b} = μ {w | rudinShapiroPhase k w = a} * _
  rw [measure_rudinShapiro_selectedPhase_sign p hp k a b, measure_rudinShapiro_selectedPhase p hp k a]

/-- The law of the complete dyadic phase sequence and the central sign is
the product of the phase marginal and the fair Boolean law. -/
theorem rudinShapiroObservations_map_eq_prod (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    (rudinShapiroOrbitLaw p : Measure SignWords).map rudinShapiroObservations =
      (rudinShapiroPhaseLaw p).prod rudinShapiroFairSign := by
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  let γ := μ.map rudinShapiroObservations
  let ν := rudinShapiroPhaseLaw p
  let : IsFiniteMeasure γ := Measure.isFiniteMeasure_map μ _
  have hPi : IsPiSystem rudinShapiroPrefixEvents := fun _ hu _ hv _ ↦
    rudinShapiroPrefixEvents_isSetAlgebra.inter_mem hu hv
  have hCover : (⋃ _ : ℕ, (univ : Set RudinShapiroObservations)) = univ := iUnion_const _
  apply Measure.ext_of_generateFrom_of_iUnion rudinShapiroPrefixEvents (fun _ ↦ univ)
    rudinShapiroPrefixEvents_generate hPi hCover
    (fun _ ↦ rudinShapiroPrefixEvents_isSetAlgebra.univ_mem)
    (fun _ ↦ measure_ne_top γ _)
  intro t ht
  let S (b : Bool) := {r : RudinShapiroPhases | (r, b) ∈ t}
  let T (b : Bool) := S b ×ˢ ({b} : Set Bool)
  have hS (b : Bool) : MeasurableSet (S b) := by
    have hm : Measurable (fun r : RudinShapiroPhases ↦ (r, b)) :=
      measurable_id.prodMk measurable_const
    exact hm (measurableSet_of_prefixEvent ht)
  have hT (b : Bool) : MeasurableSet (T b) := (hS b).prod (measurableSet_singleton b)
  have hDisj : _root_.Disjoint (T true) (T false) := Set.disjoint_left.mpr fun r h₁ h₂ ↦ by
    have h₁' : r.2 = true := h₁.2
    have h₂' : r.2 = false := h₂.2
    exact Bool.noConfusion (h₁'.symm.trans h₂')
  have he : t = T true ∪ T false := by
    ext r
    rcases r with ⟨r, b⟩
    change (r, b) ∈ t ↔ (((r, true) ∈ t ∧ b = true) ∨ ((r, false) ∈ t ∧ b = false))
    cases b <;> simp
  have hSlice (b : Bool) : γ (T b) = (ν.prod rudinShapiroFairSign) (T b) := by
    change γ (S b ×ˢ {b}) = (ν.prod rudinShapiroFairSign) (S b ×ˢ {b})
    rw [Measure.prod_prod, rudinShapiroFairSign_apply_singleton]
    change (μ.map rudinShapiroObservations) (T b) = (μ.map rudinShapiroPhaseSequence) (S b) * _
    rw [Measure.map_apply measurable_rudinShapiroObservations (hT b),
      Measure.map_apply measurable_rudinShapiroPhaseSequence (hS b)]
    exact measure_rudinShapiro_prefix_slice p hp ht b
  change γ t = (ν.prod rudinShapiroFairSign) t
  rw [he, measure_union hDisj (hT false), measure_union hDisj (hT false), hSlice, hSlice]

end Mixing
