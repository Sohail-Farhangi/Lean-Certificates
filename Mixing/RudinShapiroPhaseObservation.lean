/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroReconstruction

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped BigOperators Classical ENNReal Topology

/-- The phase read from a word, with a default value when the test is ambiguous. -/
def rudinShapiroPhase (k : ℕ) (w : SignWords) : Fin (2 ^ k) :=
  if h : ∃! a : Fin (2 ^ k), rudinShapiroResidue k a w then Classical.choose h
  else ⟨0, by positivity⟩

theorem rudinShapiroPhase_spec {w : SignWords} (hw : w ∈ rudinShapiroSubshift) (k : ℕ) :
    rudinShapiroResidue k (rudinShapiroPhase k w) w := by
  have h := rudinShapiroResidue_existsUnique_of_mem hw k
  unfold rudinShapiroPhase
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).1

theorem rudinShapiroPhase_eq_iff {w : SignWords} (hw : w ∈ rudinShapiroSubshift)
    (k : ℕ) (a : Fin (2 ^ k)) :
    rudinShapiroPhase k w = a ↔ rudinShapiroResidue k a w := by
  have h := rudinShapiroResidue_existsUnique_of_mem hw k
  constructor
  · rintro rfl
    exact rudinShapiroPhase_spec hw k
  · intro ha
    exact (h.unique (rudinShapiroPhase_spec hw k) ha)

theorem measurable_rudinShapiroPhase (k : ℕ) : Measurable (rudinShapiroPhase k) := by
  classical
  let A (w : SignWords) (a : Fin (2 ^ k)) :=
    if rudinShapiroResidue k a w then true else false
  have hA : Measurable A := Measurable.of_eval fun a ↦
    measurable_const.ite (measurableSet_rudinShapiroResidue k a) measurable_const
  let decode (b : Fin (2 ^ k) → Bool) : Fin (2 ^ k) :=
    if h : ∃! a, b a = true then Classical.choose h else ⟨0, by positivity⟩
  have he : rudinShapiroPhase k = decode ∘ A := by
    funext w
    have h (a : Fin (2 ^ k)) : A w a = true ↔ rudinShapiroResidue k a w := by
      simp [A]
    have he : (∃! a, A w a = true) ↔ ∃! a : Fin (2 ^ k), rudinShapiroResidue k a w :=
      existsUnique_congr h
    change _ = decode (A w)
    unfold rudinShapiroPhase decode
    by_cases hh : ∃! a : Fin (2 ^ k), rudinShapiroResidue k a w
    · have hA' := he.mpr hh
      rw [dite_eq_left hh, dite_eq_left hA']
      exact hh.unique (Classical.choose_spec hh).1 ((h _).mp (Classical.choose_spec hA').1)
    · rw [dite_eq_right hh, dite_eq_right (fun hA' ↦ hh (he.mp hA'))]
  rw [he]
  exact (measurable_of_finite decode).comp hA

theorem measurableSet_rudinShapiroSubshift : MeasurableSet rudinShapiroSubshift := by
  have he : rudinShapiroSubshift =
      ⋂ (I : Finset ℤ) (N : ℕ), {w : SignWords | RudinShapiroPattern I N (fun i ↦ w i)} := by
    ext w
    simp [rudinShapiroSubshift]
  rw [he]
  refine MeasurableSet.iInter fun I ↦ MeasurableSet.iInter fun N ↦ ?_
  have hm : Measurable (fun w : SignWords ↦ fun i : I ↦ w i) :=
    Measurable.of_eval fun i : I ↦ measurable_pi_apply (i : ℤ)
  exact hm (show MeasurableSet {u : I → Bool | RudinShapiroPattern I N u} from
    MeasurableSet.of_discrete)

theorem measurableSet_rudinShapiroRegularPhase : MeasurableSet {w | RudinShapiroRegularPhase w} := by
  let Witness (i : ℤ) :=
    {a : ℕ × ℕ // a.2 < 2 ^ (a.1 + 1) ∧ 0 ≤ (a.2 : ℤ) + i ∧
      (a.2 : ℤ) + i < (2 : ℤ) ^ (a.1 + 1) ∧
      a.2 / 2 ^ a.1 = ((a.2 : ℤ) + i).toNat / 2 ^ a.1}
  have he : {w | RudinShapiroRegularPhase w} =
      ⋂ i : ℤ, ⋃ t : Witness i, {w | rudinShapiroResidue (t.val.1 + 1) t.val.2 w} := by
    ext w
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, RudinShapiroRegularPhase]
    constructor
    · intro h i
      obtain ⟨k, a, ha, hr, hlo, hhi, hh⟩ := h i
      exact ⟨⟨(k, a), ha, hlo, hhi, hh⟩, hr⟩
    · intro h i
      obtain ⟨⟨⟨k, a⟩, ha, hlo, hhi, hh⟩, hr⟩ := h i
      exact ⟨k, a, ha, hr, hlo, hhi, hh⟩
  rw [he]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iUnion fun t : Witness i ↦
    measurableSet_rudinShapiroResidue (t.val.1 + 1) t.val.2

/-- The space of dyadic phase observations. -/
abbrev RudinShapiroPhases := ∀ k : ℕ, Fin (2 ^ k)

/-- The space of dyadic phase observations together with the central sign. -/
abbrev RudinShapiroObservations := RudinShapiroPhases × Bool

def rudinShapiroPhaseSequence (w : SignWords) : RudinShapiroPhases :=
  fun k ↦ rudinShapiroPhase k w

theorem measurable_rudinShapiroPhaseSequence : Measurable rudinShapiroPhaseSequence :=
  Measurable.of_eval measurable_rudinShapiroPhase

def rudinShapiroObservations (w : SignWords) : RudinShapiroObservations :=
  (rudinShapiroPhaseSequence w, w 0)

theorem measurable_rudinShapiroObservations : Measurable rudinShapiroObservations :=
  measurable_rudinShapiroPhaseSequence.prodMk (measurable_pi_apply 0)

/-- Equality of the phases at one level implies equality at every lower level. -/
theorem rudinShapiroPhase_eq_of_le {u v : SignWords} (hu : u ∈ rudinShapiroSubshift)
    (hv : v ∈ rudinShapiroSubshift) {j k : ℕ} (hjk : j ≤ k)
    (h : rudinShapiroPhase k u = rudinShapiroPhase k v) :
    rudinShapiroPhase j u = rudinShapiroPhase j v := by
  induction hjk with
  | refl => exact h
  | @step n hjn ih =>
    apply ih
    apply Fin.ext
    have hu' := rudinShapiroResidue_succ_coherence_of_mem hu n
      (rudinShapiroPhase (n + 1) u) (rudinShapiroPhase n u)
      (rudinShapiroPhase_spec hu _) (rudinShapiroPhase_spec hu _)
    have hv' := rudinShapiroResidue_succ_coherence_of_mem hv n
      (rudinShapiroPhase (n + 1) v) (rudinShapiroPhase n v)
      (rudinShapiroPhase_spec hv _) (rudinShapiroPhase_spec hv _)
    rw [h] at hu'
    exact hu'.symm.trans hv'

/-- The conull Borel set on which a phase and sign identify the word. -/
def regularRudinShapiroWords : Set SignWords :=
  {w | w ∈ rudinShapiroSubshift ∧ RudinShapiroRegularPhase w}

theorem measurableSet_regularRudinShapiroWords : MeasurableSet regularRudinShapiroWords :=
  measurableSet_rudinShapiroSubshift.inter measurableSet_rudinShapiroRegularPhase

theorem ae_mem_regularRudinShapiroWords (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    ∀ᵐ w ∂(rudinShapiroOrbitLaw p : Measure SignWords), w ∈ regularRudinShapiroWords :=
  (ae_mem_rudinShapiroSubshift p hp).and (rudinShapiro_ae_regularPhase p hp)

theorem measurableEmbedding_regularRudinShapiroObservations :
    MeasurableEmbedding (fun w : regularRudinShapiroWords ↦ rudinShapiroObservations w.val) := by
  let : StandardBorelSpace regularRudinShapiroWords :=
    measurableSet_regularRudinShapiroWords.standardBorel
  let g (w : regularRudinShapiroWords) := rudinShapiroObservations w.val
  have hg : Measurable g := measurable_rudinShapiroObservations.comp measurable_subtype_coe
  have hi : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    have hSign : u.val 0 = v.val 0 := congrArg Prod.snd huv
    have hEq (k : ℕ) : rudinShapiroPhase k u.val = rudinShapiroPhase k v.val :=
      congrFun (congrArg Prod.fst huv) k
    apply rudinShapiro_eq_of_regular_phase_and_sign u.property.1 v.property.1 u.property.2 hSign
    intro k a ha
    let b : Fin (2 ^ k) := ⟨a, ha⟩
    change rudinShapiroResidue k b u.val ↔ rudinShapiroResidue k b v.val
    rw [← rudinShapiroPhase_eq_iff u.property.1 k b,
      ← rudinShapiroPhase_eq_iff v.property.1 k b, hEq]
  exact hg.measurableEmbedding hi

/-- On a conull set the phase observations recover each measurable set of words. -/
theorem ae_eq_preimage_rudinShapiroObservations (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    {s : Set SignWords} (hs : MeasurableSet s) :
    ∃ t : Set RudinShapiroObservations, MeasurableSet t ∧
      s =ᵐ[(rudinShapiroOrbitLaw p : Measure SignWords)] (rudinShapiroObservations ⁻¹' t) := by
  let g (w : regularRudinShapiroWords) := rudinShapiroObservations w.val
  have hg : MeasurableEmbedding g := measurableEmbedding_regularRudinShapiroObservations
  let T : Set regularRudinShapiroWords := Subtype.val ⁻¹' s
  refine ⟨g '' T, hg.measurableSet_image' (measurable_subtype_coe hs), ?_⟩
  filter_upwards [ae_mem_regularRudinShapiroWords p hp] with w hw
  change w ∈ s ↔ rudinShapiroObservations w ∈ g '' T
  constructor
  · intro h
    exact ⟨⟨w, hw⟩, h, rfl⟩
  · rintro ⟨v, hv, he⟩
    have hvw : v = ⟨w, hw⟩ := hg.injective he
    simpa only [T, mem_preimage, hvw] using hv

end Mixing
