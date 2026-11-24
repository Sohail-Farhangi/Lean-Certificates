/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ZeroEntropyObservables
public import Mixing.CountableJoinings
public import Mixing.ConditionalCopiesSystem

/-! # The zero-entropy σ-algebra and preservation under joinings -/

@[expose] public section

open Filter MeasureTheory Function Set
open scoped BigOperators ENNReal Topology Classical

namespace Mixing

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- A measurable event represented as a Boolean observable. -/
noncomputable def booleanEvent (A : Set X) (x : X) : Bool :=
  if x ∈ A then true else false

theorem measurable_booleanEvent {A : Set X} (hA : MeasurableSet A) :
    Measurable (booleanEvent A) :=
  measurable_const.ite hA measurable_const

/-- An event belongs to the zero-entropy σ-algebra if its Boolean observable
has zero entropy. -/
def System.ZeroEntropyEvent (S : System G X) (A : Set X) : Prop :=
  MeasurableSet A ∧ S.ObservableZeroEntropy (booleanEvent A)

theorem System.ZeroEntropyEvent.empty (S : System G X) : S.ZeroEntropyEvent ∅ := by
  refine ⟨MeasurableSet.empty, ?_⟩
  have he : booleanEvent (∅ : Set X) = Function.const X false := by
    funext x
    simp [booleanEvent]
  rw [he]
  exact System.ObservableZeroEntropy.const S false

theorem System.ZeroEntropyEvent.compl {S : System G X} {A : Set X}
    (hA : S.ZeroEntropyEvent A) : S.ZeroEntropyEvent Aᶜ := by
  have he : Bool.not ∘ booleanEvent A = booleanEvent Aᶜ := by
    funext x
    by_cases hx : x ∈ A <;> simp [booleanEvent, hx]
  refine ⟨hA.1.compl, ?_⟩
  rw [← he]
  exact hA.2.comp (measurable_booleanEvent hA.1) (measurable_of_finite Bool.not)

theorem System.ZeroEntropyEvent.inter {S : System G X} {A B : Set X}
    (hA : S.ZeroEntropyEvent A) (hB : S.ZeroEntropyEvent B) : S.ZeroEntropyEvent (A ∩ B) := by
  let f := fun x ↦ (booleanEvent A x, booleanEvent B x)
  let d : Bool × Bool → Bool := fun b ↦ b.1 && b.2
  have he : d ∘ f = booleanEvent (A ∩ B) := by
    funext x
    by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp [d, f, booleanEvent, hxA, hxB]
  have ha := measurable_booleanEvent hA.1
  have hb := measurable_booleanEvent hB.1
  refine ⟨hA.1.inter hB.1, ?_⟩
  rw [← he]
  exact (hA.2.prod hB.2 ha hb).comp (ha.prodMk hb) (measurable_of_finite d)

theorem System.ZeroEntropyEvent.union {S : System G X} {A B : Set X}
    (hA : S.ZeroEntropyEvent A) (hB : S.ZeroEntropyEvent B) : S.ZeroEntropyEvent (A ∪ B) := by
  simpa only [compl_inter, compl_compl] using (hA.compl.inter hB.compl).compl

/-- Countable unions belong to the zero-entropy σ-algebra. The Boolean
observable is approximated in probability by those of the finite unions. -/
theorem System.ZeroEntropyEvent.iUnion {S : System G X} {A : ℕ → Set X}
    (hA : ∀ n, S.ZeroEntropyEvent (A n)) : S.ZeroEntropyEvent (⋃ n, A n) := by
  let C := accumulate A
  let U := ⋃ n, A n
  have hU : MeasurableSet U := MeasurableSet.iUnion fun n ↦ (hA n).1
  have hC (n : ℕ) : S.ZeroEntropyEvent (C n) := by
    induction n with
    | zero => simpa only [C, accumulate_zero_nat] using hA 0
    | succ n h => simpa only [C, accumulate_succ] using h.union (hA (n+1))
  have hSub (n : ℕ) : C n ⊆ U := accumulate_subset_iUnion n
  have ht : Tendsto (fun n ↦ S.measure.real (C n)) atTop (𝓝 (S.measure.real U)) :=
    (ENNReal.continuousAt_toReal (measure_ne_top S.measure U)).tendsto.comp
      (tendsto_measure_iUnion_accumulate (μ := S.measure) (s := A))
  have hDiff : Tendsto (fun n ↦ S.measure.real U - S.measure.real (C n)) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := S.measure.real U)).sub ht
  refine ⟨hU, S.observableZeroEntropy_of_approximation (measurable_booleanEvent hU) ?_⟩
  intro ε hε
  obtain ⟨n, hn⟩ := (hDiff.eventually_lt_const hε).exists
  refine ⟨booleanEvent (C n), measurable_booleanEvent (hC n).1, (hC n).2, ?_⟩
  have he : {x | booleanEvent U x ≠ booleanEvent (C n) x} = U \ C n := by
    ext x
    by_cases hUC : x ∈ U
    · by_cases hc : x ∈ C n <;> simp [booleanEvent, hUC, hc]
    · have hc : x ∉ C n := fun hc ↦ hUC (hSub n hc)
      simp [booleanEvent, hUC, hc]
  rw [he, measureReal_sdiff (hSub n) (hC n).1]
  exact hn

/-- The σ-algebra of events with zero entropy. -/
@[instance_reducible]
def System.zeroEntropySigma (S : System G X) : MeasurableSpace X where
  MeasurableSet' := S.ZeroEntropyEvent
  measurableSet_empty := System.ZeroEntropyEvent.empty S
  measurableSet_compl _ := System.ZeroEntropyEvent.compl
  measurableSet_iUnion _ := System.ZeroEntropyEvent.iUnion

theorem System.zeroEntropySigma_le (S : System G X) : S.zeroEntropySigma ≤ (inferInstance : MeasurableSpace X) :=
  fun _ hs ↦ hs.1

/-- If every measurable event has zero entropy, then so does every finite
observable. The observable is decoded from the Boolean tests of its fibres. -/
theorem System.hasZeroEntropy_of_all_events (S : System G X)
    (hS : ∀ A : Set X, MeasurableSet A → S.ZeroEntropyEvent A) : S.HasZeroEntropy := by
  intro A _ _ _ f hf
  let : Nonempty X := nonempty_of_isProbabilityMeasure S.measure
  let : Nonempty A := Nonempty.map f inferInstance
  let V (x : X) (a : A) := booleanEvent (f ⁻¹' {a}) x
  have hV (a : A) : S.ZeroEntropyEvent (f ⁻¹' {a}) :=
    hS _ (hf (measurableSet_singleton a))
  let d (v : A → Bool) : A :=
    if h : ∃ a, v a = true then Classical.choose h else Classical.choice inferInstance
  have he : d ∘ V = f := by
    funext x
    have hx : ∃ a, V x a = true := ⟨f x, by simp [V, booleanEvent]⟩
    have hchoose : V x (Classical.choose hx) = true := Classical.choose_spec hx
    have hfx : f x = Classical.choose hx := by
      change (if f x = Classical.choose hx then true else false) = true at hchoose
      split at hchoose
      · assumption
      · contradiction
    change d (V x) = f x
    simpa [d, hx] using hfx.symm
  change S.ObservableZeroEntropy f
  rw [← he]
  have hm (a : A) : Measurable (fun x ↦ V x a) :=
    measurable_booleanEvent (hV a).1
  exact (System.ObservableZeroEntropy.pi (fun a ↦ (hV a).2) hm).comp
    (Measurable.of_eval hm) (measurable_of_finite d)

/-- Zero entropy passes to a family joining of zero-entropy coordinate systems.
The product σ-algebra is generated by coordinate events. -/
theorem IsFamilyJoining.hasZeroEntropy {ι : Type*} {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)]
    {T : ∀ i, System G (Y i)} {ν : Measure (∀ i, Y i)} (h : IsFamilyJoining T ν)
    (hT : ∀ i, (T i).HasZeroEntropy) : h.system.HasZeroEntropy := by
  apply h.system.hasZeroEntropy_of_all_events
  have hc (i : ι) : @Measurable (∀ i, Y i) (Y i) h.system.zeroEntropySigma _
      (fun x ↦ x i) := by
    intro A hA
    change h.system.ZeroEntropyEvent ((fun x ↦ x i) ⁻¹' A)
    refine ⟨(measurable_pi_apply i) hA, ?_⟩
    let F := h.coordinateFactor i
    have hm := measurable_booleanEvent hA
    have hI : (T i).ObservableZeroEntropy (booleanEvent A) := hT i Bool _ hm
    change h.system.ObservableZeroEntropy (booleanEvent A ∘ F.toFun)
    intro I hFo
    simpa only [F.finiteNameEntropy_eq _ hm] using hI I hFo
  have hid : @Measurable (∀ i, Y i) (∀ i, Y i) h.system.zeroEntropySigma _ id :=
    @Measurable.of_eval _ _ _ h.system.zeroEntropySigma _ _ hc
  have hle : (inferInstance : MeasurableSpace (∀ i, Y i)) ≤ h.system.zeroEntropySigma := by
    simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hid
  intro A hA
  exact hle A hA

/-- Relatively independent samples of a zero-entropy system have zero entropy. -/
theorem IsJoining.independentCopiesSystem_hasZeroEntropy {Y : Type*}
    [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
    [Nonempty X] [Nonempty Y] {S : System G X} {T : System G Y}
    {μ : Measure (X × Y)} (h : IsJoining S T μ) (hT : T.HasZeroEntropy) :
    h.independentCopiesSystem.HasZeroEntropy := by
  let hJ : IsFamilyJoining (fun _ : ℕ ↦ T) h.independentCopiesSystem.measure :=
    ⟨h.independentCopiesSystem.probability, fun i ↦ (h.independentCopiesFactor i).preserves,
      h.independentCopiesSystem.preserves⟩
  exact hJ.hasZeroEntropy (fun _ ↦ hT)

end Mixing
