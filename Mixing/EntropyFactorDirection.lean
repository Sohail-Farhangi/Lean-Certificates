/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.IdentityDisjointness
public import Mixing.WeakMixing
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped BigOperators Topology

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- The Shannon entropy of the finite family of names of an observable
along a given finite subset of the acting group. -/
def System.finiteNameEntropy {A : Type} [Fintype A] (S : System G X) (f : X → A)
    (F : Finset G) : ℝ := by
  classical
  let p (u : F → A) := S.measure.real {x | ∀ g : F, f (S.act g x) = u g}
  exact -(∑ u : (F → A), p u * Real.log (p u))

/-- Zero measure entropy, expressed by the normalized Shannon entropy of
every finite measurable observable along Følner sequences. -/
def System.HasZeroEntropy (S : System G X) : Prop :=
  ∀ (A : Type) [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (f : X → A), Measurable f →
    ∀ F : ℕ → Finset G, IsFolnerSequence F →
      Tendsto (fun n ↦ S.finiteNameEntropy f (F n) / (F n).card) atTop (𝓝 0)

/-- The factor formulation of completely positive measure entropy:
every zero-entropy factor is trivial as a probability algebra. -/
def System.HasCompletelyPositiveEntropy (S : System G X) : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] (T : System G Y),
    FactorMap S T → T.HasZeroEntropy →
    ∀ B : Set Y, MeasurableSet B → T.measure B = 0 ∨ T.measure B = 1

/-- Each finite name of a factor observable has the same probability as
its pullback name, so its finite Shannon entropy is preserved by pullback. -/
theorem FactorMap.finiteNameEntropy_eq {Y : Type*} [MeasurableSpace Y]
    {S : System G X} {T : System G Y} (F : FactorMap S T)
    {A : Type} [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (f : Y → A) (hf : Measurable f) (I : Finset G) :
    T.finiteNameEntropy f I = S.finiteNameEntropy (f ∘ F.toFun) I := by
  classical
  simp only [System.finiteNameEntropy]
  apply congrArg (Neg.neg : ℝ → ℝ)
  apply Finset.sum_congr rfl
  intro w _
  let E : Set Y := {y | ∀ g : I, f (T.act g y) = w g}
  have hE : MeasurableSet E := by
    have he : E = ⋂ g : I, (f ∘ T.act g) ⁻¹' ({w g} : Set A) := by
      ext y
      simp [E]
    rw [he]
    exact MeasurableSet.iInter fun g ↦ (hf.comp (T.preserves g).measurable)
      (measurableSet_singleton (w g))
  have he : {x : X | ∀ g : I, (f ∘ F.toFun) (S.act g x) = w g} = F.toFun ⁻¹' E := by
    ext x
    have h (g : I) : F.toFun (S.act g x) = T.act g (F.toFun x) := congrFun (F.equivariant g) x
    simp only [mem_ofPred_eq, Function.comp_apply, mem_preimage, E, h]
  have hm : T.measure.real E = S.measure.real (F.toFun ⁻¹' E) := by
    unfold Measure.real
    rw [F.preserves.measure_preimage hE.nullMeasurableSet]
  simp only [he]
  change T.measure.real E * Real.log (T.measure.real E) = _
  rw [hm]

/-- Zero entropy passes to factors. -/
theorem FactorMap.hasZeroEntropy_target {Y : Type*} [MeasurableSpace Y]
    {S : System G X} {T : System G Y} (F : FactorMap S T) (hS : S.HasZeroEntropy) :
    T.HasZeroEntropy := by
  intro A _ _ _ f hf I hI
  simpa only [F.finiteNameEntropy_eq f hf] using
    hS A (f ∘ F.toFun) (hf.comp F.preserves.measurable) I hI

/-- The direction of Theorem 1.1(iv) from disjointness to completely
positive entropy. A nontrivial zero-entropy factor gives a graph joining
with an event of intermediate measure. -/
theorem hasCompletelyPositiveEntropy_of_disjoint_zeroEntropy (S : System G X)
    (hdis : ∀ (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] (T : System G Y),
      T.HasZeroEntropy → Disjoint S T) :
    S.HasCompletelyPositiveEntropy := by
  intro Y _ _ T F hZero B hB
  by_contra! h₂
  have hp : 0 < T.measure B := pos_iff_ne_zero.mpr h₂.1
  have hlt : T.measure B < 1 := lt_of_le_of_ne prob_le_one h₂.2
  exact F.not_disjoint_of_event hB hp hlt (hdis Y T hZero)

end Mixing
