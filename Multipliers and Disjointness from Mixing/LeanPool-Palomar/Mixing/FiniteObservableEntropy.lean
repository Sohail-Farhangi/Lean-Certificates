/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EntropyErrorBound
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
noncomputable section

namespace Mixing

open MeasureTheory Set Function
open scoped BigOperators

variable {X A B : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]

local instance : MeasurableSpace (Option A) := ⊤
local instance : DiscreteMeasurableSpace (Option A) := ⟨fun _ ↦ trivial⟩

/-- Entropy of a finite observable under a probability measure. -/
def observableEntropy (μ : Measure X) (f : X → A) : ℝ :=
  shannonEntropy fun a ↦ μ.real (f ⁻¹' {a})

theorem sum_measureReal_observable_fibres (μ : Measure X) [IsFiniteMeasure μ]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    {f : X → A} (hf : Measurable f) {E : Set X} (hE : MeasurableSet E) :
    (∑ a, μ.real (E ∩ f ⁻¹' {a})) = μ.real E := by
  have he : (⋃ a : A, E ∩ f ⁻¹' {a}) = E := by
    ext x
    constructor
    · rintro hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      exact ha.1
    · intro hx
      exact mem_iUnion.mpr ⟨f x, hx, rfl⟩
  rw [← measureReal_iUnion_fintype, he]
  · intro a b hab
    exact disjoint_left.mpr fun x ha hb ↦
      hab ((show f x = a from ha.2).symm.trans (show f x = b from hb.2))
  · intro a
    exact hE.inter (hf (measurableSet_singleton a))

theorem sum_measureReal_observable_univ (μ : Measure X) [IsProbabilityMeasure μ]
    [MeasurableSpace A] [MeasurableSingletonClass A] {f : X → A} (hf : Measurable f) :
    (∑ a, μ.real (f ⁻¹' {a})) = 1 := by
  simpa [measureReal_def] using sum_measureReal_observable_fibres μ hf MeasurableSet.univ

/-- Entropy is subadditive for two finite observables on the same space,
regardless of whether they are independent. -/
theorem observableEntropy_prod_le (μ : Measure X) [IsProbabilityMeasure μ]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]
    {f : X → A} {g : X → B} (hf : Measurable f) (hg : Measurable g) :
    observableEntropy μ (fun x ↦ (f x, g x)) ≤ observableEntropy μ f + observableEntropy μ g := by
  let w (z : A × B) := μ.real ((fun x ↦ (f x, g x)) ⁻¹' {z})
  have h₀ (z : A × B) : 0 ≤ w z := ENNReal.toReal_nonneg
  have h₁ : ∑ z, w z = 1 := sum_measureReal_observable_univ μ (hf.prodMk hg)
  have hA (a : A) : (∑ b, w (a,b)) = μ.real (f ⁻¹' {a}) := by
    have he (b : B) : (fun x ↦ (f x, g x)) ⁻¹' {(a, b)} = (f ⁻¹' {a}) ∩ (g ⁻¹' {b}) := by
      ext x
      simp
    simp_rw [w, he]
    exact sum_measureReal_observable_fibres μ hg (hf (measurableSet_singleton a))
  have hB (b : B) : (∑ a, w (a,b)) = μ.real (g ⁻¹' {b}) := by
    have he (a : A) : (fun x ↦ (f x, g x)) ⁻¹' {(a, b)} = (g ⁻¹' {b}) ∩ (f ⁻¹' {a}) := by
      ext x
      simp [and_comm]
    simp_rw [w, he]
    exact sum_measureReal_observable_fibres μ hf (hg (measurableSet_singleton b))
  have h := shannonEntropy_joint_le w h₀ h₁
  simp_rw [hA, hB] at h
  exact h

/-- Entropy decreases under deterministic postprocessing. -/
theorem observableEntropy_comp_le (μ : Measure X) [IsProbabilityMeasure μ]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSingletonClass B]
    {f : X → A} {g : A → B} (hf : Measurable f) (hg : Measurable g) :
    observableEntropy μ (g ∘ f) ≤ observableEntropy μ f := by
  classical
  let p (a : A) := μ.real (f ⁻¹' {a})
  have hq (b : B) : (∑ a, if g a = b then p a else 0) = μ.real ((g ∘ f) ⁻¹' {b}) := by
    let E := (g ∘ f) ⁻¹' ({b} : Set B)
    have he (a : A) : μ.real (E ∩ f ⁻¹' {a}) = if g a = b then p a else 0 := by
      by_cases h : g a = b
      · have hset : E ∩ f ⁻¹' {a} = f ⁻¹' {a} := inter_eq_right.2 fun x hx ↦ by
          have hx' : f x = a := hx
          show g (f x) = b
          rwa [hx']
        rw [hset, ite_eq_left h]
      · have hset : E ∩ f ⁻¹' {a} = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
          have h1 : g (f x) = b := hx.1
          have h2 : f x = a := hx.2
          exact h (h2 ▸ h1)
        rw [hset, ite_eq_right h, measureReal_empty]
    simp_rw [← he]
    exact sum_measureReal_observable_fibres μ hf ((hg.comp hf) (measurableSet_singleton b))
  have h := shannonEntropy_coarsen_le p (fun _ ↦ ENNReal.toReal_nonneg) g
  simp_rw [hq] at h
  exact h

/-- Entropy of the optional correction that records the true value when
an approximating finite observable gives the wrong value. -/
theorem observableEntropy_correction_le (μ : Measure X) [IsProbabilityMeasure μ]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [DecidableEq A]
    {f g : X → A} (hf : Measurable f) (hg : Measurable g) :
    observableEntropy μ (fun x ↦ if f x = g x then none else some (f x)) ≤
      entropyErrorBound (Fintype.card A) (μ.real {x | f x ≠ g x}) := by
  let c (x : X) := if f x = g x then none else some (f x)
  have hE : MeasurableSet {x | f x ≠ g x} := (measurableSet_eq_fun hf hg).compl
  have hC : Measurable c :=
    measurable_const.ite (measurableSet_eq_fun hf hg) ((measurable_of_finite Option.some).comp hf)
  have he (a : A) : c ⁻¹' {some a} = {x | f x ≠ g x} ∩ f ⁻¹' {a} := by
    ext x
    by_cases h : f x = g x <;> simp [c, h]
  have hsum : (∑ a, μ.real (c ⁻¹' {some a})) = μ.real {x | f x ≠ g x} := by
    simp_rw [he]
    exact sum_measureReal_observable_fibres μ hf hE
  have h := shannonEntropy_option_le (fun o ↦ μ.real (c ⁻¹' {o}))
    (fun _ ↦ ENNReal.toReal_nonneg) (sum_measureReal_observable_univ μ hC)
  rw [hsum] at h
  exact h

/-- The entropy of a finite observable is bounded by the entropy of its
approximation plus the entropy of the correction. -/
theorem observableEntropy_le_add_correction (μ : Measure X) [IsProbabilityMeasure μ]
    [MeasurableSpace A] [MeasurableSingletonClass A] [DecidableEq A]
    {f g : X → A} (hf : Measurable f) (hg : Measurable g) :
    observableEntropy μ f ≤ observableEntropy μ g +
      observableEntropy μ (fun x ↦ if f x = g x then none else some (f x)) := by
  let c (x : X) := if f x = g x then none else some (f x)
  let d (p : A × Option A) := p.2.getD p.1
  have hc : Measurable c :=
    measurable_const.ite (measurableSet_eq_fun hf hg) ((measurable_of_finite Option.some).comp hf)
  have he : d ∘ (fun x ↦ (g x, c x)) = f := by
    funext x
    by_cases h : f x = g x <;> simp [d, c, h]
  have h := observableEntropy_comp_le μ (hg.prodMk hc) (measurable_of_finite d)
  rw [he] at h
  exact h.trans (observableEntropy_prod_le μ hg hc)

/-- An upper bound on the entropy of a finite tuple of observations. -/
theorem observableEntropy_fin_le (μ : Measure X) [IsProbabilityMeasure μ]
    [MeasurableSpace A] [MeasurableSingletonClass A] {n : ℕ}
    (f : Fin n → X → A) (hF : ∀ i, Measurable (f i)) :
    observableEntropy μ (fun x i ↦ f i x) ≤ ∑ i, observableEntropy μ (f i) := by
  induction n with
  | zero =>
    simp [observableEntropy, shannonEntropy, show ∀ w : Fin 0 → A,
      (fun x i ↦ f i x) ⁻¹' {w} = Set.univ from fun w ↦ eq_univ_of_forall fun x ↦
        Subsingleton.elim _ _]
  | succ n ih =>
    let t (x : X) (i : Fin n) := f i.succ x
    have ht : Measurable t := Measurable.of_eval fun i ↦ hF i.succ
    have he : (fun z : A × (Fin n → A) ↦ Fin.cons z.1 z.2) ∘ (fun x ↦ (f 0 x, t x)) =
        (fun x i ↦ f i x) := by
      funext x i
      cases i using Fin.cases <;> rfl
    have h := observableEntropy_comp_le μ ((hF 0).prodMk ht)
      (measurable_of_finite (fun z : A × (Fin n → A) ↦ (Fin.cons z.1 z.2 : Fin (n + 1) → A)))
    rw [he] at h
    rw [Fin.sum_univ_succ]
    exact (h.trans (observableEntropy_prod_le μ (hF 0) ht)).trans
      (add_le_add_right (ih (fun i ↦ f i.succ) (fun i ↦ hF i.succ)) _)

end Mixing
