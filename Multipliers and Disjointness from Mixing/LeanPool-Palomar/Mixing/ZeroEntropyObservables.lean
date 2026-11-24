/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EntropyWindows

/-! # Coarsening and finite products of zero-entropy observables -/

@[expose] public section

open Filter MeasureTheory Function Set
open scoped BigOperators ENNReal Topology Classical

namespace Mixing

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]
variable {A B : Type} [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- A constant observable has zero name entropy on every window. -/
theorem System.ObservableZeroEntropy.const (S : System G X) (a : A) :
    S.ObservableZeroEntropy (Function.const X a) := by
  have he (I : Finset G) : S.finiteNameEntropy (Function.const X a) I = 0 := by
    rw [S.finiteNameEntropy_eq_observableEntropy]
    unfold observableEntropy shannonEntropy
    have hzero (u : I → A) :
        S.measure.real ((S.windowName I (Function.const X a)) ⁻¹' {u}) *
          Real.log (S.measure.real ((S.windowName I (Function.const X a)) ⁻¹' {u})) = 0 := by
      have he : (S.windowName I (Function.const X a)) ⁻¹' {u} =
          if (fun _ : I ↦ a) = u then univ else ∅ := by
        ext x
        have hx : S.windowName I (Function.const X a) x = fun _ : I ↦ a := rfl
        by_cases h : (fun _ : I ↦ a) = u <;> simp [hx, h]
      rw [he]
      split <;> simp
    rw [Finset.sum_eq_zero fun u _ ↦ hzero u, neg_zero]
  intro I _
  simp_rw [he, zero_div]
  exact tendsto_const_nhds

/-- A function of a finite zero-entropy observable has zero entropy. -/
theorem System.ObservableZeroEntropy.comp {S : System G X} {f : X → A} (h : S.ObservableZeroEntropy f)
    (hf : Measurable f) {d : A → B} (hd : Measurable d) :
    S.ObservableZeroEntropy (d ∘ f) := by
  have hI (I : Finset G) : S.finiteNameEntropy (d ∘ f) I ≤ S.finiteNameEntropy f I := by
    let decode (w : I → A) (i : I) := d (w i)
    have hdecode : Measurable decode :=
      Measurable.of_eval fun i ↦ hd.comp (measurable_pi_apply i)
    have he : decode ∘ S.windowName I f = S.windowName I (d ∘ f) := rfl
    rw [S.finiteNameEntropy_eq_observableEntropy, S.finiteNameEntropy_eq_observableEntropy]
    rw [← he]
    exact observableEntropy_comp_le S.measure (f := S.windowName I f) (g := decode)
      (S.measurable_windowName I hf) hdecode
  intro I hF
  refine squeeze_zero (fun n ↦ div_nonneg (S.finiteNameEntropy_nonneg _ _) (by positivity))
    (fun n ↦ div_le_div_of_nonneg_right (hI (I n)) (by positivity)) (h I hF)

/-- Two finite zero-entropy observables jointly have zero entropy. -/
theorem System.ObservableZeroEntropy.prod {S : System G X} {f : X → A} {g : X → B}
    (h : S.ObservableZeroEntropy f) (h' : S.ObservableZeroEntropy g)
    (hf : Measurable f) (hg : Measurable g) :
    S.ObservableZeroEntropy (fun x ↦ (f x, g x)) := by
  have hb (I : Finset G) :
      S.finiteNameEntropy (fun x ↦ (f x, g x)) I ≤
        S.finiteNameEntropy f I + S.finiteNameEntropy g I := by
    let decode (v : (I → A) × (I → B)) (i : I) := (v.1 i, v.2 i)
    let w (x : X) := (S.windowName I f x, S.windowName I g x)
    have hw := (S.measurable_windowName I hf).prodMk (S.measurable_windowName I hg)
    have ha := observableEntropy_comp_le S.measure hw (measurable_of_finite decode)
    change observableEntropy S.measure (S.windowName I (fun x ↦ (f x, g x))) ≤
      observableEntropy S.measure w at ha
    simp_rw [S.finiteNameEntropy_eq_observableEntropy]
    exact ha.trans (observableEntropy_prod_le S.measure
      (S.measurable_windowName I hf) (S.measurable_windowName I hg))
  intro I hI
  have ht := (h I hI).add (h' I hI)
  have hbound (n : ℕ) : S.finiteNameEntropy (fun x ↦ (f x, g x)) (I n) / (I n).card ≤
      S.finiteNameEntropy f (I n) / (I n).card + S.finiteNameEntropy g (I n) / (I n).card := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (hb (I n)) (by positivity)
  exact squeeze_zero (fun n ↦ div_nonneg (S.finiteNameEntropy_nonneg _ _) (by positivity))
    hbound (by simpa only [zero_add] using ht)

set_option maxHeartbeats 600000 in
/-- A finite family of zero-entropy observables with a common alphabet jointly
has zero entropy. -/
theorem System.ObservableZeroEntropy.pi {ι : Type} [Fintype ι]
    {S : System G X} {f : ι → X → A}
    (h : ∀ i, S.ObservableZeroEntropy (f i)) (hf : ∀ i, Measurable (f i)) :
    S.ObservableZeroEntropy (fun x i ↦ f i x) := by
  have hb (I : Finset G) : S.finiteNameEntropy (fun x i ↦ f i x) I ≤
      ∑ i, S.finiteNameEntropy (f i) I := by
    let decode (v : ι → (I → A)) (j : I) (i : ι) := v i j
    let w (x : X) (i : ι) := S.windowName I (f i) x
    have hw (i : ι) : Measurable (fun x ↦ w x i) := S.measurable_windowName I (hf i)
    have ha := observableEntropy_comp_le S.measure (Measurable.of_eval hw)
      (measurable_of_finite decode)
    change observableEntropy S.measure (S.windowName I (fun x i ↦ f i x)) ≤
      observableEntropy S.measure w at ha
    simp_rw [S.finiteNameEntropy_eq_observableEntropy]
    have hW : observableEntropy S.measure w ≤
        ∑ i, observableEntropy S.measure (S.windowName I (f i)) :=
      observableEntropy_pi_le (ι := ι) S.measure
        (f := fun i ↦ S.windowName I (f i)) hw
    exact ha.trans hW
  intro I hI
  have ht : Tendsto (fun n ↦ ∑ i, S.finiteNameEntropy (f i) (I n) / (I n).card) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (s := Finset.univ) fun i _ ↦ h i I hI
  have hbound (n : ℕ) : S.finiteNameEntropy (fun x i ↦ f i x) (I n) / (I n).card ≤
      ∑ i, S.finiteNameEntropy (f i) (I n) / (I n).card := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hb (I n)) (by positivity)
  exact squeeze_zero (fun n ↦ div_nonneg (S.finiteNameEntropy_nonneg _ _) (by positivity)) hbound ht

end Mixing
