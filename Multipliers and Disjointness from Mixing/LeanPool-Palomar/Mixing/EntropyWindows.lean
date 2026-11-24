/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EntropyFactorDirection
public import Mixing.FiniteObservableEntropy

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set Function
open scoped BigOperators Classical ENNReal Topology

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]
variable {A B : Type} [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]

local instance : MeasurableSpace (Option A) := ⊤
local instance : DiscreteMeasurableSpace (Option A) := ⟨fun _ ↦ trivial⟩

/-- The observable of names indexed by a finite window. -/
def System.windowName (S : System G X) (I : Finset G) (f : X → A) (x : X) (i : I) : A :=
  f (S.act i x)

omit [Fintype A] [MeasurableSingletonClass A] in
theorem System.measurable_windowName (S : System G X) (I : Finset G)
    {f : X → A} (hf : Measurable f) : Measurable (S.windowName I f) :=
  Measurable.of_eval fun i ↦ hf.comp (S.preserves i).measurable

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem System.finiteNameEntropy_eq_observableEntropy (S : System G X) (f : X → A) (I : Finset G) :
    S.finiteNameEntropy f I = observableEntropy S.measure (S.windowName I f) := by
  unfold System.finiteNameEntropy observableEntropy shannonEntropy
  apply congrArg (Neg.neg : ℝ → ℝ)
  apply Finset.sum_congr rfl
  intro u _
  have he : {x | ∀ i : I, f (S.act i x) = u i} = (S.windowName I f) ⁻¹' {u} := by
    ext x
    exact ⟨fun hx ↦ funext hx, fun hx ↦ congrFun (show S.windowName I f x = u from hx)⟩
  dsimp only
  rw [he]

theorem observableEntropy_comp_preserving {U : Type*} [MeasurableSpace U]
    {α : Measure U} {μ : Measure X} {t : U → X} (ht : MeasurePreserving t α μ)
    {f : X → A} (hf : Measurable f) :
    observableEntropy α (f ∘ t) = observableEntropy μ f := by
  unfold observableEntropy
  congr 1
  funext a
  change (α (t ⁻¹' (f ⁻¹' {a}))).toReal = (μ (f ⁻¹' {a})).toReal
  rw [ht.measure_preimage (hf (measurableSet_singleton a)).nullMeasurableSet]

theorem observableEntropy_pi_le {ι D : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {f : ι → X → D} (hf : ∀ i, Measurable (f i)) :
    observableEntropy μ (fun x i ↦ f i x) ≤ ∑ i, observableEntropy μ (f i) := by
  let e := Fintype.equivFin ι
  let g (x : X) (i : Fin (Fintype.card ι)) := f (e.symm i) x
  have hg (i : Fin (Fintype.card ι)) : Measurable (fun x ↦ g x i) := hf _
  have h : observableEntropy μ (fun x i ↦ f i x) ≤ observableEntropy μ g := by
    have he : (fun w i ↦ w (e i)) ∘ g = fun x i ↦ f i x := by
      funext x i
      simp [g]
    have hh := observableEntropy_comp_le μ (Measurable.of_eval hg)
      (measurable_of_finite (fun w : Fin (Fintype.card ι) → D ↦ fun i ↦ w (e i)))
    rw [he] at hh
    exact hh
  refine h.trans ((observableEntropy_fin_le μ (fun i x ↦ g x i) hg).trans_eq ?_)
  exact e.symm.sum_comp (fun i ↦ observableEntropy μ (f i))

/-- A uniform finite-window approximation bound. The normalized error
depends on the single-observable mismatch probability. -/
theorem System.finiteNameEntropy_le_of_approximation (S : System G X) (I : Finset G)
    [Nonempty A] [DecidableEq A] {f g : X → A} (hf : Measurable f) (hg : Measurable g) :
    S.finiteNameEntropy f I ≤ S.finiteNameEntropy g I +
      I.card * entropyErrorBound (Fintype.card A) (S.measure.real {x | f x ≠ g x}) := by
  let c (x : X) := if f x = g x then none else some (f x)
  let w (x : X) := (S.windowName I g x, S.windowName I c x)
  let d (v : (I → A) × (I → Option A)) (i : I) := (v.2 i).getD (v.1 i)
  have hc : Measurable c := measurable_const.ite (measurableSet_eq_fun hf hg)
    ((measurable_of_finite Option.some).comp hf)
  have he : d ∘ w = S.windowName I f := by
    funext x i
    change (if f (S.act i x) = g (S.act i x) then none else some (f (S.act i x))).getD
      (g (S.act i x)) = f (S.act i x)
    by_cases h : f (S.act i x) = g (S.act i x) <;> simp [h]
  have h := observableEntropy_comp_le S.measure
    ((S.measurable_windowName I hg).prodMk (S.measurable_windowName I hc))
    (measurable_of_finite d)
  change observableEntropy S.measure (d ∘ w) ≤ observableEntropy S.measure w at h
  rw [he] at h
  rw [S.finiteNameEntropy_eq_observableEntropy, S.finiteNameEntropy_eq_observableEntropy]
  refine h.trans ((observableEntropy_prod_le S.measure
    (S.measurable_windowName I hg) (S.measurable_windowName I hc)).trans ?_)
  gcongr
  refine (observableEntropy_pi_le (ι := I) S.measure
    (f := fun i x ↦ c (S.act i x)) (fun i ↦ hc.comp (S.preserves i).measurable)).trans ?_
  simp_rw [show ∀ i : I, observableEntropy S.measure (fun x ↦ c (S.act i x)) =
    observableEntropy S.measure c from
      fun i ↦ observableEntropy_comp_preserving (S.preserves i) hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (observableEntropy_correction_le S.measure hf hg) (by positivity)

/-- A finite observable has zero entropy if its name entropy divided by
window size tends to zero along every Følner sequence. -/
def System.ObservableZeroEntropy (S : System G X) (f : X → A) : Prop :=
  ∀ I : ℕ → Finset G, IsFolnerSequence I →
    Tendsto (fun n ↦ S.finiteNameEntropy f (I n) / (I n).card) atTop (𝓝 0)

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem System.finiteNameEntropy_nonneg (S : System G X) (f : X → A) (I : Finset G) :
    0 ≤ S.finiteNameEntropy f I := by
  unfold System.finiteNameEntropy
  apply neg_nonneg.mpr
  refine Finset.sum_nonpos ?_
  intro a _
  exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
    (Real.log_nonpos ENNReal.toReal_nonneg (by
      simpa only [measureReal_def, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := S.measure) (s := {x | ∀ i : I, f (S.act i x) = a i}))))

/-- A finite measurable observable approximable in probability by
zero-entropy observables has zero entropy. -/
theorem System.observableZeroEntropy_of_approximation (S : System G X)
    [Nonempty A] [DecidableEq A] {f : X → A} (hf : Measurable f)
    (hApprox : ∀ ε : ℝ, 0 < ε → ∃ g : X → A, Measurable g ∧ S.ObservableZeroEntropy g ∧
      S.measure.real {x | f x ≠ g x} < ε) :
    S.ObservableZeroEntropy f := by
  intro I hI
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp
    (continuous_entropyErrorBound (Fintype.card A)).continuousAt (ε / 2) (by positivity)
  obtain ⟨g, hg, hZero, hErr⟩ := hApprox δ hδ
  have hEB : entropyErrorBound (Fintype.card A) (S.measure.real {x | f x ≠ g x}) < ε / 2 := by
    have hdist : dist (S.measure.real {x | f x ≠ g x}) 0 < δ := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hErr
    have h := hsmall hdist
    rw [entropyErrorBound_zero, Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans_lt h
  have hG := Metric.tendsto_nhds.mp (hZero I hI) (ε / 2) (by positivity)
  filter_upwards [hG] with n hgn
  have hn : (0 : ℝ) < (I n).card :=
    by exact_mod_cast Finset.card_pos.mpr (hI.1 n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (S.finiteNameEntropy_nonneg f (I n)) hn.le)]
  have hbound := div_le_div_of_nonneg_right
    (S.finiteNameEntropy_le_of_approximation (I n) hf hg) hn.le
  rw [add_div, mul_div_cancel_left₀ _ hn.ne'] at hbound
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (S.finiteNameEntropy_nonneg g (I n)) hn.le)] at hgn
  linarith

end Mixing
