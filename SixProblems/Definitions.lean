/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.System
public import Mixing.ErgodicBarycenters
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing

/-- The correlation in Definition 4.1, using positive time in the first entry. -/
def correlation {G X : Type*} [Group G] [MeasurableSpace X]
    (S : System G X) (f : X → ℂ) (g : G) : ℂ :=
  ∫ x, f (S.act g x) * (starRingEnd ℂ) (f x) ∂S.measure

/-- The dynamical van der Corput condition of Definition 4.1. -/
def IsVdC {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (f : X → ℂ), Measurable f →
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      (∀ r ∈ R, correlation S f r = 0) → ∫ x, f x ∂S.measure = 0

/-- Measure-theoretic compact-group van der Corput condition, relative to
the normalized Haar measure `m`, as in Definition 4.4. -/
def IsMeasureTheoreticVdC {G K : Type} [Group G] [Group K] [MeasurableSpace K]
    (R : Set G) (m : Measure K) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (F : X → K), Measurable F →
      (∀ h ∈ R, S.measure.map (fun x ↦ F (S.act h x) * (F x)⁻¹) = m) →
      S.measure.map F = m

/-- Nice event recurrence, Theorem 2.2(a). -/
def NiceRecurrence {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (A : Set X), MeasurableSet A →
    ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
      (S.measure A).toReal ^ 2 - ε ≤ (S.measure (A ∩ S.act r ⁻¹' A)).toReal

/-- The event test restricted to ergodic systems, Theorem 2.2(b). -/
def ErgodicNiceRecurrence {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X), S.IsErgodic → ∀ (A : Set X), MeasurableSet A →
    ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
      (S.measure A).toReal ^ 2 - ε ≤ (S.measure (A ∩ S.act r ⁻¹' A)).toReal

/-- The bounded-function condition of Theorem 2.2(e). Positive and inverse
time give the same absolute value of the correlation. -/
def NiceVdC {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (f : X → ℂ), Measurable f →
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) → ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
      ‖∫ x, f x ∂S.measure‖ ^ 2 - ε ≤ ‖correlation S f r⁻¹‖

end SixProblems
