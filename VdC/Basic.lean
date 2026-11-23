/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Basic -/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace VdC

def BoundedSeq (x : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖x n‖ ≤ C

noncomputable def cesaro (x : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, x n) / (N : ℂ)

noncomputable def realCesaro (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, x n) / (N : ℝ)

noncomputable def corr (x y : ℕ → ℂ) (h N : ℕ) : ℂ :=
  cesaro (fun n => x (n + h) * star (y n)) N

def CorrLimits (x y : ℕ → ℂ) (N : ℕ → ℕ) (r : ℕ → ℂ) : Prop :=
  ∀ h, Tendsto (fun q => corr x y h (N q)) atTop (𝓝 (r h))

structure PermissibleTriple (x y : ℕ → ℂ) (N : ℕ → ℕ) : Prop where
  boundedX : BoundedSeq x
  boundedY : BoundedSeq y
  strictMono : StrictMono N
  xx : ∃ r, CorrLimits x x N r
  xy : ∃ r, CorrLimits x y N r
  yx : ∃ r, CorrLimits y x N r
  yy : ∃ r, CorrLimits y y N r

def NearlyOrthogonal (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r → ∀ h, 0 < h → r h = 0

def NearlyWeakMixing (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ y N r, PermissibleTriple x y N → CorrLimits x y N r →
    Tendsto (realCesaro (fun h => ‖r (h + 1)‖)) atTop (𝓝 0)

def CompactAlong (x : ℕ → ℂ) (M : ℕ → ℕ) : Prop :=
  BoundedSeq x ∧ StrictMono M ∧ ∀ σ r, StrictMono σ → CorrLimits x x (M ∘ σ) r →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m : ℕ, ∃ k ≤ K, ∃ e : ℝ, e < ε ∧
      Tendsto (fun q => realCesaro (fun n => ‖x (n + (m + 1)) - x (n + (k + 1))‖ ^ 2)
        ((M ∘ σ) q)) atTop (𝓝 e)

def CompactSeq (x : ℕ → ℂ) : Prop := CompactAlong x id

end VdC
