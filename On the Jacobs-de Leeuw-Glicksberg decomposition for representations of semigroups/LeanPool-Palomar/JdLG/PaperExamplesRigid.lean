/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Rigidity obstructions in Examples 4.6 and 4.7

The operator arguments below start with their stated strong rigidity
hypothesis. The lacunary subsequence construction is independent of any
operator existence theorem.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter
open scoped Topology

/-- A subset of the integers that meets every interval of a fixed length. -/
def BoundedGaps (A : Set ℤ) : Prop :=
  ∃ L : ℕ, ∀ a : ℤ, ∃ l : Fin (L + 1), a + (l.val : ℤ) ∈ A

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Weak convergence of an integer-indexed orbit to zero within a set of
times, measured against every continuous linear functional. -/
def WeakDecayOn (x : ℤ → E) (A : Set ℤ) : Prop :=
  ∀ f : StrongDual ℂ E, Tendsto (fun s ↦ f (x s)) (cofinite ⊓ principal A) (𝓝 0)

/-- Bounded gaps force a weakly null set of times to meet a bounded shift of the
rigidity sequence in a way that contradicts its nonzero limits. -/
theorem not_weakDecayOn_of_rigid_boundedGaps
    (V : ℤ → E ≃ₗᵢ[ℂ] E) (hmul : ∀ a b, V (a + b) = (V b).trans (V a))
    (ξ : E) (hξ : ξ ≠ 0) (u : ℕ → ℤ) (hu : Tendsto u atTop cofinite)
    (hstrong : Tendsto (fun k ↦ V (u k) ξ) atTop (𝓝 ξ))
    (A : Set ℤ) (hA : BoundedGaps A) : ¬ WeakDecayOn (fun s ↦ V s ξ) A := by
  classical
  intro hweak
  obtain ⟨L, hL⟩ := hA
  have hoff (l : Fin (L + 1)) :
      ∀ᶠ k in atTop, u k + (l.val : ℤ) ∉ A := by
    let y := V (l.val : ℤ) ξ
    have hy : y ≠ 0 := by
      intro h
      apply hξ
      exact (V (l.val : ℤ)).injective (h.trans (map_zero _).symm)
    obtain ⟨f, -, hf⟩ := exists_dual_vector ℂ y (norm_ne_zero_iff.2 hy)
    have hfy : f y ≠ 0 := by
      rw [hf]
      exact fun h ↦ hy (norm_eq_zero.1 (Complex.ofReal_eq_zero.1 h))
    let ε := ‖f y‖ / 2
    have hε : 0 < ε := half_pos (norm_pos_iff.2 hfy)
    have hun : Tendsto (fun k ↦ u k + (l.val : ℤ)) atTop cofinite :=
      (Equiv.addRight (l.val : ℤ)).injective.tendsto_cofinite.comp hu
    have hw : ∀ᶠ k in atTop, u k + (l.val : ℤ) ∈ A →
        dist (f (V (u k + (l.val : ℤ)) ξ)) 0 < ε :=
      hun.eventually (eventually_inf_principal.1 (Metric.tendsto_nhds.1 (hweak f) ε hε))
    have hcont : Continuous (fun x ↦ f (V (l.val : ℤ) x)) :=
      f.continuous.comp (V (l.val : ℤ)).continuous
    have hs : Tendsto (fun k ↦ f (V (u k + (l.val : ℤ)) ξ)) atTop (𝓝 (f y)) := by
      have ht := (hcont.tendsto ξ).comp hstrong
      simpa [Function.comp_def, add_comm (u _) (l.val : ℤ), hmul, y] using ht
    filter_upwards [hw, Metric.tendsto_nhds.1 hs ε hε] with k hweak' hclose hmem
    have hs' := hweak' hmem
    have htriangle := dist_triangle (f y) (f (V (u k + (l.val : ℤ)) ξ)) 0
    rw [dist_comm (f y) (f (V (u k + (l.val : ℤ)) ξ)), dist_zero_right (f y)] at htriangle
    dsimp [ε] at hs' hclose
    linarith
  obtain ⟨k, hk⟩ := (eventually_all.2 hoff).exists
  obtain ⟨l, hl⟩ := hL (u k)
  exact hk l hl

/-- Every infinite set of positive times contains a strictly increasing
subsequence whose successive ratios diverge, as used in Example 4.7. -/
theorem exists_lacunary_subsequence (A : Set ℕ) (hA : A.Infinite) :
    ∃ u : ℕ → ℕ, (∀ n, u n ∈ A) ∧ StrictMono u ∧ (∀ n, 0 < u n) ∧
      Tendsto (fun n ↦ (u (n + 1) : ℝ) / (u n : ℝ)) atTop atTop := by
  classical
  have hu (m : ℕ) : ∃ a ∈ A, m < a := not_bddAbove_iff.1 hA.not_bddAbove m
  let u : ℕ → ℕ := Nat.rec (hu 0).choose fun n a ↦ (hu ((n + 2) * a)).choose
  have hstep (n : ℕ) : (n + 2) * u n < u (n + 1) := (hu _).choose_spec.2
  have hpos (n : ℕ) : 0 < u n := by
    cases n with
    | zero => exact (hu 0).choose_spec.2
    | succ n => exact (Nat.zero_le _).trans_lt (hstep n)
  refine ⟨u, fun n ↦ ?_, strictMono_nat_of_lt_succ fun n ↦ ?_, hpos, ?_⟩
  · cases n with
    | zero => exact (hu 0).choose_spec.1
    | succ n => exact (hu _).choose_spec.1
  · exact (Nat.le_mul_of_pos_left _ (by omega)).trans_lt (hstep n)
  · apply tendsto_atTop.2
    intro C
    obtain ⟨N, hN⟩ := exists_nat_ge C
    refine (eventually_ge_atTop N).mono fun (n : ℕ) hn ↦ ?_
    have hposReal : (0 : ℝ) < Nat.cast (u n) := Nat.cast_pos.2 (hpos n)
    have hratio : (n : ℝ) + 2 < Nat.cast (u (n + 1)) / Nat.cast (u n) := by
      apply (lt_div_iff₀ hposReal).2
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
        (Nat.cast_lt.2 (hstep n) :
          (Nat.cast ((n + 2) * u n) : ℝ) < Nat.cast (u (n + 1)))
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact hN.trans (hNn.trans (by linarith))

/-- A nonzero rigid vector cannot converge weakly to zero on any set that
contains its escaping rigidity sequence. -/
theorem not_weakDecayOn_of_rigidity_sequence (x : ℤ → E) (A : Set ℤ)
    (u : ℕ → ℤ) (hu : Tendsto u atTop cofinite) (hmem : ∀ k, u k ∈ A)
    (ξ : E) (hξ : ξ ≠ 0) (hstrong : Tendsto (x ∘ u) atTop (𝓝 ξ)) :
    ¬ WeakDecayOn x A := by
  intro hweak
  obtain ⟨f, -, hf⟩ := exists_dual_vector ℂ ξ (norm_ne_zero_iff.2 hξ)
  have huA : Tendsto u atTop (cofinite ⊓ principal A) :=
    tendsto_inf.2 ⟨hu, tendsto_principal.2 (Eventually.of_forall hmem)⟩
  have heq := tendsto_nhds_unique ((hweak f).comp huA) ((f.continuous.tendsto ξ).comp hstrong)
  rw [hf] at heq
  exact hξ (norm_eq_zero.1 (Complex.ofReal_eq_zero.1 heq.symm))

end JdLG.PaperExamplesRigid
