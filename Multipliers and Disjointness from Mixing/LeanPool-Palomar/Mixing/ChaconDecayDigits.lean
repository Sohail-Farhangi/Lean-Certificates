/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconDecayPolynomials
public import Mathlib.Topology.Order.MonotoneConvergence

/-! # Decay along the successive prefixes of an infinite ternary expansion -/

@[expose] public section

open Filter Set
open scoped Classical Topology

namespace Mixing

private theorem exists_chacon_contraction_digits (d : ℕ → Fin 3)
    (hNoZeroTail : ¬ ∃ N, ∀ n ≥ N, d n = 0)
    (hNoTwoTail : ¬ ∃ N, ∀ n ≥ N, d n = 2) (N : ℕ) :
    ∃ n ≥ N, d n = 1 ∨ (d n = 0 ∧ d (n + 1) = 2) ∨ (d n = 2 ∧ d (n + 1) = 0) := by
  by_contra! h
  have hstep (n : ℕ) (hn : N ≤ n) : d (n+1) = d n := by
    have ha := h n hn
    have hb := h (n+1) (by omega)
    generalize hdn : d n = a
    generalize hds : d (n + 1) = b
    rw [hdn, hds] at ha
    rw [hds] at hb
    fin_cases a <;> fin_cases b <;> simp_all
  have hconst (n : ℕ) (hn : N ≤ n) : d n = d N := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [hstep n hn, ih]
  have hn := h N le_rfl
  generalize he : d N = a
  fin_cases a
  · exact hNoZeroTail ⟨N, fun n hn ↦ (hconst n hn).trans he⟩
  · exact hn.1 he
  · exact hNoTwoTail ⟨N, fun n hn ↦ (hconst n hn).trans he⟩

/-- If the ternary digits are eventually neither all zero nor all two, the
pair of spacer-polynomial values at the prefixes tends to zero off the
trivial spectral parameter. -/
theorem tendsto_chaconDecayPair_ternary_prefix_zero {z : ℂ}
    (hz : ‖z‖ = 1) (hne : z ≠ 1) (m : ℕ → ℕ) (d : ℕ → Fin 3)
    (hm : ∀ n, m (n+1) = 3 * m n + (d n).val)
    (hNoZeroTail : ¬ ∃ N, ∀ n ≥ N, d n = 0)
    (hNoTwoTail : ¬ ∃ N, ∀ n ≥ N, d n = 2) :
    Tendsto (fun n ↦ chaconDecayPair z (m n)) atTop (𝓝 0) := by
  let f n := chaconDecayPair z (m n)
  let c := chaconDecayRatio z
  have hf : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    change chaconDecayPair z (m (n+1)) ≤ _
    rw [hm]
    exact chaconDecayPair_append_le hz (m n) (d n)
  have hB : BddBelow (range f) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact chaconDecayPair_nonneg z _⟩
  have hlim := tendsto_atTop_ciInf hf hB
  have hContract (N : ℕ) : ∃ k, f k ≤ c * f N := by
    obtain ⟨n, hn, h | h | h⟩ := exists_chacon_contraction_digits d hNoZeroTail hNoTwoTail N
    · refine ⟨n+1, ?_⟩
      have hEq : m (n+1) = 3 * m n + 1 := by rw [hm, h]; rfl
      calc
        f (n+1) ≤ c * f n := by
          change chaconDecayPair z (m (n+1)) ≤ _
          rw [hEq]
          exact chaconDecayPair_append_one hz _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hf hn) (chaconDecayRatio_nonneg z)
    · refine ⟨n+1+1, ?_⟩
      have hEq : m (n+1+1) = 3 * (3 * m n) + 2 := by rw [hm, hm, h.1, h.2]; rfl
      calc
        f (n+1+1) ≤ c * f n := by
          change chaconDecayPair z (m (n+1+1)) ≤ _
          rw [hEq]
          exact chaconDecayPair_append_zero_two hz _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hf hn) (chaconDecayRatio_nonneg z)
    · refine ⟨n+1+1, ?_⟩
      have hEq : m (n+1+1) = 3 * (3 * m n + 2) := by
        rw [hm, hm, h.1, h.2]
        simp
      calc
        f (n+1+1) ≤ c * f n := by
          change chaconDecayPair z (m (n+1+1)) ≤ _
          rw [hEq]
          exact chaconDecayPair_append_two_zero hz _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hf hn) (chaconDecayRatio_nonneg z)
  have hI : (⨅ n, f n) ≤ c * (⨅ n, f n) := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim.const_mul c)
    intro N
    obtain ⟨k, hk⟩ := hContract N
    exact (ciInf_le hB k).trans hk
  have hnonneg : 0 ≤ ⨅ n, f n := le_ciInf fun n ↦ chaconDecayPair_nonneg z _
  have hc : c < 1 := chaconDecayRatio_lt_one hz hne
  have hzero : (⨅ n, f n) = 0 := by nlinarith
  rw [hzero] at hlim
  exact hlim

end Mixing
