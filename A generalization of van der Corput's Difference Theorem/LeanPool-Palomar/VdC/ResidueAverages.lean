/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import VdC.Permissible
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Cesàro averages split over residue classes, including incomplete last blocks. -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

theorem sum_range_mul_residue {A : Type*} [AddCommMonoid A] (u : ℕ → A) (r N : ℕ) :
    ∑ n ∈ range (r * N), u n = ∑ t ∈ range r, ∑ n ∈ range N, u (r * n + t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]

/-- The average over a complete collection of `N` blocks of size `r`. -/
theorem cesaro_mul_residue (u : ℕ → ℂ) (r N : ℕ) :
    cesaro u (r * N) =
      (∑ t ∈ range r, cesaro (fun n ↦ u (r * n + t)) N) / (r : ℂ) := by
  simp only [cesaro]
  rw [sum_range_mul_residue, Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm (N : ℂ)]

private theorem natCast_mul_cesaro (u : ℕ → ℂ) (N : ℕ) :
    (N : ℂ) * cesaro u N = ∑ n ∈ range N, u n := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [cesaro]
  · rw [cesaro, ← mul_div_assoc, mul_div_cancel_left₀ _ (by exact_mod_cast hN)]

/-- Omitting the last `N-M` entries changes a normalized bounded average by at most
`2 C (N-M)/N`. Lean's zero-length average is zero. -/
theorem norm_cesaro_sub_prefix_le (u : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) {M N : ℕ} (hMN : M ≤ N) :
    ‖cesaro u N - cesaro u M‖ ≤ 2 * C * (↑(N - M) : ℝ) / (N : ℝ) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have : M = 0 := by omega
    simp [this]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have he : cesaro u N - cesaro u M =
      ((∑ n ∈ Ico M N, u n) - ((N - M : ℕ) : ℂ) * cesaro u M) / (N : ℂ) := by
    calc
      _ = ((M : ℂ) * cesaro u M + (∑ n ∈ Ico M N, u n)) / (N : ℂ) - cesaro u M := by
        rw [natCast_mul_cesaro, Finset.sum_range_add_sum_Ico _ hMN]
        rfl
      _ = _ := by rw [Nat.cast_sub hMN]; field_simp; ring
  rw [he, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have htail : ‖∑ n ∈ Ico M N, u n‖ ≤ (↑(N - M) : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ Ico M N, ‖u n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Ico M N, C := Finset.sum_le_sum fun n _ ↦ hu n
      _ = _ := by simp [Nat.card_Ico]
  have hscale : ‖((N - M : ℕ) : ℂ) * cesaro u M‖ ≤ (↑(N - M) : ℝ) * C := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_cesaro_le u hC hu M) (Nat.cast_nonneg _)
  exact (norm_sub_le _ _).trans (by nlinarith only [htail, hscale])

/-- A bounded sequence has the same limiting average along all lengths as along
lengths divisible by a fixed positive integer. -/
theorem tendsto_cesaro_of_chunked {u : ℕ → ℂ} {r : ℕ} {z : ℂ} (hr : 0 < r)
    (hu : BoundedSeq u) (h : Tendsto (fun N ↦ cesaro u (r * N)) atTop (𝓝 z)) :
    Tendsto (cesaro u) atTop (𝓝 z) := by
  obtain ⟨C, hC, hbound⟩ := hu
  have hdiv : Tendsto (fun N : ℕ ↦ N / r) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ eventually_atTop.2 ⟨b * r, fun N hN ↦ ?_⟩
    exact (Nat.le_div_iff_mul_le hr).2 hN
  have hchunk := h.comp hdiv
  have herr (N : ℕ) : ‖cesaro u N - cesaro u (r * (N / r))‖ ≤ (2 * C * r) / (N : ℝ) := by
    have he := Nat.mod_add_div N r
    have hle : r * (N / r) ≤ N := by omega
    have hrem : N - r * (N / r) ≤ r := by
      have hm := Nat.mod_lt N hr
      omega
    apply (norm_cesaro_sub_prefix_le u hC hbound hle).trans
    gcongr
  have hlim : Tendsto (fun N : ℕ ↦ (2 * C * (r : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
        (2 * C * (r : ℝ))
  have hnorm := squeeze_zero (fun _ ↦ norm_nonneg _) herr hlim
  have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [Function.comp_def, zero_add, sub_add_cancel] using hzero.add hchunk

/-- Combine the limiting averages of all residues of a bounded sequence. -/
theorem tendsto_cesaro_of_residue_limits {u : ℕ → ℂ} {r : ℕ} (hr : 0 < r)
    (hu : BoundedSeq u) (z : ℕ → ℂ)
    (h : ∀ t < r, Tendsto (cesaro (fun n ↦ u (r * n + t))) atTop (𝓝 (z t))) :
    Tendsto (cesaro u) atTop (𝓝 ((∑ t ∈ range r, z t) / (r : ℂ))) := by
  apply tendsto_cesaro_of_chunked hr hu
  simp_rw [cesaro_mul_residue]
  exact (tendsto_finsetSum _ (fun t ht ↦ h t (mem_range.1 ht))).div_const _

end VdC
