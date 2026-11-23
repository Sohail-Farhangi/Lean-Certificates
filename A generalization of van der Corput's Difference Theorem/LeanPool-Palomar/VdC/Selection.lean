/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Permissible
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Selection -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

noncomputable def selectionWeight (A : Set ℕ) (n : ℕ) : ℂ := A.indicator (fun _ => 1) n

noncomputable def initialCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter (· ∈ A)).card

/-- An eventual positive lower bound for the initial-segment densities. -/
def HasPositiveLowerDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ (N : ℕ) in atTop, δ * (N : ℝ) ≤ initialCount A N

noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (initialCount A N : ℝ) / (N : ℝ)) atTop

theorem hasPositiveLowerDensity_iff (A : Set ℕ) : HasPositiveLowerDensity A ↔ 0 < lowerDensity A := by
  have hnonneg (N : ℕ) : 0 ≤ (initialCount A N : ℝ) / (N : ℝ) := by positivity
  have hupper (N : ℕ) : (initialCount A N : ℝ) / (N : ℝ) ≤ 1 := by
    by_cases hN : 0 < N
    · have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
      rw [div_le_iff₀ hNr, one_mul]
      classical
      exact_mod_cast (card_filter_le _ _).trans_eq (card_range N)
    · simp [Nat.eq_zero_of_not_pos hN]
  constructor
  · rintro ⟨δ, hδ, hd⟩
    refine hδ.trans_le (le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hupper) ?_)
    filter_upwards [hd, eventually_gt_atTop (0 : ℕ)] with N hD hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    exact (le_div_iff₀ hNr).2 hD
  · intro h
    obtain ⟨δ, hδ, hδ'⟩ := exists_between h
    refine ⟨δ, hδ, ?_⟩
    have hh := eventually_lt_of_lt_liminf hδ' (isBoundedUnder_of ⟨0, hnonneg⟩)
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hD hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    exact (lt_div_iff₀ hNr).1 hD |>.le

private theorem range_filter_eq_map (σ : ℕ → ℕ) (hσ : StrictMono σ) (K : ℕ) :
    letI := Classical.decPred (· ∈ Set.range σ)
    (range (σ K + 1)).filter (· ∈ Set.range σ) = (range (K + 1)).map ⟨σ, hσ.injective⟩ := by
  classical
  ext n
  simp only [mem_filter, mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hn, k, rfl⟩
    exact ⟨k, Nat.lt_succ_of_le (hσ.le_iff_le.mp (Nat.le_of_lt_succ hn)), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Nat.lt_succ_of_le (hσ.monotone (Nat.le_of_lt_succ hk)), ⟨k, rfl⟩⟩

theorem initialCount_at_selection {σ : ℕ → ℕ} (hσ : StrictMono σ) (K : ℕ) :
    initialCount (Set.range σ) (σ K + 1) = K + 1 := by
  classical
  rw [initialCount, range_filter_eq_map σ hσ K, card_map, card_range]

private theorem selection_sum (u : ℕ → ℂ) {σ : ℕ → ℕ} (hσ : StrictMono σ) (K : ℕ) :
    ∑ n ∈ range (σ K + 1), u n * selectionWeight (Set.range σ) n =
      ∑ k ∈ range (K + 1), u (σ k) := by
  classical
  calc
    _ = ∑ n ∈ (range (σ K + 1)).filter (· ∈ Set.range σ), u n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n ∈ Set.range σ <;> simp [selectionWeight, hn]
    _ = _ := by rw [range_filter_eq_map σ hσ K, Finset.sum_map]; rfl

theorem tendsto_cesaro_selected_zero (u : ℕ → ℂ) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hd : HasPositiveLowerDensity (Set.range σ))
    (h : Tendsto (cesaro fun n => u n * selectionWeight (Set.range σ) n) atTop (𝓝 0)) :
    Tendsto (cesaro fun k => u (σ k)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hden⟩ := hd
  have hσ' : Tendsto (fun K => σ K + 1) atTop atTop :=
    (show StrictMono (fun K => σ K + 1) from fun _ _ h => Nat.add_lt_add_right (hσ h) _).tendsto_atTop
  have hb : ∀ᶠ K in atTop, δ * ((σ K + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    simpa only [initialCount_at_selection hσ] using hσ'.eventually hden
  have hn := (h.comp hσ').norm
  have hbound : ∀ᶠ K in atTop,
      ‖cesaro (fun k => u (σ k)) (K + 1)‖ ≤
        δ⁻¹ * ‖cesaro (fun n => u n * selectionWeight (Set.range σ) n) (σ K + 1)‖ := by
    filter_upwards [hb] with K hK
    simp only [cesaro, selection_sum u hσ, norm_div, Complex.norm_natCast]
    have hratio : ((σ K + 1 : ℕ) : ℝ) ≤ δ⁻¹ * ((K + 1 : ℕ) : ℝ) := by
      rwa [inv_mul_eq_div, le_div_iff₀ hδ, mul_comm]
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hratio (norm_nonneg (∑ k ∈ range (K + 1), u (σ k)))
  have ht := squeeze_zero' (Eventually.of_forall fun K => norm_nonneg (cesaro (fun k => u (σ k)) (K + 1)))
    hbound (by simpa using tendsto_const_nhds.mul hn (a := δ⁻¹))
  exact (tendsto_add_atTop_iff_nat 1).1 (tendsto_zero_iff_norm_tendsto_zero.mpr ht)

end VdC
