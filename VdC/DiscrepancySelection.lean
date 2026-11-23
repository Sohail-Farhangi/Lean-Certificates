/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.RectangleMeasure
public import VdC.Selection

/-! # Discrepancy Selection -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology

namespace VdC

private theorem prefix_filter_range {σ : ℕ → ℕ} (hσ : StrictMono σ) (N : ℕ) :
    let A := Set.range σ
    letI := Classical.decPred (· ∈ A)
    let K := initialCount A N
    (range N).filter (· ∈ A) = (range K).map ⟨σ, hσ.injective⟩ := by
  classical
  dsimp only
  have hex : ∃ k, N ≤ σ k := ⟨N, hσ.id_le N⟩
  let M := Nat.find hex
  have HM : N ≤ σ M := Nat.find_spec hex
  have Hlt (k : ℕ) : σ k < N ↔ k < M := by
    constructor
    · intro hk
      by_contra! h
      exact (not_lt_of_ge (HM.trans (hσ.monotone h))) hk
    · intro hk
      exact lt_of_not_ge (Nat.find_min hex hk)
  have he : (range N).filter (· ∈ Set.range σ) = (range M).map ⟨σ, hσ.injective⟩ := by
    ext n
    simp only [mem_filter, mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hn, k, rfl⟩
      exact ⟨k, (Hlt k).mp hn, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Hlt k).mpr hk, ⟨k, rfl⟩⟩
  have hc : initialCount (Set.range σ) N = M := by unfold initialCount; rw [he, card_map, card_range]
  simpa only [hc] using he

/-- Erasing observations can account for at most the erased fraction of
rectangle discrepancy, plus the discrepancy in the retained observations. -/
theorem rectangleDiscrepancy_le_erased {d : ℕ} (u : ℕ → Cube d) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {N : ℕ} (hN : 0 < N) :
    let K := initialCount (Set.range σ) N
    rectangleDiscrepancy u N ≤ 1 - (K : ℝ) / (N : ℝ) + rectangleDiscrepancy (u ∘ σ) K := by
  classical
  let A := Set.range σ
  let K := initialCount A N
  let F := range N
  let e : ℕ ↪ ℕ := ⟨σ, hσ.injective⟩
  change rectangleDiscrepancy u N ≤ 1 - (K : ℝ) / (N : ℝ) + rectangleDiscrepancy (u ∘ σ) K
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmap : F.filter (· ∈ A) = (range K).map e := prefix_filter_range hσ N
  have hk : K = (F.filter (· ∈ A)).card := rfl
  have hK : K ≤ N := by rw [hk, ← card_range N]; exact card_filter_le ..
  have hKN : (K : ℝ) ≤ N := by exact_mod_cast hK
  have hbad : ((F.filter (· ∉ A)).card : ℝ) = N-K := by
    have he := card_filter_add_card_filter_not (s := F) (· ∈ A)
    rw [← hk, card_range] at he
    have heR : (K : ℝ) + ((F.filter (· ∉ A)).card : ℝ) = N := by exact_mod_cast he
    linarith
  unfold rectangleDiscrepancy
  apply csSup_le ⟨_, Set.mem_range_self ((fun _ => ⟨0, by simp⟩), (fun _ => ⟨0, by simp⟩))⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  let P (n : ℕ) := ∀ i, (a i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ b i
  let L := ((F.filter (· ∉ A)).filter P).card
  let v := rectangleVolume a b
  have hv : v ∈ Set.Icc (0 : ℝ) 1 := by
    change rectangleVolume a b ∈ _
    rw [rectangleVolume_eq_measure]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hl : (L : ℝ) ≤ N-K := by
    rw [← hbad]
    exact_mod_cast card_filter_le (F.filter (· ∉ A)) P
  have hf : rectangleFrequency u N a b =
      (K * rectangleFrequency (u ∘ σ) K a b + L) / (N : ℝ) := by
    have hc : (F.filter P).card = ((F.filter (· ∈ A)).filter P).card + L := by
      have hh := card_filter_add_card_filter_not (s := F.filter P) (· ∈ A)
      simpa [L, filter_filter, and_comm] using hh.symm
    have hgood : ((F.filter (· ∈ A)).filter P).card = ((range K).filter (P ∘ σ)).card := by
      rw [hmap, filter_map, card_map]
      rfl
    have hv' : (K : ℝ) * rectangleFrequency (u ∘ σ) K a b = (((range K).filter (P ∘ σ)).card : ℝ) := by
      by_cases hk' : K = 0
      · simp [hk']
      · change (K : ℝ) * ((((range K).filter (P ∘ σ)).card : ℝ) / K) = _
        have hk'R : (K : ℝ) ≠ 0 := by exact_mod_cast hk'
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hk'R]
    change ((F.filter P).card : ℝ) / N = _
    rw [hc, Nat.cast_add, hgood, hv']
  have he : rectangleFrequency u N a b - v =
      (K : ℝ)/N*(rectangleFrequency (u ∘ σ) K a b-v) + ((L : ℝ) - (N-K)*v)/N := by
    rw [hf]
    field_simp
    ring
  have hterm : |((L : ℝ)-(N-K)*v)/N| ≤ 1 - (K : ℝ)/N := by
    rw [abs_div, abs_of_pos hN', show 1 - (K : ℝ)/N = (N-K)/N by field_simp]
    apply div_le_div_of_nonneg_right _ hN'.le
    have hL0 : (0:ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have ha : 0 ≤ ((N:ℝ)-K)*v := mul_nonneg (sub_nonneg.mpr hKN) hv.1
    have hb : ((N:ℝ)-K)*v ≤ N-K := mul_le_of_le_one_right (sub_nonneg.mpr hKN) hv.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmain : |(K : ℝ)/N*(rectangleFrequency (u ∘ σ) K a b-v)| ≤ rectangleDiscrepancy (u ∘ σ) K := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (K : ℝ)/N)]
    have hh : (K : ℝ)/N ≤ 1 := (div_le_one hN').mpr hKN
    exact (mul_le_of_le_one_left (abs_nonneg _) hh).trans (rectangle_deviation_le_discrepancy _ _ _ _)
  change |rectangleFrequency u N a b - v| ≤ 1 - (K : ℝ) / N + rectangleDiscrepancy (u ∘ σ) K
  rw [he]
  exact (abs_add_le ..).trans (by linarith only [hterm, hmain])

theorem limsup_rectangleDiscrepancy_le_erased {d : ℕ} (u : ℕ → Cube d) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) {δ : ℝ}
    (hUD : Tendsto (rectangleDiscrepancy (u ∘ σ)) atTop (𝓝 0))
    (hbad : ∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
      1 - (initialCount (Set.range σ) N : ℝ) / (N : ℝ) ≤ δ + ε) :
    limsup (rectangleDiscrepancy u) atTop ≤ δ := by
  have hmono : Monotone (initialCount (Set.range σ)) := by
    intro M N hMN
    classical
    exact card_le_card (filter_subset_filter _ (range_mono hMN))
  have hKt : Tendsto (initialCount (Set.range σ)) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    refine eventually_atTop.2 ⟨σ K + 1, fun N hN => ?_⟩
    exact (Nat.le_succ K).trans ((initialCount_at_selection hσ K).ge.trans (hmono hN))
  refine (limsup_le_iff' (isCoboundedUnder_le_of_le atTop fun N => (rectangleDiscrepancy_mem_Icc u N).1)
    (isBoundedUnder_of ⟨1, fun N => (rectangleDiscrepancy_mem_Icc u N).2⟩)).2 ?_
  intro y hy
  let ε := (y-δ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsmall := (hUD.comp hKt).eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, hbad ε hε, eventually_gt_atTop (0 : ℕ)] with N hsmall hbad' hN
  have hsplit := rectangleDiscrepancy_le_erased u hσ hN
  dsimp only at hsmall hsplit
  dsimp [ε] at hsmall hbad'
  linarith only [hsplit, hsmall, hbad']

end VdC
