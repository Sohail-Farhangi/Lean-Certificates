/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.DuplicationSpectrum
public import VdC.DiscrepancySelection
public import VdC.ErgodicExamples
public import VdC.ThesisWeakMixing

/-! # Duplication Discrepancy -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology

namespace VdC

noncomputable section

def duplicationRetained (request : ℕ → ℕ) (h : ℕ) : Set ℕ :=
  {n | ¬ duplicationCoincidence request h n}

theorem duplicationRetained_count (request : ℕ → ℕ) (h N : ℕ) :
    N ≤ 2 * initialCount (duplicationRetained request h) N + h := by
  classical
  let A := duplicationRetained request h
  let G := (range N).filter (· ∈ A)
  let B := (range N).filter (· ∉ A)
  have hSum : G.card + B.card = N := by
    simpa only [G, B, card_range] using card_filter_add_card_filter_not (s := range N) (· ∈ A)
  have hnear : (B.filter fun n => n+h < N).card ≤ G.card := by
    apply card_le_card_of_injOn (fun n => n+h)
    · intro n hn
      obtain ⟨hnB, hnN⟩ := mem_filter.mp hn
      have hc : duplicationCoincidence request h n := by
        simpa [B, A, duplicationRetained] using (mem_filter.mp hnB).2
      exact mem_filter.2 ⟨mem_range.2 hnN, (duplicationCoincidence_pair hc).2⟩
    · intro n _ m _ he
      change n+h = m+h at he
      omega
  have hfar : (B.filter fun n => ¬ n+h < N).card ≤ h := by
    rw [← card_range h]
    apply card_le_card_of_injOn (fun n => N-(n+1))
    · intro n hn
      obtain ⟨hnB, hnN⟩ := mem_filter.mp hn
      have hnlt := mem_range.mp (mem_filter.mp hnB).1
      simp only [card_range] at hnN
      apply mem_range.2
      change N-(n+1) < h
      omega
    · intro n hn m hm he
      have hnlt := mem_range.mp (mem_filter.mp (mem_filter.mp hn).1).1
      have hmlt := mem_range.mp (mem_filter.mp (mem_filter.mp hm).1).1
      change N-(n+1) = N-(m+1) at he
      omega
  have hcard := card_filter_add_card_filter_not (s := B) (fun n => n+h < N)
  change N ≤ 2*G.card+h
  omega

theorem duplicationRetained_positiveDensity (request : ℕ → ℕ) (h : ℕ) :
    HasPositiveLowerDensity (duplicationRetained request h) := by
  refine ⟨1/4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2*h)] with N hN
  have hc : (N : ℝ) ≤ 2 * (initialCount (duplicationRetained request h) N : ℝ) + h := by
    exact_mod_cast duplicationRetained_count request h N
  have he : (2 : ℝ) * h ≤ N := by exact_mod_cast hN
  linarith

def duplicationDifferenceCube (request : ℕ → ℕ) (α : ℝ) (h n : ℕ) : Cube 1 :=
  fun i => unitRepresentative ((duplicationSequence request α (n+h) - duplicationSequence request α n) i)

theorem duplication_differenceCharacter (request : ℕ → ℕ) (α : ℝ) (h n : ℕ) (m : Fin 1 → ℤ) :
    torusCharacter m (cubeToTorus (duplicationDifferenceCube request α h n)) =
      phase ((m 0 : ℝ) * α *
        ((duplicationIndex request (n+h) : ℝ)^2 - (duplicationIndex request n : ℝ)^2)) := by
  have he : cubeToTorus (duplicationDifferenceCube request α h n) =
      duplicationSequence request α (n+h) - duplicationSequence request α n := by
    funext i
    exact unitRepresentative_coe _
  rw [he]
  exact torusCharacter_duplication_difference request α m h n

theorem duplication_differenceCharacter_times_retained (request : ℕ → ℕ) (α : ℝ) (h n : ℕ)
    (m : Fin 1 → ℤ) :
    torusCharacter m (cubeToTorus (duplicationDifferenceCube request α h n)) *
        selectionWeight (duplicationRetained request h) n = duplicationMaskedPhase request α (m 0) h n := by
  rw [duplication_differenceCharacter]
  by_cases hc : duplicationCoincidence request h n
  · have hm : n ∉ duplicationRetained request h := fun hn => hn hc
    simp [selectionWeight, hm, duplicationMaskedPhase, hc]
  · have hm : n ∈ duplicationRetained request h := hc
    simp [selectionWeight, hm, duplicationMaskedPhase, hc]

theorem equidistributed_duplication_retained {α : ℝ} (hα : Irrational α) {h : ℕ} (hh : 0 < h)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (hA : Set.range σ = duplicationRetained (duplicationGrowth α) h) :
    Equidistributed (cubeLebesgue 1) (duplicationDifferenceCube (duplicationGrowth α) α h ∘ σ) := by
  apply equidistributed_of_cubeToTorus
  apply (equidistributed_torus_iff _).2
  intro m hm
  have hm0 : m 0 ≠ 0 := by
    intro he
    apply hm
    funext i
    fin_cases i
    exact he
  let f n := torusCharacter m (cubeToTorus (duplicationDifferenceCube (duplicationGrowth α) α h n))
  change Tendsto (cesaro fun k => f (σ k)) atTop (𝓝 0)
  apply tendsto_cesaro_selected_zero f hσ
  · rw [hA]
    exact duplicationRetained_positiveDensity ..
  · rw [hA]
    have he : (fun n => f n * selectionWeight (duplicationRetained (duplicationGrowth α) h) n) =
        duplicationMaskedPhase (duplicationGrowth α) α (m 0) h := by
      funext n
      exact duplication_differenceCharacter_times_retained (duplicationGrowth α) α h n m
    rw [he]
    exact tendsto_cesaro_duplicationMaskedPhase_zero hα hm0 hh

theorem duplication_upper_discrepancy_eq_half {α : ℝ} (hα : Irrational α) (j : ℕ) :
    upperDifferenceDiscrepancy (duplicationSequence (duplicationGrowth α) α) j = (1 : ℝ)/2 := by
  apply le_antisymm _ (duplication_upper_discrepancy_ge_half (duplicationGrowth α) α j)
  let h := j+1
  let A := duplicationRetained (duplicationGrowth α) h
  have hden : HasPositiveLowerDensity A := duplicationRetained_positiveDensity ..
  obtain ⟨σ, hσ, hA⟩ := exists_enumeration_of_positiveLowerDensity hden
  change limsup (rectangleDiscrepancy (duplicationDifferenceCube (duplicationGrowth α) α h)) atTop ≤ (1:ℝ)/2
  refine limsup_rectangleDiscrepancy_le_erased _ hσ
    (tendsto_rectangleDiscrepancy_of_equidistributed (equidistributed_duplication_retained hα (Nat.succ_pos _) hσ hA)) ?_
  intro ε hε
  have ht := (tendsto_const_div_atTop_nhds_zero_nat ((h : ℝ)/2)).eventually (gt_mem_nhds hε)
  filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with N hN' hN
  rw [hA]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let K := (initialCount A N : ℝ)
  have hc : (N : ℝ) ≤ 2*K+h := by
    dsimp [K, A]
    exact_mod_cast duplicationRetained_count (duplicationGrowth α) h N
  have hq := div_le_div_of_nonneg_right hc hNr.le
  rw [div_self hNr.ne', add_div, mul_div_assoc] at hq
  change (h : ℝ)/2/N < ε at hN'
  have he : (h : ℝ)/N = 2*((h : ℝ)/2/N) := by ring
  rw [he] at hq
  change 1-K/(N : ℝ) ≤ (1:ℝ)/2+ε
  linarith only [hq, hN']

end
end VdC
