/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesBilateral

/-!
# Density-one weak return sets for Example 4.5

Weak return sets contain all but finitely many horizontal coordinates.
Every finite set of horizontal coordinates contributes zero asymptotic
density along the two-parameter row net.
-/

@[expose] public section

namespace JdLG.PaperExamplesBilateral

open Filter PaperExamplesRows
open scoped Topology

local notation "H" => lp (fun _ : ℤ ↦ ℂ) 2

private theorem fst_tendsto_atTop : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
  refine tendsto_atTop.2 fun n ↦ ?_
  exact eventually_atTop.2 ⟨(n, 0), fun _ hk ↦ hk.1⟩

private theorem row_sparse_columns_density_zero (B : Set ℤ) (hB : B.Finite) :
    Tendsto (rowDensity {p | p.first ∈ B}) atTop (𝓝 0) := by
  classical
  have hbound (L n : ℕ) : ((row L n).filter fun p ↦ p.first ∈ B).card ≤ hB.toFinset.card := by
    apply Finset.card_le_card_of_injOn Point.first
    · intro p hp
      exact hB.mem_toFinset.2 (Finset.mem_filter.1 hp).2
    · intro p hp q hq hpq
      have hp' := (mem_row_iff _ _ _).1 (Finset.mem_filter.1 hp).1
      have hq' := (mem_row_iff _ _ _).1 (Finset.mem_filter.1 hq).1
      exact Point.ext hpq (hp'.2.2.trans hq'.2.2.symm)
  have htop := (tendsto_const_div_atTop_nhds_zero_nat (hB.toFinset.card : ℝ)).comp
    fst_tendsto_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Eventually.of_forall fun _ ↦ div_nonneg (by positivity) (by positivity)) ?_
  refine Eventually.of_forall fun p ↦ ?_
  change (((row p.1 p.2).filter fun q ↦ q.first ∈ B).card : ℝ) / (row p.1 p.2).card ≤
    ((hB.toFinset.card : ℝ) / p.1)
  rw [row_card]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hbound p.1 p.2) (by positivity)

theorem row_cosparse_columns_density_one (B : Set ℤ) (hB : Bᶜ.Finite) :
    Tendsto (rowDensity {p | p.first ∈ B}) atTop (𝓝 1) := by
  classical
  have hlim := (row_sparse_columns_density_zero Bᶜ hB).const_sub 1
  have hlim' : Tendsto (fun p ↦ 1 - rowDensity {q | q.first ∈ Bᶜ} p) atTop (𝓝 1) := by
    simpa only [sub_zero] using hlim
  refine hlim'.congr' ((eventually_ge_atTop ((1, 0) : ℕ × ℕ)).mono fun p hp ↦ ?_)
  have hpos : 0 < ((row p.1 p.2).card : ℝ) := by
    rw [row_card]
    exact Nat.cast_pos.2 hp.1
  simp only [rowDensity, Set.mem_ofPred_eq, Set.mem_compl_iff]
  have hsum := Finset.card_filter_add_card_filter_not (s := row p.1 p.2)
    (fun q : Point ↦ q.first ∈ B)
  have hsumReal : (((row p.1 p.2).filter fun q ↦ q.first ∈ B).card : ℝ) +
      (((row p.1 p.2).filter fun q ↦ q.first ∉ B).card : ℝ) = ((row p.1 p.2).card : ℝ) := by
    exact_mod_cast hsum
  field_simp
  linarith

/-- Example 4.5 validates the density-limit clause for each weak neighborhood,
even though there is no density-one set of times giving a weak limit. -/
theorem e0_density_one_weak_returns (U : Set (WeakSpace ℂ H)) (hU : U ∈ 𝓝 0) :
    Tendsto (rowDensity {s | toWeakSpace ℂ H
        (representation (Multiplicative.ofAdd s) (basisVector 0)) ∈ U}) atTop (𝓝 1) := by
  let B := {a : ℤ | toWeakSpace ℂ H (basisVector a) ∈ U}
  have hi : Function.Injective (topDualPairing ℂ H).flip := by
    intro x y h
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ) hne
    exact hf (LinearMap.congr_fun h f)
  have ht : Tendsto (fun a : ℤ ↦ toWeakSpace ℂ H (basisVector a)) cofinite (𝓝 0) := by
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hi).2
    intro f
    change Tendsto (fun a : ℤ ↦ f (basisVector a)) cofinite (𝓝 (f 0))
    rw [map_zero]
    simpa only [basisVector, shift_single, zero_add] using eval_shift_tendsto_zero f (basisVector 0)
  have hB : Bᶜ.Finite := eventually_cofinite.1 (ht.eventually hU)
  convert row_cosparse_columns_density_one B hB using 1
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, B, representation_e0]

end JdLG.PaperExamplesBilateral
