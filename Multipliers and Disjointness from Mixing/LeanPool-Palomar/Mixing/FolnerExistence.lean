/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.WeakMixing
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi

/-! # Finite Følner blocks for countable abelian groups -/

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace Mixing

variable {G : Type*} [CommGroup G]

noncomputable def powerBox (S : Finset G) (n : ℕ) : Finset G := by
  classical
  exact Finset.univ.image (fun f : ↥S → Fin (n + 1) =>
    ∏ a : ↥S, (a : G) ^ (f a : ℕ))

theorem powerBox_nonempty (S : Finset G) (n : ℕ) : (powerBox S n).Nonempty := by
  classical
  unfold powerBox
  exact ⟨_, Finset.mem_image.mpr ⟨fun _ => 0, Finset.mem_univ _, rfl⟩⟩

theorem powerBox_card_le (S : Finset G) (n : ℕ) :
    (powerBox S n).card ≤ (n + 1) ^ S.card := by
  classical
  unfold powerBox
  refine Finset.card_image_le.trans_eq ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

theorem powerBox_subset_succ (S : Finset G) (n : ℕ) : powerBox S n ⊆ powerBox S (n + 1) := by
  classical
  unfold powerBox
  rintro x hx
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨fun a => (f a).castSucc, Finset.mem_univ _, rfl⟩

theorem mul_mem_powerBox_succ (S : Finset G) (n : ℕ) (a : G) (ha : a ∈ S)
    {x : G} (hx : x ∈ powerBox S n) : a * x ∈ powerBox S (n + 1) := by
  classical
  unfold powerBox at hx ⊢
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
  let i : S := ⟨a, ha⟩
  let f' (j : S) : Fin (n + 1 + 1) :=
    ⟨(f j : ℕ) + if j = i then 1 else 0, by
      have h := (f j).isLt
      split <;> omega⟩
  refine Finset.mem_image.mpr ⟨f', Finset.mem_univ _, ?_⟩
  simp only [f', pow_add, Finset.prod_mul_distrib]
  have h := Finset.prod_ite_eq' Finset.univ i (fun j : S => (j : G))
  simp only [Finset.mem_univ, ite_true] at h
  have he : (∏ j : S, (j : G) ^ (if j = i then 1 else 0)) = a := by
    simp only [apply_ite, pow_one, pow_zero]
    simpa only [i] using h
  rw [he, mul_comm]

theorem exists_powerBox_small_growth (S : Finset G) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ((powerBox S (n + 1)).card : ℝ) ≤ (1 + ε) * (powerBox S n).card := by
  by_contra! hNot
  have hLower (n : ℕ) : (1 + ε) ^ n ≤ ((powerBox S n).card : ℝ) := by
    induction n with
    | zero =>
      rw [pow_zero]
      exact_mod_cast (powerBox_nonempty S 0).card_pos
    | succ n ih =>
      rw [pow_succ, mul_comm]
      exact (mul_le_mul_of_nonneg_left ih (by positivity)).trans (hNot n).le
  have hUpper (n : ℕ) : ((powerBox S n).card : ℝ) ≤ (n + 1 : ℝ) ^ S.card := by
    exact_mod_cast powerBox_card_le S n
  have hLim : Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ S.card / (1 + ε) ^ (n + 1))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt S.card (r := 1 + ε)
      (by linarith)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have hEv := hLim.eventually_lt_const (show 0 < (1 + ε)⁻¹ by positivity)
  obtain ⟨n, hn⟩ := hEv.exists
  have hGe : (1 + ε)⁻¹ ≤ (n + 1 : ℝ) ^ S.card / (1 + ε) ^ (n + 1) := by
    rw [pow_succ, ← div_div, inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using (hLower n).trans (hUpper n))
  exact hn.not_ge hGe

theorem exists_finite_block_small_deficit (S : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset G, E.Nonempty ∧ ∀ a ∈ S,
      finsetDensity E {g | ∀ y ∈ E, g ≠ a * y} ≤ ε := by
  classical
  obtain ⟨n, hn⟩ := exists_powerBox_small_growth S ε hε
  let E := powerBox S n
  have hE : E.Nonempty := powerBox_nonempty _ _
  refine ⟨E, hE, ?_⟩
  intro a ha
  let T := E.image (a * ·)
  have hT : T.card = E.card := Finset.card_image_of_injective _ (mul_right_injective a)
  have hSub : E ∪ T ⊆ powerBox S (n + 1) := by
    apply Finset.union_subset (powerBox_subset_succ S n)
    rintro _ hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    exact mul_mem_powerBox_succ S n a ha hx
  have hBound : ((E \ T).card : ℝ) + E.card ≤ ((powerBox S (n + 1)).card : ℝ) := by
    have h := Finset.card_sdiff_add_card E T
    rw [hT] at h
    exact_mod_cast h.le.trans (Finset.card_le_card hSub)
  unfold finsetDensity
  rw [div_le_iff₀ (by exact_mod_cast hE.card_pos)]
  refine le_trans (b := ((E \ T).card : ℝ)) ?_ ?_
  · norm_cast
    apply Finset.card_le_card
    intro g hg
    simp only [Finset.mem_filter, Set.mem_ofPred_eq, Finset.mem_sdiff, T, Finset.mem_image,
      not_exists, not_and] at hg ⊢
    tauto
  change ((powerBox S (n + 1)).card : ℝ) ≤ (1 + ε) * (E.card : ℝ) at hn
  linarith

/-- Every countable abelian group admits a Følner sequence of finite nonempty blocks. -/
theorem exists_isFolnerSequence [Countable G] : ∃ F : ℕ → Finset G, IsFolnerSequence F := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat G
  let S (n : ℕ) := (Finset.range n).preimage e he.injOn
  choose F hF hDef using fun n : ℕ => exists_finite_block_small_deficit (S n)
    (ε := 1 / (n + 1)) (by positivity)
  refine ⟨F, hF, fun a => ?_⟩
  apply squeeze_zero' (f := fun n => finsetDensity (F n) {g | ∀ y ∈ F n, g ≠ a * y})
    (.of_forall fun n => finsetDensity_nonneg _ _) _ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_gt_atTop (e a)] with n hn
  exact hDef n a (by simpa [S] using hn)

end Mixing
