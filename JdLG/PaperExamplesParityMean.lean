/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParityFolner
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Left amenability of the parity semigroup

The explicit Følner grids yield a normalized, positive, finitely additive
set function invariant under taking left-translation preimages.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

open Filter
open scoped Topology

/-- The nonempty members of the left Følner sequence in the even ideal. -/
def positiveGrid (n : ℕ) : Finset Point := folnerGrid (n + 1)

theorem positiveGrid_nonempty (n : ℕ) : (positiveGrid n).Nonempty :=
  folnerGrid_nonempty (Nat.succ_pos _)

open Classical in
/-- Normalized counting mass of a subset of the semigroup on one grid. -/
noncomputable def gridMass (A : Set Point) (n : ℕ) : ℝ :=
  (((positiveGrid n).filter fun s ↦ s ∈ A).card : ℝ) / ((positiveGrid n).card : ℝ)

theorem gridMass_mem_unitInterval (A : Set Point) (n : ℕ) :
    gridMass A n ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold gridMass
  have hpos : 0 < ((positiveGrid n).card : ℝ) :=
    Nat.cast_pos.2 (positiveGrid_nonempty n).card_pos
  exact ⟨div_nonneg (by positivity) hpos.le,
    (div_le_one hpos).2 (by
      exact_mod_cast Finset.card_filter_le (positiveGrid n) (fun s ↦ s ∈ A))⟩

/-- Each counting mass has an ultrafilter limit along the given sequence. -/
theorem exists_gridMass_limit (A : Set Point) :
    ∃ m ∈ Set.Icc (0 : ℝ) 1, Tendsto (gridMass A) (hyperfilter ℕ : Filter ℕ) (𝓝 m) := by
  have hmem : Set.Icc (0 : ℝ) 1 ∈ (hyperfilter ℕ).map (gridMass A) := by
    change ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), gridMass A n ∈ Set.Icc (0 : ℝ) 1
    exact Eventually.of_forall (gridMass_mem_unitInterval A)
  exact isCompact_Icc.ultrafilter_le_nhds' _ hmem

/-- The left-invariant finitely additive probability obtained from the grids. -/
noncomputable def parityMean (A : Set Point) : ℝ := (exists_gridMass_limit A).choose

theorem parityMean_mem_unitInterval (A : Set Point) : parityMean A ∈ Set.Icc (0 : ℝ) 1 :=
  (exists_gridMass_limit A).choose_spec.1

theorem gridMass_tendsto_parityMean (A : Set Point) :
    Tendsto (gridMass A) (hyperfilter ℕ : Filter ℕ) (𝓝 (parityMean A)) :=
  (exists_gridMass_limit A).choose_spec.2

theorem parityMean_empty : parityMean ∅ = 0 := by
  have h := gridMass_tendsto_parityMean (∅ : Set Point)
  have heq : gridMass (∅ : Set Point) = fun _ ↦ 0 := by
    funext n
    simp [gridMass]
  rw [heq] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem parityMean_univ : parityMean Set.univ = 1 := by
  have hgrid (n : ℕ) : gridMass Set.univ n = 1 := by
    simp [gridMass, (positiveGrid_nonempty n).card_ne_zero]
  have h := gridMass_tendsto_parityMean (Set.univ : Set Point)
  rw [funext hgrid] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem parityMean_union {A B : Set Point} (hAB : Disjoint A B) :
    parityMean (A ∪ B) = parityMean A + parityMean B := by
  classical
  have hmass (n : ℕ) : gridMass (A ∪ B) n = gridMass A n + gridMass B n := by
    have hdisj : Disjoint ((positiveGrid n).filter (fun x ↦ x ∈ A))
        ((positiveGrid n).filter (fun x ↦ x ∈ B)) := Finset.disjoint_left.2 fun _ hx hy ↦
      Set.disjoint_left.1 hAB (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2
    unfold gridMass
    rw [← add_div, ← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj]
    apply congrArg (fun F : Finset Point ↦ (F.card : ℝ) / (positiveGrid n).card)
    ext x
    simp only [Finset.mem_filter, Set.mem_union, Finset.mem_union]
    tauto
  have hlim := (gridMass_tendsto_parityMean A).add (gridMass_tendsto_parityMean B)
  exact tendsto_nhds_unique (gridMass_tendsto_parityMean (A ∪ B))
    (hlim.congr' (Eventually.of_forall fun n ↦ (hmass n).symm))

open Classical in
private theorem filtered_card_diff (F G : Finset Point) (A : Set Point) :
    |(((F.filter fun x ↦ x ∈ A).card : ℝ) - (G.filter fun x ↦ x ∈ A).card)| ≤
      ((F \ G).card : ℝ) + ((G \ F).card : ℝ) := by
  classical
  let F' := F.filter (fun x ↦ x ∈ A)
  let G' := G.filter (fun x ↦ x ∈ A)
  have hF : (F' \ G').card ≤ (F \ G).card := by
    apply Finset.card_mono
    intro x hx
    simp only [F', G', Finset.mem_sdiff, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1.1, fun hg ↦ hx.2 ⟨hg, hx.1.2⟩⟩
  have hG : (G' \ F').card ≤ (G \ F).card := by
    apply Finset.card_mono
    intro x hx
    simp only [F', G', Finset.mem_sdiff, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1.1, fun hf ↦ hx.2 ⟨hf, hx.1.2⟩⟩
  have hF' : ((F' \ G').card : ℝ) + ((F' ∩ G').card : ℝ) = (F'.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter F' G'
  have hG' : ((G' \ F').card : ℝ) + ((F' ∩ G').card : ℝ) = (G'.card : ℝ) := by
    rw [Finset.inter_comm]
    exact_mod_cast Finset.card_sdiff_add_card_inter G' F'
  have hF'' : ((F' \ G').card : ℝ) ≤ (F \ G).card := by exact_mod_cast hF
  have hG'' : ((G' \ F').card : ℝ) ≤ (G \ F).card := by exact_mod_cast hG
  change |(F'.card : ℝ) - G'.card| ≤ ((F \ G).card : ℝ) + ((G \ F).card : ℝ)
  exact abs_le.2 ⟨by linarith [Nat.cast_nonneg (α := ℝ) ((F' \ G').card)],
    by linarith [Nat.cast_nonneg (α := ℝ) ((G' \ F').card)]⟩

open Classical in
private theorem positiveGrid_mass_deficit_bound (s : Point) (A : Set Point) (n : ℕ) :
    |gridMass {x | s * x ∈ A} n - gridMass A n| ≤
      2 * (((positiveGrid n \ (positiveGrid n).image (s * ·)).card : ℝ) /
        ((positiveGrid n).card : ℝ)) := by
  classical
  let F := positiveGrid n
  let G := F.image (s * ·)
  have hcard : G.card = F.card :=
    Finset.card_image_of_injOn (left_multiplication_injective s).injOn
  have htranslate : ((G.filter fun x ↦ x ∈ A).card) = ((F.filter fun x ↦ s * x ∈ A).card) := by
    dsimp only [G]
    rw [Finset.filter_image, Finset.card_image_of_injOn (left_multiplication_injective s).injOn]
  have hdiff : (G \ F).card = (F \ G).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, hcard, Finset.inter_comm G F]
  change |(((F.filter fun x ↦ s * x ∈ A).card : ℝ) / F.card) -
    (((F.filter fun x ↦ x ∈ A).card : ℝ) / F.card)| ≤
      2 * (((F \ G).card : ℝ) / F.card)
  rw [← htranslate, ← sub_div, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ F.card)]
  have h := filtered_card_diff G F A
  rw [hdiff] at h
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- Left translation preserves the finitely additive probability. -/
theorem parityMean_left_invariant (s : Point) (A : Set Point) :
    parityMean {x | s * x ∈ A} = parityMean A := by
  have h₁ := gridMass_tendsto_parityMean {x | s * x ∈ A}
  have h₂ := gridMass_tendsto_parityMean A
  have hc := (h₁.sub h₂).abs
  have hu : Tendsto (fun n : ℕ ↦
      2 * (((positiveGrid n \ (positiveGrid n).image (s * ·)).card : ℝ) /
        ((positiveGrid n).card : ℝ))) atTop (𝓝 0) := by
    simpa only [positiveGrid, Function.comp_apply, mul_zero] using
      ((folnerGrid_left_folner s).comp (tendsto_add_atTop_nat 1)).const_mul 2
  have hzero : Tendsto (fun n ↦ |gridMass {x | s * x ∈ A} n - gridMass A n|)
      (hyperfilter ℕ : Filter ℕ) (𝓝 0) :=
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun _ ↦ abs_nonneg _) (Eventually.of_forall
        (positiveGrid_mass_deficit_bound s A))).mono_left
      (hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop)
  exact sub_eq_zero.1 (abs_eq_zero.1 (tendsto_nhds_unique hc hzero))

/-- There is no normalized right-invariant finitely additive probability
on the same semigroup. The two disjoint principal left ideals would both
have mass one. -/
theorem no_right_invariant_probability (m : Set Point → ℝ)
    (hone : m Set.univ = 1) (hbounded : ∀ A, m A ≤ 1)
    (hadd : ∀ A B, Disjoint A B → m (A ∪ B) = m A + m B)
    (hinv : ∀ s A, m {x | x * s ∈ A} = m A) : False := by
  let A := Set.range (· * evenPoint)
  let B := Set.range (· * oddPoint)
  have ha : {x | x * evenPoint ∈ A} = Set.univ := Set.eq_univ_of_forall fun _ ↦ ⟨_, rfl⟩
  have hb : {x | x * oddPoint ∈ B} = Set.univ := Set.eq_univ_of_forall fun _ ↦ ⟨_, rfl⟩
  have ha₁ := hinv evenPoint A
  have hb₁ := hinv oddPoint B
  rw [ha, hone] at ha₁
  rw [hb, hone] at hb₁
  have hs := hadd A B principal_left_ideals_disjoint
  linarith [hbounded (A ∪ B)]

end JdLG.PaperExamplesParity
