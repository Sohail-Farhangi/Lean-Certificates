/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceTiling

@[expose] public section
noncomputable section

namespace SixProblems

open scoped Classical
open Filter
open scoped Topology

variable {G : Type*} [Group G] [DecidableEq G]

/-- Right translate of a finite shape, consistent with left-invariance of the blocks. -/
def tileTranslate (S : Finset G) (center : G) : Finset G := S.image (· * center)

@[simp] theorem card_tileTranslate (S : Finset G) (center : G) :
    (tileTranslate S center).card = S.card :=
  Finset.card_image_of_injective _ fun _ _ h ↦ mul_right_cancel h

theorem mem_tileTranslate {S : Finset G} {c g : G} :
    g ∈ tileTranslate S c ↔ g * c⁻¹ ∈ S := by
  constructor
  · intro h
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h
    simpa using hd
  · intro h
    exact Finset.mem_image.mpr ⟨g * c⁻¹, h, by simp⟩

/-- Sites of a translate available before adding it to the covered set. -/
private def availableSites (S : Finset G) (center : G) (U : Set G) : Finset G :=
  (tileTranslate S center).filter (· ∉ U)

private theorem availableSites_antitone (S : Finset G) (center : G) :
    Antitone (availableSites S center) := by
  intro U V hUV g hg
  obtain ⟨hTile, hOut⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨hTile, fun h ↦ hOut (hUV h)⟩

/-- Scan an enumeration of centers, retaining a translate if it contributes at
least `b` sites outside the set already covered. -/
private def greedyCoverStage (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) : ℕ → Set G :=
  Nat.rec U (fun n C ↦
    if b ≤ (availableSites S (e n) C).card then C ∪ ↑(tileTranslate S (e n)) else C)

private theorem greedyCoverStage_monotone (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) :
    Monotone (greedyCoverStage S e b U) := by
  apply monotone_nat_of_le_succ
  intro n
  change greedyCoverStage S e b U n ⊆ if b ≤ _ then _ ∪ _ else _
  split_ifs
  · exact Set.subset_union_left
  · exact Set.Subset.rfl

/-- Covered sites after scanning all centers. -/
private def greedyCover (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) : Set G :=
  ⋃ n, greedyCoverStage S e b U n

private theorem greedyCover_subset (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) (n : ℕ) :
    greedyCoverStage S e b U n ⊆ greedyCover S e b U :=
  Set.subset_iUnion _ n

/-- The part of the current translate that newly contributes to the cover. -/
private def greedyCore (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) (n : ℕ) : Finset G :=
  let C := greedyCoverStage S e b U n
  if b ≤ (availableSites S (e n) C).card then availableSites S (e n) C else ∅

private theorem greedyCoverStage_succ_eq_union_core (S : Finset G) (e : ℕ → G) (b : ℕ)
    (U : Set G) (n : ℕ) :
    greedyCoverStage S e b U (n + 1) = greedyCoverStage S e b U n ∪ ↑(greedyCore S e b U n) := by
  let C := greedyCoverStage S e b U n
  change (if b ≤ (availableSites S (e n) C).card then C ∪ ↑(tileTranslate S (e n)) else C) = _
  by_cases h : b ≤ (availableSites S (e n) C).card
  · simp only [greedyCore, ← show C = greedyCoverStage S e b U n from rfl, h, ite_true]
    ext g
    change (g ∈ C ∨ g ∈ tileTranslate S (e n)) ↔ g ∈ C ∨ g ∈ availableSites S (e n) C
    rw [availableSites, Finset.mem_filter]
    tauto
  · simp [greedyCore, ← show C = greedyCoverStage S e b U n from rfl, h]

private theorem greedyCore_subset_tile (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) (n : ℕ) :
    greedyCore S e b U n ⊆ tileTranslate S (e n) := by
  dsimp only [greedyCore]
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

private theorem greedyCore_disjoint_stage (S : Finset G) (e : ℕ → G) (b : ℕ)
    (U : Set G) (n : ℕ) :
    Disjoint (↑(greedyCore S e b U n) : Set G) (greedyCoverStage S e b U n) := by
  rw [Set.disjoint_left]
  intro g hg hStage
  dsimp only [greedyCore] at hg
  split_ifs at hg
  · exact (Finset.mem_filter.mp hg).2 hStage
  · simp at hg

private theorem greedyCore_disjoint (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) :
    Pairwise (fun i j ↦ Disjoint (greedyCore S e b U i) (greedyCore S e b U j)) := by
  have hLt {i j : ℕ} (hij : i < j) : Disjoint (greedyCore S e b U i) (greedyCore S e b U j) := by
    rw [← Finset.disjoint_coe]
    apply (greedyCore_disjoint_stage S e b U j).symm.mono_left
    exact (Set.subset_union_right.trans (greedyCoverStage_succ_eq_union_core S e b U i).symm.subset).trans
      (greedyCoverStage_monotone S e b U (Nat.succ_le_of_lt hij))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hLt h
  · exact (hLt h).symm

private theorem greedyCover_eq_union_cores (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) :
    greedyCover S e b U = U ∪ ⋃ n, ↑(greedyCore S e b U n) := by
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro n
    induction n with
    | zero => exact Set.subset_union_left
    | succ n hn =>
      rw [greedyCoverStage_succ_eq_union_core]
      exact Set.union_subset hn ((Set.subset_iUnion
        (fun i ↦ (↑(greedyCore S e b U i) : Set G)) n).trans Set.subset_union_right)
  · apply Set.union_subset (greedyCover_subset S e b U 0)
    apply Set.iUnion_subset
    intro n
    exact (Set.subset_union_right.trans (greedyCoverStage_succ_eq_union_core S e b U n).symm.subset).trans
      (greedyCover_subset S e b U (n + 1))

private theorem availableSites_greedyCover_card_lt (S : Finset G) (e : ℕ → G)
    (he : Function.Surjective e) {b : ℕ} (hb : 0 < b) (U : Set G) (c : G) :
    (availableSites S c (greedyCover S e b U)).card < b := by
  obtain ⟨n, rfl⟩ := he c
  by_cases h : b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card
  · have hg : ↑(tileTranslate S (e n)) ⊆ greedyCover S e b U := by
      apply Set.Subset.trans _ (greedyCover_subset S e b U (n + 1))
      change (↑(tileTranslate S (e n)) : Set G) ⊆
        if b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card then
          greedyCoverStage S e b U n ∪ ↑(tileTranslate S (e n)) else greedyCoverStage S e b U n
      simp only [h, ite_true]
      exact Set.subset_union_right
    have hEmpty : availableSites S (e n) (greedyCover S e b U) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hmem
      exact (Finset.mem_filter.mp hmem).2 (hg (Finset.mem_filter.mp hmem).1)
    simpa [hEmpty] using hb
  · exact (Finset.card_le_card (availableSites_antitone S (e n) (greedyCover_subset S e b U n))).trans_lt
      (Nat.lt_of_not_ge h)

/-- One maximal greedy layer produces disjoint cores of approved translates.
Every translate of the chosen shape has fewer than `b` sites outside the enlarged cover. -/
theorem exists_greedyCover [Countable G] (S : Finset G) {b : ℕ} (hb : 0 < b) (U : Set G) :
    ∃ (V : Set G) (e : ℕ → G) (R : ℕ → Finset G),
      V = U ∪ ⋃ n, ↑(R n) ∧
      Pairwise (fun i j ↦ Disjoint (R i) (R j)) ∧
      (∀ n, Disjoint (↑(R n) : Set G) U) ∧
      (∀ n, R n ⊆ tileTranslate S (e n) ∧ (R n = ∅ ∨ b ≤ (R n).card)) ∧
      (∀ n, (R n).Nonempty → ↑(tileTranslate S (e n)) ⊆ V) ∧
      (∀ c : G, ((tileTranslate S c).filter (· ∉ V)).card < b) := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  refine ⟨greedyCover S e b U, e, greedyCore S e b U,
    greedyCover_eq_union_cores S e b U, greedyCore_disjoint S e b U, ?_, ?_, ?_,
    availableSites_greedyCover_card_lt S e he hb U⟩
  · intro n
    exact (greedyCore_disjoint_stage S e b U n).mono_right
      (greedyCoverStage_monotone S e b U (Nat.zero_le n))
  · intro n
    refine ⟨greedyCore_subset_tile S e b U n, ?_⟩
    dsimp only [greedyCore]
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl
  · intro n hn
    have h : b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card := by
      by_contra h
      simp [greedyCore, h] at hn
    apply Set.Subset.trans _ (greedyCover_subset S e b U (n + 1))
    change (↑(tileTranslate S (e n)) : Set G) ⊆
      if b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card then
        greedyCoverStage S e b U n ∪ ↑(tileTranslate S (e n)) else greedyCoverStage S e b U n
    simp only [h, ite_true]
    exact Set.subset_union_right

/-- Count selected pairs `(shape element, center)` to bound from below the coverage of a
maximal greedy layer inside a finite region. The centers tested here have their entire
translate in that region and outside the prior covered set. -/
theorem card_greedyCover_layer (S centers region : Finset G) {U V : Set G} {b : ℕ}
    (hMaximal : ∀ c : G, ((tileTranslate S c).filter (· ∉ V)).card < b)
    (hInside : ∀ c ∈ centers, tileTranslate S c ⊆ region)
    (hOutside : ∀ c ∈ centers, ∀ g ∈ tileTranslate S c, g ∉ U) :
    centers.card * (S.card + 1 - b) ≤
      S.card * (region.filter (fun g ↦ g ∈ V ∧ g ∉ U)).card := by
  let newSites := region.filter (fun g ↦ g ∈ V ∧ g ∉ U)
  have hLower (c : G) : S.card + 1 - b ≤ (S.filter (fun s ↦ s * c ∈ V)).card := by
    have hImage : ((S.filter (fun s ↦ s * c ∉ V)).image (· * c)) =
        (tileTranslate S c).filter (· ∉ V) := by
      ext g
      simp only [Finset.mem_image, Finset.mem_filter, tileTranslate]
      constructor
      · rintro ⟨s, ⟨hs, hV⟩, rfl⟩
        exact ⟨⟨s, hs, rfl⟩, hV⟩
      · rintro ⟨⟨s, hs, rfl⟩, hV⟩
        exact ⟨s, ⟨hs, hV⟩, rfl⟩
    have hsmall := hMaximal c
    rw [← hImage, Finset.card_image_of_injective _
      (show Function.Injective ((· * c) : G → G) from fun _ _ h ↦ mul_right_cancel h)] at hsmall
    have hsum := Finset.card_filter_add_card_filter_not (s := S) (fun s ↦ s * c ∈ V)
    omega
  have hUpper (s : G) (hs : s ∈ S) : (centers.filter (fun c ↦ s * c ∈ V)).card ≤ newSites.card := by
    rw [← Finset.card_image_of_injective _
      (show Function.Injective ((s * ·) : G → G) from fun _ _ h ↦ mul_left_cancel h)]
    apply Finset.card_le_card
    intro g hg
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hC, hV⟩ := Finset.mem_filter.mp hc
    have hmem : s * c ∈ tileTranslate S c := Finset.mem_image.mpr ⟨s, hs, rfl⟩
    exact Finset.mem_filter.mpr ⟨hInside c hC hmem, hV, hOutside c hC _ hmem⟩
  calc
    _ = ∑ c ∈ centers, (S.card + 1 - b) := by simp
    _ ≤ ∑ c ∈ centers, (S.filter (fun s ↦ s * c ∈ V)).card :=
      Finset.sum_le_sum fun c _ ↦ hLower c
    _ = ∑ s ∈ S, (centers.filter (fun c ↦ s * c ∈ V)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ s ∈ S, newSites.card := Finset.sum_le_sum hUpper
    _ = _ := by simp [newSites]

omit [Group G] [DecidableEq G] in
private theorem finiteAverage_sum (A D : Finset G) (w : G → G → ℝ) :
    finiteAverage A (fun g ↦ ∑ d ∈ D, w d g) = ∑ d ∈ D, finiteAverage A (w d) := by
  simp only [finiteAverage, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- For a bounded transport by finitely many left displacements, the difference between
averaged outgoing and incoming mass vanishes along the prescribed Følner sequence. -/
theorem LeftFolnerSequence.tendsto_transport_balance (F : LeftFolnerSequence G) (D : Finset G)
    (w : G → G → ℝ) (C : ℝ) (hBound : ∀ d ∈ D, ∀ g, ‖w d g‖ ≤ C) :
    Tendsto (fun n ↦ finiteAverage (F.blocks n) (fun g ↦ ∑ d ∈ D, w d g) -
      finiteAverage (F.blocks n) (fun g ↦ ∑ d ∈ D, w d (d⁻¹ * g))) atTop (𝓝 0) := by
  simp_rw [finiteAverage_sum, ← Finset.sum_sub_distrib]
  induction D using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using tendsto_const_nhds
  | insert d D hd ih =>
    have hD : ∀ x ∈ D, ∀ g, ‖w x g‖ ≤ C := fun x hx ↦ hBound x (Finset.mem_insert_of_mem hx)
    have h := (F.tendsto_average_sub_translate d⁻¹ (w d) C (hBound d (Finset.mem_insert_self _ _))).neg
    simp only [neg_zero, neg_sub] at h
    simpa only [Finset.sum_insert hd, zero_add] using h.add (ih hD)

omit [Group G] [DecidableEq G] in
private theorem finiteAverage_indicator (A : Finset G) (B : Set G) :
    finiteAverage A (fun g ↦ if g ∈ B then (1 : ℝ) else 0) = ((A.filter (· ∈ B)).card : ℝ) / A.card := by
  rw [finiteAverage, smul_eq_mul, ← Finset.sum_filter]
  simp [div_eq_mul_inv, mul_comm]

/-- If the sites of `B` each send one unit, the other sites send zero, and each
site receives at most `ρ` units, then `ρ` bounds the eventual upper density of `B`. -/
theorem LeftFolnerSequence.eventually_density_le_of_transport (F : LeftFolnerSequence G)
    (D : Finset G) (w : G → G → ℝ) (C : ℝ) (hBound : ∀ d ∈ D, ∀ g, ‖w d g‖ ≤ C)
    (B : Set G) (ρ : ℝ) (hOut : ∀ g, (∑ d ∈ D, w d g) = if g ∈ B then 1 else 0)
    (hIn : ∀ g, ∑ d ∈ D, w d (d⁻¹ * g) ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (((F.blocks n).filter (· ∈ B)).card : ℝ) / (F.blocks n).card < ρ + ε := by
  have hb := F.tendsto_transport_balance D w C hBound
  simp_rw [hOut, finiteAverage_indicator] at hb
  filter_upwards [hb.eventually_lt_const hε] with n hn
  let A := F.blocks n
  have hCard : 0 < (A.card : ℝ) := by exact_mod_cast (F.nonempty n).card_pos
  have hAvg : finiteAverage A (fun g ↦ ∑ d ∈ D, w d (d⁻¹ * g)) ≤ ρ := by
    simp only [finiteAverage, smul_eq_mul]
    calc
      _ ≤ (A.card : ℝ)⁻¹ * ∑ g ∈ A, ρ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ ↦ hIn g) (inv_nonneg.mpr hCard.le)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hCard.ne', one_mul]
  linarith

/-- The points outside `A` which enter `A` after some left shift from `Q`. -/
def externalBoundary (Q A : Finset G) : Finset G :=
  (Q.biUnion fun a ↦ A.image (a⁻¹ * ·)) \ A

theorem mem_externalBoundary {Q A : Finset G} {g : G} :
    g ∈ externalBoundary Q A ↔ g ∉ A ∧ ∃ q ∈ Q, q * g ∈ A := by
  simp only [externalBoundary, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_image]
  refine ⟨fun ⟨⟨q, hq, x, hx, he⟩, hg⟩ ↦ ⟨hg, q, hq, ?_⟩,
    fun ⟨hg, q, hq, hx⟩ ↦ ⟨⟨q, hq, q * g, hx, inv_mul_cancel_left _ _⟩, hg⟩⟩
  rwa [← he, mul_inv_cancel_left]

theorem externalBoundary_tileTranslate (Q A : Finset G) (c : G) :
    externalBoundary Q (tileTranslate A c) = tileTranslate (externalBoundary Q A) c := by
  ext g
  simp only [mem_externalBoundary, mem_tileTranslate, mul_assoc]

theorem externalBoundary_mono {P Q : Finset G} (hPQ : P ⊆ Q) (A : Finset G) :
    externalBoundary P A ⊆ externalBoundary Q A := by
  intro g hg
  obtain ⟨hOut, a, ha, hIn⟩ := mem_externalBoundary.mp hg
  exact mem_externalBoundary.mpr ⟨hOut, a, hPQ ha, hIn⟩

/-- The external boundary of a fixed finite collection of shifts has vanishing
relative cardinality on a left Følner sequence. -/
theorem LeftFolnerSequence.tendsto_externalBoundary (F : LeftFolnerSequence G) (Q : Finset G) :
    Tendsto (fun n ↦ ((externalBoundary Q (F.blocks n)).card : ℝ) / (F.blocks n).card)
      atTop (𝓝 0) := by
  let P := Q.image Inv.inv
  have hCard (A : Finset G) : (externalBoundary Q A).card ≤ Q.card * (leftBoundary P A).card := by
    have hSub : externalBoundary Q A ⊆ Q.biUnion (fun q ↦ (leftBoundary P A).image (q⁻¹ * ·)) := by
      intro g hg
      obtain ⟨hOut, q, hq, hIn⟩ := mem_externalBoundary.mp hg
      exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr ⟨q * g,
        mem_leftBoundary.mpr ⟨hIn, q⁻¹, Finset.mem_image_of_mem _ hq, by simpa using hOut⟩,
        inv_mul_cancel_left _ _⟩⟩
    exact (Finset.card_le_card hSub).trans (Finset.card_biUnion_le_card_mul _ _ _
      fun q _ ↦ Finset.card_image_le)
  have h := (F.tendsto_leftBoundary P).const_mul (Q.card : ℝ)
  rw [mul_zero] at h
  apply squeeze_zero (fun _ ↦ by positivity) _ h
  intro n
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hCard (F.blocks n)) (Nat.cast_nonneg _)

/-- A union of disjoint trimmed cores inherits a small external boundary when the whole
original translates have small boundaries compared with their cores. -/
theorem LeftFolnerSequence.eventually_externalCoverBoundary_le {ι : Type*}
    (F : LeftFolnerSequence G) (Q D : Finset G) (U : Set G) (A R : ι → Finset G)
    (hR : ∀ i, R i ⊆ A i) (hU : ∀ i, (R i).Nonempty → ↑(A i) ⊆ U)
    (hCover : ∀ g ∈ U, ∃ i, g ∈ R i) (hPair : Pairwise (fun i j ↦ Disjoint (R i) (R j)))
    (hD : ∀ i, ∀ g ∈ externalBoundary Q (A i), ∀ y ∈ R i, y * g⁻¹ ∈ D)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hSmall : ∀ i, (R i).Nonempty → ((externalBoundary Q (A i)).card : ℝ) ≤ ρ * (R i).card)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (((F.blocks n).filter (fun g ↦ g ∉ U ∧ ∃ q ∈ Q, q * g ∈ U)).card : ℝ) /
      (F.blocks n).card < ρ + ε := by
  let B : Set G := {g | g ∉ U ∧ ∃ q ∈ Q, q * g ∈ U}
  have pick (g : B) : ∃ i, (R i).Nonempty ∧ (g : G) ∈ externalBoundary Q (A i) := by
    obtain ⟨hg, q, hq, hqU⟩ := g.property
    obtain ⟨i, hi⟩ := hCover (q * (g : G)) hqU
    have hn : (R i).Nonempty := ⟨_, hi⟩
    exact ⟨i, hn, mem_externalBoundary.mpr ⟨fun h ↦ hg (hU i hn h), q, hq, hR i hi⟩⟩
  choose loc hLoc using pick
  let w (d g : G) : ℝ :=
    if hg : g ∈ B then
      let i := loc ⟨g, hg⟩
      if d * g ∈ R i then ((R i).card : ℝ)⁻¹ else 0
    else 0
  have hSize (g : B) : 0 < ((R (loc g)).card : ℝ) := by
    exact_mod_cast (hLoc g).1.card_pos
  have hw (d : G) (_hd : d ∈ D) (g : G) : ‖w d g‖ ≤ 1 := by
    by_cases hg : g ∈ B
    · simp only [w, hg, dite_true]
      split_ifs
      · rw [Real.norm_of_nonneg (inv_nonneg.mpr (hSize ⟨g, hg⟩).le),
          inv_le_one₀ (hSize ⟨g, hg⟩)]
        exact_mod_cast (hLoc ⟨g, hg⟩).1.card_pos
      · simp
    · simp [w, hg]
  have hOut (g : G) : (∑ d ∈ D, w d g) = if g ∈ B then 1 else 0 := by
    by_cases hg : g ∈ B
    · let i := loc ⟨g, hg⟩
      let C := D.filter (fun d ↦ d * g ∈ R i)
      have hImage : C.image (· * g) = R i := by
        ext y
        constructor
        · intro hy
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_filter.mp hd).2
        · intro hy
          refine Finset.mem_image.mpr ⟨y * g⁻¹, Finset.mem_filter.mpr
            ⟨hD i g (hLoc ⟨g, hg⟩).2 y hy, ?_⟩, by simp⟩
          simpa using hy
      have hCard : C.card = (R i).card := by
        rw [← hImage, Finset.card_image_of_injective _
          (show Function.Injective ((· * g) : G → G) from fun _ _ h ↦ mul_right_cancel h)]
      simp only [w, hg, dite_true, ite_true, ← Finset.sum_filter]
      change (∑ d ∈ C, ((R i).card : ℝ)⁻¹) = 1
      simp only [Finset.sum_const, nsmul_eq_mul, hCard]
      exact mul_inv_cancel₀ (hSize ⟨g, hg⟩).ne'
    · simp [w, hg]
  have hIn (g : G) : ∑ d ∈ D, w d (d⁻¹ * g) ≤ ρ := by
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hCover g hg
      let C := D.filter (fun d ↦ d⁻¹ * g ∈ externalBoundary Q (A i))
      have hCard : C.card ≤ (externalBoundary Q (A i)).card := by
        rw [← Finset.card_image_of_injective _ (show Function.Injective (fun d : G ↦ d⁻¹ * g) from
          fun _ _ h ↦ inv_injective (mul_right_cancel h))]
        exact Finset.card_le_card (Finset.image_subset_iff.mpr fun _ h ↦ (Finset.mem_filter.mp h).2)
      have hSize : 0 < ((R i).card : ℝ) := by exact_mod_cast (show (R i).Nonempty from ⟨g, hi⟩).card_pos
      calc
        _ ≤ ∑ d ∈ D, if d⁻¹ * g ∈ externalBoundary Q (A i) then ((R i).card : ℝ)⁻¹ else 0 := by
          apply Finset.sum_le_sum
          intro d _
          by_cases hx : d⁻¹ * g ∈ B
          · simp only [w, hx, dite_true, mul_inv_cancel_left]
            split_ifs with hy hz hz
            · have hEq : loc ⟨d⁻¹ * g, hx⟩ = i := by
                by_contra hn
                exact Finset.disjoint_left.mp (hPair hn) hy hi
              rw [hEq]
            · exfalso
              have hEq : loc ⟨d⁻¹ * g, hx⟩ = i := by
                by_contra hn
                exact Finset.disjoint_left.mp (hPair hn) hy hi
              exact hz (hEq ▸ (hLoc ⟨d⁻¹ * g, hx⟩).2)
            · exact inv_nonneg.mpr hSize.le
            · rfl
          · simp only [w, hx, dite_false]
            split_ifs
            · exact inv_nonneg.mpr hSize.le
            · rfl
        _ = (C.card : ℝ) * ((R i).card : ℝ)⁻¹ := by
          rw [← Finset.sum_filter]
          simp [C]
        _ ≤ ((externalBoundary Q (A i)).card : ℝ) * ((R i).card : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) (inv_nonneg.mpr hSize.le)
        _ ≤ ρ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hSize]
          exact hSmall i ⟨g, hi⟩
    · have hZero (d : G) : w d (d⁻¹ * g) = 0 := by
        by_cases hx : d⁻¹ * g ∈ B
        · have hy : g ∉ R (loc ⟨d⁻¹ * g, hx⟩) := fun h ↦
            hg (hU _ (hLoc ⟨d⁻¹ * g, hx⟩).1 (hR _ h))
          simp [w, hx, hy]
        · simp [w, hx]
      simpa [hZero] using hρ
  have hOut' (g : G) : (∑ d ∈ D, w d g) = @ite ℝ (g ∈ B) (Classical.propDecidable _) 1 0 := by
    have h := hOut g
    by_cases hg : g ∈ B <;> simpa [hg] using h
  filter_upwards [F.eventually_density_le_of_transport D w 1 hw B ρ hOut' hIn hε] with n hn
  have he : @Finset.filter G (· ∈ B) (fun g ↦ Classical.propDecidable (g ∈ B)) (F.blocks n) =
      (F.blocks n).filter (fun g ↦ g ∉ U ∧ ∃ q ∈ Q, q * g ∈ U) := by
    ext g
    simp only [Finset.mem_filter, B, Set.mem_ofPred_eq]
  rwa [he] at hn

/-- Fraction of a finite region lying in a specified set. -/
def finiteFraction (A : Finset G) (U : Set G) : ℝ :=
  ((A.filter (· ∈ U)).card : ℝ) / A.card

omit [Group G] [DecidableEq G] in
theorem finiteFraction_eq_blockProportion (A : Finset G) (U : Set G) :
    finiteFraction A U = blockProportion A U := rfl

omit [Group G] [DecidableEq G] in
theorem finiteFraction_eq_filter (A : Finset G) (U : Set G) (d : DecidablePred (· ∈ U)) :
    finiteFraction A U = ((@Finset.filter G (· ∈ U) d A).card : ℝ) / A.card := by
  unfold finiteFraction
  apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / A.card)
  ext g
  simp only [Finset.mem_filter]

omit [Group G] [DecidableEq G] in
theorem finiteFraction_setOf (A : Finset G) (p : G → Prop) :
    finiteFraction A {g | p g} = ((A.filter p).card : ℝ) / A.card := by
  unfold finiteFraction
  apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / A.card)
  ext g
  simp only [Finset.mem_filter, Set.mem_ofPred_eq]

/-- A greedy layer reduces the uncovered fraction by a fixed proportion, allowing for
centers whose translates meet the outside of the region or the previous cover. -/
theorem finiteFraction_complement_le_of_greedyLayer (S A : Finset G) (hS : S.Nonempty)
    {U V : Set G} (hUV : U ⊆ V) {b : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hηb : η * S.card ≤ ((S.card + 1 - b : ℕ) : ℝ))
    (hMaximal : ∀ c : G, ((tileTranslate S c).filter (· ∉ V)).card < b) :
    finiteFraction A Vᶜ ≤ (1 - η) * finiteFraction A Uᶜ +
      η * (finiteFraction A {g | ∃ s ∈ S, s * g ∉ A} +
        finiteFraction A {g | g ∉ U ∧ ∃ s ∈ S, s * g ∈ U}) := by
  let Z := A.filter (· ∉ U)
  let C := Z.filter (fun c ↦ ∀ s ∈ S, s * c ∈ A ∧ s * c ∉ U)
  let B := leftBoundary S A
  let E := A.filter (fun g ↦ g ∉ U ∧ ∃ s ∈ S, s * g ∈ U)
  let W := A.filter (fun g ↦ g ∈ V ∧ g ∉ U)
  have hBlame : Z \ C ⊆ B ∪ E := by
    intro g hg
    obtain ⟨hZ, hNC⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨hA, hU⟩ := Finset.mem_filter.mp hZ
    have hFail : ¬ ∀ s ∈ S, s * g ∈ A ∧ s * g ∉ U :=
      fun h ↦ hNC (Finset.mem_filter.mpr ⟨hZ, h⟩)
    push Not at hFail
    obtain ⟨s, hs, h⟩ := hFail
    by_cases hIn : s * g ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, hU, s, hs, h hIn⟩)
    · exact Finset.mem_union_left _ (mem_leftBoundary.mpr ⟨hA, s, hs, hIn⟩)
  have hZ : Z.card ≤ C.card + B.card + E.card := by
    have hle : (Z \ C).card ≤ B.card + E.card :=
      (Finset.card_le_card hBlame).trans (Finset.card_union_le _ _)
    have hsub : C ⊆ Z := Finset.filter_subset _ _
    have he := Finset.card_sdiff_add_card_eq_card hsub
    omega
  have hNew : (η * (C.card : ℝ)) ≤ W.card := by
    have hCount := card_greedyCover_layer S C A hMaximal
      (fun c hc g hg ↦ by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
        exact ((Finset.mem_filter.mp hc).2 s hs).1)
      (fun c hc g hg ↦ by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
        exact ((Finset.mem_filter.mp hc).2 s hs).2)
    have hCountR : (C.card : ℝ) * ((S.card + 1 - b : ℕ) : ℝ) ≤ S.card * (W.card : ℝ) := by
      exact_mod_cast hCount
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    refine (mul_le_mul_iff_right₀ hSpos).mp ?_
    calc
      (S.card : ℝ) * (η * (C.card : ℝ)) = (C.card : ℝ) * (η * S.card) := by ring
      _ ≤ (C.card : ℝ) * ((S.card + 1 - b : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hηb (Nat.cast_nonneg _)
      _ ≤ S.card * (W.card : ℝ) := hCountR
  have hcard : (A.filter (· ∉ V)).card + W.card = Z.card := by
    have h₁ : Z.filter (· ∈ V) = W := by
      ext g
      simp [Z, W, and_assoc, and_comm]
    have h₂ : Z.filter (· ∉ V) = A.filter (· ∉ V) := by
      ext g
      simp only [Z, Finset.mem_filter]
      exact ⟨fun ⟨⟨hA, _⟩, hV⟩ ↦ ⟨hA, hV⟩, fun ⟨hA, hV⟩ ↦ ⟨⟨hA, fun hu ↦ hV (hUV hu)⟩, hV⟩⟩
    rw [← h₁, ← h₂, add_comm, Finset.card_filter_add_card_filter_not]
  have hZr : (Z.card : ℝ) ≤ C.card + B.card + E.card := by exact_mod_cast hZ
  have hCardR : ((A.filter (· ∉ V)).card : ℝ) + W.card = Z.card := by exact_mod_cast hcard
  have he : ((A.filter (· ∉ V)).card : ℝ) ≤ (1 - η) * Z.card + η * (B.card + E.card) := by
    linarith [mul_le_mul_of_nonneg_left hZr hη]
  have hdiv := div_le_div_of_nonneg_right he (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  rw [add_div, mul_div_assoc, mul_div_assoc, add_div] at hdiv
  have hfrac (U : Set G) (p : G → Prop) [DecidablePred p] (h : ∀ g ∈ A, g ∈ U ↔ p g) :
      finiteFraction A U = ((A.filter p).card : ℝ) / A.card := by
    unfold finiteFraction
    rw [Finset.filter_congr h]
  have hB : A.filter (fun g ↦ ∃ s ∈ S, s * g ∉ A) = B := by
    ext g
    exact Finset.mem_filter.trans mem_leftBoundary.symm
  rw [hfrac Vᶜ (· ∉ V) (fun _ _ ↦ Iff.rfl), hfrac Uᶜ (· ∉ U) (fun _ _ ↦ Iff.rfl),
    hfrac _ (fun g ↦ ∃ s ∈ S, s * g ∉ A) (fun _ _ ↦ Iff.rfl), hB,
    hfrac _ (fun g ↦ g ∉ U ∧ ∃ s ∈ S, s * g ∈ U) (fun _ _ ↦ Iff.rfl)]
  exact hdiv

end SixProblems
