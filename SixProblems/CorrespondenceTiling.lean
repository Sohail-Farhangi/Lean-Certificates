/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceAverages
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section
noncomputable section

namespace SixProblems

open Filter
open scoped Topology symmDiff

variable {G : Type*} [Group G] [DecidableEq G]

/-- The points of `A` that leave `A` after at least one left shift from `D`. -/
def leftBoundary (D A : Finset G) : Finset G := by
  classical
  exact A.filter fun g ↦ ∃ d ∈ D, d * g ∉ A

theorem mem_leftBoundary {D A : Finset G} {g : G} :
    g ∈ leftBoundary D A ↔ g ∈ A ∧ ∃ d ∈ D, d * g ∉ A := by
  simp [leftBoundary]

private theorem leftBoundary_subset_union (D A : Finset G) :
    leftBoundary D A ⊆ D.biUnion (fun d ↦ (A.image (d⁻¹ * ·)) ∆ A) := by
  intro g hg
  obtain ⟨hgA, d, hd, hdg⟩ := mem_leftBoundary.mp hg
  refine Finset.mem_biUnion.mpr ⟨d, hd, Finset.symmDiff_subset_sdiff' ?_⟩
  refine Finset.mem_sdiff.mpr ⟨hgA, fun hm ↦ ?_⟩
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hm
  apply hdg
  have : z = d * g := by rw [← he, mul_inv_cancel_left]
  simpa [← this] using hz

/-- The fraction of points in the boundary for any fixed finite set of shifts tends to zero. -/
theorem LeftFolnerSequence.tendsto_leftBoundary (F : LeftFolnerSequence G) (D : Finset G) :
    Tendsto (fun n ↦ ((leftBoundary D (F.blocks n)).card : ℝ) / (F.blocks n).card)
      atTop (𝓝 0) := by
  let defect (d : G) (n : ℕ) :=
    ((F.blocks n).image (d⁻¹ * ·) ∆ F.blocks n).card / ((F.blocks n).card : ℝ)
  have hsum : Tendsto (fun n ↦ ∑ d ∈ D, defect d n) atTop (𝓝 0) := by
    induction D using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using tendsto_const_nhds
    | insert d D hd hD =>
      simp only [Finset.sum_insert hd]
      simpa only [zero_add] using (F.tendsto_defect d⁻¹).add hD
  apply squeeze_zero (fun _ ↦ by positivity) _ hsum
  intro n
  rw [← Finset.sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.card_le_card (leftBoundary_subset_union D (F.blocks n))).trans
    Finset.card_biUnion_le

/-- An arbitrary Følner sequence in an infinite group eventually has at least any given size. -/
theorem LeftFolnerSequence.tendsto_card [Infinite G] (F : LeftFolnerSequence G) :
    Tendsto (fun n ↦ (F.blocks n).card) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  obtain ⟨D, hD⟩ := Infinite.exists_subset_card_eq G k
  filter_upwards [(F.tendsto_leftBoundary D).eventually_lt_const (zero_lt_one' ℝ)] with n hn
  let A := F.blocks n
  have hA : (0 : ℝ) < A.card := by exact_mod_cast (F.nonempty n).card_pos
  have hlt : (leftBoundary D A).card < A.card := by
    have h := (div_lt_iff₀ hA).mp hn
    rw [one_mul] at h
    exact_mod_cast h
  have hNot : ¬ A ⊆ leftBoundary D A := fun h ↦ (Finset.card_le_card h).not_gt hlt
  obtain ⟨g, hg, hgB⟩ := Finset.not_subset.mp hNot
  have hgD (d : G) (hd : d ∈ D) : d * g ∈ A := by
    by_contra hdg
    exact hgB (mem_leftBoundary.mpr ⟨hg, d, hd, hdg⟩)
  have hsub : D.image (· * g) ⊆ A := Finset.image_subset_iff.mpr hgD
  have hinj : Function.Injective ((· * g) : G → G) := fun _ _ h ↦ mul_right_cancel h
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective D hinj, hD] at hcard

/-- A partition of the group into finite cells, with a uniform finite bound on the left
displacements between elements of each cell. A tiling with finitely many right-translate
shapes has this property. -/
structure BoundedTilePartition (G : Type*) [Group G] [DecidableEq G] where
  cell : G → Finset G
  mem_cell (g : G) : g ∈ cell g
  cell_eq {g h : G} (hh : h ∈ cell g) : cell h = cell g
  displacements : Finset G
  mem_displacements {g h : G} (hh : h ∈ cell g) : h * g⁻¹ ∈ displacements

/-- Boundary points whose partition cell is not contained in the block. -/
def tileBoundary (T : G → Finset G) (A : Finset G) : Finset G :=
  A.filter fun g ↦ ¬ T g ⊆ A

omit [Group G] [DecidableEq G] in
/-- The proportion of a block that belongs to a specified set. -/
def blockProportion (A : Finset G) (E : Set G) : ℝ := by
  classical
  exact ((A.filter (· ∈ E)).card : ℝ) / A.card

private theorem coherentTilePartitions_monotone (P : ℕ → BoundedTilePartition G)
    (hP : ∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g) (g : G) :
    Monotone (fun k ↦ (P k).cell g) := monotone_nat_of_le_succ fun k ↦ hP k g

/-- From congruent tilings and a prescribed Følner sequence, choose a single partition
using finitely many cells from each level, such that almost every point of a late block
belongs to a cell entirely inside the block. This is the diagonal partition step in the
inverse correspondence argument. -/
theorem exists_mixedTilePartition [Countable G] [Infinite G] (F : LeftFolnerSequence G)
    (P : ℕ → BoundedTilePartition G)
    (hP : ∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g)
    (bad : ℕ → Set G) (δs : ℕ → ℝ) (hδs : ∀ k, 0 ≤ δs k) (hSum : Summable δs)
    (hSparse : ∀ k, ∀ᶠ n in atTop, blockProportion (F.blocks n) (bad k) ≤ δs k) :
    ∃ level : G → ℕ,
      (∀ g h, h ∈ (P (level g)).cell g → level h = level g) ∧
      (∀ k, {g | level g ≤ k}.Finite) ∧
      Tendsto (fun n ↦ ((tileBoundary (fun g ↦ (P (level g)).cell g) (F.blocks n)).card : ℝ) /
        (F.blocks n).card) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ blockProportion (F.blocks n) {g | g ∈ bad (level g)}) atTop (𝓝 0) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let moves (k : ℕ) := (Finset.range (k + 1)).biUnion (fun j ↦ (P j).displacements)
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hThreshold (k : ℕ) : ∃ N, ∀ n ≥ N,
      ((leftBoundary (moves (k + 1)) (F.blocks n)).card : ℝ) / (F.blocks n).card < ε k ∧
      ∀ j ∈ Finset.range (k+2), blockProportion (F.blocks n) (bad j) ≤ δs j := by
    apply eventually_atTop.1
    exact ((F.tendsto_leftBoundary (moves (k+1))).eventually_lt_const (hε k)).and
      ((eventually_all_finset (Finset.range (k+2))).mpr (fun j _ ↦ hSparse j))
  choose N hN using hThreshold
  let cutoff : ℕ → ℕ := Nat.rec (N 0) (fun k c ↦ max (c + 1) (N (k + 1)))
  have hCut (k : ℕ) : N k ≤ cutoff k := by cases k <;> simp [cutoff]
  have hCutMono : Monotone cutoff := monotone_nat_of_le_succ fun k ↦ by
    show cutoff k ≤ max (cutoff k + 1) (N (k + 1))
    exact (Nat.le_succ _).trans (le_max_left _ _)
  have hCutLarge (k : ℕ) : k ≤ cutoff k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k hk =>
      show k + 1 ≤ max (cutoff k + 1) (N (k + 1))
      exact (Nat.succ_le_succ hk).trans (le_max_left _ _)
  let seeds (k : ℕ) := ((Finset.range (cutoff k + 1)).biUnion F.blocks) ∪
    ((Finset.range (k + 1)).image e)
  let D (k : ℕ) := (seeds k).biUnion (P (k + 1)).cell
  have hSeeds {j k : ℕ} (hjk : j ≤ k) : seeds j ⊆ seeds k := by
    apply Finset.union_subset_union
    · exact Finset.biUnion_subset_biUnion_of_subset_left _
        (Finset.range_mono (Nat.succ_le_succ (hCutMono hjk)))
    · exact Finset.image_subset_image (Finset.range_mono (Nat.succ_le_succ hjk))
  have hDMono : Monotone D := by
    intro j k hjk g hg
    obtain ⟨z, hz, hgz⟩ := Finset.mem_biUnion.mp hg
    exact Finset.mem_biUnion.mpr ⟨z, hSeeds hjk hz,
      coherentTilePartitions_monotone P hP z (Nat.succ_le_succ hjk) hgz⟩
  have hSeedD (k : ℕ) : seeds k ⊆ D k := fun g hg ↦
    Finset.mem_biUnion.mpr ⟨g, hg, (P (k + 1)).mem_cell g⟩
  have hDClose {k : ℕ} {g h : G} (hg : g ∈ D k) (hh : h ∈ (P (k + 1)).cell g) : h ∈ D k := by
    obtain ⟨z, hz, hgz⟩ := Finset.mem_biUnion.mp hg
    exact Finset.mem_biUnion.mpr ⟨z, hz, (P (k + 1)).cell_eq hgz ▸ hh⟩
  have hBlocksIn {n k : ℕ} (hn : n ≤ cutoff k) : F.blocks n ⊆ D k := fun g hg ↦
    hSeedD k (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨n,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hn), hg⟩))
  have hExhaust (g : G) : ∃ k, g ∈ D k := by
    obtain ⟨k, rfl⟩ := he g
    exact ⟨k, hSeedD k (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩))⟩
  let level (g : G) := Nat.find (hExhaust g)
  have hLevelMem (g : G) : g ∈ D (level g) := Nat.find_spec (hExhaust g)
  have hLevelLe {g : G} {k : ℕ} (h : g ∈ D k) : level g ≤ k := Nat.find_min' (hExhaust g) h
  have hSameLevel (g h : G) (hh : h ∈ (P (level g)).cell g) : level h = level g := by
    have hle : level h ≤ level g :=
      hLevelLe (hDClose (hLevelMem g) (hP (level g) g hh))
    apply Nat.le_antisymm hle
    by_contra hng
    have hlt : level h < level g := Nat.lt_of_not_ge hng
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hlt)
    rw [hk] at hh hlt
    have hg : g ∈ (P (k + 1)).cell h := by
      rw [(P (k + 1)).cell_eq hh]
      exact (P (k + 1)).mem_cell g
    have hhD : h ∈ D k := hDMono (Nat.le_of_lt_succ hlt) (hLevelMem h)
    have hgLe := hLevelLe (hDClose hhD hg)
    omega
  let T (g : G) := (P (level g)).cell g
  have hBound {n k : ℕ} (hn : n ≤ cutoff k) :
      tileBoundary T (F.blocks n) ⊆ leftBoundary (moves k) (F.blocks n) := by
    intro g hg
    obtain ⟨hg, hNot⟩ := Finset.mem_filter.mp hg
    obtain ⟨h, hh, hhNot⟩ := Finset.not_subset.mp hNot
    have hk : level g ≤ k := hLevelLe (hBlocksIn hn hg)
    have hMove := (P (level g)).mem_displacements hh
    exact mem_leftBoundary.mpr ⟨hg, h * g⁻¹, Finset.mem_biUnion.mpr
      ⟨level g, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hMove⟩, by simpa using hhNot⟩
  have hIndex {J n : ℕ} (hn : cutoff J < n) :
      ∃ j, J ≤ j ∧ n ≤ cutoff (j+1) ∧ cutoff j < n := by
    have hex : ∃ k, n ≤ cutoff k := ⟨n, hCutLarge n⟩
    let dec : DecidablePred (fun a ↦ n ≤ cutoff a) := fun a ↦ Nat.decLe n (cutoff a)
    let k := @Nat.find _ dec hex
    have hk : n ≤ cutoff k := @Nat.find_spec _ dec hex
    have hJk : J < k := Nat.lt_of_not_ge (fun h ↦ hn.not_ge (hk.trans (hCutMono h)))
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hJk)
    have hnj : cutoff j < n := Nat.lt_of_not_ge
      (@Nat.find_min _ dec hex j (by omega : j < k))
    exact ⟨j,by omega,by rw [show j+1 = k from hj.symm]; exact hk,hnj⟩
  refine ⟨level, hSameLevel, fun k ↦ (D k).finite_toSet.subset ?_, ?_, ?_⟩
  · exact fun g hg ↦ hDMono hg (hLevelMem g)
  · apply Metric.tendsto_nhds.2
    intro δ hδ
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hεlim.eventually_lt_const hδ)
    filter_upwards [eventually_ge_atTop (cutoff J + 1)] with n hn
    obtain ⟨j,hj,hk,hnj⟩ := hIndex (by omega : cutoff J < n)
    have hSmall := (hN j n ((hCut j).trans hnj.le)).1
    have hCompare : ((tileBoundary T (F.blocks n)).card : ℝ) / (F.blocks n).card ≤
        ((leftBoundary (moves (j + 1)) (F.blocks n)).card : ℝ) / (F.blocks n).card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (hBound hk)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    exact hCompare.trans_lt (hSmall.trans (hJ j hj))
  · apply Metric.tendsto_nhds.2
    intro r hr
    obtain ⟨J,hJ⟩ := ((_root_.tendsto_sum_nat_add δs).eventually_lt_const (half_pos hr)).exists
    have hSize : Tendsto (fun n ↦ ((F.blocks n).card : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp F.tendsto_card
    have hSmallD : Tendsto (fun n ↦ ((D J).card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := by
      simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using
        (tendsto_inv_atTop_zero.comp hSize).const_mul ((D J).card : ℝ)
    filter_upwards [eventually_ge_atTop (cutoff J+1), hSmallD.eventually_lt_const (half_pos hr)] with n hn hnD
    obtain ⟨j,hj,hk,hnj⟩ := hIndex (by omega : cutoff J < n)
    let A := F.blocks n
    let I := Finset.range (j+2-J)
    let B (l : ℕ) := A.filter (· ∈ bad (l+J))
    have hSub : A.filter (fun g ↦ g ∈ bad (level g)) ⊆ D J ∪ I.biUnion B := by
      intro g hg
      obtain ⟨hgn,hgb⟩ := Finset.mem_filter.mp hg
      by_cases hle : level g ≤ J
      · exact Finset.mem_union_left _ (hDMono hle (hLevelMem g))
      · have hUpper := hLevelLe (hBlocksIn (k := j+1) hk hgn)
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨level g-J,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨hgn,?_⟩⟩)
        simpa only [Nat.sub_add_cancel (by omega : J ≤ level g)] using hgb
    have hSumI : (∑ l ∈ I, ((B l).card : ℝ) / A.card) ≤ ∑ l ∈ I, δs (l+J) := by
      apply Finset.sum_le_sum
      intro l hl
      have hL : l+J ∈ Finset.range (j+2) := Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hl
        omega)
      exact (hN j n ((hCut j).trans hnj.le)).2 _ hL
    have hTail : (∑ l ∈ I, δs (l+J)) ≤ ∑' l, δs (l+J) :=
      ((summable_nat_add_iff J).mpr hSum).sum_le_tsum I (fun l _ ↦ hδs (l+J))
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by unfold blockProportion; positivity),blockProportion]
    change (((A.filter (fun g ↦ g ∈ bad (level g))).card : ℝ) / A.card) < r
    calc
      _ ≤ (((D J).card : ℝ) + ∑ l ∈ I, ((B l).card : ℝ)) / A.card := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_card hSub).trans
          (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left Finset.card_biUnion_le _))
      _ = _ := by rw [add_div, Finset.sum_div]
      _ < r := by
        change ((D J).card : ℝ) / A.card + ∑ l ∈ I, ((B l).card : ℝ) / A.card < r
        linarith [hSumI,hTail]

omit [Group G] in
private theorem norm_finiteAverage_le_sparse {A B : Finset G} (hA : A.Nonempty)
    {f : G → ℝ} {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hBound : ∀ g ∈ A, ‖f g‖ ≤ c) (hSparse : ∀ g ∈ A, g ∉ B → ‖f g‖ ≤ d) :
    ‖finiteAverage A f‖ ≤ ((B.card : ℝ) / A.card) * c + d := by
  have hSize : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hsum : ‖∑ g ∈ A, f g‖ ≤ (B.card : ℝ) * c + A.card * d := by
    calc
      _ ≤ ∑ g ∈ A, ‖f g‖ := norm_sum_le _ _
      _ ≤ ∑ g ∈ A, ((if g ∈ B then c else 0) + d) := by
        apply Finset.sum_le_sum
        intro g hg
        split_ifs with h
        · exact (hBound g hg).trans (le_add_of_nonneg_right hd)
        · simpa only [zero_add] using hSparse g hg h
      _ = ((A.filter (· ∈ B)).card : ℝ) * c + A.card * d := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_right ?_ hc) (le_refl _)
        exact_mod_cast Finset.card_le_card fun g hg ↦ (Finset.mem_filter.mp hg).2
  simp only [finiteAverage, smul_eq_mul, norm_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr hSize.le)]
  calc
    _ ≤ (A.card : ℝ)⁻¹ * ((B.card : ℝ) * c + A.card * d) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hSize.le)
    _ = _ := by field_simp

omit [Group G] [DecidableEq G] in
private theorem finiteAverage_sub (A : Finset G) (f q : G → ℝ) :
    finiteAverage A (fun g ↦ f g - q g) = finiteAverage A f - finiteAverage A q := by
  simp [finiteAverage, Finset.sum_sub_distrib, mul_sub]

omit [Group G] in
private theorem sum_cell_averages (A : Finset G) (T : G → Finset G) (f : G → ℝ)
    (hMem : ∀ g, g ∈ T g) (hEq : ∀ {g h}, h ∈ T g → T h = T g)
    (hClosed : ∀ g ∈ A, T g ⊆ A) :
    ∑ g ∈ A, finiteAverage (T g) f = ∑ h ∈ A, f h := by
  have hFilter (g : G) (hg : g ∈ A) : A.filter (· ∈ T g) = T g := by
    ext h
    exact Finset.mem_filter.trans ⟨And.right, fun hh ↦ ⟨hClosed g hg hh, hh⟩⟩
  calc
    _ = ∑ g ∈ A, ∑ h ∈ A, if h ∈ T g then ((T g).card : ℝ)⁻¹ * f h else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← Finset.sum_filter, hFilter g hg, ← Finset.mul_sum]
      rfl
    _ = ∑ h ∈ A, ∑ g ∈ A, if h ∈ T g then ((T g).card : ℝ)⁻¹ * f h else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [← Finset.sum_filter]
      have hFilter' : A.filter (fun g ↦ h ∈ T g) = T h := by
        ext g
        rw [Finset.mem_filter]
        refine ⟨fun ⟨_, hg⟩ ↦ ?_, fun hg ↦ ⟨hClosed h hh hg, ?_⟩⟩
        · rw [hEq hg]
          exact hMem g
        · rw [hEq hg]
          exact hMem h
      rw [hFilter']
      have hSize : (T h).card ≠ 0 := Finset.Nonempty.card_ne_zero ⟨h, hMem h⟩
      calc
        _ = ∑ g ∈ T h, ((T h).card : ℝ)⁻¹ * f h := by
          exact Finset.sum_congr rfl fun g hg ↦ by rw [hEq hg]
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          field_simp

/-- Glue the supplied finite-tile approximations into one configuration. Each centered
test depends on finitely many translate coordinates. The conclusion uses every block
of the prescribed Følner sequence. -/
theorem exists_tendsto_finiteTimeTests_of_tiledApproximations [Countable G] [Infinite G]
    {K : Type*} (F : LeftFolnerSequence G) (P : ℕ → BoundedTilePartition G)
    (hP : ∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g)
    (badCell : ℕ → Set G)
    (hBadCell : ∀ k g h, h ∈ (P k).cell g → (h ∈ badCell k ↔ g ∈ badCell k))
    (δs : ℕ → ℝ) (hδs : ∀ k, 0 ≤ δs k) (hSum : Summable δs)
    (hSparse : ∀ k, ∀ᶠ n in atTop, blockProportion (F.blocks n) (badCell k) ≤ δs k)
    (support : ℕ → Finset G) (q : ℕ → (G → K) → G → ℝ) (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hNorm : ∀ i x g, ‖q i x g‖ ≤ C i)
    (hLocal : ∀ i x y g, (∀ a ∈ support i, x (a * g) = y (a * g)) → q i x g = q i y g)
    (sample : ℕ → Finset G → G → K)
    (hApprox : ∀ k g i, i ≤ k → g ∉ badCell k →
      ‖finiteAverage ((P k).cell g) (q i (sample k ((P k).cell g)))‖ ≤ 1 / ((k : ℝ) + 1))
    (hSmallBoundary : ∀ k g i, i ≤ k → g ∉ badCell k →
      ((leftBoundary (support i) ((P k).cell g)).card : ℝ) / ((P k).cell g).card ≤
        1 / ((k : ℝ) + 1)) :
    ∃ x : G → K, ∀ i, Tendsto (fun n ↦ finiteAverage (F.blocks n) (q i x)) atTop (𝓝 0) := by
  classical
  obtain ⟨level, hLevel, hFinite, hBoundary, hBad⟩ :=
    exists_mixedTilePartition F P hP badCell δs hδs hSum hSparse
  let T (g : G) := (P (level g)).cell g
  let x (g : G) := sample (level g) (T g) g
  have hMem (g : G) : g ∈ T g := (P (level g)).mem_cell g
  have hEq {g h : G} (hh : h ∈ T g) : T h = T g := by
    simp only [T, hLevel g h hh]
    exact (P (level g)).cell_eq hh
  have hSample {g h : G} (hh : h ∈ T g) : x h = sample (level g) (T g) h := by
    rw [show x h = sample (level h) (T h) h from rfl, hEq hh, hLevel g h hh]
  have hTile (i : ℕ) (g : G) (hi : i ≤ level g) (hg : g ∉ badCell (level g)) :
      ‖finiteAverage (T g) (q i x)‖ ≤ (2 * C i + 1) * (1 / ((level g : ℝ) + 1)) := by
    let y := sample (level g) (T g)
    let A := T g
    let B := leftBoundary (support i) A
    have hc : 0 ≤ 2 * C i := mul_nonneg (by norm_num) (hC i)
    have hDiff : ‖finiteAverage A (q i x) - finiteAverage A (q i y)‖ ≤
        ((B.card : ℝ) / A.card) * (2 * C i) := by
      rw [← finiteAverage_sub]
      have h := norm_finiteAverage_le_sparse (A := A) (B := B) (f := fun z ↦ q i x z - q i y z)
        ⟨g, hMem g⟩ hc (le_refl 0)
      rw [add_zero] at h
      apply h
      · intro z _
        calc
          _ ≤ ‖q i x z‖ + ‖q i y z‖ := norm_sub_le _ _
          _ ≤ 2 * C i := by linarith [hNorm i x z, hNorm i y z]
      · intro z hz hzB
        have heq : q i x z = q i y z := by
          apply hLocal
          intro a ha
          apply hSample
          by_contra hn
          exact hzB (mem_leftBoundary.mpr ⟨hz, a, ha, hn⟩)
        simp [heq]
    calc
      _ = ‖(finiteAverage A (q i x) - finiteAverage A (q i y)) +
          finiteAverage A (q i y)‖ := by rw [sub_add_cancel]
      _ ≤ ‖finiteAverage A (q i x) - finiteAverage A (q i y)‖ +
          ‖finiteAverage A (q i y)‖ := norm_add_le _ _
      _ ≤ ((B.card : ℝ) / A.card) * (2 * C i) + 1 / ((level g : ℝ) + 1) :=
        add_le_add hDiff (hApprox (level g) g i hi hg)
      _ ≤ (1 / ((level g : ℝ) + 1)) * (2 * C i) + 1 / ((level g : ℝ) + 1) :=
        add_le_add (mul_le_mul_of_nonneg_right (hSmallBoundary (level g) g i hi hg) hc) (le_refl _)
      _ = _ := by ring
  refine ⟨x, fun i ↦ Metric.tendsto_nhds.2 ?_⟩
  intro δ hδ
  have hlim : Tendsto (fun k : ℕ ↦ (2 * C i + 1) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C i + 1)
  obtain ⟨j, hj⟩ := eventually_atTop.1 (hlim.eventually_lt_const (half_pos hδ))
  let J := max i j
  let E := (hFinite J).toFinset
  let B (n : ℕ) := (F.blocks n).filter (fun g ↦ g ∈ badCell (level g))
  let bad (n : ℕ) := tileBoundary T (F.blocks n) ∪ E ∪ B n
  let good (n : ℕ) := F.blocks n \ bad n
  have hGood (n : ℕ) {g : G} (hg : g ∈ good n) :
      J < level g ∧ T g ⊆ F.blocks n ∧ g ∉ badCell (level g) := by
    obtain ⟨hgA, hgBad⟩ := Finset.mem_sdiff.mp hg
    refine ⟨Nat.lt_of_not_ge (fun h ↦ hgBad (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))), ?_, ?_⟩
    · exact (Set.Finite.mem_toFinset (hFinite J)).mpr h
    · by_contra hn
      exact hgBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgA, hn⟩)))
    · intro hb
      exact hgBad (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hgA,hb⟩))
  have hClosed (n : ℕ) (g : G) (hg : g ∈ good n) : T g ⊆ good n := by
    intro h hh
    have hgGood := hGood n hg
    refine Finset.mem_sdiff.mpr ⟨hgGood.2.1 hh, fun hBad ↦ ?_⟩
    rcases Finset.mem_union.mp hBad with hBE | hB
    · rcases Finset.mem_union.mp hBE with hBoundary | hE
      · exact (Finset.mem_filter.mp hBoundary).2 ((hEq hh).symm ▸ hgGood.2.1)
      · have hle : level h ≤ J := (Set.Finite.mem_toFinset (hFinite J)).mp hE
        exact hgGood.1.not_ge ((hLevel g h hh) ▸ hle)
    · apply hgGood.2.2
      apply (hBadCell (level g) g h hh).mp
      exact (hLevel g h hh) ▸ (Finset.mem_filter.mp hB).2
  let mixed (n : ℕ) (g : G) : ℝ :=
    if g ∈ good n then finiteAverage (T g) (q i x) else q i x g
  have hAverage (n : ℕ) : finiteAverage (F.blocks n) (mixed n) =
      finiteAverage (F.blocks n) (q i x) := by
    simp only [finiteAverage]
    congr 1
    have hsub : good n ⊆ F.blocks n := Finset.sdiff_subset
    rw [← Finset.sum_sdiff (f := mixed n) hsub, ← Finset.sum_sdiff (f := q i x) hsub]
    congr 1
    · apply Finset.sum_congr rfl
      intro g hg
      simp [mixed, (Finset.mem_sdiff.mp hg).2]
    · calc
        _ = ∑ g ∈ good n, finiteAverage (T g) (q i x) :=
          Finset.sum_congr rfl fun g hg ↦ by simp [mixed, hg]
        _ = _ := sum_cell_averages (good n) T (q i x) hMem (fun hg ↦ hEq hg) (hClosed n)
  have hSize : Tendsto (fun n ↦ ((F.blocks n).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.tendsto_card
  have hEden : Tendsto (fun n ↦ (E.card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hSize).const_mul (E.card : ℝ)
  have hBadDen : Tendsto (fun n ↦ ((bad n).card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := by
    have hBd : Tendsto (fun n ↦ ((B n).card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := hBad
    have hBound := (hBoundary.add hEden).add hBd
    simp only [zero_add] at hBound
    apply squeeze_zero (fun _ ↦ by positivity) _ hBound
    intro n
    rw [← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hSmall := hBadDen.mul_const (C i)
  rw [zero_mul] at hSmall
  filter_upwards [hSmall.eventually_lt_const (half_pos hδ)] with n hn
  have hGoodNorm {g : G} (hg : g ∈ good n) : ‖mixed n g‖ < δ / 2 := by
    simp only [mixed, hg, ite_true]
    have hlg := (hGood n hg).1
    exact (hTile i g ((le_max_left i j).trans hlg.le) (hGood n hg).2.2).trans_lt
      (hj (level g) ((le_max_right i j).trans hlg.le))
  have hMixed (g : G) (_hg : g ∈ F.blocks n) : ‖mixed n g‖ ≤ C i := by
    by_cases h : g ∈ good n
    · simp only [mixed, h, ite_true]
      simpa only [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul, zero_add] using
        norm_finiteAverage_le_sparse (A := T g) (B := ∅) ⟨g, hMem g⟩ (hC i) (hC i)
          (fun z _ ↦ hNorm i x z) (fun z _ _ ↦ hNorm i x z)
    · simp only [mixed, h, ite_false]
      exact hNorm i x g
  rw [dist_zero_right, ← hAverage n]
  have hBound := norm_finiteAverage_le_sparse (F.nonempty n) (B := bad n)
    (hC i) (half_pos hδ).le hMixed
    (fun g hg hbad ↦ (hGoodNorm (Finset.mem_sdiff.mpr ⟨hg, hbad⟩)).le)
  exact hBound.trans_lt (by linarith)

end SixProblems
