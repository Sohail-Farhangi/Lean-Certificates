/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section
noncomputable section

namespace Mixing

open Filter Function Metric Set TopologicalSpace
open scoped Classical Topology

section Construction

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompactSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]

local instance : MeasurableSpace (List ℕ) := ⊤

local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

private def selectionRadius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

private def selectionCell (d : ℕ → X) : List ℕ → Set X
  | [] => univ
  | i :: l => selectionCell d l ∩ closedBall (d i) (selectionRadius l.length)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
private theorem isClosed_selectionCell (d : ℕ → X) (l : List ℕ) :
    IsClosed (selectionCell d l) := by
  induction l with
  | nil => exact isClosed_univ
  | cons i l ih => exact ih.inter isClosed_closedBall

omit [TopologicalSpace Y] [T2Space Y] [BorelSpace Y] in
private theorem measurable_find_cover (U : ℕ → Set Y) (hU : ∀ i, MeasurableSet (U i))
    (hCover : ∀ y, ∃ i, y ∈ U i) : Measurable (fun y => Nat.find (hCover y)) := by
  classical
  apply measurable_to_countable'
  intro i
  have he : (fun y => Nat.find (hCover y)) ⁻¹' {i} =
      U i ∩ ⋂ j : {j : ℕ // j < i}, (U j)ᶜ := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Nat.find_eq_iff, mem_inter_iff, mem_iInter,
      mem_compl_iff, Subtype.forall]
  rw [he]
  exact (hU i).inter (MeasurableSet.iInter fun j => (hU j).compl)

private structure SelectionStage (f : X → Y) (d : ℕ → X) (n : ℕ) where
  indices : Y → List ℕ
  measurable_indices : Measurable indices
  length_indices : ∀ y, (indices y).length = n
  intersects_fibre : ∀ y, y ∈ f '' selectionCell d (indices y)

private def selectionStep {f : X → Y} (hf : Continuous f) {d : ℕ → X} (hd : DenseRange d)
    {n : ℕ} (prev : SelectionStage f d n) : SelectionStage f d (n + 1) := by
  classical
  let U (i : ℕ) : Set Y := {y | y ∈ f '' selectionCell d (i :: prev.indices y)}
  have hU (i : ℕ) : MeasurableSet (U i) := by
    have he : U i = ⋃ l : List ℕ, (prev.indices ⁻¹' {l}) ∩ f '' selectionCell d (i :: l) := by
      ext y
      simp only [U, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun hy => ⟨_, rfl, hy⟩, fun ⟨l, hl, hy⟩ => hl.symm ▸ hy⟩
    rw [he]
    exact MeasurableSet.iUnion fun l => (prev.measurable_indices (measurableSet_singleton l)).inter
      (((isClosed_selectionCell d (i :: l)).isCompact.image hf).isClosed.measurableSet)
  have hCover (y : Y) : ∃ i, y ∈ U i := by
    obtain ⟨x, hx, hxy⟩ := prev.intersects_fibre y
    have hr : 0 < selectionRadius (prev.indices y).length := by simp [selectionRadius]
    obtain ⟨i, hi⟩ := hd.exists_dist_lt x hr
    exact ⟨i, x, ⟨hx, hi.le⟩, hxy⟩
  let next (y : Y) := Nat.find (hCover y)
  have hNext : Measurable next := measurable_find_cover U hU hCover
  refine ⟨fun y => next y :: prev.indices y, ?_, ?_, ?_⟩
  · exact (measurable_of_countable (fun z : ℕ × List ℕ => z.1 :: z.2)).comp
      (hNext.prodMk prev.measurable_indices)
  · intro y
    simp only [List.length_cons, prev.length_indices]
  · exact fun y => Nat.find_spec (hCover y)

private def selectionStage {f : X → Y} (hf : Continuous f) (hsurj : Surjective f)
    {d : ℕ → X} (hd : DenseRange d) : (n : ℕ) → SelectionStage f d n
  | 0 =>
    ⟨fun _ => [], measurable_const, fun _ => rfl, fun y =>
      let ⟨x, hxy⟩ := hsurj y
      ⟨x, mem_univ _, hxy⟩⟩
  | n + 1 => selectionStep hf hd (selectionStage hf hsurj hd n)

omit [MeasurableSpace X] [BorelSpace X] in
private theorem selectionStage_subset {f : X → Y} (hf : Continuous f) (hsurj : Surjective f)
    {d : ℕ → X} (hd : DenseRange d) (n : ℕ) (y : Y) :
    selectionCell d ((selectionStage hf hsurj hd (n + 1)).indices y) ⊆
      selectionCell d ((selectionStage hf hsurj hd n).indices y) := by
  rw [selectionStage]
  exact inter_subset_left

omit [MeasurableSpace X] [BorelSpace X] in
private theorem selectionStage_dist {f : X → Y} (hf : Continuous f) (hsurj : Surjective f)
    {d : ℕ → X} (hd : DenseRange d) (n : ℕ) (y : Y) {x : X}
    (hx : x ∈ selectionCell d ((selectionStage hf hsurj hd (n + 1)).indices y)) :
    dist (d (((selectionStage hf hsurj hd (n + 1)).indices y).headD 0)) x ≤ selectionRadius n := by
  rw [selectionStage] at hx ⊢
  rw [dist_comm]
  calc
    _ ≤ selectionRadius (((selectionStage hf hsurj hd n).indices y).length) := hx.2
    _ = selectionRadius n := congrArg selectionRadius ((selectionStage hf hsurj hd n).length_indices y)

/-- A continuous surjection from a compact metric space to a Hausdorff space
has a Borel-measurable section. Successively chosen closed balls have radii
tending to zero and each finite intersection meets the corresponding fibre. -/
theorem exists_measurable_section_of_continuous_compact
    (f : X → Y) (hf : Continuous f) (hsurj : Surjective f) :
    ∃ s : Y → X, Measurable s ∧ RightInverse s f := by
  classical
  by_cases hX : Nonempty X
  · let d := denseSeq X
    have hd : DenseRange d := denseRange_denseSeq X
    let C (y : Y) (n : ℕ) := selectionCell d ((selectionStage hf hsurj hd n).indices y) ∩
      f ⁻¹' {y}
    have hClosed (y : Y) (n : ℕ) : IsClosed (C y n) :=
      (isClosed_selectionCell d _).inter (isClosed_singleton.preimage hf)
    have hLim (y : Y) : (⋂ n, C y n).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ _ _
        ((hClosed y 0).isCompact) (hClosed y)
      · exact fun n => inter_subset_inter_left _ (selectionStage_subset hf hsurj hd n y)
      · intro n
        obtain ⟨x, hx, hxy⟩ := (selectionStage hf hsurj hd n).intersects_fibre y
        exact ⟨x, hx, hxy⟩
    choose s hs using hLim
    have hRight : RightInverse s f := fun y => (mem_iInter.mp (hs y) 0).2
    refine ⟨s, ?_, hRight⟩
    let center (n : ℕ) (y : Y) := d (((selectionStage hf hsurj hd (n + 1)).indices y).headD 0)
    apply measurable_of_tendsto_metrizable (f := center)
    · intro n
      exact (measurable_of_countable (fun l : List ℕ => d (l.headD 0))).comp
        (selectionStage hf hsurj hd (n + 1)).measurable_indices
    · apply tendsto_pi_nhds.2
      intro y
      apply tendsto_iff_dist_tendsto_zero.2
      refine squeeze_zero (g := selectionRadius) (fun _ => dist_nonneg) ?_ ?_
      · intro n
        exact selectionStage_dist hf hsurj hd n y (mem_iInter.mp (hs y) (n + 1)).1
      · exact tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  · have hY : IsEmpty Y := ⟨fun y => let ⟨x, _⟩ := hsurj y; hX ⟨x⟩⟩
    exact ⟨isEmptyElim, measurable_of_empty _, fun y => isEmptyElim y⟩

end Construction

section CountableCompactCover

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]

/-- A continuous surjection from a σ-compact metric space to a Hausdorff space
has a Borel-measurable section. Each point is assigned the compact section for
the first compact piece whose image contains it. -/
theorem exists_measurable_section_of_continuous_sigmaCompact
    [SigmaCompactSpace X] (f : X → Y) (hf : Continuous f) (hsurj : Surjective f) :
    ∃ s : Y → X, Measurable s ∧ RightInverse s f := by
  classical
  let C := compactCovering X
  let U (i : ℕ) := f '' C i
  have hU (i : ℕ) : MeasurableSet (U i) :=
    ((isCompact_compactCovering X i).image hf).isClosed.measurableSet
  have hCover (y : Y) : ∃ i, y ∈ U i := by
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨i, hi⟩ := exists_mem_compactCovering x
    exact ⟨i, x, hi, rfl⟩
  let g (i : ℕ) (x : C i) : U i := ⟨f x, x, x.property, rfl⟩
  have hsection (i : ℕ) : ∃ s : U i → C i, Measurable s ∧ RightInverse s (g i) := by
    let : CompactSpace (C i) := isCompact_iff_compactSpace.1 (isCompact_compactCovering X i)
    have hg : Continuous (g i) :=
      (hf.comp continuous_subtype_val).subtype_mk _
    refine exists_measurable_section_of_continuous_compact (g i) hg ?_
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  choose s hsMeas hsRight using hsection
  let index (y : Y) := Nat.find (hCover y)
  have hIndex : Measurable index := measurable_find_cover U hU hCover
  let t (y : Y) : X := s (index y) ⟨y, Nat.find_spec (hCover y)⟩
  refine ⟨t, ?_, fun y => congrArg Subtype.val (hsRight (index y) ⟨y, Nat.find_spec (hCover y)⟩)⟩
  intro A hA
  have he : t ⁻¹' A =
      ⋃ i : ℕ, (index ⁻¹' {i}) ∩
        Subtype.val '' ((fun z : U i => (s i z : X)) ⁻¹' A) := by
    ext y
    constructor
    · intro hy
      exact mem_iUnion.mpr ⟨index y, rfl, ⟨⟨y, Nat.find_spec (hCover y)⟩, hy, rfl⟩⟩
    · intro hy
      obtain ⟨i, hi, z, hz, hzy⟩ := mem_iUnion.mp hy
      have hi' : index y = i := hi
      subst i
      have hz' : z = (⟨y, Nat.find_spec (hCover y)⟩ : U (index y)) := Subtype.ext hzy
      subst z
      exact hz
  rw [he]
  exact MeasurableSet.iUnion fun i => (hIndex (measurableSet_singleton i)).inter
    ((MeasurableEmbedding.subtype_coe (hU i)).measurableSet_image.2
      ((measurable_subtype_coe.comp (hsMeas i)) hA))

end CountableCompactCover

end Mixing
