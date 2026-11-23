/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The row net of Example 4.5

The semigroup is `ℤ × ℕ` with ordinary addition in the first coordinate and
maximum in the second. The row at `(L,n)` is `[1,L] × {n}`.
-/

@[expose] public section

namespace JdLG.PaperExamplesRows

open Filter
open scoped Topology

/-- A point in the commutative semigroup of Example 4.5. -/
structure Point where
  first : ℤ
  level : ℕ
  deriving DecidableEq

@[ext] theorem Point.ext {a b : Point} (hfirst : a.first = b.first) (hlevel : a.level = b.level) :
    a = b := by
  cases a
  cases b
  simp_all

instance : Zero Point := ⟨⟨0, 0⟩⟩

instance : Add Point := ⟨fun a b ↦ ⟨a.first + b.first, max a.level b.level⟩⟩

instance : AddCommMonoid Point where
  add_assoc a b c := Point.ext (add_assoc _ _ _) (max_assoc _ _ _)
  zero_add a := Point.ext (zero_add _) (zero_max _)
  add_zero a := Point.ext (add_zero _) (max_zero _)
  add_comm a b := Point.ext (add_comm _ _) (max_comm _ _)
  nsmul := nsmulRec

@[simp] theorem first_add (a b : Point) : (a + b).first = a.first + b.first := rfl

@[simp] theorem level_add (a b : Point) : (a + b).level = max a.level b.level := rfl

/-- Embed a horizontal coordinate in a single row. -/
def rowEmbedding (level : ℕ) : ℤ ↪ Point where
  toFun z := ⟨z, level⟩
  inj' _ _ h := congrArg Point.first h

/-- The net of finite rows; rows of length zero are harmless at the tail. -/
def row (L n : ℕ) : Finset Point := (Finset.Icc 1 (L : ℤ)).map (rowEmbedding n)

theorem mem_row_iff (L n : ℕ) (s : Point) :
    s ∈ row L n ↔ 1 ≤ s.first ∧ s.first ≤ (L : ℤ) ∧ s.level = n := by
  simp only [row, Finset.mem_map, Finset.mem_Icc]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1, ha.2, rfl⟩
  · rintro ⟨ha, hb, hc⟩
    exact ⟨s.first, ⟨ha, hb⟩, Point.ext rfl hc.symm⟩

@[simp] theorem row_card (L n : ℕ) : (row L n).card = L := by
  rw [row, Finset.card_map, Int.card_Icc]
  simp

/-- The translate of one row by a fixed point; the row height is their maximum. -/
def translateRow (s : Point) (L n : ℕ) : Finset Point := (row L n).image (s + ·)

theorem mem_translateRow_iff (s x : Point) (L n : ℕ) :
    x ∈ translateRow s L n ↔
      1 + s.first ≤ x.first ∧ x.first ≤ L + s.first ∧ x.level = max s.level n := by
  simp only [translateRow, Finset.mem_image, mem_row_iff]
  constructor
  · rintro ⟨u, ⟨hu, hu', he⟩, rfl⟩
    simp only [first_add, level_add]
    exact ⟨by omega, by omega, congrArg (max s.level) he⟩
  · rintro ⟨ha, hb, hc⟩
    refine ⟨⟨x.first - s.first, n⟩, ⟨?_, ?_, rfl⟩, Point.ext ?_ hc.symm⟩
    · change 1 ≤ x.first - s.first
      omega
    · change x.first - s.first ≤ (L : ℤ)
      omega
    · change s.first + (x.first - s.first) = x.first
      omega

theorem translateRow_card (s : Point) (L n : ℕ) : (translateRow s L n).card = L := by
  unfold translateRow
  rw [Finset.card_image_of_injOn (fun a ha b hb h ↦ ?_), row_card]
  have hh : a.first = b.first := add_left_cancel (congrArg Point.first h)
  have ha' := ((mem_row_iff _ _ _).1 ha).2.2
  have hb' := ((mem_row_iff _ _ _).1 hb).2.2
  exact Point.ext hh (ha'.trans hb'.symm)

theorem row_overlap_lower_bound (s : Point) {L n : ℕ} (hn : s.level ≤ n) :
    L - s.first.natAbs ≤ ((row L n) ∩ (translateRow s L n)).card := by
  let inside := (Finset.Icc (max 1 (1 + s.first)) (min (L : ℤ) (L + s.first))).map
    (rowEmbedding n)
  have hsubset : inside ⊆ (row L n) ∩ (translateRow s L n) := by
    intro x hx
    rcases Finset.mem_map.1 hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_Icc.1 ha with ⟨ha₁, ha₂⟩
    refine Finset.mem_inter.2 ⟨(mem_row_iff _ _ _).2 ?_, (mem_translateRow_iff _ _ _ _).2 ?_⟩
    · exact ⟨(le_max_left _ _).trans ha₁, ha₂.trans (min_le_left _ _), rfl⟩
    · exact ⟨(le_max_right _ _).trans ha₁, ha₂.trans (min_le_right _ _),
        (max_eq_right hn).symm⟩
  apply le_trans ?_ (Finset.card_mono hsubset)
  simp only [inside, Finset.card_map, Int.card_Icc]
  by_cases h : 0 ≤ s.first
  · rw [max_eq_right (by omega), min_eq_left (by omega)]
    omega
  · rw [max_eq_left (by omega), min_eq_right (by omega)]
    omega

theorem row_deficit_le (s : Point) {L n : ℕ} (hn : s.level ≤ n) :
    (row L n \ translateRow s L n).card ≤ s.first.natAbs := by
  rw [Finset.card_sdiff, Finset.inter_comm, row_card]
  have h := row_overlap_lower_bound s (L := L) hn
  omega

/-- Example 4.5's rows satisfy the strong left Følner condition for counting
measure. Both sides of the symmetric difference have equal cardinality. -/
theorem row_folner_deficit (s : Point) :
    Tendsto (fun k : ℕ × ℕ ↦ ((row k.1 k.2 \ translateRow s k.1 k.2).card : ℝ) /
      (row k.1 k.2).card) atTop (𝓝 0) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    refine tendsto_atTop.2 fun n ↦ ?_
    exact eventually_atTop.2 ⟨(n, 0), fun _ hk ↦ hk.1⟩
  have hu := (tendsto_const_div_atTop_nhds_zero_nat (s.first.natAbs : ℝ)).comp hfst
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · exact Eventually.of_forall fun k ↦ div_nonneg (by positivity) (by positivity)
  · refine eventually_atTop.2 ⟨(0, s.level), fun k hk ↦ ?_⟩
    rw [row_card]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast row_deficit_le s (L := k.1) hk.2

open Classical in
/-- The counting density in a finite row. -/
noncomputable def rowDensity (A : Set Point) (k : ℕ × ℕ) : ℝ :=
  ((row k.1 k.2).filter fun x ↦ x ∈ A).card / (row k.1 k.2).card

/-- If every vertical fiber of `A` is finite, then there are rows arbitrarily
far out in the directed net that miss `A` entirely. -/
theorem exists_row_miss_of_finite_fibers (A : Set Point)
    (h : ∀ a : ℤ, {p ∈ A | p.first = a}.Finite) (L n₀ : ℕ) :
    ∃ n ≥ n₀, ∀ s ∈ row L n, s ∉ A := by
  classical
  let bad (a : ℤ) := ((h a).image Point.level).toFinset
  let forbidden := (Finset.Icc 1 (L : ℤ)).biUnion bad
  obtain ⟨b, hb⟩ := forbidden.finite_toSet.bddAbove
  let n := max n₀ (b + 1)
  refine ⟨n, le_max_left _ _, fun s hs hA ↦ ?_⟩
  obtain ⟨ha, ha', hn⟩ := (mem_row_iff _ _ _).1 hs
  have hm : n ∈ forbidden := by
    apply Finset.mem_biUnion.2
    refine ⟨s.first, Finset.mem_Icc.2 ⟨ha, ha'⟩, ?_⟩
    exact (((h s.first).image Point.level).mem_toFinset).2 ⟨s, ⟨hA, rfl⟩, hn⟩
  have hle : n ≤ b := hb hm
  have hgt : b + 1 ≤ n := le_max_right _ _
  omega

/-- A set with finite vertical fibers cannot have density one along the row net. -/
theorem no_density_one_of_finite_fibers (A : Set Point)
    (h : ∀ a : ℤ, {p ∈ A | p.first = a}.Finite) :
    ¬ Tendsto (rowDensity A) atTop (𝓝 1) := by
  intro hlim
  have he := (tendsto_order.1 hlim).1 (1 / 2 : ℝ) (by norm_num)
  obtain ⟨⟨L, n₀⟩, htail⟩ := eventually_atTop.1 he
  obtain ⟨n, hn, hmiss⟩ := exists_row_miss_of_finite_fibers A h L n₀
  have hlt := htail (L, n) (show (L, n₀) ≤ (L, n) from ⟨le_rfl, hn⟩)
  classical
  have hempty : ((row L n).filter fun x ↦ x ∈ A) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    exact fun x hx ↦ hmiss x (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx).2
  change 1 / 2 < (((row L n).filter fun x ↦ x ∈ A).card : ℝ) / (row L n).card at hlt
  norm_num [hempty] at hlt

end JdLG.PaperExamplesRows
