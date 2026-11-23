/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Prod

/-!
# A left Følner sequence for the parity semigroup

The rectangles have even first coordinate below twice the width and have
heights from two to one more than the number of rows. Exponential growth
of the width absorbs the shear in left multiplication.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

open Filter
open scoped Topology

/-- Place a rectangle in the even principal left ideal. -/
def evenGridEmbedding : ℕ × ℕ ↪ Point where
  toFun p := ⟨2 * p.1, p.2 + 1⟩
  inj' p q h := by
    have ha := congrArg Point.first h
    have hb := congrArg Point.heightIndex h
    apply Prod.ext <;> dsimp at ha hb ⊢ <;> omega

/-- A grid of given width and number of rows in the even ideal. -/
def evenGrid (width rows : ℕ) : Finset Point :=
  ((Finset.range width).product (Finset.range rows)).map evenGridEmbedding

theorem mem_evenGrid {width rows : ℕ} {s : Point} :
    s ∈ evenGrid width rows ↔
      ∃ i < width, ∃ j < rows, s = evenGridEmbedding (i, j) := by
  simp only [evenGrid, Finset.mem_map]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    have hij' := Finset.mem_product.1 hij
    exact ⟨i, Finset.mem_range.1 hij'.1, j, Finset.mem_range.1 hij'.2, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨(i, j), Finset.mk_mem_product (Finset.mem_range.2 hi) (Finset.mem_range.2 hj), rfl⟩

@[simp] theorem evenGrid_card (width rows : ℕ) : (evenGrid width rows).card = width * rows := by
  simp [evenGrid]

theorem evenGrid_subset_even_ideal (width rows : ℕ) :
    (evenGrid width rows : Set Point) ⊆ Set.range (· * evenPoint) := by
  intro s hs
  rcases mem_evenGrid.1 hs with ⟨i, -, j, -, rfl⟩
  apply (even_ideal_shape _).2
  change (2 * i) % 2 = 0 ∧ 0 < j + 1
  omega

/-- The explicit Følner sequence in the parity example, with index zero omitted
when nonempty sets are required. -/
def folnerGrid (n : ℕ) : Finset Point := evenGrid ((2 ^ n) ^ 2) n

theorem folnerGrid_nonempty {n : ℕ} (hn : 0 < n) : (folnerGrid n).Nonempty := by
  refine ⟨evenGridEmbedding (0, 0), mem_evenGrid.2 ⟨0, ?_, 0, hn, rfl⟩⟩
  positivity

theorem folnerGrid_subset_even_ideal (n : ℕ) :
    (folnerGrid n : Set Point) ⊆ Set.range (· * evenPoint) :=
  evenGrid_subset_even_ideal _ _

/-- Fixed left multiplication moves each point horizontally by at most the
shear bound and vertically by a fixed number of rows. -/
theorem evenGrid_overlap (s : Point) (width rows : ℕ) :
    (width - 2 ^ rows * s.first) * (rows - (s.heightIndex + 1)) ≤
      (evenGrid width rows ∩ (evenGrid width rows).image (s * ·)).card := by
  let core := evenGrid (width - 2 ^ rows * s.first) (rows - (s.heightIndex + 1))
  have hinj : Set.InjOn (s * ·) (core : Set Point) :=
    (left_multiplication_injective s).injOn
  have hsub : core.image (s * ·) ⊆
      evenGrid width rows ∩ (evenGrid width rows).image (s * ·) := by
    intro u hu
    rcases Finset.mem_image.1 hu with ⟨v, hv, rfl⟩
    rcases mem_evenGrid.1 hv with ⟨i, hi, j, hj, rfl⟩
    apply Finset.mem_inter.2
    constructor
    · have hj' : j + 1 ≤ rows := by omega
      have hslope : 2 ^ (j + 1) * s.first ≤ 2 ^ rows * s.first :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hj')
      refine mem_evenGrid.2 ⟨i + 2 ^ (j + 1) * s.first, by omega,
        j + s.heightIndex + 1, by omega, ?_⟩
      apply Point.ext
      · change 2 ^ (j + 1 + 1) * s.first + 2 * i = 2 * (i + 2 ^ (j + 1) * s.first)
        rw [pow_succ]
        ring
      · change s.heightIndex + (j + 1) + 1 = j + s.heightIndex + 1 + 1
        omega
    · exact Finset.mem_image.2 ⟨_, mem_evenGrid.2 ⟨i, by omega, j, by omega, rfl⟩, rfl⟩
  calc
    _ = core.card := (evenGrid_card _ _).symm
    _ = (core.image (s * ·)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_mono hsub

private theorem rectangle_deficit (width rows shear height : ℕ) :
    width * rows - (width - shear) * (rows - height) ≤ shear * rows + width * height := by
  have hwidth : width * rows = (width - shear) * rows + min width shear * rows := by
    rw [← add_mul, tsub_add_min]
  have hrows : (width - shear) * rows =
      (width - shear) * (rows - height) + (width - shear) * min rows height := by
    rw [← mul_add, tsub_add_min]
  have hs : min width shear * rows ≤ shear * rows := Nat.mul_le_mul_right _ (min_le_right _ _)
  have hh : (width - shear) * min rows height ≤ width * height :=
    Nat.mul_le_mul (Nat.sub_le _ _) (min_le_right _ _)
  omega

theorem evenGrid_deficit (s : Point) (width rows : ℕ) :
    (evenGrid width rows \ (evenGrid width rows).image (s * ·)).card ≤
      (2 ^ rows * s.first) * rows + width * (s.heightIndex + 1) := by
  rw [Finset.card_sdiff, Finset.inter_comm, evenGrid_card]
  exact (Nat.sub_le_sub_left (evenGrid_overlap s width rows) _).trans
    (rectangle_deficit _ _ _ _)

/-- The normalized left Følner deficit tends to zero for the explicit sequence.
Injectivity of left multiplication gives the same deficit on the other side. -/
theorem folnerGrid_left_folner (s : Point) :
    Tendsto (fun n ↦ ((folnerGrid n \ (folnerGrid n).image (s * ·)).card : ℝ) /
      (folnerGrid n).card) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have ht₁ : Tendsto (fun n : ℕ ↦ (s.first : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hp
  have ht₂ := tendsto_const_div_atTop_nhds_zero_nat ((s.heightIndex + 1 : ℕ) : ℝ)
  have hu : Tendsto (fun n : ℕ ↦ (s.first : ℝ) / 2 ^ n + (s.heightIndex + 1 : ℕ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [zero_add] using ht₁.add ht₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun n ↦ div_nonneg (by positivity) (by positivity)) ?_
  refine (eventually_ge_atTop 1).mono fun n hn ↦ ?_
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  simp only [folnerGrid, evenGrid_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ ((2 : ℝ) ^ n * (s.first : ℝ) * n + ((2 : ℝ) ^ n) ^ 2 * (s.heightIndex + 1 : ℕ)) /
        (((2 : ℝ) ^ n) ^ 2 * n) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast evenGrid_deficit s ((2 ^ n) ^ 2) n
    _ = _ := by
      have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp

theorem folnerGrid_coefficient_average (n : ℕ) (hn : 0 < n) (s₀ : Point) :
    (∑ s ∈ folnerGrid n, ‖rightTranslation s indicator s₀‖) /
        ((folnerGrid n).card : ℝ) = 1 :=
  normalized_coefficient_average_on_even_ideal _ (folnerGrid_nonempty hn)
    (folnerGrid_subset_even_ideal n) s₀

end JdLG.PaperExamplesParity
