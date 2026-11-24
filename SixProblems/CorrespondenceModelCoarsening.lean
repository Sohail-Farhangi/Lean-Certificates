/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceQuasiTilingCoarsen

@[expose] public section
noncomputable section

namespace SixProblems

open Filter
open scoped Classical Topology

variable {G K : Type*} [Group G] [DecidableEq G] [Countable G] [Nonempty K]

omit [Countable G] in
private theorem leftBoundary_mono_support (A : Finset G) {D E : Finset G} (h : D ⊆ E) :
    leftBoundary D A ⊆ leftBoundary E A := by
  intro g hg
  obtain ⟨hgA, d, hd, hdA⟩ := mem_leftBoundary.mp hg
  exact mem_leftBoundary.mpr ⟨hgA, d, h hd, hdA⟩

/-- Refine the approximation accuracy by grouping whole prior cells. Large Følner
blocks bearing local models become the shapes of the new cells. Cells that could
not be grouped are allowed on a set of arbitrarily small eventual density. -/
theorem exists_modelCoarsening {ι : Type*} (F : LeftFolnerSequence G) (P : BoundedTilePartition G)
    (I : Finset ι) (support : ι → Finset G) (q : ι → (G → K) → G → ℝ) {C τ δ : ℝ}
    (hC : 0 ≤ C) (hτ : 0 < τ) (hδ : 0 < δ)
    (hBound : ∀ i ∈ I, ∀ x g, ‖q i x g‖ ≤ C)
    (hTranslate : ∀ i ∈ I, ∀ c (x : G → K) g, q i (fun h ↦ x (h * c⁻¹)) (g * c) = q i x g)
    (hModels : ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ∈ I,
      ‖finiteAverage (F.blocks n) (q i x)‖ ≤ τ / 2) :
    ∃ (Q : BoundedTilePartition G) (bad : Set G) (sample : Finset G → G → K),
      (∀ g, P.cell g ⊆ Q.cell g) ∧
      (∀ g h, h ∈ Q.cell g → (g ∈ bad ↔ h ∈ bad)) ∧
      (∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ δ) ∧
      (∀ g ∉ bad, ∀ i ∈ I, ‖finiteAverage (Q.cell g) (q i (sample (Q.cell g)))‖ ≤ τ) ∧
      (∀ g ∉ bad, ∀ i ∈ I, ((leftBoundary (support i) (Q.cell g)).card : ℝ) / (Q.cell g).card ≤ τ) := by
  let D := I.biUnion support
  let E := D ∪ P.displacements
  let c : ℝ := 1 + C + D.card
  have hc : 0 < c := by dsimp [c]; positivity
  let r := min (1 / 4 : ℝ) (min (δ / 8) (τ / (4 * c)))
  have hr : 0 < r := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hrOne : r ≤ 1 / 4 := min_le_left _ _
  have hrδ : r ≤ δ / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r * (4 * c) ≤ τ := (le_div_iff₀ (by positivity : 0 < 4 * c)).mp
    ((min_le_right _ _).trans (min_le_right _ _))
  let η := r / (2 * (1 + (P.displacements.card : ℝ)))
  let θ := r / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηHalf : η ≤ 1 / 2 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + (P.displacements.card : ℝ)))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) P.displacements.card]
  have hθ : 0 < θ := half_pos hr
  have hIdentity : (1 + (P.displacements.card : ℝ)) * η + θ = r := by
    dsimp [η, θ]
    field_simp
    norm_num
  let allowed : Set (Finset G) := {S | S.Nonempty ∧
    ((leftBoundary E S).card : ℝ) ≤ θ * S.card ∧
    ∃ x : G → K, ∀ i ∈ I, ‖finiteAverage S (q i x)‖ ≤ τ / 2}
  have hAvailable (A : Finset G) (ε : ℝ) (hε : 0 < ε) : ∃ S ∈ allowed, S.Nonempty ∧
      ((externalBoundary A S).card : ℝ) ≤ ε * S.card := by
    obtain ⟨n, hmodel, hLeft, hExt⟩ :=
      (hModels.and (((F.tendsto_leftBoundary E).eventually_lt_const hθ).and
        ((F.tendsto_externalBoundary A).eventually_lt_const hε))).exists
    have hn : (0 : ℝ) < (F.blocks n).card := by exact_mod_cast (F.nonempty n).card_pos
    exact ⟨F.blocks n, ⟨F.nonempty n, ((div_lt_iff₀ hn).mp hLeft).le, hmodel⟩,
      F.nonempty n, ((div_lt_iff₀ hn).mp hExt).le⟩
  obtain ⟨T, hAllowed, hCovered⟩ := PartialQuasiTiling.exists_eventually_cover F allowed hη
    (by linarith : η < 1) (by positivity : 0 < δ / 4) hAvailable
  let excess (i : T.index) := tileTranslate (T.shape i) (T.center i) \ P.interior (T.core i)
  have hExcess (i : T.index) (hi : (T.core i).Nonempty) :
      ((excess i).card : ℝ) ≤ r * (T.shape i).card := by
    have he := T.card_sdiff_interior_le P i hi
    have hLeft : ((leftBoundary P.displacements (T.shape i)).card : ℝ) ≤ θ * (T.shape i).card :=
      (Nat.cast_le.mpr (Finset.card_le_card
        (leftBoundary_mono_support (T.shape i) (Finset.subset_union_right : P.displacements ⊆ E)))).trans
          (hAllowed (T.shape i) (T.shape_mem i)).2.1
    calc
      _ ≤ ((1 + (P.displacements.card : ℝ)) * η) * (T.shape i).card + θ * (T.shape i).card :=
        he.trans (add_le_add (le_refl _) hLeft)
      _ = _ := by rw [← add_mul, hIdentity]
  have hLoss (i : T.index) (hi : (T.core i).Nonempty) :
      (((T.core i) \ P.interior (T.core i)).card : ℝ) ≤ (2 * r) * (T.core i).card := by
    have hCore : (T.shape i).card ≤ 2 * ((T.core i).card : ℝ) := by
      linarith [T.core_card i hi, mul_le_mul_of_nonneg_right hηHalf (Nat.cast_nonneg (α := ℝ) (T.shape i).card)]
    calc
      _ ≤ ((excess i).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card (fun g hg ↦ by
        obtain ⟨hgR, hgOut⟩ := Finset.mem_sdiff.mp hg
        exact Finset.mem_sdiff.mpr ⟨T.core_subset i hgR, hgOut⟩))
      _ ≤ r * (T.shape i).card := hExcess i hi
      _ ≤ r * (2 * ((T.core i).card : ℝ)) := mul_le_mul_of_nonneg_left hCore hr.le
      _ = _ := by ring
  obtain ⟨Q, hCoarsen, hConstant, hGood⟩ := T.exists_coarsening P
  let bad := T.exceptional P
  have hBad : ∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ δ := by
    have h := T.eventually_exceptional P F (a := δ / 4) (loss := 2 * r) (ε := δ / 4)
      (by positivity) (by positivity) hLoss hCovered
    exact h.mono fun n hn ↦ hn.le.trans (by linarith)
  have hModel (g : G) (hg : g ∉ bad) :
      (∃ x, ∀ j ∈ I, ‖finiteAverage (Q.cell g) (q j x)‖ ≤ τ) ∧
      ∀ j ∈ I, ((leftBoundary (support j) (Q.cell g)).card : ℝ) / (Q.cell g).card ≤ τ := by
    obtain ⟨i, hgi, hCell⟩ := hGood g hg
    let S := T.shape i
    let A := tileTranslate S (T.center i)
    let B := P.interior (T.core i)
    have hB : B.Nonempty := ⟨g, hgi⟩
    have hBA : B ⊆ A := (P.interior_subset _).trans (T.core_subset i)
    have hAS : A.card = S.card := card_tileTranslate _ _
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast (hB.mono hBA).card_pos
    have hi : (T.core i).Nonempty := ⟨g, P.interior_subset _ hgi⟩
    have hAB : (((A \ B).card : ℕ) : ℝ) ≤ r * A.card := by rw [hAS]; exact hExcess i hi
    have hABden : (((A \ B).card : ℕ) : ℝ) / A.card ≤ r := (div_le_iff₀ hApos).mpr hAB
    have hSize : ((A.card : ℕ) : ℝ) ≤ 2 * (B.card : ℝ) := by
      have he : (((A \ B).card : ℕ) : ℝ) + B.card = A.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hBA
      linarith [mul_le_mul_of_nonneg_right hrOne hApos.le]
    obtain ⟨_, hBoundary, x, hx⟩ := hAllowed S (T.shape_mem i)
    let z : G → K := fun a ↦ x (a * (T.center i)⁻¹)
    rw [hCell]
    refine ⟨⟨z, ?_⟩, ?_⟩
    · intro j hj
      have hAvgEq : finiteAverage A (q j z) = finiteAverage S (q j x) := by
        rw [finiteAverage, finiteAverage, hAS]
        congr 1
        change (∑ a ∈ S.image (· * T.center i), q j z a) = ∑ a ∈ S, q j x a
        rw [Finset.sum_image (fun _ _ _ _ he ↦ mul_right_cancel he)]
        exact Finset.sum_congr rfl fun a _ ↦ hTranslate j hj (T.center i) x a
      have hDist := (norm_finiteAverage_sub_of_subset hBA hB (q j z) (hBound j hj z)).trans
        (mul_le_mul_of_nonneg_left hABden (mul_nonneg (by norm_num) hC))
      have hComp : 2 * C * r ≤ τ / 2 := by
        dsimp [c] at hrτ
        nlinarith [mul_nonneg hr.le (Nat.cast_nonneg (α := ℝ) D.card)]
      calc
        _ = ‖(finiteAverage B (q j z) - finiteAverage A (q j z)) +
            finiteAverage A (q j z)‖ := by rw [sub_add_cancel]
        _ ≤ ‖finiteAverage B (q j z) - finiteAverage A (q j z)‖ +
            ‖finiteAverage A (q j z)‖ := norm_add_le _ _
        _ ≤ 2 * C * r + τ / 2 := by
          apply add_le_add
          · rw [norm_sub_rev]
            exact hDist
          · rw [hAvgEq]
            exact hx j hj
        _ ≤ τ := by linarith
    · intro j hj
      have hDE : support j ⊆ D := fun d hd ↦ Finset.mem_biUnion.mpr ⟨j, hj, hd⟩
      have hDcard : ((support j).card : ℝ) ≤ D.card := Nat.cast_le.mpr (Finset.card_le_card hDE)
      have hAleft : ((leftBoundary (support j) A).card : ℝ) ≤ θ * A.card := by
        rw [show A = _ from rfl, leftBoundary_tileTranslate, card_tileTranslate, card_tileTranslate]
        exact (Nat.cast_le.mpr (Finset.card_le_card (leftBoundary_mono_support S
          (hDE.trans (Finset.subset_union_left : D ⊆ E))))).trans hBoundary
      have hBorder : ((leftBoundary (support j) B).card : ℝ) ≤
          θ * A.card + (D.card : ℝ) * (r * A.card) := by
        have hNat := card_leftBoundary_le_of_subset (support j) hBA
        have hCast : ((leftBoundary (support j) B).card : ℝ) ≤
            (leftBoundary (support j) A).card + (support j).card * (((A \ B).card : ℕ) : ℝ) := by
          exact_mod_cast hNat
        exact hCast.trans (add_le_add hAleft (mul_le_mul hDcard hAB (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      apply (div_le_iff₀ hBpos).mpr
      have hLast : 2 * (θ + (D.card : ℝ) * r) ≤ τ := by
        dsimp [θ, c] at *
        nlinarith [mul_nonneg hr.le hC, mul_nonneg hr.le (Nat.cast_nonneg (α := ℝ) D.card)]
      calc
        _ ≤ (θ + (D.card : ℝ) * r) * A.card := hBorder.trans (le_of_eq (by ring))
        _ ≤ (θ + (D.card : ℝ) * r) * (2 * (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hSize (by positivity)
        _ = (2 * (θ + (D.card : ℝ) * r)) * (B.card : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hLast hBpos.le
  let sample (B : Finset G) : G → K :=
    if h : ∃ x, ∀ j ∈ I, ‖finiteAverage B (q j x)‖ ≤ τ then Classical.choose h else fun _ ↦ Classical.ofNonempty
  refine ⟨Q, bad, sample, hCoarsen, hConstant, hBad, ?_, fun g hg ↦ (hModel g hg).2⟩
  intro g hg
  have h := (hModel g hg).1
  simpa only [sample, h, dite_true] using Classical.choose_spec h

omit [Countable G] in
/-- The finest partition, used to start a sequence of coarsenings. -/
def singletonTilePartition (G : Type*) [Group G] [DecidableEq G] : BoundedTilePartition G where
  cell g := {g}
  mem_cell g := Finset.mem_singleton_self g
  cell_eq h := by rw [Finset.mem_singleton.mp h]
  displacements := {1}
  mem_displacements h := by rw [Finset.mem_singleton.mp h]; simp

/-- A bounded partition with small cylinder boundaries apart from exceptional
cells of arbitrarily small eventual density. The construction starts from singletons
and uses the coarsening theorem with a zero observable. -/
theorem exists_smallBoundaryTilePartition {ι : Type*} (F : LeftFolnerSequence G)
    (I : Finset ι) (support : ι → Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : BoundedTilePartition G) (bad : Set G),
      (∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ ε) ∧
      (∀ i ∈ I, ∀ g ∉ bad,
        ((leftBoundary (support i) (P.cell g)).card : ℝ) ≤ ε * (P.cell g).card) := by
  have hModels : ∀ᶠ n in atTop, ∃ x : G → Unit, ∀ i ∈ I,
      ‖finiteAverage (F.blocks n) (fun _ ↦ (0 : ℝ))‖ ≤ ε / 2 :=
    Filter.Eventually.of_forall fun _ ↦ ⟨fun _ ↦ (), fun _ _ ↦ by
      simpa [finiteAverage] using (half_pos hε).le⟩
  obtain ⟨P, bad, _, _, _, hBad, _, hBoundary⟩ := exists_modelCoarsening F
    (singletonTilePartition G) I support (fun _ (_ : G → Unit) _ ↦ 0) (C := 0) (τ := ε) (δ := ε)
    (le_refl 0) hε hε (by simp) (by simp) hModels
  refine ⟨P, bad, hBad, fun i hi g hg ↦ ?_⟩
  have hCard : (0 : ℝ) < (P.cell g).card := by
    exact_mod_cast (Finset.Nonempty.card_pos ⟨g, P.mem_cell g⟩)
  exact (div_le_iff₀ hCard).mp (hBoundary g hg i hi)

/-- Iterate the coarsening construction so that both the model accuracies and the
exceptional-site bounds have the required decay as the number of tests grows. -/
theorem exists_congruentModelCoarsenings (F : LeftFolnerSequence G)
    (support : ℕ → Finset G) (q : ℕ → (G → K) → G → ℝ) (C : ℕ → ℝ)
    (hC : ∀ k, 0 ≤ C k)
    (hNorm : ∀ k i, i ≤ k → ∀ x g, ‖q i x g‖ ≤ C k)
    (hTranslate : ∀ i c (x : G → K) g, q i (fun h ↦ x (h * c⁻¹)) (g * c) = q i x g)
    (hModels : ∀ k, ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ≤ k,
      ‖finiteAverage (F.blocks n) (q i x)‖ ≤ (1 / ((k : ℝ) + 1)) / 2) :
    ∃ (P : ℕ → BoundedTilePartition G) (bad : ℕ → Set G) (sample : ℕ → Finset G → G → K),
      (∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g) ∧
      (∀ k g h, h ∈ (P k).cell g → (g ∈ bad k ↔ h ∈ bad k)) ∧
      (∀ k, ∀ᶠ n in atTop, finiteFraction (F.blocks n) (bad k) ≤ (1 / 2 : ℝ) ^ k) ∧
      (∀ k g, g ∉ bad k → ∀ i ≤ k,
        ‖finiteAverage ((P k).cell g) (q i (sample k ((P k).cell g)))‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ k g, g ∉ bad k → ∀ i ≤ k,
        ((leftBoundary (support i) ((P k).cell g)).card : ℝ) / ((P k).cell g).card ≤ 1 / ((k : ℝ) + 1)) := by
  let τ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let δ (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
  have hStep (k : ℕ) (P : BoundedTilePartition G) :
      ∃ (Q : BoundedTilePartition G) (bad : Set G) (sample : Finset G → G → K),
        (∀ g, P.cell g ⊆ Q.cell g) ∧
        (∀ g h, h ∈ Q.cell g → (g ∈ bad ↔ h ∈ bad)) ∧
        (∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ δ k) ∧
        (∀ g ∉ bad, ∀ i ≤ k, ‖finiteAverage (Q.cell g) (q i (sample (Q.cell g)))‖ ≤ τ k) ∧
        (∀ g ∉ bad, ∀ i ≤ k, ((leftBoundary (support i) (Q.cell g)).card : ℝ) / (Q.cell g).card ≤ τ k) := by
    have hRange (i : ℕ) : i ∈ Finset.range (k + 1) ↔ i ≤ k := Finset.mem_range.trans Nat.lt_succ_iff
    have hInput : ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ∈ Finset.range (k + 1),
        ‖finiteAverage (F.blocks n) (q i x)‖ ≤ τ k / 2 :=
      (hModels k).mono fun _ ⟨x, hx⟩ ↦ ⟨x, fun i hi ↦ hx i ((hRange i).mp hi)⟩
    obtain ⟨Q, bad, sample, hCoarsen, hConstant, hDensity, hTest, hBorder⟩ :=
      exists_modelCoarsening F P (Finset.range (k + 1)) support q (hC k)
        (show 0 < τ k by dsimp [τ]; positivity) (show 0 < δ k by dsimp [δ]; positivity)
        (fun i hi ↦ hNorm k i ((hRange i).mp hi)) (fun i _ ↦ hTranslate i) hInput
    exact ⟨Q, bad, sample, hCoarsen, hConstant, hDensity,
      fun g hg i hi ↦ hTest g hg i ((hRange i).mpr hi),
      fun g hg i hi ↦ hBorder g hg i ((hRange i).mpr hi)⟩
  choose next bad sample hCoarsen hConstant hDensity hTest hBorder using hStep
  let prev : ℕ → BoundedTilePartition G := Nat.rec (singletonTilePartition G) next
  let P (k : ℕ) := next k (prev k)
  exact ⟨P, fun k ↦ bad k (prev k), fun k ↦ sample k (prev k),
    fun k ↦ hCoarsen (k + 1) (prev (k + 1)), fun k ↦ hConstant k (prev k),
    fun k ↦ hDensity k (prev k), fun k ↦ hTest k (prev k), fun k ↦ hBorder k (prev k)⟩

end SixProblems
