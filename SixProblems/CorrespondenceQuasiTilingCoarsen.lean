/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceQuasiTilingCover

@[expose] public section
noncomputable section

namespace SixProblems

open Filter
open scoped Classical Topology

variable {G : Type*} [Group G] [DecidableEq G]

/-- The union of the cells of `P` entirely contained in `A`. -/
def BoundedTilePartition.interior (P : BoundedTilePartition G) (A : Finset G) : Finset G :=
  A.filter fun g ↦ P.cell g ⊆ A

theorem BoundedTilePartition.mem_interior_iff (P : BoundedTilePartition G) {A : Finset G} {g : G} :
    g ∈ P.interior A ↔ P.cell g ⊆ A :=
  ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun h ↦ Finset.mem_filter.mpr ⟨h (P.mem_cell g), h⟩⟩

theorem BoundedTilePartition.interior_subset (P : BoundedTilePartition G) (A : Finset G) :
    P.interior A ⊆ A := Finset.filter_subset _ _

theorem leftBoundary_tileTranslate (Q A : Finset G) (c : G) :
    leftBoundary Q (tileTranslate A c) = tileTranslate (leftBoundary Q A) c := by
  ext g
  simp only [mem_leftBoundary, mem_tileTranslate, mul_assoc]

/-- Restricting a finite set creates additional boundary only near the sites removed. -/
theorem card_leftBoundary_le_of_subset (D : Finset G) {A B : Finset G} (hBA : B ⊆ A) :
    (leftBoundary D B).card ≤ (leftBoundary D A).card + D.card * (A \ B).card := by
  let C := D.biUnion (fun d ↦ (A \ B).image (d⁻¹ * ·))
  have hSub : leftBoundary D B ⊆ leftBoundary D A ∪ C := by
    intro g hg
    obtain ⟨hgB, d, hd, hdB⟩ := mem_leftBoundary.mp hg
    by_cases hdA : d * g ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr
        ⟨d * g, Finset.mem_sdiff.mpr ⟨hdA, hdB⟩, inv_mul_cancel_left _ _⟩⟩)
    · exact Finset.mem_union_left _ (mem_leftBoundary.mpr ⟨hBA hgB, d, hd, hdA⟩)
  have hC : C.card ≤ D.card * (A \ B).card :=
    Finset.card_biUnion_le_card_mul _ _ _ fun _ _ ↦ Finset.card_image_le
  exact (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans (add_le_add (le_refl _) hC))

omit [Group G] in
/-- Removing a fraction of a block perturbs a bounded real average by at most
twice the bound times that fraction. -/
theorem norm_finiteAverage_sub_of_subset {A B : Finset G} (hBA : B ⊆ A) (hB : B.Nonempty)
    (f : G → ℝ) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) :
    ‖finiteAverage A f - finiteAverage B f‖ ≤ 2 * C * (((A \ B).card : ℝ) / A.card) := by
  have hA := hB.mono hBA
  have hCount (I : Finset G) (hI : I.Nonempty) : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  have hMean : ‖finiteAverage B f‖ ≤ C := by
    rw [finiteAverage, smul_eq_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (hCount B hB).le)]
    have hSum : ‖∑ g ∈ B, f g‖ ≤ (B.card : ℝ) * C := by
      apply (norm_sum_le _ _).trans
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun (g : G) (_hg : g ∈ B) ↦ hf g)
    calc
      _ ≤ (B.card : ℝ)⁻¹ * ((B.card : ℝ) * C) := mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (hCount B hB).ne', one_mul]
  have hSumEq (I : Finset G) (hI : I.Nonempty) :
      (I.card : ℝ) * finiteAverage I f = ∑ g ∈ I, f g := by
    rw [finiteAverage, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (hCount I hI).ne', one_mul]
  have hSize : (A.card : ℝ) = ((A \ B).card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hBA).symm
  have hIdentity : (A.card : ℝ) * (finiteAverage A f - finiteAverage B f) =
      ∑ g ∈ A \ B, (f g - finiteAverage B f) := by
    rw [mul_sub, hSumEq A hA, ← Finset.sum_sdiff hBA (f := f), hSize, add_mul, hSumEq B hB,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hEq : finiteAverage A f - finiteAverage B f =
      (∑ g ∈ A \ B, (f g - finiteAverage B f)) / (A.card : ℝ) :=
    (eq_div_iff (hCount A hA).ne').mpr (by rwa [mul_comm])
  rw [hEq, norm_div, Real.norm_of_nonneg (hCount A hA).le]
  have hNorm : ‖∑ g ∈ A \ B, (f g - finiteAverage B f)‖ ≤ ((A \ B).card : ℝ) * (2 * C) := by
    calc
      _ ≤ ∑ g ∈ A \ B, ‖f g - finiteAverage B f‖ := norm_sum_le _ _
      _ ≤ ∑ g ∈ A \ B, 2 * C := Finset.sum_le_sum fun g _ ↦ (norm_sub_le _ _).trans (by linarith [hf g])
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (((A \ B).card : ℝ) * (2 * C)) / (A.card : ℝ) :=
      div_le_div_of_nonneg_right hNorm (hCount A hA).le
    _ = _ := by rw [mul_comm (((A \ B).card : ℝ)), mul_div_assoc]

namespace PartialQuasiTiling

variable {η : ℝ}

/-- A finite set containing differences between any two sites of any original tile. -/
def displacements (T : PartialQuasiTiling G η) : Finset G :=
  T.shapes.biUnion (fun A ↦ A.biUnion (fun y ↦ A.image (fun x ↦ y * x⁻¹)))

theorem mem_displacements (T : PartialQuasiTiling G η) (i : T.index) {x y : G}
    (hx : x ∈ tileTranslate (T.shape i) (T.center i))
    (hy : y ∈ tileTranslate (T.shape i) (T.center i)) : y * x⁻¹ ∈ T.displacements := by
  have hx' := mem_tileTranslate.mp hx
  have hy' := mem_tileTranslate.mp hy
  refine Finset.mem_biUnion.mpr ⟨T.shape i, T.shape_mem i, Finset.mem_biUnion.mpr
    ⟨y * (T.center i)⁻¹, hy', Finset.mem_image.mpr ⟨x * (T.center i)⁻¹, hx', ?_⟩⟩⟩
  simp [mul_assoc]

/-- Sites in prior cells which cannot be assigned whole to any one trimmed core. -/
def exceptional (T : PartialQuasiTiling G η) (P : BoundedTilePartition G) : Set G :=
  {g | ¬ ∃ i, g ∈ P.interior (T.core i)}

/-- Turn the trimmed cores into cells of a coarser partition. Any former cell
that is outside these cores survives as an exceptional cell. -/
theorem exists_coarsening (T : PartialQuasiTiling G η) (P : BoundedTilePartition G) :
    ∃ Q : BoundedTilePartition G,
      (∀ g, P.cell g ⊆ Q.cell g) ∧
      (∀ g h, h ∈ Q.cell g → (g ∈ T.exceptional P ↔ h ∈ T.exceptional P)) ∧
      (∀ g ∉ T.exceptional P, ∃ i, g ∈ P.interior (T.core i) ∧ Q.cell g = P.interior (T.core i)) := by
  let S := fun i : T.index ↦ P.interior (T.core i)
  let U : Set G := {g | ∃ i, g ∈ S i}
  have hex (g : U) : ∃ i, (g : G) ∈ S i := g.property
  choose label hLabel using hex
  let cell (g : G) := if hg : g ∈ U then S (label ⟨g, hg⟩) else P.cell g
  have hAssign (i : T.index) {g : G} (hg : g ∈ S i) : cell g = S i := by
    have hU : g ∈ U := ⟨i, hg⟩
    simp only [cell, hU, dite_true]
    have heq : label ⟨g, hU⟩ = i := by
      by_contra hn
      exact Finset.disjoint_left.mp (T.disjoint_core hn)
        (P.interior_subset _ (hLabel ⟨g, hU⟩)) (P.interior_subset _ hg)
    rw [heq]
  have hOutside {g h : G} (hg : g ∉ U) (hh : h ∈ P.cell g) : h ∉ U := by
    rintro ⟨i, hi⟩
    apply hg
    refine ⟨i, (P.mem_interior_iff).mpr ?_⟩
    rw [← P.cell_eq hh]
    exact P.mem_interior_iff.mp hi
  have hCoarsen (g : G) : P.cell g ⊆ cell g := by
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hg
      rw [hAssign i hi]
      intro h hh
      exact P.mem_interior_iff.mpr ((P.cell_eq hh).symm ▸ P.mem_interior_iff.mp hi)
    · simp [cell, hg]
  have hMem (g : G) : g ∈ cell g := hCoarsen g (P.mem_cell g)
  have hSame {g h : G} (hh : h ∈ cell g) : cell h = cell g := by
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hg
      rw [hAssign i hi] at hh ⊢
      exact hAssign i hh
    · have hhP : h ∈ P.cell g := by simpa [cell, hg] using hh
      simpa [cell, hg, hOutside hg hhP] using P.cell_eq hhP
  let Q : BoundedTilePartition G :=
    { cell := cell, mem_cell := hMem, cell_eq := hSame,
      displacements := P.displacements ∪ T.displacements,
      mem_displacements := by
        intro g h hh
        by_cases hg : g ∈ U
        · obtain ⟨i, hi⟩ := hg
          rw [hAssign i hi] at hh
          exact Finset.mem_union_right _ (T.mem_displacements i (T.core_subset i (P.interior_subset _ hi))
            (T.core_subset i (P.interior_subset _ hh)))
        · exact Finset.mem_union_left _ (P.mem_displacements (by simpa [cell, hg] using hh)) }
  refine ⟨Q, hCoarsen, ?_, ?_⟩
  · intro g h hh
    change g ∉ U ↔ h ∉ U
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hg
      change h ∈ cell g at hh
      rw [hAssign i hi] at hh
      exact ⟨fun hn ↦ (hn ⟨i, hi⟩).elim, fun hn ↦ (hn ⟨i, hh⟩).elim⟩
    · exact ⟨fun hng ↦ hOutside hng (by simpa [Q, cell, hg] using hh), fun _ ↦ hg⟩
  · intro g hg
    have hg' : g ∈ U := Classical.not_not.mp hg
    obtain ⟨i, hi⟩ := hg'
    exact ⟨i, hi, hAssign i hi⟩

/-- Discarding old cells that cross a core boundary loses only near-boundary sites or
sites near a point removed in the original trimming. -/
theorem card_sdiff_interior_le (T : PartialQuasiTiling G η) (P : BoundedTilePartition G)
    (i : T.index) (hi : (T.core i).Nonempty) :
    (((tileTranslate (T.shape i) (T.center i)) \ P.interior (T.core i)).card : ℝ) ≤
      ((1 + P.displacements.card) * η) * (T.shape i).card +
        ((leftBoundary P.displacements (T.shape i)).card : ℝ) := by
  let A := tileTranslate (T.shape i) (T.center i)
  let R := T.core i
  let B := A \ R
  let L := leftBoundary P.displacements A
  let E := P.displacements.biUnion (fun d ↦ B.image (d⁻¹ * ·))
  have hSub : A \ P.interior R ⊆ (B ∪ E) ∪ L := by
    intro g hg
    obtain ⟨hgA, hgLost⟩ := Finset.mem_sdiff.mp hg
    by_cases hR : g ∈ R
    · obtain ⟨h, hhP, hhR⟩ := Finset.not_subset.mp (fun h ↦ hgLost (P.mem_interior_iff.mpr h))
      have hMove := P.mem_displacements hhP
      by_cases hhA : h ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨h * g⁻¹, hMove, Finset.mem_image.mpr ⟨h, Finset.mem_sdiff.mpr ⟨hhA, hhR⟩, by simp⟩⟩))
      · exact Finset.mem_union_right _ (mem_leftBoundary.mpr
          ⟨hgA, h * g⁻¹, hMove, by simpa using hhA⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hgA, hR⟩))
  have hCard : (A \ P.interior R).card ≤ B.card + P.displacements.card * B.card + L.card := by
    have hE : E.card ≤ P.displacements.card * B.card :=
      Finset.card_biUnion_le_card_mul _ _ _ fun _ _ ↦ Finset.card_image_le
    exact (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_union_le _ _) (le_refl _)) |>.trans
      (add_le_add (add_le_add (le_refl _) hE) (le_refl _)))
  have hB : (B.card : ℝ) ≤ η * (T.shape i).card := by
    have he := Finset.card_sdiff_add_card_eq_card (T.core_subset i)
    rw [card_tileTranslate] at he
    have he' : (B.card : ℝ) + (R.card : ℝ) = (T.shape i).card := by exact_mod_cast he
    linarith [T.core_card i hi]
  have hL : L.card = (leftBoundary P.displacements (T.shape i)).card := by
    simp only [L, A, leftBoundary_tileTranslate, card_tileTranslate]
  have hCardR : ((A \ P.interior R).card : ℝ) ≤ B.card + P.displacements.card * (B.card : ℝ) + L.card := by
    exact_mod_cast hCard
  rw [hL] at hCardR
  linarith [mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg P.displacements.card : (0 : ℝ) ≤ _)]

/-- Compare the loss from coarsening on a finite region with the total loss of the
cores contained in the region. Cores crossing the region boundary are counted separately. -/
theorem finiteFraction_exceptional_le (T : PartialQuasiTiling G η) (P : BoundedTilePartition G)
    (A : Finset G) (hA : A.Nonempty) {loss : ℝ} (hloss : 0 ≤ loss)
    (hLoss : ∀ i, (T.core i).Nonempty →
      (((T.core i) \ P.interior (T.core i)).card : ℝ) ≤ loss * (T.core i).card) :
    finiteFraction A (T.exceptional P) ≤ finiteFraction A T.coveredᶜ +
      ((leftBoundary T.displacements A).card : ℝ) / A.card + loss := by
  let B := leftBoundary T.displacements A
  let W := (A \ B).filter (· ∈ T.covered)
  have hex (g : W) : ∃ i, (g : G) ∈ T.core i := by
    have hg : (g : G) ∈ T.covered := (Finset.mem_filter.mp g.property).2
    rw [T.covered_eq, Set.mem_iUnion] at hg
    exact hg
  choose label hLabel using hex
  let cores := W.attach.image (fun g : W ↦ T.core (label g))
  have hActive (R : Finset G) (hR : R ∈ cores) : ∃ i, R = T.core i ∧ R.Nonempty ∧ R ⊆ A := by
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hR
    have hg := (Finset.mem_filter.mp g.property).1
    refine ⟨label g, rfl, ⟨_, hLabel g⟩, fun z hz ↦ ?_⟩
    by_contra hOut
    have hMove := T.mem_displacements (label g) (T.core_subset _ (hLabel g)) (T.core_subset _ hz)
    exact (Finset.mem_sdiff.mp hg).2 (mem_leftBoundary.mpr
      ⟨(Finset.mem_sdiff.mp hg).1, z * (g : G)⁻¹, hMove, by simpa using hOut⟩)
  have hPair : (↑cores : Set (Finset G)).PairwiseDisjoint id := by
    intro R hR S hS hne
    obtain ⟨i, rfl, _, _⟩ := hActive R hR
    obtain ⟨j, rfl, _, _⟩ := hActive S hS
    exact T.disjoint_core (fun he ↦ hne (congrArg T.core he))
  have hSum : (∑ R ∈ cores, R.card) ≤ A.card := by
    have he := Finset.card_biUnion hPair
    change (cores.biUnion id).card = ∑ R ∈ cores, R.card at he
    rw [← he]
    refine Finset.card_le_card (Finset.biUnion_subset.mpr ?_)
    intro R hR
    obtain ⟨_, _, _, hSub⟩ := hActive R hR
    exact hSub
  let E := A.filter (· ∈ T.coveredᶜ)
  let L := cores.biUnion (fun R ↦ R \ P.interior R)
  have hSub : A.filter (· ∈ T.exceptional P) ⊆ (E ∪ B) ∪ L := by
    intro g hg
    obtain ⟨hgA, hgBad⟩ := Finset.mem_filter.mp hg
    by_cases hgU : g ∈ T.covered
    · by_cases hgB : g ∈ B
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hgB)
      · let x : W := ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hgA, hgB⟩, hgU⟩⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨T.core (label x), Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩,
            Finset.mem_sdiff.mpr ⟨hLabel x, fun hd ↦ hgBad ⟨label x, hd⟩⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgA, hgU⟩))
  have hLCast : (L.card : ℝ) ≤ loss * (A.card : ℝ) := by
    calc
      _ ≤ ∑ R ∈ cores, (((R \ P.interior R).card : ℕ) : ℝ) := by
        exact_mod_cast (show L.card ≤ ∑ R ∈ cores, (R \ P.interior R).card from Finset.card_biUnion_le)
      _ ≤ ∑ R ∈ cores, loss * (R.card : ℝ) := by
        refine Finset.sum_le_sum fun R hR ↦ ?_
        obtain ⟨i, rfl, hn, _⟩ := hActive R hR
        exact hLoss i hn
      _ = loss * ∑ R ∈ cores, (R.card : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hSum) hloss
  have hNat : (A.filter (· ∈ T.exceptional P)).card ≤ E.card + B.card + L.card :=
    (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_union_le _ _) (le_refl _)))
  have hReal : ((A.filter (· ∈ T.exceptional P)).card : ℝ) ≤ E.card + B.card + L.card := by
    exact_mod_cast hNat
  have hCard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  have h := div_le_div_of_nonneg_right (hReal.trans (add_le_add (le_refl _) hLCast))
    (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  rw [add_div, add_div, mul_div_assoc, div_self hCard, mul_one] at h
  rw [finiteFraction_eq_filter A (T.exceptional P) (fun _ ↦ inferInstance),
    finiteFraction_eq_filter A T.coveredᶜ (fun _ ↦ inferInstance)]
  exact h

/-- Prescribing a small loss in each core and a small uncovered fraction gives a small
eventual density for the exceptional cells of the coarsened partition. -/
theorem eventually_exceptional (T : PartialQuasiTiling G η) (P : BoundedTilePartition G)
    (F : LeftFolnerSequence G) {a loss ε : ℝ} (hloss : 0 ≤ loss) (hε : 0 < ε)
    (hLoss : ∀ i, (T.core i).Nonempty →
      (((T.core i) \ P.interior (T.core i)).card : ℝ) ≤ loss * (T.core i).card)
    (hCovered : ∀ᶠ n in atTop, finiteFraction (F.blocks n) T.coveredᶜ < a) :
    ∀ᶠ n in atTop, finiteFraction (F.blocks n) (T.exceptional P) < a + loss + ε := by
  filter_upwards [hCovered, (F.tendsto_leftBoundary T.displacements).eventually_lt_const hε] with n hC hB
  exact (T.finiteFraction_exceptional_le P _ (F.nonempty n) hloss hLoss).trans_lt (by linarith)

end PartialQuasiTiling

end SixProblems
