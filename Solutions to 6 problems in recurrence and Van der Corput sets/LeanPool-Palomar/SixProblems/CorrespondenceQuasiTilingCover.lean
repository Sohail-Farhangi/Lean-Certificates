/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceQuasiTiling
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section
noncomputable section

namespace SixProblems

open Filter
open scoped Classical Topology

universe u
variable {G : Type u} [Group G] [DecidableEq G]

/-- A finite-shape family of translates with pairwise disjoint trimmed cores.
The cores cover exactly the set occupied by all translates with nonempty cores. -/
structure PartialQuasiTiling (G : Type u) [Group G] [DecidableEq G] (η : ℝ) where
  index : Type u
  shapes : Finset (Finset G)
  shape : index → Finset G
  shape_mem (i : index) : shape i ∈ shapes
  center : index → G
  core : index → Finset G
  covered : Set G
  covered_eq : covered = ⋃ i, ↑(core i)
  disjoint_core : Pairwise (fun i j ↦ Disjoint (core i) (core j))
  core_subset (i : index) : core i ⊆ tileTranslate (shape i) (center i)
  tile_subset (i : index) : (core i).Nonempty → ↑(tileTranslate (shape i) (center i)) ⊆ covered
  core_card (i : index) : (core i).Nonempty → (1 - η) * (shape i).card ≤ ((core i).card : ℝ)

namespace PartialQuasiTiling

variable {η : ℝ}

theorem core_subset_covered (T : PartialQuasiTiling G η) (i : T.index) : ↑(T.core i) ⊆ T.covered := by
  rw [T.covered_eq]
  exact Set.subset_iUnion (fun j ↦ (↑(T.core j) : Set G)) i

/-- Empty cover before the first greedy layer. -/
def empty : PartialQuasiTiling G η where
  index := PEmpty
  shapes := ∅
  shape := fun i ↦ i.elim
  shape_mem := fun i ↦ i.elim
  center := fun i ↦ i.elim
  core := fun i ↦ i.elim
  covered := ∅
  covered_eq := by simp
  disjoint_core := fun i ↦ i.elim
  core_subset := fun i ↦ i.elim
  tile_subset := fun i ↦ i.elim
  core_card := fun i ↦ i.elim

/-- Extend the finite family by one maximal layer, retaining at least the prescribed
proportion in each new nonempty core. -/
theorem exists_extend [Countable G] (T : PartialQuasiTiling G η) (S : Finset G)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) :
    ∃ (T' : PartialQuasiTiling G η) (b : ℕ),
      T'.shapes = insert S T.shapes ∧ T.covered ⊆ T'.covered ∧
      η * (S.card : ℝ) ≤ ((S.card + 1 - b : ℕ) : ℝ) ∧
      (∀ c : G, ((tileTranslate S c).filter (· ∉ T'.covered)).card < b) := by
  let r := ⌈η * (S.card : ℝ)⌉₊
  have hr : r ≤ S.card := Nat.ceil_le.mpr (by
    calc
      η * (S.card : ℝ) ≤ 1 * (S.card : ℝ) := mul_le_mul_of_nonneg_right hη₁ (Nat.cast_nonneg _)
      _ = _ := one_mul _)
  let b := S.card + 1 - r
  have hb : 0 < b := by dsimp [b]; omega
  have hηb : η * (S.card : ℝ) ≤ ((S.card + 1 - b : ℕ) : ℝ) := by
    rw [show S.card + 1 - b = r by dsimp [b]; omega]
    exact Nat.le_ceil _
  have hηb' : (1 - η) * (S.card : ℝ) ≤ (b : ℝ) := by
    have hr' : (r : ℝ) < η * (S.card : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    dsimp only [b]
    rw [Nat.cast_sub (by omega : r ≤ S.card + 1), Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨V, e, R, hV, hDis, hNewDis, hNewCore, hNewTile, hMax⟩ :=
    exists_greedyCover S hb T.covered
  have hUV : T.covered ⊆ V := hV ▸ Set.subset_union_left
  let T' : PartialQuasiTiling G η :=
    { index := T.index ⊕ ℕ,
      shapes := insert S T.shapes,
      shape := Sum.elim T.shape (fun _ ↦ S),
      shape_mem := fun i ↦ match i with
        | .inl j => Finset.mem_insert_of_mem (T.shape_mem j)
        | .inr _ => Finset.mem_insert_self _ _,
      center := Sum.elim T.center e,
      core := Sum.elim T.core R,
      covered := V,
      covered_eq := by rw [hV, T.covered_eq, Set.iUnion_sum]; rfl,
      disjoint_core := by
        intro i j hne
        cases i with
        | inl i =>
          cases j with
          | inl j => exact T.disjoint_core (fun h ↦ hne (congrArg Sum.inl h))
          | inr j =>
            rw [← Finset.disjoint_coe]
            exact (hNewDis j).symm.mono_left (T.core_subset_covered i)
        | inr i =>
          cases j with
          | inl j =>
            rw [← Finset.disjoint_coe]
            exact (hNewDis i).mono_right (T.core_subset_covered j)
          | inr j => exact hDis (fun h ↦ hne (congrArg Sum.inr h)),
      core_subset := fun i ↦ match i with
        | .inl j => T.core_subset j
        | .inr j => (hNewCore j).1,
      tile_subset := fun i ↦ match i with
        | .inl j => fun hj ↦ (T.tile_subset j hj).trans hUV
        | .inr j => hNewTile j,
      core_card := fun i ↦ match i with
        | .inl j => T.core_card j
        | .inr j => fun hj ↦ hηb'.trans (Nat.cast_le.mpr ((hNewCore j).2.resolve_left hj.ne_empty)) }
  exact ⟨T', b, rfl, hUV, hηb, hMax⟩

/-- Boundary of a partial cover, using only the finitely many possible tile shapes. -/
theorem eventually_externalBoundary (T : PartialQuasiTiling G η) (F : LeftFolnerSequence G)
    (Q : Finset G) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hShapes : ∀ S ∈ T.shapes, ((externalBoundary Q S).card : ℝ) ≤ ρ * (1 - η) * S.card)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, finiteFraction (F.blocks n) {g | g ∉ T.covered ∧ ∃ q ∈ Q, q * g ∈ T.covered} < ρ + ε := by
  let M := T.shapes.biUnion (fun S ↦ S.biUnion (fun y ↦ S.image (fun x ↦ y * x⁻¹)))
  let D := M.biUnion (fun d ↦ Q.image (d * ·))
  let A (i : T.index) := tileTranslate (T.shape i) (T.center i)
  have hD (i : T.index) (g : G) (hg : g ∈ externalBoundary Q (A i))
      (y : G) (hy : y ∈ T.core i) : y * g⁻¹ ∈ D := by
    obtain ⟨_, q, hq, hqA⟩ := mem_externalBoundary.mp hg
    have hyS := mem_tileTranslate.mp (T.core_subset i hy)
    have hqS : q * g * (T.center i)⁻¹ ∈ T.shape i := mem_tileTranslate.mp hqA
    let d := (y * (T.center i)⁻¹) * (q * g * (T.center i)⁻¹)⁻¹
    have hd : d ∈ M := Finset.mem_biUnion.mpr ⟨T.shape i, T.shape_mem i,
      Finset.mem_biUnion.mpr ⟨y * (T.center i)⁻¹, hyS, Finset.mem_image.mpr ⟨_, hqS, rfl⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨q, hq, by simp [d, mul_assoc]⟩⟩
  have hSmall (i : T.index) (hi : (T.core i).Nonempty) :
      ((externalBoundary Q (A i)).card : ℝ) ≤ ρ * (T.core i).card := by
    rw [show A i = _ from rfl, externalBoundary_tileTranslate, card_tileTranslate]
    have hs := hShapes (T.shape i) (T.shape_mem i)
    rw [mul_assoc] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (T.core_card i hi) hρ)
  have hCover (g : G) (hg : g ∈ T.covered) : ∃ i, g ∈ T.core i := by
    rw [T.covered_eq, Set.mem_iUnion] at hg
    exact hg
  have h := F.eventually_externalCoverBoundary_le Q D T.covered A T.core T.core_subset T.tile_subset
    hCover T.disjoint_core hD ρ hρ hSmall hε
  filter_upwards [h] with n hn
  have he : finiteFraction (F.blocks n) {g | g ∉ T.covered ∧ ∃ q ∈ Q, q * g ∈ T.covered} =
      (((F.blocks n).filter (fun g ↦ g ∉ T.covered ∧ ∃ q ∈ Q, q * g ∈ T.covered)).card : ℝ) /
        (F.blocks n).card := by
    unfold finiteFraction
    apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / (F.blocks n).card)
    ext g
    simp only [Finset.mem_filter, Set.mem_ofPred_eq]
  rwa [he]

/-- Greedy layers with progressively less invariant shapes give a finite-shape cover
whose uncovered fraction is eventually below the prescribed tolerance. The allowable
shapes can impose additional conditions, provided arbitrarily invariant shapes are available. -/
theorem exists_eventually_cover [Countable G] (F : LeftFolnerSequence G) (allowed : Set (Finset G))
    {η δ : ℝ} (hη : 0 < η) (hη₁ : η < 1) (hδ : 0 < δ)
    (hAvailable : ∀ (Q : Finset G) (ε : ℝ), 0 < ε →
      ∃ S ∈ allowed, S.Nonempty ∧ ((externalBoundary Q S).card : ℝ) ≤ ε * S.card) :
    ∃ T : PartialQuasiTiling G η, (∀ S ∈ T.shapes, S ∈ allowed) ∧
      ∀ᶠ n in atTop, finiteFraction (F.blocks n) T.coveredᶜ < δ := by
  let ρ : ℝ := δ / 8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hOneη : 0 ≤ 1 - η := sub_nonneg.mpr hη₁.le
  have hL (m : ℕ) (Q : Finset G) : ∃ T : PartialQuasiTiling G η,
      (∀ S ∈ T.shapes, S ∈ allowed) ∧
      (∀ S ∈ T.shapes, ((externalBoundary Q S).card : ℝ) ≤ ρ * (1 - η) * S.card) ∧
      ∀ᶠ n in atTop, finiteFraction (F.blocks n) T.coveredᶜ ≤ (1 - η) ^ m + δ / 2 := by
    induction m generalizing Q with
    | zero =>
      let T : PartialQuasiTiling G η := empty
      refine ⟨T, by simp [T, empty], by simp [T, empty], Filter.Eventually.of_forall fun n ↦ ?_⟩
      have hCard : ((F.blocks n).card : ℝ) ≠ 0 := by exact_mod_cast (F.nonempty n).card_ne_zero
      simp only [T, empty, Set.compl_empty, finiteFraction, Set.mem_univ, Finset.filter_true,
        div_self hCard, pow_zero]
      linarith
    | succ m ih =>
      obtain ⟨S, hSAllow, hS, hSBoundary⟩ := hAvailable Q (ρ * (1 - η))
        (mul_pos hρ (sub_pos.mpr hη₁))
      obtain ⟨T, hAllow, hShape, hOldDensity⟩ := ih (Q ∪ S)
      obtain ⟨T', b, hShapes, hUV, hηb, hMaximal⟩ := T.exists_extend S hη.le hη₁.le
      refine ⟨T', ?_, ?_, ?_⟩
      · intro A hA
        rw [hShapes, Finset.mem_insert] at hA
        rcases hA with rfl | hA
        · exact hSAllow
        · exact hAllow A hA
      · intro A hA
        rw [hShapes, Finset.mem_insert] at hA
        rcases hA with rfl | hA
        · exact hSBoundary
        · exact (Nat.cast_le.mpr (Finset.card_le_card
            (externalBoundary_mono Finset.subset_union_left A))).trans (hShape A hA)
      have hShapeOld (A : Finset G) (hA : A ∈ T.shapes) :
          ((externalBoundary S A).card : ℝ) ≤ ρ * (1 - η) * A.card :=
        (Nat.cast_le.mpr (Finset.card_le_card
          (externalBoundary_mono Finset.subset_union_right A))).trans (hShape A hA)
      have hSmallU := T.eventually_externalBoundary F S hρ.le hShapeOld hρ
      have hSmallA := (F.tendsto_leftBoundary S).eventually_lt_const (show 0 < δ / 4 by positivity)
      filter_upwards [hOldDensity, hSmallU, hSmallA] with n hOld hU hA
      have hB := finiteFraction_complement_le_of_greedyLayer S (F.blocks n) hS hUV hη.le hηb hMaximal
      have hFrac : finiteFraction (F.blocks n) {g | ∃ s ∈ S, s * g ∉ F.blocks n} =
          ((leftBoundary S (F.blocks n)).card : ℝ) / (F.blocks n).card := by
        unfold finiteFraction
        apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / (F.blocks n).card)
        ext g
        simp only [Finset.mem_filter, Set.mem_ofPred_eq, mem_leftBoundary]
      rw [hFrac] at hB
      rw [pow_succ]
      calc
        _ ≤ (1 - η) * ((1 - η) ^ m + δ / 2) + η * (δ / 2) := by
          refine hB.trans (add_le_add (mul_le_mul_of_nonneg_left hOld hOneη)
            (mul_le_mul_of_nonneg_left ?_ hη.le))
          dsimp [ρ] at hU
          linarith
        _ = _ := by ring
  have hPow : Tendsto (fun m : ℕ ↦ (1 - η) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hOneη (by linarith)
  obtain ⟨m, hm⟩ := (hPow.eventually_lt_const (half_pos hδ)).exists
  obtain ⟨T, hT, _, hDensity⟩ := hL m ∅
  exact ⟨T, hT, hDensity.mono fun n hn ↦ hn.trans_lt (by linarith)⟩

end PartialQuasiTiling

end SixProblems
