module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

namespace Mixing

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal symmDiff

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private def rectangles (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] :
    Set (Set (X × Y)) :=
  Set.image2 (· ×ˢ ·) {A : Set X | MeasurableSet A} {B : Set Y | MeasurableSet B}

private theorem rectangles_isSetSemiring : IsSetSemiring (rectangles X Y) := by
  classical
  constructor
  · exact ⟨∅, MeasurableSet.empty, univ, MeasurableSet.univ, empty_prod⟩
  · rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨C, hC, D, hD, rfl⟩
    exact ⟨A ∩ C, hA.inter hC, B ∩ D, hB.inter hD, prod_inter_prod.symm⟩
  · rintro _ ⟨A, hA, B, hB, rfl⟩ _ ⟨C, hC, D, hD, rfl⟩
    let L := (A \ C) ×ˢ B
    let R := (A ∩ C) ×ˢ (B \ D)
    have hd : _root_.Disjoint L R := by
      refine Set.disjoint_left.2 ?_
      intro w hw₁ hw₂
      exact hw₁.1.2 hw₂.1.2
    have hL : L ∈ rectangles X Y := ⟨_, hA.diff hC, B, hB, rfl⟩
    have hR : R ∈ rectangles X Y := ⟨_, hA.inter hC, _, hB.diff hD, rfl⟩
    refine ⟨{L, R}, ?_, ?_, ?_⟩
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hL
      · exact hR
    · intro s hs t ht hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hs ht
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
      · exact (hne rfl).elim
      · exact hd
      · exact hd.symm
      · exact (hne rfl).elim
    · simp only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton]
      ext w
      change (w.1 ∈ A ∧ w.2 ∈ B) ∧ ¬ (w.1 ∈ C ∧ w.2 ∈ D) ↔
        ((w.1 ∈ A ∧ w.1 ∉ C) ∧ w.2 ∈ B) ∨ ((w.1 ∈ A ∧ w.1 ∈ C) ∧ w.2 ∈ B ∧ w.2 ∉ D)
      tauto

private theorem measure_le_add_measure_symmDiff
    {W : Type*} [MeasurableSpace W] (μ : Measure W) (A B : Set W) :
    μ A ≤ μ B + μ (A ∆ B) :=
  (measure_mono (show A ⊆ B ∪ (A ∆ B) from fun x hx ↦ by
    by_cases h : x ∈ B
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hx, h⟩))).trans (measure_union_le _ _)

/-- Domination between finite measures on a product can be tested on measurable
rectangles. The semiring approximation uses the sum of the two measures. -/
theorem measure_le_of_rectangles {μ ν : Measure (X × Y)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ A B, MeasurableSet A → MeasurableSet B → μ (A ×ˢ B) ≤ ν (A ×ˢ B)) :
    μ ≤ ν := by
  let C := rectangles X Y
  have hC : IsSetSemiring C := rectangles_isSetSemiring
  have hMeas : ∀ A ∈ C, MeasurableSet A := by
    rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hA.prod hB
  have hbound : ∀ A ∈ supClosure C, μ A ≤ ν A := by
    intro A hA
    obtain ⟨P, hP⟩ := hC.mem_supClosure_iff.mp hA
    rw [← P.sup_parts, Finset.sup_set_eq_biUnion, measure_biUnion_finset P.disjoint
      (fun B hB ↦ hMeas B (hP hB)), measure_biUnion_finset P.disjoint
      (fun B hB ↦ hMeas B (hP hB))]
    apply Finset.sum_le_sum
    intro B hB
    obtain ⟨E, hE, F, hF, rfl⟩ := hP hB
    exact h E F hE hF
  apply Measure.le_iff.mpr
  intro A hA
  have hcover : ∃ D : Set (Set (X × Y)), D.Countable ∧ D ⊆ C ∧
      (μ + ν) (⋃₀ D)ᶜ = 0 := by
    exact ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr
      ⟨univ, MeasurableSet.univ, univ, MeasurableSet.univ, univ_prod_univ⟩, by simp⟩
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  by_contra! hbad
  let e := (μ.real A - ν.real A) / 2
  have he : 0 < e := by
    change 0 < ((μ A).toReal - (ν A).toReal) / 2
    linarith
  obtain ⟨B, hB, hε⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    (μ := μ + ν) hC hcover generateFrom_prod.symm hA (ENNReal.ofReal_pos.mpr he)
  have hb := ENNReal.toReal_mono (measure_ne_top ν B) (hbound B hB)
  have hμ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ B, measure_ne_top μ _⟩)
    (measure_le_add_measure_symmDiff μ A B)
  have hν := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top ν A, measure_ne_top ν _⟩)
    (measure_le_add_measure_symmDiff ν B A)
  have hδ := (ENNReal.toReal_lt_toReal (measure_ne_top (μ + ν) _) ENNReal.ofReal_ne_top).mpr hε
  rw [add_apply, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top ν _),
    ENNReal.toReal_ofReal he.le] at hδ
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), symmDiff_comm A B] at hμ
  rw [ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)] at hν
  simp only [measureReal_def, e] at he hbad hδ
  linarith

end Mixing
