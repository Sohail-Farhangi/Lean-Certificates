/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ErgodicBarycenters
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-! # Ergodicity of an independent product with one mixing coordinate -/

@[expose] public section
noncomputable section

namespace SixProblems

open Set MeasureTheory Filter Mixing
open scoped ENNReal Topology symmDiff

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]

private def measurableRectangles : Set (Set (X × Y)) :=
  image2 (· ×ˢ ·) {U : Set X | MeasurableSet U} {V : Set Y | MeasurableSet V}

private theorem measurableRectangles_isSetSemiring :
    IsSetSemiring (measurableRectangles (X := X) (Y := Y)) := by
  classical
  refine ⟨⟨∅, MeasurableSet.empty, ∅, MeasurableSet.empty, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨U,hU,V,hV,rfl⟩ _ ⟨U',hU',V',hV',rfl⟩
    exact ⟨U ∩ U', hU.inter hU', V ∩ V', hV.inter hV', prod_inter_prod.symm⟩
  · rintro _ ⟨U,hU,V,hV,rfl⟩ _ ⟨U',hU',V',hV',rfl⟩
    let R := (U \ U') ×ˢ V
    let S := (U ∩ U') ×ˢ (V \ V')
    have hR : R ∈ measurableRectangles := ⟨_, hU.diff hU', _, hV, rfl⟩
    have hS : S ∈ measurableRectangles := ⟨_, hU.inter hU', _, hV.diff hV', rfl⟩
    have hd : _root_.Disjoint R S := by
      apply Set.disjoint_left.mpr
      rintro x ⟨hx, _⟩ ⟨hx', _⟩
      exact hx.2 hx'.2
    refine ⟨{R,S}, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_insert, Finset.coe_singleton, insert_subset_iff, singleton_subset_iff]
        using And.intro hR hS
    · rw [Finset.coe_insert, Finset.coe_singleton]
      exact (Set.pairwise_pair.mpr fun _ ↦ ⟨hd, hd.symm⟩)
    · ext x
      simp only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton,
        R, S, mem_union, mem_prod, Set.mem_sdiff, mem_inter_iff]
      tauto

private theorem measureReal_le_one (μ : Measure Y) [IsProbabilityMeasure μ] (A : Set Y) :
    μ.real A ≤ 1 := (measureReal_mono (subset_univ _) (measure_ne_top μ _)).trans_eq (by simp)

/-- Asymptotic independence from a moving rectangle in a product with one
mixing coordinate. Its first-coordinate event can vary arbitrarily. -/
private theorem tendsto_moving_rectangle (S : System G X) (T : System G Y) (g : ℕ → G)
    (hMix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n ↦ T.measure.real (A ∩ T.act (g n) ⁻¹' B)) atTop
        (𝓝 (T.measure.real A * T.measure.real B)))
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (V : Set Y) (hV : MeasurableSet V)
    (A : Set (X × Y)) (hA : MeasurableSet A) :
    let ν := (S.prod T).measure
    Tendsto (fun n ↦ ν.real (A ∩ (U n ×ˢ (T.act (g n) ⁻¹' V))) -
      ν.real (A ∩ (U n ×ˢ univ)) * T.measure.real V) atTop (𝓝 0) := by
  classical
  let ν := (S.prod T).measure
  let F (n : ℕ) := U n ×ˢ (T.act (g n) ⁻¹' V)
  let F₀ (n : ℕ) := U n ×ˢ (univ : Set Y)
  let D (B : Set (X × Y)) (n : ℕ) := ν.real (B ∩ F n) - ν.real (B ∩ F₀ n) * T.measure.real V
  change Tendsto (D A) atTop (𝓝 0)
  have hF n : MeasurableSet (F n) := (hU n).prod ((T.preserves _).measurable hV)
  have hF₀ n : MeasurableSet (F₀ n) := (hU n).prod MeasurableSet.univ
  have hrect {B : Set (X × Y)} (hB : B ∈ measurableRectangles) : Tendsto (D B) atTop (𝓝 0) := by
    obtain ⟨W,hW,Z,hZ,rfl⟩ := hB
    have hz : Tendsto (fun n ↦ T.measure.real (Z ∩ T.act (g n) ⁻¹' V) -
        T.measure.real Z * T.measure.real V) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ ↦ T.measure.real Z * T.measure.real V) atTop
          (𝓝 (T.measure.real Z * T.measure.real V)) := tendsto_const_nhds
      simpa only [sub_self] using (hMix Z V hZ hV).sub hconst
    have hbounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun n ↦ S.measure.real (W ∩ U n)) :=
      ⟨1, eventually_map.mpr (Eventually.of_forall fun n ↦ by
        change ‖S.measure.real (W ∩ U n)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ S.measure.real (W ∩ U n) from ENNReal.toReal_nonneg)]
        exact measureReal_le_one S.measure (W ∩ U n))⟩
    apply (isBoundedUnder_le_mul_tendsto_zero hbounded hz).congr
    intro n
    change _ = (S.measure.prod T.measure).real ((W ×ˢ Z) ∩ F n) -
      (S.measure.prod T.measure).real ((W ×ˢ Z) ∩ F₀ n) * T.measure.real V
    simp only [F, F₀, prod_inter_prod, measureReal_prod_prod, inter_univ]
    ring
  have hfinite {B : Set (X × Y)} (P : Finpartition B)
      (hP : (↑P.parts : Set (Set (X × Y))) ⊆ measurableRectangles) :
      Tendsto (D B) atTop (𝓝 0) := by
    have hsum {C : Set (X × Y)} (hC : MeasurableSet C) :
        ν.real (B ∩ C) = ∑ W ∈ P.parts, ν.real (W ∩ C) := by
      have hd := (Finset.supIndep_iff_pairwiseDisjoint.mp P.supIndep).mono
        (fun (W : Set (X × Y)) ↦ inter_subset_left (s := W) (t := C))
      have hmeas : ∀ W ∈ P.parts, MeasurableSet (W ∩ C) := by
        intro W hW
        obtain ⟨L,hL,R,hR,rfl⟩ := hP hW
        exact (hL.prod hR).inter hC
      have he : B ∩ C = ⋃ W ∈ P.parts, W ∩ C := calc
        B ∩ C = P.parts.sup id ∩ C := congrArg (· ∩ C) P.sup_parts.symm
        _ = _ := by
          rw [Finset.sup_id_set_eq_sUnion, sUnion_eq_biUnion, iUnion₂_inter]
          simp only [Finset.mem_coe]
      rw [he]
      exact measureReal_biUnion_finset hd hmeas
    have hl := tendsto_finsetSum P.parts (fun W hW ↦ hrect (hP hW))
    simp only [Finset.sum_const_zero] at hl
    apply hl.congr
    intro n
    simp only [D, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum (hF n), hsum (hF₀ n)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε₀ : 0 < ε / 3 := by positivity
  have hcover : ∃ C : Set (Set (X × Y)), C.Countable ∧ C ⊆ measurableRectangles ∧
      ν (⋃₀ C)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr ?_, by simp⟩
    exact ⟨univ, MeasurableSet.univ, univ, MeasurableSet.univ, univ_prod_univ⟩
  obtain ⟨B, hB, hclose⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    (μ := ν) measurableRectangles_isSetSemiring hcover generateFrom_prod.symm hA
      (ENNReal.ofReal_pos.mpr hε₀)
  obtain ⟨P,hP⟩ := measurableRectangles_isSetSemiring.mem_supClosure_iff.mp hB
  have hBm := measurableSet_generateFrom_of_mem_supClosure hB
  rw [show MeasurableSpace.generateFrom measurableRectangles =
    (inferInstance : MeasurableSpace (X × Y)) from generateFrom_prod] at hBm
  have hdiff {C : Set (X × Y)} (hC : MeasurableSet C) :
      |ν.real (A ∩ C) - ν.real (B ∩ C)| ≤ ν.real (B ∆ A) := by
    have hsub : (A ∩ C) ∆ (B ∩ C) ⊆ B ∆ A := by
      intro x
      simp only [symmDiff_def, mem_union, Set.mem_sdiff, mem_inter_iff]
      tauto
    exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
      (hA.inter hC).nullMeasurableSet (hBm.inter hC).nullMeasurableSet).trans (measureReal_mono hsub)
  have hclose' : ν.real (B ∆ A) < ε / 3 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hclose
    rwa [ENNReal.toReal_ofReal hε₀.le] at h
  filter_upwards [(Metric.tendsto_nhds.mp (hfinite P hP)) _ hε₀] with n hn
  rw [Real.dist_eq, sub_zero] at hn ⊢
  have hcoef : 0 ≤ T.measure.real V := ENNReal.toReal_nonneg
  have herror : |D A n - D B n| ≤ ν.real (B ∆ A) + ν.real (B ∆ A) := by
    calc
      _ = |(ν.real (A ∩ F n) - ν.real (B ∩ F n)) -
          (ν.real (A ∩ F₀ n) - ν.real (B ∩ F₀ n)) * T.measure.real V| := by
        congr 1
        dsimp [D]
        ring
      _ ≤ |ν.real (A ∩ F n) - ν.real (B ∩ F n)| +
          |(ν.real (A ∩ F₀ n) - ν.real (B ∩ F₀ n)) * T.measure.real V| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le _ (0 : ℝ) _
      _ ≤ ν.real (B ∆ A) + ν.real (B ∆ A) := by
        refine add_le_add (hdiff (hF n)) ?_
        rw [abs_mul, abs_of_nonneg hcoef]
        exact (mul_le_mul_of_nonneg_right (hdiff (hF₀ n)) hcoef).trans
          (mul_le_of_le_one_right ENNReal.toReal_nonneg (measureReal_le_one T.measure V))
  calc
    |D A n| ≤ |D A n - D B n| + |D B n| := by simpa only [sub_zero] using abs_sub_le (D A n) (D B n) 0
    _ ≤ ν.real (B ∆ A) + ν.real (B ∆ A) + |D B n| := add_le_add herror le_rfl
    _ < ε := by linarith

private theorem invariant_measure_rect (S : System G X) (T : System G Y) (g : ℕ → G)
    (hMix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n ↦ T.measure.real (A ∩ T.act (g n) ⁻¹' B)) atTop
        (𝓝 (T.measure.real A * T.measure.real B)))
    {A : Set (X × Y)} (hA : MeasurableSet A)
    (hInv : ∀ k, (S.prod T).act k ⁻¹' A =ᵐ[(S.prod T).measure] A)
    {U : Set X} {V : Set Y} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    let ν := (S.prod T).measure
    ν (A ∩ (U ×ˢ V)) = ν (A ∩ (U ×ˢ univ)) * T.measure V := by
  let P := S.prod T
  let ν := P.measure
  let Uₙ (n : ℕ) := S.act (g n) ⁻¹' U
  have hUₙ n : MeasurableSet (Uₙ n) := (S.preserves _).measurable hU
  have hmeasure (k : G) {F : Set (X × Y)} (hF : MeasurableSet F) :
      ν.real (A ∩ F) = ν.real (A ∩ P.act k ⁻¹' F) := by
    have hpres := (P.preserves k).measure_preimage (hA.inter hF).nullMeasurableSet
    have hd : P.act k ⁻¹' (A ∩ F) =ᵐ[ν] A ∩ P.act k ⁻¹' F := by
      filter_upwards [hInv k] with x hx
      change (P.act k x ∈ A ∧ P.act k x ∈ F) ↔ (x ∈ A ∧ P.act k x ∈ F)
      exact and_congr_left' hx
    exact congrArg ENNReal.toReal (hpres.symm.trans (measure_congr hd))
  have hEquiv (n : ℕ) : ν.real (A ∩ (Uₙ n ×ˢ (T.act (g n) ⁻¹' V))) -
      ν.real (A ∩ (Uₙ n ×ˢ univ)) * T.measure.real V =
      ν.real (A ∩ (U ×ˢ V)) - ν.real (A ∩ (U ×ˢ univ)) * T.measure.real V := by
    rw [hmeasure (g n) (hU.prod hV), hmeasure (g n) (hU.prod MeasurableSet.univ)]
    rfl
  have hl := (tendsto_moving_rectangle S T g hMix Uₙ hUₙ V hV A hA).congr hEquiv
  have he := sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hl)
  have h := congrArg ENNReal.ofReal he
  change ENNReal.ofReal (ν (A ∩ (U ×ˢ V))).toReal =
    ENNReal.ofReal ((ν (A ∩ (U ×ˢ univ))).toReal * (T.measure V).toReal) at h
  change ν (A ∩ (U ×ˢ V)) = ν (A ∩ (U ×ˢ univ)) * T.measure V
  rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal (measure_ne_top ν _),
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (measure_ne_top ν _) (measure_ne_top T.measure _))] at h
  exact h

/-- The product with an ergodic system is ergodic when all measurable event
correlations in the other system converge to independence along one sequence. -/
theorem prod_isErgodic_of_eventMixing (S : System G X) (T : System G Y) (hS : S.IsErgodic)
    (g : ℕ → G) (hMix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n ↦ T.measure.real (A ∩ T.act (g n) ⁻¹' B)) atTop
        (𝓝 (T.measure.real A * T.measure.real B))) :
    (S.prod T).IsErgodic := by
  intro A hA hInv
  let P := S.prod T
  let ν := P.measure
  let ρ := ν.restrict A
  let η := ρ.map Prod.fst
  have hρ₁ (k : G) : MeasurePreserving (P.act k) ρ ρ := by
    have h := (P.preserves k).restrict_preimage hA
    have hr : ν.restrict (P.act k ⁻¹' A) = ρ := Measure.restrict_congr_set (hInv k)
    rwa [hr] at h
  have hη₁ (k : G) : MeasurePreserving (S.act k) η η := by
    refine ⟨(S.preserves k).measurable, ?_⟩
    have hcomp : S.act k ∘ Prod.fst = Prod.fst ∘ P.act k := rfl
    change (ρ.map Prod.fst).map (S.act k) = η
    rw [Measure.map_map (S.preserves k).measurable measurable_fst, hcomp,
      ← Measure.map_map measurable_fst (hρ₁ k).measurable, (hρ₁ k).map_eq]
  have hη_le : η ≤ S.measure := by
    calc
      η ≤ ν.map Prod.fst := Measure.map_mono Measure.restrict_le_self measurable_fst
      _ = S.measure := by
        change (S.measure.prod T.measure).map Prod.fst = S.measure
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hη_eq := S.eq_smul_of_invariant_absolutelyContinuous hS η hη₁ hη_le.absolutelyContinuous
  have hη_univ : η univ = ν A := by
    change ρ.map Prod.fst univ = _
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
  have hProd : ρ = η.prod T.measure := by
    apply Measure.ext_prod
    intro U V hU hV
    have hη_apply : η U = ν (A ∩ (U ×ˢ univ)) := by
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU), inter_comm]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    rw [Measure.prod_prod, hη_apply, Measure.restrict_apply (hU.prod hV), inter_comm]
    exact invariant_measure_rect S T g hMix hA hInv hU hV
  have hρ_eq : ρ = ν A • ν := by
    rw [hProd, hη_eq, hη_univ, Measure.prod_smul_left]
    rfl
  have hzero := congrArg (fun q : Measure (X × Y) ↦ q Aᶜ) hρ_eq
  change (ν.restrict A) Aᶜ = (ν A • ν) Aᶜ at hzero
  rw [Measure.restrict_apply hA.compl, compl_inter_self, measure_empty, smul_apply, smul_eq_mul] at hzero
  change Filter.EventuallyEmptyOrUniv A (ae ν)
  apply eventuallyEmptyOrUniv_iff.mpr
  rcases mul_eq_zero.mp hzero.symm with h | h
  · exact Or.inr (by simpa [ae_iff] using h)
  · exact Or.inl (ae_iff.mpr h)

end SixProblems
