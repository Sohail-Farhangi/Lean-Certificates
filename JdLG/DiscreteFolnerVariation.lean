/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.FolnerBanachDensities
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Total-variation defect of a finite counting block

A translation need only be a function, possibly identifying points of the
block. Choose one preimage for each point common to the original block and
its translated image. These paired terms cancel in the difference of the
averages. The remaining terms attain the total-variation bound when tested
by the sign of the complement of the translated image in the original block.
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ENNReal Topology symmDiff

namespace JdLG

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Integration over a normalized finite counting block equals its ordinary
finite average. -/
theorem integral_normalizedCountingBlock (F : Finset S) (g : S → ℝ) :
    (∫ s, g s ∂normalizedRestrictedMeasure Measure.count (F : Set S)) =
      (∑ s ∈ F, g s) / (F.card : ℝ) := by
  have hi : IntegrableOn g (F : Set S) Measure.count := by
    rw [← (F : Set S).biUnion_of_singleton]
    apply integrableOn_finset_iUnion.2
    intro s _
    exact integrableOn_singleton (by finiteness) (by rw [Measure.count_singleton]; norm_num)
  rw [normalizedRestrictedMeasure_integral_eq_div, setIntegral_finset _ hi,
    Measure.real, Measure.count_apply_finset, ENNReal.toReal_natCast]
  simp only [count_real_singleton, one_smul]

variable [DecidableEq S]

omit [DecidableEq S] in
/-- A nonempty finite counting block gives a probability measure. -/
theorem normalizedCountingBlock_probability (F : Finset S) (hF : F.Nonempty) :
    IsProbabilityMeasure (normalizedRestrictedMeasure Measure.count (F : Set S)) :=
  normalizedRestrictedMeasure_probability Measure.count
    (by rw [Measure.count_apply_finset]; exact_mod_cast hF.card_ne_zero)
    (by rw [Measure.count_apply_finset]; exact ENNReal.natCast_ne_top _)

/-- The total-variation norm, expressed as the maximum normalized integral
defect over all real measurable tests of norm at most one, is twice the
proportion of the original finite block missing from its translated image. -/
theorem isGreatest_countingBlock_translation_defect
    (F : Finset S) (hF : F.Nonempty) (t : S → S) :
    let ν := normalizedRestrictedMeasure Measure.count (F : Set S)
    IsGreatest {r : ℝ | ∃ g : S → ℝ, Measurable g ∧ (∀ s, ‖g s‖ ≤ 1) ∧
      ‖(∫ s, g (t s) ∂ν) - ∫ s, g s ∂ν‖ = r}
      (2 * ((F \ F.image t).card : ℝ) / (F.card : ℝ)) := by
  classical
  let : Nonempty S := ⟨hF.choose⟩
  let G := F ∩ F.image t
  let u := invFunOn t (F : Set S)
  let P := G.image u
  let D := F \ F.image t
  have hinv (y : S) (hy : y ∈ G) : u y ∈ F ∧ t (u y) = y := by
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hy).2
    exact invFunOn_pos ⟨x, hx, hxy⟩
  have hinj : Set.InjOn u (G : Set S) := by
    intro x hx y hy he
    rw [← (hinv x hx).2, ← (hinv y hy).2, he]
  have hPF : P ⊆ F := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact (hinv y hy).1
  have hG : F \ G = D := Finset.sdiff_inter_self_left _ _
  have hc : (F \ P).card = D.card := by
    rw [← hG, Finset.card_sdiff_of_subset hPF,
      Finset.card_sdiff_of_subset Finset.inter_subset_left,
      Finset.card_image_of_injOn hinj]
  have hsum (g : S → ℝ) : (∑ x ∈ F, g (t x)) - (∑ x ∈ F, g x) =
      (∑ x ∈ F \ P, g (t x)) - (∑ x ∈ D, g x) := by
    have hs : (∑ x ∈ P, g (t x)) = ∑ y ∈ G, g y := by
      change (∑ x ∈ G.image u, g (t x)) = _
      rw [Finset.sum_image (fun x hx y hy hxy ↦ hinj hx hy hxy)]
      exact Finset.sum_congr rfl (fun y hy ↦ congrArg g (hinv y hy).2)
    rw [← hG]
    linarith [Finset.sum_sdiff (f := fun x ↦ g (t x)) hPF,
      Finset.sum_sdiff (f := g) (Finset.inter_subset_left : G ⊆ F)]
  have hn (g : S → ℝ) :
      ‖(∫ s, g (t s) ∂normalizedRestrictedMeasure Measure.count (F : Set S)) -
        ∫ s, g s ∂normalizedRestrictedMeasure Measure.count (F : Set S)‖ =
      ‖(∑ x ∈ F \ P, g (t x)) - ∑ x ∈ D, g x‖ / (F.card : ℝ) := by
    rw [integral_normalizedCountingBlock, integral_normalizedCountingBlock,
      ← sub_div, hsum g, norm_div, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hb (K : Finset S) (g : S → ℝ) (hg : ∀ x, ‖g x‖ ≤ 1) :
      ‖∑ s ∈ K, g s‖ ≤ (K.card : ℝ) := calc
    _ ≤ ∑ s ∈ K, ‖g s‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ K, (1 : ℝ) := Finset.sum_le_sum fun s _ ↦ hg s
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  constructor
  · let g (s : S) : ℝ := if s ∈ D then -1 else 1
    refine ⟨g, Measurable.of_discrete, fun s ↦ ?_, ?_⟩
    · by_cases hs : s ∈ D <;> simp [g, hs]
    · rw [hn]
      have hpos : (∑ x ∈ F \ P, g (t x)) = ((F \ P).card : ℝ) := by
        calc
          _ = ∑ _x ∈ F \ P, (1 : ℝ) := Finset.sum_congr rfl fun x hx ↦ by
            have ht : t x ∈ F.image t := Finset.mem_image_of_mem t (Finset.mem_sdiff.1 hx).1
            have hd : t x ∉ D := fun h ↦ (Finset.mem_sdiff.1 h).2 ht
            simp [g, hd]
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hneg : (∑ x ∈ D, g x) = -(D.card : ℝ) := by
        calc
          _ = ∑ _x ∈ D, (-1 : ℝ) := Finset.sum_congr rfl fun x hx ↦ by simp [g, hx]
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      rw [hpos, hneg, hc, sub_neg_eq_add,
        Real.norm_of_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      congr 1
      ring
  · rintro r ⟨g, _, hg, rfl⟩
    rw [hn]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    have h₁ := hb (F \ P) (g ∘ t) (fun x ↦ hg (t x))
    have h₂ := hb D g hg
    change ‖∑ x ∈ F \ P, g (t x)‖ ≤ ((F \ P).card : ℝ) at h₁
    rw [hc] at h₁
    change _ ≤ 2 * (D.card : ℝ)
    linarith

omit [DiscreteMeasurableSpace S] [DecidableEq S] in
private theorem integral_sign_indicator (ν : Measure S) [IsProbabilityMeasure ν]
    {A : Set S} (hA : MeasurableSet A) :
    (∫ s, 2 * A.indicator (fun _ ↦ (1 : ℝ)) s - 1 ∂ν) = 2 * ν.real A - 1 := by
  have hI := (integrable_const (1 : ℝ) : Integrable (fun _ : S ↦ (1 : ℝ)) ν).indicator hA
  rw [integral_sub (hI.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_indicator hA, setIntegral_const, integral_const, smul_eq_mul, smul_eq_mul,
    probReal_univ, one_mul, mul_one]

/-- The Hahn–Jordan total variation of the difference between the
translated counting probability and the original counting probability. -/
theorem countingBlock_totalVariation_map_sub
    (F : Finset S) (hF : F.Nonempty) (t : S → S) :
    let ν := normalizedRestrictedMeasure Measure.count (F : Set S)
    letI : IsProbabilityMeasure ν := normalizedCountingBlock_probability F hF
    ((ν.map t).toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ =
      2 * ((F \ F.image t).card : ℝ) / (F.card : ℝ) := by
  classical
  let ν := normalizedRestrictedMeasure Measure.count (F : Set S)
  have hcount : IsProbabilityMeasure ν := normalizedCountingBlock_probability F hF
  let : IsProbabilityMeasure ν := hcount
  let θ := ν.map t
  have htm : Measurable t := Measurable.of_discrete
  let : IsProbabilityMeasure θ := (Measure.isProbabilityMeasure_map_iff htm.aemeasurable).2 hcount
  let σ := θ.toSignedMeasure - ν.toSignedMeasure
  let D := F \ F.image t
  have hσ (A : Set S) : σ A = θ.real A - ν.real A :=
    Measure.toSignedMeasure_sub_apply MeasurableSet.of_discrete
  have hsum (A : Set S) : σ A + σ Aᶜ = 0 := by
    rw [← σ.of_union disjoint_compl_right MeasurableSet.of_discrete MeasurableSet.of_discrete,
      union_compl_self, hσ, probReal_univ, probReal_univ, sub_self]
  change σ.totalVariation.real univ = 2 * (D.card : ℝ) / (F.card : ℝ)
  apply le_antisymm
  · obtain ⟨A, hA, hAp, hAn, hpos, hneg⟩ := σ.toJordanDecomposition_spec
    have hvar : σ.totalVariation.real univ = 2 * σ A := by
      rw [SignedMeasure.totalVariation, measureReal_add_apply, hpos, hneg,
        σ.toMeasureOfZeroLE_real_apply hAp hA MeasurableSet.univ,
        σ.toMeasureOfLEZero_real_apply hAn hA.compl MeasurableSet.univ, inter_univ, inter_univ]
      linarith [hsum A]
    let g (s : S) : ℝ := 2 * A.indicator (fun _ ↦ (1 : ℝ)) s - 1
    have hg (s : S) : ‖g s‖ ≤ 1 := by
      by_cases hs : s ∈ A <;> norm_num [g, hs]
    have he : ‖(∫ s, g (t s) ∂ν) - ∫ s, g s ∂ν‖ = σ.totalVariation.real univ := by
      have hgm : Measurable g := Measurable.of_discrete
      rw [← integral_map htm.aemeasurable hgm.aestronglyMeasurable]
      change ‖(∫ s, g s ∂θ) - ∫ s, g s ∂ν‖ = _
      dsimp only [g]
      rw [integral_sign_indicator θ hA, integral_sign_indicator ν hA, hvar, hσ]
      have hpos' := σ.nonneg_of_zero_le_restrict hAp
      rw [hσ] at hpos'
      rw [Real.norm_of_nonneg (by linarith)]
      ring
    exact (isGreatest_countingBlock_translation_defect F hF t).2
      ⟨g, Measurable.of_discrete, hg, he⟩
  · let B : Set S := D
    have hB : MeasurableSet B := MeasurableSet.of_discrete
    have hBD (s : S) (hs : s ∈ F) : t s ∉ B :=
      fun hd ↦ (Finset.mem_sdiff.1 hd).2 (Finset.mem_image_of_mem t hs)
    have hθB : θ.real B = 0 := by
      rw [Measure.real, Measure.map_apply htm hB]
      have hpre : (t ⁻¹' B) ∩ (F : Set S) = ∅ :=
        eq_empty_iff_forall_notMem.2 fun s hs ↦ hBD s hs.2 hs.1
      change (normalizedRestrictedMeasure Measure.count (F : Set S) (t ⁻¹' B)).toReal = 0
      rw [normalizedRestrictedMeasure, smul_apply, Measure.restrict_apply (htm hB), hpre,
        measure_empty, smul_zero, ENNReal.toReal_zero]
    have hνB : ν.real B = (D.card : ℝ) / (F.card : ℝ) := by
      rw [normalizedRestrictedMeasure_real_eq_div Measure.count (F : Set S) hB,
        inter_eq_left.2 (show B ⊆ (F : Set S) from Finset.sdiff_subset)]
      simp only [B, Measure.real, Measure.count_apply_finset, ENNReal.toReal_natCast]
    have hsB : σ B = -ν.real B := by rw [hσ, hθB, zero_sub]
    have hsBc : σ Bᶜ = ν.real B := by linarith [hsum B]
    have hm := add_le_add (σ.norm_le_totalVariation B) (σ.norm_le_totalVariation Bᶜ)
    rw [hsB, hsBc, norm_neg, Real.norm_of_nonneg measureReal_nonneg,
      measureReal_add_measureReal_compl hB, hνB] at hm
    rwa [mul_div_assoc, two_mul]

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- For an injective translation the symmetric-difference cardinality is
twice the number of points missing from the translated image. -/
theorem card_symmDiff_image_eq_two_mul_sdiff
    (F : Finset S) {t : S → S} (ht : Injective t) :
    (F ∆ F.image t).card = 2 * (F \ F.image t).card := by
  have hd : Disjoint (F \ F.image t) (F.image t \ F) :=
    Finset.disjoint_left.2 fun _ hx hy ↦ (Finset.mem_sdiff.1 hx).2 (Finset.mem_sdiff.1 hy).1
  have hc : (F \ F.image t).card = (F.image t \ F).card :=
    Finset.card_sdiff_eq_card_sdiff_iff.2 (Finset.card_image_of_injective F ht).symm
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd, ← hc, two_mul]

variable {I : Type*} [Semigroup S]

/-- For counting measure, the left Følner probability condition is equivalent
to the strong Følner condition given by the proportion missing from the
left-translated block. No cancellation assumption is needed. -/
theorem leftFolnerProbabilities_counting_iff_strongFolner
    (F : I → Finset S) (hF : ∀ i, (F i).Nonempty) (l : Filter I) :
    LeftFolnerProbabilities
      (fun i ↦ normalizedRestrictedMeasure Measure.count (F i : Set S)) l ↔
    ∀ s : S, Tendsto (fun i ↦ ((F i \ (F i).image (s * ·)).card : ℝ) / (F i).card)
      l (𝓝 0) := by
  let ν (i : I) := normalizedRestrictedMeasure Measure.count (F i : Set S)
  let d (s : S) (i : I) := ((F i \ (F i).image (s * ·)).card : ℝ) / (F i).card
  have hnonneg (s : S) (i : I) : 0 ≤ d s i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmax (s : S) (i : I) := isGreatest_countingBlock_translation_defect (F i) (hF i) (s * ·)
  constructor
  · intro h s
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    filter_upwards [h s (2 * ε) (by positivity)] with i hi
    obtain ⟨g, hg, hgn, he⟩ := (hmax s i).1
    have hb := hi g hg hgn
    change ‖(∫ x, g (s * x) ∂ν i) - ∫ x, g x ∂ν i‖ = _ at he
    rw [he, mul_div_assoc] at hb
    change 2 * d s i < 2 * ε at hb
    change dist (d s i) 0 < ε
    rw [dist_zero_right, Real.norm_of_nonneg (hnonneg s i)]
    linarith
  · intro h s ε hε
    filter_upwards [Metric.tendsto_nhds.1 (h s) (ε / 2) (by positivity)] with i hi g hg hgn
    change dist (d s i) 0 < ε / 2 at hi
    rw [dist_zero_right, Real.norm_of_nonneg (hnonneg s i)] at hi
    have hb := (hmax s i).2 ⟨g, hg, hgn, rfl⟩
    rw [mul_div_assoc] at hb
    exact hb.trans_lt (show 2 * d s i < ε by linarith)

end JdLG
