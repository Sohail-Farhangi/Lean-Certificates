/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceCylinder
public import SixProblems.CorrespondenceSampling

@[expose] public section

namespace SixProblems

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical Topology ProbabilityTheory

section LocalPatterns

variable {G : Type*} [Group G] [DecidableEq G]

/-- Points in the block whose test coordinates cross a boundary of the partition. -/
def tileTestBoundary (P : BoundedTilePartition G) (D A : Finset G) : Finset G :=
  A.filter fun g ↦ g ∈ leftBoundary D (P.cell g)

/-- Cells crossing the block boundary are detected by the finitely many
    possible displacements inside a partition cell. -/
theorem tileBoundary_subset_displacements (P : BoundedTilePartition G) (A : Finset G) :
    tileBoundary P.cell A ⊆ leftBoundary P.displacements A := by
  intro g hg
  obtain ⟨hgA, hgP⟩ := Finset.mem_filter.mp hg
  obtain ⟨a, ha, haA⟩ := Finset.not_subset.mp hgP
  exact mem_leftBoundary.mpr ⟨hgA, a*g⁻¹, P.mem_displacements ha, by simpa using haA⟩

/-- The test boundary is bounded by the bad sites, the sites in incomplete
    cells, and the sum of the internal boundaries of the remaining cells. -/
theorem tileTestBoundary_card_le (P : BoundedTilePartition G) (D A : Finset G)
    (bad : Set G) (η : ℝ) (hη : 0 ≤ η)
    (hRel : ∀ a ∉ bad, ((leftBoundary D (P.cell a)).card : ℝ) ≤ η * (P.cell a).card) :
    ((tileTestBoundary P D A).card : ℝ) ≤
      ((A.filter (· ∈ bad)).card : ℝ) + (leftBoundary P.displacements A).card + η * A.card := by
  let R := (A.filter fun g ↦ g ∉ bad ∧ P.cell g ⊆ A).image P.cell
  have hDisjoint : (↑R : Set (Finset G)).PairwiseDisjoint id := by
    intro U hU V hV hUV
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hV
    exact Finset.disjoint_left.mpr fun a hua hva ↦ hUV ((P.cell_eq hua).symm.trans (P.cell_eq hva))
  have hCover : R.biUnion id ⊆ A := by
    intro a ha
    obtain ⟨U, hU, haU⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hU
    exact (Finset.mem_filter.mp hu).2.2 haU
  have hSum : ∑ U ∈ R, (U.card : ℝ) ≤ A.card := by
    have he := Finset.card_biUnion hDisjoint
    simp only [id_eq] at he
    rw [← Nat.cast_sum, ← he]
    exact_mod_cast Finset.card_le_card hCover
  have hInternal : ((R.biUnion (leftBoundary D)).card : ℝ) ≤ η * A.card := calc
    _ ≤ ∑ U ∈ R, ((leftBoundary D U).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ U ∈ R, η * (U.card : ℝ) := by
      apply Finset.sum_le_sum
      intro U hU
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hU
      exact hRel u (Finset.mem_filter.mp hu).2.1
    _ ≤ η * A.card := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hSum hη
  have hSite : tileTestBoundary P D A ⊆
      ((A.filter (· ∈ bad)) ∪ leftBoundary P.displacements A) ∪ R.biUnion (leftBoundary D) := by
    intro a ha
    obtain ⟨haA, haD⟩ := Finset.mem_filter.mp ha
    by_cases hb : a ∈ bad
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haA, hb⟩))
    by_cases hP : P.cell a ⊆ A
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨P.cell a, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨haA, hb, hP⟩), haD⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (tileBoundary_subset_displacements P A (Finset.mem_filter.mpr ⟨haA, hP⟩)))
  refine le_trans ?_ (add_le_add le_rfl hInternal)
  norm_cast
  exact (Finset.card_le_card hSite).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))

set_option maxHeartbeats 1000000 in
/-- Glue independent configurations on the cells meeting a finite block. The
    variance term depends on the largest cell, while the deterministic error
    comes from the sites whose test coordinates cross cell boundaries. -/
theorem exists_localPattern_of_tileVariance {K I : Type*}
    [MeasurableSpace K] [Nonempty K] [Fintype I]
    (μ : Measure (G → K)) [IsProbabilityMeasure μ] (P : BoundedTilePartition G)
    (A : Finset G) (hA : A.Nonempty) (M : ℕ) (hM : ∀ a ∈ A, (P.cell a).card ≤ M)
    (D : I → Finset G) (q : I → (G → K) → G → ℝ) (C : I → ℝ)
    (hBound : ∀ i x a, ‖q i x a‖ ≤ C i)
    (hMeas : ∀ i a, Measurable (fun x ↦ q i x a))
    (hMean : ∀ i a, (∫ x, q i x a ∂μ) = 0)
    (hLocal : ∀ i x y a, (∀ d ∈ D i, x (d*a) = y (d*a)) → q i x a = q i y a)
    (ε : ℝ) (hε : 0 < ε) (hSmall : (M : ℝ) * (∑ i, C i ^ 2) < (A.card : ℝ) * ε ^ 2) :
    ∃ x : G → K, ∀ i,
      ‖finiteAverage A (q i x)‖ <
        ε + ((tileTestBoundary P (D i) A).card : ℝ) / A.card * (2 * C i) := by
  let B := A.image P.cell
  let : DecidableEq B := inferInstance
  let label (a : A) : B := ⟨P.cell a, Finset.mem_image_of_mem _ a.property⟩
  have hFiber (b : B) : (Finset.univ.filter (fun a ↦ label a = b)).card ≤ M := by
    obtain ⟨g, hg, hgb⟩ := Finset.mem_image.mp b.property
    have hSub (a : A) (ha : a ∈ Finset.univ.filter (fun a ↦ label a = b)) :
        (a : G) ∈ P.cell g := by
      have he : P.cell a = P.cell g :=
        (congrArg Subtype.val (Finset.mem_filter.mp ha).2).trans hgb.symm
      rw [← he]
      exact P.mem_cell a
    exact (Finset.card_le_card_of_injOn Subtype.val hSub Subtype.val_injective.injOn).trans (hM g hg)
  have hcard : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hCount : (Fintype.card A : ℝ) * M * (∑ i, C i ^ 2) < (ε * (A.card : ℝ)) ^ 2 := by
    have h := mul_lt_mul_of_pos_left hSmall hcard
    rw [Fintype.card_coe]
    convert h using 1 <;> ring
  obtain ⟨y, hy⟩ := exists_small_groupedSums μ label (fun i (a : A) x ↦ q i x a) C
    (fun i a x ↦ hBound i x a) (fun i a ↦ hMeas i a) (fun i a ↦ hMean i a)
    M hFiber (ε * A.card) (mul_pos hε hcard) hCount
  let x (g : G) := if hg : P.cell g ∈ B then y ⟨P.cell g, hg⟩ g else Classical.choice ‹Nonempty K›
  refine ⟨x, fun i ↦ ?_⟩
  let E := tileTestBoundary P (D i) A
  let total := ∑ a : A, q i (y (label a)) a
  have hAgree (a : A) (ha : (a : G) ∉ E) : q i x a = q i (y (label a)) a := by
    apply hLocal
    intro d hd
    have hg : d * (a : G) ∈ P.cell a := by
      by_contra h
      exact ha (Finset.mem_filter.mpr ⟨a.property,
        mem_leftBoundary.mpr ⟨P.mem_cell a, d, hd, h⟩⟩)
    have he := P.cell_eq hg
    have hb : P.cell (d * (a : G)) ∈ B := he.symm ▸ (label a).property
    simp only [x, dite_eq_left hb]
    exact congrArg (fun b : B ↦ y b (d * (a : G))) (Subtype.ext he)
  have hDiff : ‖(∑ a ∈ A, q i x a) - total‖ ≤ (E.card : ℝ) * (2 * C i) := by
    have hSum : (∑ a : A, q i x a) = ∑ a ∈ A, q i x a := Finset.sum_attach _ _
    rw [← hSum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ a : A, ‖q i x a - q i (y (label a)) a‖ := norm_sum_le _ _
      _ ≤ ∑ a : A, if (a : G) ∈ E then 2 * C i else 0 := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · exact (norm_sub_le _ _).trans (by linarith [hBound i x a, hBound i (y (label a)) a])
        · simp [hAgree a ha]
      _ = _ := by
        have hSum' : (∑ a : A, if (a : G) ∈ E then 2 * C i else 0) =
            ∑ a ∈ A, if a ∈ E then 2 * C i else 0 :=
          Finset.sum_attach A (fun a : G ↦ if a ∈ E then 2 * C i else 0)
        rw [hSum', ← Finset.sum_filter]
        have hFilter : A.filter (· ∈ E) = E := by
          ext a
          exact Finset.mem_filter.trans ⟨And.right, fun ha ↦
            ⟨(Finset.mem_filter.mp ha).1, ha⟩⟩
        rw [hFilter, Finset.sum_const, nsmul_eq_mul]
  have hApprox : ‖∑ a ∈ A, q i x a‖ < (E.card : ℝ) * (2 * C i) + ε * A.card := by
    calc
      _ = ‖((∑ a ∈ A, q i x a) - total) + total‖ := by rw [sub_add_cancel]
      _ ≤ ‖(∑ a ∈ A, q i x a) - total‖ + ‖total‖ := norm_add_le _ _
      _ < _ := add_lt_add_of_le_of_lt hDiff (hy i)
  calc
    _ = (A.card : ℝ)⁻¹ * ‖∑ a ∈ A, q i x a‖ := by
      simp [finiteAverage, smul_eq_mul, norm_mul, Real.norm_eq_abs]
    _ < (A.card : ℝ)⁻¹ * ((E.card : ℝ) * (2 * C i) + ε * A.card) :=
      mul_lt_mul_of_pos_left hApprox (inv_pos.mpr hcard)
    _ = _ := by field_simp; ring

/-- A fixed bounded partition gives local models throughout the tail of the
    prescribed Følner sequence, with errors controlled by the exceptional
    sites and the relative test boundaries on the other cells. -/
theorem eventually_exists_localPattern_of_tileDensity {K I : Type*}
    [Infinite G] [MeasurableSpace K] [Nonempty K] [Fintype I]
    (μ : Measure (G → K)) [IsProbabilityMeasure μ] (F : LeftFolnerSequence G)
    (P : BoundedTilePartition G) (bad : Set G) (η : ℝ) (hη : 0 ≤ η)
    (hBad : ∀ᶠ n in atTop,
      (((F.blocks n).filter (· ∈ bad)).card : ℝ) / (F.blocks n).card ≤ η)
    (D : I → Finset G) (q : I → (G → K) → G → ℝ) (C : I → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hBound : ∀ i x a, ‖q i x a‖ ≤ C i)
    (hMeas : ∀ i a, Measurable (fun x ↦ q i x a))
    (hMean : ∀ i a, (∫ x, q i x a ∂μ) = 0)
    (hLocal : ∀ i x y a, (∀ d ∈ D i, x (d*a) = y (d*a)) → q i x a = q i y a)
    (hRel : ∀ i a, a ∉ bad → ((leftBoundary (D i) (P.cell a)).card : ℝ) ≤ η * (P.cell a).card)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ x : G → K, ∀ i,
      ‖finiteAverage (F.blocks n) (q i x)‖ < ε + (2*η + ε)*(2*C i) := by
  let M := P.displacements.card
  have hCard (a : G) : (P.cell a).card ≤ M :=
    Finset.card_le_card_of_injOn (fun b ↦ b*a⁻¹) (fun b hb ↦ P.mem_displacements hb)
      (fun b _ c _ heq ↦ mul_right_cancel heq)
  have hSize : Tendsto (fun n ↦ ((F.blocks n).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.tendsto_card
  have hSmall : ∀ᶠ n in atTop, (M : ℝ) * (∑ i, C i ^ 2) < ((F.blocks n).card : ℝ) * ε^2 := by
    have hp : 0 < ε^2 := pow_pos hε 2
    filter_upwards [tendsto_atTop.1 hSize ((M : ℝ) * (∑ i, C i ^ 2) / ε^2 + 1)]
      with n hn
    exact (div_lt_iff₀ hp).mp ((lt_add_one _).trans_le hn)
  filter_upwards [hBad, hSmall, (F.tendsto_leftBoundary P.displacements).eventually_lt_const hε]
    with n hn hV hBoundary
  obtain ⟨x, hx⟩ := exists_localPattern_of_tileVariance μ P (F.blocks n) (F.nonempty n)
    M (fun g _ ↦ hCard g) D q C hBound hMeas hMean hLocal ε hε hV
  have hCoef (i : I) : 0 ≤ 2*C i := mul_nonneg (by norm_num) (hC i)
  refine ⟨x, fun i ↦ (hx i).trans_le (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right ?_ (hCoef i)))⟩
  let A := F.blocks n
  have hA : 0 < (A.card : ℝ) := by exact_mod_cast (F.nonempty n).card_pos
  have hDiv := div_le_div_of_nonneg_right
    (tileTestBoundary_card_le P (D i) A bad η hη (hRel i)) hA.le
  rw [add_div, add_div, mul_div_cancel_right₀ _ hA.ne'] at hDiv
  exact hDiv.trans (by linarith)

end LocalPatterns

section CylinderPatterns

variable {G K : Type} [Group G] [DecidableEq G] [Countable G] [Infinite G]
  [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K]

set_option maxHeartbeats 1000000 in
/-- A sufficiently sparse test boundary gives finite models for a prescribed
    finite family of cylinder tests of an invariant shift law. -/
theorem eventually_exists_localCylinderPattern (F : LeftFolnerSequence G)
    (ν : ProbabilityMeasure (G → K))
    (hInvariant : ∀ a : G, (ν : Measure (G → K)).map (fun x g ↦ x (g * a)) = ν)
    (f : ℕ → C(G → K, ℝ)) (D : ℕ → Finset G) (I : Finset ℕ)
    (hD : ∀ i ∈ I, IsCylinderOn (D i) (f i))
    (P : BoundedTilePartition G) (bad : Set G) (η : ℝ) (hη : 0 ≤ η)
    (hBad : ∀ᶠ n in atTop,
      (((F.blocks n).filter (· ∈ bad)).card : ℝ) / (F.blocks n).card ≤ η)
    (hRel : ∀ i ∈ I, ∀ a ∉ bad,
      ((leftBoundary (D i) (P.cell a)).card : ℝ) ≤ η * (P.cell a).card)
    (τ : ℝ) (hτ : 0 < τ) (hBudget : 8*η*(∑ i ∈ I, ‖f i‖) ≤ τ / 4) :
    ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ∈ I, ‖finiteAverage (F.blocks n)
      (fun a ↦ f i (correspondenceShift a x) - ∫ y, f i y ∂(ν : Measure (G → K)))‖ ≤ τ / 2 := by
  let μ : Measure (G → K) := ν
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (ν : Measure (G → K)))
  let C (i : I) : ℝ := 2 * ‖f i‖
  let m (i : I) : ℝ := ∫ y, f i y ∂μ
  let q (i : I) (x : G → K) (a : G) := f i (correspondenceShift a x) - m i
  have hC (i : I) : 0 ≤ C i := by dsimp [C]; positivity
  have hBound (i : I) (x : G → K) (a : G) : ‖q i x a‖ ≤ C i := by
    have hm : ‖m i‖ ≤ ‖f i‖ := by
      simpa [Measure.real, m] using norm_integral_le_of_norm_le_const (μ := μ)
        (.of_forall (ContinuousMap.norm_coe_le_norm (f i)))
    have hf := ContinuousMap.norm_coe_le_norm (f i) (correspondenceShift a x)
    calc
      _ ≤ ‖f i (correspondenceShift a x)‖ + ‖m i‖ := norm_sub_le _ _
      _ ≤ ‖f i‖ + ‖f i‖ := add_le_add hf hm
      _ = C i := (two_mul _).symm
  have hMeas (i : I) (a : G) : Measurable (fun x ↦ q i x a) :=
    ((f i).continuous.comp (correspondenceShift a).continuous).measurable.sub measurable_const
  have hMean (i : I) (a : G) : (∫ x, q i x a ∂μ) = 0 := by
    have hp : MeasurePreserving (correspondenceShift (K := K) a) μ μ :=
      ⟨(correspondenceShift a).continuous.measurable, hInvariant a⟩
    have hi : Integrable (f i) μ :=
      (f i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hShift : (∫ x, f i (correspondenceShift a x) ∂μ) = m i := by
      have h := integral_map (μ := μ) hp.measurable.aemeasurable
        (f i).continuous.aestronglyMeasurable
      rw [hp.map_eq] at h
      exact h.symm
    have ha : Integrable (fun x ↦ f i (correspondenceShift a x)) μ :=
      hp.integrable_comp_of_integrable hi
    have hk : Integrable (fun _ : G → K ↦ m i) μ := integrable_const _
    change (∫ x, f i (correspondenceShift a x) - m i ∂μ) = _
    rw [integral_sub ha hk, hShift]
    simp [Measure.real]
  have hLocal (i : I) (x y : G → K) (a : G)
      (h : ∀ d ∈ D i, x (d*a) = y (d*a)) : q i x a = q i y a :=
    congrArg (· - m i) (hD i i.property _ _ h)
  let B : ℝ := ∑ i ∈ I, ‖f i‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ norm_nonneg (f i)
  let ε := τ / (4*(1+4*B))
  have hε : 0 < ε := div_pos hτ (by positivity)
  have hEq : ε * (1+4*B) = τ / 4 := by
    have hb : 0 < 1+4*B := by positivity
    dsimp [ε]
    field_simp
  have ht := eventually_exists_localPattern_of_tileDensity μ F P bad η hη hBad
    (fun i : I ↦ D i) q C hC hBound hMeas hMean hLocal
    (fun i ↦ hRel i i.property) ε hε
  filter_upwards [ht] with n hn
  obtain ⟨x, hx⟩ := hn
  refine ⟨x, fun i hi ↦ (hx ⟨i, hi⟩).le.trans ?_⟩
  have hNorm : ‖f i‖ ≤ B :=
    Finset.single_le_sum (fun j _ ↦ norm_nonneg (f j)) hi
  change ε + (2*η+ε)*(2*(2*‖f i‖)) ≤ τ / 2
  calc
    _ ≤ ε + (2*η+ε)*(2*(2*B)) := by gcongr
    _ = ε*(1+4*B) + 8*η*B := by ring
    _ ≤ _ := by
      rw [hEq]
      change 8*η*B ≤ τ / 4 at hBudget
      linarith

end CylinderPatterns

end

end SixProblems
