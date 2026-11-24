/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceModelCoarsening
public import SixProblems.CorrespondenceLocalModels

@[expose] public section
noncomputable section

namespace SixProblems

open Filter MeasureTheory
open scoped Topology

variable {G K : Type} [Group G] [DecidableEq G] [Countable G] [Infinite G]
  [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Finite local models, coarsened partitions and the exceptional-density
bounds needed by the diagonal gluing argument. -/
theorem hasTiledCylinderApproximations [Nonempty K] (F : LeftFolnerSequence G) :
    HasTiledCylinderApproximations K F := by
  classical
  intro ν f D hInvariant hD
  let μ : Measure (G → K) := ν
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (ν : Measure (G → K)))
  let m (i : ℕ) := ∫ x, f i x ∂μ
  let q (i : ℕ) (x : G → K) (a : G) := f i (correspondenceShift a x) - m i
  let B (k : ℕ) := ∑ i ∈ Finset.range (k+1), ‖f i‖
  have hB (k : ℕ) : 0 ≤ B k := Finset.sum_nonneg (fun i _ ↦ norm_nonneg (f i))
  have hNorm (k i : ℕ) (hi : i ≤ k) (x : G → K) (g : G) : ‖q i x g‖ ≤ 2*B k := by
    have hMi : ‖m i‖ ≤ ‖f i‖ := by
      simpa [m, Measure.real] using norm_integral_le_of_norm_le_const (μ := μ)
        (.of_forall (ContinuousMap.norm_coe_le_norm (f i)))
    have hFi : ‖f i‖ ≤ B k := Finset.single_le_sum (fun j _ ↦ norm_nonneg (f j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact (norm_sub_le _ _).trans (by linarith [ContinuousMap.norm_coe_le_norm (f i) (correspondenceShift g x)])
  have hTranslate (i : ℕ) (c : G) (x : G → K) (a : G) :
      q i (fun h ↦ x (h*c⁻¹)) (a*c) = q i x a := by
    have he : correspondenceShift (a * c) (fun h ↦ x (h * c⁻¹)) = correspondenceShift a x := by
      funext g
      simp [mul_assoc]
    simp [q, he]
  have hModels (k : ℕ) : ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ≤ k,
      ‖finiteAverage (F.blocks n) (q i x)‖ ≤ (1 / ((k : ℝ) + 1)) / 2 := by
    let I := Finset.range (k+1)
    let τ : ℝ := 1 / ((k : ℝ) + 1)
    have hτ : 0 < τ := by dsimp [τ]; positivity
    let η := τ / (32*(1+B k))
    have hη : 0 < η := div_pos hτ (by linarith [hB k])
    obtain ⟨P,bad,hSparse,hRel⟩ := exists_smallBoundaryTilePartition F I D hη
    have hSparse' : ∀ᶠ n in atTop, (((F.blocks n).filter (· ∈ bad)).card : ℝ) / (F.blocks n).card ≤ η := by
      simpa only [finiteFraction] using hSparse
    have hBudget : 8*η*B k ≤ τ/4 := by
      have hEq : η * (32*(1+B k)) = τ :=
        div_mul_cancel₀ _ (by linarith [hB k])
      nlinarith only [hEq,hη.le]
    filter_upwards [eventually_exists_localCylinderPattern F ν hInvariant f D I
      (fun i _ ↦ hD i) P bad η hη.le hSparse' hRel τ hτ hBudget] with n hn
    obtain ⟨x,hx⟩ := hn
    exact ⟨x,fun i hi ↦ hx i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))⟩
  obtain ⟨P,bad,sample,hP,hBad,hSparse,hApprox,hRel⟩ := exists_congruentModelCoarsenings F D q
    (fun k ↦ 2*B k) (fun k ↦ by linarith [hB k]) hNorm hTranslate hModels
  let δ (k : ℕ) : ℝ := (1/2)^k
  have hδ (k : ℕ) : 0 ≤ δ k := pow_nonneg (by norm_num) _
  have hSum : Summable δ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact ⟨P,sample,bad,δ,hP,fun k g h hh ↦ (hBad k g h hh).symm,hδ,hSum,
    (fun k ↦ by simpa only [finiteFraction_eq_blockProportion] using hSparse k),
    fun k g i hi hg ↦ hApprox k g hg i hi,fun k g i hi hg ↦ hRel k g hg i hi⟩

/-- Inverse correspondence along the given left Følner sequence. Every
invariant law on the full shift is realized by one configuration along all
blocks of that sequence. -/
theorem hasFolnerGenericRealizations [Nonempty K] (F : LeftFolnerSequence G) :
    HasFolnerGenericRealizations F K :=
  hasFolnerGenericRealizations_of_tiledCylinderApproximations F (hasTiledCylinderApproximations F)

variable [Group K] [IsTopologicalGroup K]

/-- Theorem 4.8. Sequential and measure-theoretic compact-group van der
Corput agree along any given left Følner sequence. This includes the case
where `m` is normalized Haar measure. -/
theorem theorem4_8 (F : LeftFolnerSequence G) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] : IsFolnerVdC F R m ↔ IsMeasureTheoreticVdC R m := by
  exact folnerVdC_iff_measureTheoretic_of_genericRealizations F (hasFolnerGenericRealizations F) R m

end SixProblems
