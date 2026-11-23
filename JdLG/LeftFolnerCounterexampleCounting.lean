/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.FolnerCriteria
public import JdLG.ExactBlockMeans
public import JdLG.LeftFolnerCounterexample
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Counting measure for the left Følner counterexample -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace JdLG.LeftFolnerCounterexample

instance : MeasurableSpace G := ⊤

instance : DiscreteMeasurableSpace G := ⟨fun _ ↦ trivial⟩

/-- The normalized restrictions of counting measure to the right cosets. -/
noncomputable def countingProb (n : ℕ) : Measure G :=
  normalizedRestrictedMeasure Measure.count (block n : Set G)

theorem countingProb_probability (n : ℕ) : IsProbabilityMeasure (countingProb n) :=
  normalizedRestrictedMeasure_probability Measure.count
    (by rw [Measure.count_apply_finset]; exact_mod_cast (block_nonempty n).card_ne_zero)
    (by rw [Measure.count_apply_finset]; exact ENNReal.natCast_ne_top _)

private theorem integral_countingProb (n : ℕ) (g : G → ℝ) :
    (∫ s, g s ∂countingProb n) = (∑ s ∈ block n, g s) / (block n).card := by
  have hi : IntegrableOn g (block n : Set G) Measure.count := by
    rw [← (block n : Set G).biUnion_of_singleton]
    apply integrableOn_finset_iUnion.2
    intro s _
    exact integrableOn_singleton (by finiteness) (by rw [Measure.count_singleton]; norm_num)
  rw [countingProb, normalizedRestrictedMeasure, integral_smul_measure, setIntegral_finset _ hi,
    Measure.count_apply_finset, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, div_eq_inv_mul]
  simp only [count_real_singleton, one_smul]

/-- The cosets satisfy the left Følner condition with zero defect
eventually for each fixed left translation. -/
theorem countingProb_leftFolner : LeftFolnerProbabilities countingProb atTop := by
  intro a ε hε
  classical
  filter_upwards [eventually_leftTranslate_block a] with n htranslate g _ _
  have hfin : (block n).image (a * ·) = block n :=
    Finset.coe_injective (by simpa only [Finset.coe_image] using htranslate)
  have hsum : (∑ s ∈ block n, g (a * s)) = ∑ s ∈ block n, g s := by
    conv_rhs => rw [← hfin]
    exact (Finset.sum_image (fun _ _ _ _ h ↦ mul_left_cancel h)).symm
  rw [integral_countingProb, integral_countingProb, hsum, sub_self, norm_zero]
  exact hε

/-- Finite subgroups before the shifts used in the counterexample. -/
noncomputable def unshiftedBlock (n : ℕ) : Finset G := by
  classical
  letI := Fintype.ofFinite (level n)
  exact Finset.univ.image (fun a : level n ↦ a.val)

theorem mem_unshiftedBlock (n : ℕ) (g : G) : g ∈ unshiftedBlock n ↔ g ∈ level n := by
  classical
  let := Fintype.ofFinite (level n)
  unfold unshiftedBlock
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨by rintro ⟨a, rfl⟩; exact a.property, fun h ↦ ⟨⟨g, h⟩, rfl⟩⟩

/-- The finitary permutation group has a two-sided invariant mean on
counting-measure L∞. The unshifted subgroup exhaustion provides the mean. -/
theorem countingBiInvariantMean :
    ∃ m : MeasuredMean (Measure.count : Measure G), m.IsLeftInvariant ∧ m.IsRightInvariant := by
  apply exists_measuredBiInvariantMean_of_exactBlocks unshiftedBlock
    (fun n ↦ ⟨1, (mem_unshiftedBlock n 1).2 (Subgroup.one_mem _)⟩)
  · intro a
    obtain ⟨N, hN⟩ := a.property
    filter_upwards [eventually_ge_atTop N] with n hn
    have ha : a ∈ level n := fun k hk ↦ hN k (hn.trans_lt hk)
    ext g
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (mem_unshiftedBlock n _).2
        ((level n).mul_mem ha ((mem_unshiftedBlock n t).1 ht))
    · intro hg
      refine ⟨a⁻¹ * g, (mem_unshiftedBlock n _).2
        ((level n).mul_mem ((level n).inv_mem ha) ((mem_unshiftedBlock n g).1 hg)), ?_⟩
      exact mul_inv_cancel_left a g
  · intro a
    obtain ⟨N, hN⟩ := a.property
    filter_upwards [eventually_ge_atTop N] with n hn
    have ha : a ∈ level n := fun k hk ↦ hN k (hn.trans_lt hk)
    ext g
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (mem_unshiftedBlock n _).2
        ((level n).mul_mem ((mem_unshiftedBlock n t).1 ht) ha)
    · intro hg
      refine ⟨g * a⁻¹, (mem_unshiftedBlock n _).2
        ((level n).mul_mem ((mem_unshiftedBlock n g).1 hg) ((level n).inv_mem ha)), ?_⟩
      exact inv_mul_cancel_right g a

local notation "H" => lp (fun _ : ℕ ↦ ℂ) 2

theorem integral_powerAverage (p : ℝ) (n : ℕ) (f : StrongDual ℂ H) :
    (∫ s, ‖f (representation s (e 0))‖ ^ p ∂countingProb n) = powerAverage p n f :=
  integral_countingProb n _

/-- The printed uniform coefficient statement fails for every positive
power with the actual normalized counting measures of a left Følner net. -/
theorem counting_uniform_powerAverage_counterexample :
    LeftFolnerProbabilities countingProb atTop ∧
    (∀ n, IsProbabilityMeasure (countingProb n)) ∧
    IsCompact (weakOperatorClosure representation : Set (H →WOT[ℂ] H)) ∧
    IsAlmostWeaklyStable (closureAction representation) (e 0) ∧
    ∀ (p : ℝ), 0 < p →
      (∀ f : StrongDual ℂ H,
        Tendsto (fun n ↦ ∫ s, ‖f (representation s (e 0))‖ ^ p ∂countingProb n) atTop (𝓝 0)) ∧
      ∀ n, sSup {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ ≤ 1 ∧
        (∫ s, ‖f (representation s (e 0))‖ ^ p ∂countingProb n) = r} = 1 := by
  refine ⟨countingProb_leftFolner, countingProb_probability, weakly_compact,
    e_zero_almostWeaklyStable, fun p hp ↦ ⟨fun f ↦ ?_, fun n ↦ ?_⟩⟩
  · simp_rw [integral_powerAverage]
    exact powerAverage_tendsto_zero hp f
  · simp_rw [integral_powerAverage]
    exact uniform_powerAverage_eq_one hp n

end JdLG.LeftFolnerCounterexample
