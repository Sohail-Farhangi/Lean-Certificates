/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParityAmenability
public import JdLG.UltrafilterMoreDiscreteMean
public import JdLG.WapSubspace

/-!
# Invariant means on the literal WAP space in Example 4.4

The indicator of the even principal left ideal has exactly two right
translates. This proves weak almost periodicity and excludes a normalized
right-invariant mean on the WAP space itself. The grid mean supplies a
positive normalized left-invariant functional on that same space.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

open Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal Topology

instance : TopologicalSpace Point := ⊥

instance : DiscreteTopology Point := ⟨rfl⟩

instance : ContinuousMul Point := ⟨continuous_of_discreteTopology⟩

instance : MeasurableSpace Point := ⊤

instance : DiscreteMeasurableSpace Point := ⟨fun _ ↦ trivial⟩

instance : BorelSpace Point := ⟨borel_eq_top_of_discrete.symm⟩

local notation "BC" => Point →ᵇ ℝ

/-- The indicator of the even ideal as a real bounded continuous function on
the literal discrete parity semigroup. -/
noncomputable def parityIndicatorBC : BC where
  toFun s := if s.first % 2 = 0 ∧ 0 < s.heightIndex then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := ⟨1, fun x y ↦ by
    split_ifs <;> norm_num [Real.dist_eq]⟩

theorem rightTranslateBC_parityIndicator (s : Point) :
    rightTranslateBC parityIndicatorBC s = if s.first % 2 = 0 then 1 else 0 := by
  apply BoundedContinuousFunction.ext
  intro t
  change (if (t * s).first % 2 = 0 ∧ 0 < (t * s).heightIndex then (1 : ℝ) else 0) =
    ((if s.first % 2 = 0 then (1 : BC) else 0) t)
  have h : 0 < (t * s).heightIndex := by
    change 0 < t.heightIndex + s.heightIndex + 1
    omega
  rw [first_mod_two_mul]
  simp only [h, and_true]
  split_ifs <;> rfl

theorem parityIndicatorBC_isWeaklyAlmostPeriodic : IsWeaklyAlmostPeriodic parityIndicatorBC := by
  let W := WeakSpace ℝ BC
  have hf : (Set.range (fun s ↦ toWeakSpace ℝ BC (rightTranslateBC parityIndicatorBC s))).Finite :=
    ((Set.finite_singleton (toWeakSpace ℝ BC 1 : W)).insert 0).subset (by
      rintro _ ⟨s, rfl⟩
      change toWeakSpace ℝ BC (rightTranslateBC parityIndicatorBC s) ∈
        ({0, toWeakSpace ℝ BC 1} : Set W)
      rw [rightTranslateBC_parityIndicator]
      split_ifs <;> simp)
  change IsCompact (closure (Set.range (fun s ↦ toWeakSpace ℝ BC
    (rightTranslateBC parityIndicatorBC s))))
  rw [hf.isClosed.closure_eq]
  exact hf.isCompact

local notation "WAP" => weaklyAlmostPeriodicSubmodule (S := Point)

/-- The right-invariance obstruction holds within the literal weakly almost
periodic subspace, without any assumptions on the functional outside it. -/
theorem parityWap_no_right_invariant_mean
    (m : WAP →ₗ[ℝ] ℝ) (h1 : m ⟨1, isWap_one⟩ = 1)
    (hinv : ∀ (s : Point) (f g : WAP),
      (∀ t : Point, g.val t = f.val (t * s)) → m g = m f) : False := by
  let x : WAP := ⟨parityIndicatorBC, parityIndicatorBC_isWeaklyAlmostPeriodic⟩
  have he := hinv evenPoint x ⟨1, isWap_one⟩ fun t ↦ by
    change (1 : BC) t = rightTranslateBC parityIndicatorBC evenPoint t
    rw [rightTranslateBC_parityIndicator]
    rfl
  have ho := hinv oddPoint x 0 fun t ↦ by
    change (0 : BC) t = rightTranslateBC parityIndicatorBC oddPoint t
    rw [rightTranslateBC_parityIndicator]
    rfl
  rw [h1] at he
  rw [map_zero] at ho
  linarith

/-- Therefore the WAP space admits no bi-invariant normalized mean. -/
theorem parityWap_no_biInvariantMean : ¬ Nonempty (WapBiInvariantMean (S := Point)) := by
  rintro ⟨m⟩
  exact parityWap_no_right_invariant_mean m.functional m.one' m.right'

theorem bound_continuous_memLp (f : BC) :
    MemLp f ∞ (Measure.count : Measure Point) :=
  memLp_top_of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)

/-- The left-invariant grid mean restricted to the literal WAP subspace. -/
noncomputable def parityWap_leftMean : WAP →ₗ[ℝ] ℝ where
  toFun f := parityLeftSetMean.toDiscreteMeasuredMean.value f.val (bound_continuous_memLp f.val)
  map_add' f g := by
    let m := parityLeftSetMean.toDiscreteMeasuredMean
    exact (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
      (m.value_add (bound_continuous_memLp f.val) (bound_continuous_memLp g.val))
  map_smul' c f := by
    let m := parityLeftSetMean.toDiscreteMeasuredMean
    exact (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
      (m.value_smul c (bound_continuous_memLp f.val))

theorem parityWap_leftMean_monotone (f g : WAP) (h : ∀ s, f.val s ≤ g.val s) :
    parityWap_leftMean f ≤ parityWap_leftMean g :=
  parityLeftSetMean.toDiscreteMeasuredMean.value_mono (Eventually.of_forall h)

theorem parityWap_leftMean_one : parityWap_leftMean ⟨1, isWap_one⟩ = 1 := by
  let m := parityLeftSetMean.toDiscreteMeasuredMean
  exact (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans m.value_one

theorem parityWap_leftMean_invariant (s : Point) (f g : WAP)
    (h : ∀ t : Point, g.val t = f.val (s * t)) :
    parityWap_leftMean g = parityWap_leftMean f := by
  let m := parityLeftSetMean.toDiscreteMeasuredMean
  have hg : MemLp (fun t ↦ f.val (s * t)) ∞ (Measure.count : Measure Point) :=
    MemLp.ae_eq (Eventually.of_forall h) (bound_continuous_memLp g.val)
  exact (m.value_congr_ae (Eventually.of_forall h)).trans
    (parityLeftSetMean.toDiscreteMeasuredMean_leftInvariant s f.val
      (bound_continuous_memLp f.val) hg)

/-- Equation (15) along the explicit nonempty left Følner sequence. -/
theorem parity_coefficient_average_tendsto_one (s₀ : Point) :
    Tendsto (fun n ↦ (∑ s ∈ positiveGrid n, ‖rightTranslation s indicator s₀‖) /
      ((positiveGrid n).card : ℝ)) atTop (𝓝 1) := by
  exact tendsto_const_nhds.congr fun n ↦ (folnerGrid_coefficient_average (n + 1)
    (Nat.succ_pos _) s₀).symm

end JdLG.PaperExamplesParity
