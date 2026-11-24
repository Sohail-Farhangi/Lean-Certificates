/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceAverages
public import SixProblems.Definitions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

@[expose] public section
noncomputable section

namespace SixProblems

open Filter MeasureTheory Mixing
open scoped Topology BoundedContinuousFunction

variable {G K : Type} [Group G] [DecidableEq G]
variable [Group K] [MetricSpace K] [CompactSpace K] [IsTopologicalGroup K]
variable [MeasurableSpace K] [BorelSpace K]

/-- Uniform distribution of a configuration along the prescribed Følner sequence.
Real tests suffice since a complex test splits into its real and imaginary parts. -/
def IsFolnerUniformlyDistributed (F : LeftFolnerSequence G) (x : G → K)
    (m : Measure K) : Prop :=
  ∀ f : C(K, ℝ), Tendsto (fun n ↦ finiteAverage (F.blocks n) (f ∘ x))
    atTop (𝓝 (∫ k, f k ∂m))

omit [Group K] [IsTopologicalGroup K] in
private theorem empiricalLaw_tendsto_iff_distribution_tests (𝕜 : Type*) [RCLike 𝕜]
    (F : LeftFolnerSequence G) (x : G → K) (m : ProbabilityMeasure K) :
    Tendsto (fun n ↦ finiteEmpiricalLaw (F.blocks n) (F.nonempty n) x) atTop (𝓝 m) ↔
    ∀ f : C(K, 𝕜), Tendsto (fun n ↦ finiteAverage (F.blocks n) (f ∘ x))
      atTop (𝓝 (∫ k, f k ∂(m : Measure K))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]
  simp only [integral_finiteEmpiricalLaw]
  constructor
  · intro h f
    exact h (BoundedContinuousFunction.mkOfCompact f)
  · intro h f
    exact h f.toContinuousMap

omit [Group K] [IsTopologicalGroup K] in
/-- Testing real continuous functions is equivalent to the paper's complex test convention. -/
theorem isFolnerUniformlyDistributed_iff_complex_tests (F : LeftFolnerSequence G) (x : G → K)
    (m : Measure K) [IsProbabilityMeasure m] :
    IsFolnerUniformlyDistributed F x m ↔
    ∀ f : C(K, ℂ), Tendsto (fun n ↦ finiteAverage (F.blocks n) (f ∘ x))
      atTop (𝓝 (∫ k, f k ∂m)) := by
  let ν : ProbabilityMeasure K := ⟨m, inferInstance⟩
  exact (empiricalLaw_tendsto_iff_distribution_tests ℝ F x ν).symm.trans
    (empiricalLaw_tendsto_iff_distribution_tests ℂ F x ν)

/-- The sequence formulation of compact-group van der Corput sets, Definition 4.7. -/
def IsFolnerVdC (F : LeftFolnerSequence G) (R : Set G) (m : Measure K) : Prop :=
  ∀ x : G → K, (∀ h ∈ R, IsFolnerUniformlyDistributed F (fun g ↦ x (h * g) * (x g)⁻¹) m) →
    IsFolnerUniformlyDistributed F x m

/-- The continuous left action on the full shift, expressed by right multiplication
on the coordinates. -/
def correspondenceShift (a : G) : C(G → K, G → K) :=
  ⟨fun x b ↦ x (b * a), continuous_pi fun b ↦ continuous_apply (b * a)⟩

omit [DecidableEq G] [Group K] [CompactSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
  [BorelSpace K] in
@[simp] theorem correspondenceShift_apply (a b : G) (x : G → K) :
    correspondenceShift a x b = x (b * a) := rfl

/-- The identity-coordinate factor on the full shift of the group. -/
def correspondenceOrigin : C(G → K, K) :=
  ⟨fun x ↦ x 1, continuous_apply 1⟩

/-- The pair correlation coordinate with the article's order of multiplication. -/
def correspondenceDifference (h : G) : C(G → K, K) :=
  ⟨fun x ↦ x h * (x 1)⁻¹, (continuous_apply h).mul (continuous_apply 1).inv⟩

private theorem measure_eq_of_continuous_tests {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure Y) [μ.Regular] [ν.Regular]
    (h : ∀ f : C(Y, ℝ), ∫ y, f y ∂μ = ∫ y, f y ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact h f.toContinuousMap

variable [Countable G]

/-- The empirical probability measures of a configuration on the given left Følner blocks. -/
def correspondenceOrbitLaw (F : LeftFolnerSequence G) (x : G → K) (n : ℕ) :
    ProbabilityMeasure (G → K) :=
  finiteEmpiricalLaw (F.blocks n) (F.nonempty n) (fun g ↦ correspondenceShift g x)

omit [Group K] [IsTopologicalGroup K] in
private theorem correspondenceShift_invariant_of_limit (F : LeftFolnerSequence G) (x : G → K)
    {p : Ultrafilter ℕ} (hp : (p : Filter ℕ) ≤ atTop) {ν : ProbabilityMeasure (G → K)}
    (hν : Tendsto (correspondenceOrbitLaw F x) p (𝓝 ν)) (a : G) :
    MeasurePreserving (correspondenceShift a) (ν : Measure (G → K)) (ν : Measure (G → K)) := by
  have hcont : Continuous (correspondenceShift a : (G → K) → (G → K)) :=
    (correspondenceShift a).continuous
  refine ⟨hcont.measurable, ?_⟩
  apply measure_eq_of_continuous_tests
  intro f
  rw [integral_map hcont.aemeasurable f.continuous.aestronglyMeasurable]
  let b : (G → K) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
  have hcl : MapClusterPt ν atTop (correspondenceOrbitLaw F x) :=
    mapClusterPt_iff_ultrafilter.mpr ⟨p, hp, hν⟩
  apply ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt hcont hcl (g := b)
  let w : G → ℝ := fun g ↦ f (correspondenceShift g x)
  have hw (g : G) : ‖w g‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f _
  have h := F.tendsto_average_sub_translate a w ‖f‖ hw
  refine h.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  simp only [correspondenceOrbitLaw, integral_finiteEmpiricalLaw]
  congr 2
  · funext g
    change f (correspondenceShift (a * g) x) = f (correspondenceShift a (correspondenceShift g x))
    congr 1
    funext j
    simp [mul_assoc]

private def correspondenceShiftSystem (ν : ProbabilityMeasure (G → K))
    (hν : ∀ a : G, MeasurePreserving (correspondenceShift a)
      (ν : Measure (G → K)) (ν : Measure (G → K))) : System G (G → K) where
  measure := ν
  probability := inferInstance
  act := fun a ↦ correspondenceShift a
  act_one := by funext x b; simp
  act_mul := by
    intro g h
    funext x b
    simp [mul_assoc]
  preserves := hν

/-- Every empirical limit of the coordinate (x_h x_1^{-1}) has the prescribed law
if the difference configuration is uniformly distributed. -/
private theorem correspondenceDifference_map_of_limit
    (F : LeftFolnerSequence G) (x : G → K) (m : Measure K) [IsProbabilityMeasure m] (h : G)
    (hx : IsFolnerUniformlyDistributed F (fun g ↦ x (h * g) * (x g)⁻¹) m)
    {p : Ultrafilter ℕ} (hp : (p : Filter ℕ) ≤ atTop) {ν : ProbabilityMeasure (G → K)}
    (hν : Tendsto (correspondenceOrbitLaw F x) p (𝓝 ν)) :
    (ν : Measure (G → K)).map (correspondenceDifference h) = m := by
  have hc : Continuous (correspondenceDifference h : (G → K) → K) :=
    (correspondenceDifference h).continuous
  apply measure_eq_of_continuous_tests
  intro f
  let b : (G → K) →ᵇ ℝ := (BoundedContinuousFunction.mkOfCompact f).compContinuous
    (correspondenceDifference h)
  rw [integral_map hc.aemeasurable f.continuous.aestronglyMeasurable]
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) b
  have htest := (hx f).mono_left hp
  apply tendsto_nhds_unique _ htest
  refine hw.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  rw [correspondenceOrbitLaw, integral_finiteEmpiricalLaw]
  congr 1
  funext g
  change f (x (h * g) * (x (1 * g))⁻¹) = _
  simp only [one_mul, Function.comp_apply]

/-- The measure-theoretic formulation implies the Følner-sequence formulation.
This is the compactness direction of Theorem 4.8. -/
theorem folnerVdC_of_measureTheoretic (F : LeftFolnerSequence G) (R : Set G)
    (m : Measure K) [IsProbabilityMeasure m] (hm : IsMeasureTheoreticVdC R m) :
    IsFolnerVdC F R m := by
  intro x hx f
  rw [tendsto_iff_ultrafilter]
  intro p hp
  let v := correspondenceOrbitLaw F x
  let ν := (p.map v).lim
  have hν : Tendsto v p (𝓝 ν) := (p.map v).le_nhds_lim
  let S := correspondenceShiftSystem ν
    (correspondenceShift_invariant_of_limit F x hp hν)
  have hLaw : (ν : Measure (G → K)).map correspondenceOrigin = m := by
    apply hm S correspondenceOrigin correspondenceOrigin.continuous.measurable
    intro h hr
    have hfun : (fun x ↦ correspondenceOrigin (S.act h x) * (correspondenceOrigin x)⁻¹) =
        (correspondenceDifference h : (G → K) → K) := by funext y; simp [S, correspondenceShiftSystem,
      correspondenceOrigin, correspondenceDifference]
    rw [hfun]
    exact correspondenceDifference_map_of_limit F x m h (hx h hr) hp hν
  let b : (G → K) →ᵇ ℝ := (BoundedContinuousFunction.mkOfCompact f).compContinuous
    (correspondenceOrigin : C(G → K, K))
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) b
  have he : (∫ y, b y ∂(ν : Measure (G → K))) = ∫ y, f y ∂m := by
    change (∫ y, f (correspondenceOrigin y) ∂(ν : Measure (G → K))) = _
    rw [← integral_map correspondenceOrigin.continuous.aemeasurable
      f.continuous.aestronglyMeasurable, hLaw]
  rw [← he]
  refine hw.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  change (∫ y, b y ∂(correspondenceOrbitLaw F x n : Measure (G → K))) = _
  rw [correspondenceOrbitLaw, integral_finiteEmpiricalLaw]
  congr 1
  funext g
  change f (x (1 * g)) = _
  simp only [one_mul, Function.comp_apply]

end SixProblems
