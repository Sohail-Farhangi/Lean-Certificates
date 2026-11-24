/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.UltrafilterAction
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

/-- The empirical probability measure on the first n points of a sequence. -/
def empiricalProbability (x : ℕ → X) (n : ℕ) (hn : n ≠ 0) : ProbabilityMeasure X :=
  ⟨(n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (x i), ⟨by
    have hSum (m : ℕ) : (∑ i ∈ Finset.range m, Measure.dirac (x i)) univ = (m : ℝ≥0∞) := by
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, add_apply, ih, measure_univ, Nat.cast_succ]
    rw [smul_apply, smul_eq_mul, hSum]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hn) (ENNReal.natCast_ne_top n)⟩⟩

omit [TopologicalSpace X] [BorelSpace X] in
/-- Integration against an empirical probability is arithmetic averaging. -/
theorem integral_empiricalProbability (x : ℕ → X) (n : ℕ) (hn : n ≠ 0)
    (f : X → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(empiricalProbability x n hn : Measure X)) =
      (∑ i ∈ Finset.range n, f (x i)) / n := by
  change (∫ t, f t ∂((n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (x i))) = _
  rw [integral_smul_measure, integral_finsetSum_measure
    (fun i _ ↦ integrable_dirac' (a := x i) hf.stronglyMeasurable (by simp)),
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_dirac' f (x i) hf.stronglyMeasurable

variable [CompactSpace X] [T2Space X] [MetrizableSpace X]

/-- A dyadic empirical law of an orbit, obtained by taking a weak
ultrafilter limit in the compact space of probability measures. -/
def dyadicOrbitLaw (t : X → X) (x : X) (p : Ultrafilter ℕ) : ProbabilityMeasure X :=
  Ultrafilter.extend
    (fun n : ℕ ↦ empiricalProbability (fun j ↦ t^[j] x) (2 ^ n) (by positivity)) p

/-- The construction preserves the limiting integrals of continuous tests. -/
theorem tendsto_integral_dyadicOrbitLaw (t : X → X) (x : X) (p : Ultrafilter ℕ) (f : C(X, ℝ)) :
    Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (2 ^ n), f (t^[i] x)) / (2 ^ n : ℝ))
      (p : Filter ℕ) (𝓝 (∫ y, f y ∂(dyadicOrbitLaw t x p : Measure X))) := by
  have h := ((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto _).comp
    (tendsto_ultrafilterExtend
      (fun n : ℕ ↦ empiricalProbability (fun j ↦ t^[j] x) (2 ^ n) (by positivity)) p)
  simpa only [Function.comp_def, integral_empiricalProbability _ _ _ _ f.continuous.measurable,
    Nat.cast_pow, Nat.cast_ofNat, dyadicOrbitLaw] using h

/-- The dyadic empirical law of an orbit along a free ultrafilter is invariant
under the continuous transformation. -/
theorem dyadicOrbitLaw_preserving (t : X → X) (ht : Continuous t) (x : X)
    (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    MeasurePreserving t (dyadicOrbitLaw t x p : Measure X) (dyadicOrbitLaw t x p : Measure X) := by
  let L := dyadicOrbitLaw t x p
  let ν (n : ℕ) := empiricalProbability (fun j ↦ t^[j] x) (2 ^ n) (by positivity)
  refine ⟨ht.measurable, ?_⟩
  have hL : Tendsto ν (p : Filter ℕ) (𝓝 L) := tendsto_ultrafilterExtend ν p
  have hMap : Tendsto (fun n ↦ (ν n).map t) (p : Filter ℕ) (𝓝 (L.map t)) :=
    ((ProbabilityMeasure.continuous_map ht).tendsto L).comp hL
  have hTest : Tendsto (fun n ↦ (ν n).map t) (p : Filter ℕ) (𝓝 L) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hDiff (n : ℕ) :
        (∫ y, f y ∂((ν n).map t : Measure X)) =
          (∫ y, f y ∂(ν n : Measure X)) +
            (f (t^[2 ^ n] x) - f x) / (2 ^ n : ℝ) := by
      change (∫ y, f y ∂((ν n : Measure X).map t)) = _
      rw [integral_map ht.measurable.aemeasurable f.continuous.aestronglyMeasurable]
      have hm : Measurable (fun y ↦ f (t y)) := f.continuous.measurable.comp ht.measurable
      simp only [ν, integral_empiricalProbability _ _ _ _ hm,
        integral_empiricalProbability _ _ _ _ f.continuous.measurable, Nat.cast_pow, Nat.cast_ofNat,
        ← Function.iterate_succ_apply']
      let N := 2 ^ n
      have hsum : (∑ j ∈ Finset.range N, f (t^[j + 1] x)) + f x =
          (∑ j ∈ Finset.range N, f (t^[j] x)) + f (t^[N] x) := by
        calc
          _ = ∑ j ∈ Finset.range (N + 1), f (t^[j] x) := by
            rw [Finset.sum_range_succ']
            simp only [Function.iterate_zero_apply]
          _ = _ := Finset.sum_range_succ _ _
      have hsum' : (∑ j ∈ Finset.range N, f (t^[j + 1] x)) =
          (∑ j ∈ Finset.range N, f (t^[j] x)) + (f (t^[N] x) - f x) := by linarith
      rw [← add_div, hsum']
    have hBound : ∃ C : ℝ, ∀ n : ℕ, ‖f (t^[2 ^ n] x) - f x‖ ≤ C :=
      ⟨2 * ‖f‖, fun n ↦ (norm_sub_le _ _).trans (by
        nlinarith [BoundedContinuousFunction.norm_coe_le_norm f (t^[2 ^ n] x),
          BoundedContinuousFunction.norm_coe_le_norm f x])⟩
    have hZero : Tendsto (fun n : ℕ ↦ (f (t^[2 ^ n] x) - f x) / (2 ^ n : ℝ))
        (p : Filter ℕ) (𝓝 0) := by
      have hDec := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)).mono_left hp
      have hg : IsBoundedUnder (· ≤ ·) (p : Filter ℕ)
          (fun n : ℕ ↦ ‖f (t^[2 ^ n] x) - f x‖) := ⟨hBound.choose,
        eventually_map.mpr (Eventually.of_forall hBound.choose_spec)⟩
      simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hDec.zero_mul_isBoundedUnder_le hg
    have hBase :=
      (((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto L).comp hL).add hZero
    simpa only [hDiff, add_zero, Function.comp_def] using hBase
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hMap hTest)

end Mixing
