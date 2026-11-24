/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.FourierUniqueness
public import Mixing.SpectralMeasureClass
public import Mixing.SpectralOrthogonality

/-! # Absolute continuity of vector spectral measures -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

section RegularOrder

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Order on finite regular measures can be tested by nonnegative continuous functions. -/
theorem measure_le_of_integral_nonnegative (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular]
    (h : ∀ f : C(X, ℝ), 0 ≤ f → ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  refine Measure.le_iff.mpr fun A hA => ?_
  by_contra! hNot
  obtain ⟨K, hKA, hK, hKt⟩ := hA.exists_lt_isCompact_of_ne_top (measure_ne_top μ A) hNot
  obtain ⟨O, hKO, hO, hOt⟩ := K.exists_isOpen_lt_of_lt (μ K) ((measure_mono hKA).trans_lt hKt)
  obtain ⟨f, hf1, _, hf2, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  have hLow (x : X) : K.indicator (fun _ => (1 : ℝ)) x ≤ f x := by
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, hf1 hx]
      exact le_rfl
    · rw [Set.indicator_of_notMem hx]
      exact (hf3 x).1
  have hHigh (x : X) : f x ≤ O.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx]
      exact (hf3 x).2
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hf2 h))]
  have hiμ : Integrable (⇑f) μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiν : Integrable (⇑f) ν :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hReal : μ.real K ≤ ν.real O := calc
    _ = ∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂μ := (integral_indicator_one hK.measurableSet).symm
    _ ≤ ∫ x, f x ∂μ := integral_mono ((integrable_const _).indicator hK.measurableSet) hiμ hLow
    _ ≤ ∫ x, f x ∂ν := h f (fun x => (hf3 x).1)
    _ ≤ ∫ x, O.indicator (fun _ => (1 : ℝ)) x ∂ν :=
      integral_mono hiν ((integrable_const _).indicator hO.measurableSet) hHigh
    _ = _ := integral_indicator_one hO.measurableSet
  exact hOt.not_ge ((ENNReal.toReal_le_toReal (measure_ne_top μ K) (measure_ne_top ν O)).mp hReal)

end RegularOrder

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The integral of a nonnegative continuous spectral test is the squared norm of its
square-root multiplier on the vector. -/
theorem integral_vectorSpectralMeasure_eq_sqrt_norm (x : H)
    (f : C(RepresentationSpectrum U, ℝ)) (hf : 0 ≤ f) :
    (∫ z, f z ∂vectorSpectralMeasure U x) =
      ‖spectralCalculus U (complexify
        ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩) x‖ ^ 2 := by
  rw [norm_spectralCalculus_complexify_sq]
  apply integral_congr_ae
  exact .of_forall fun z => (Real.sq_sqrt (hf z)).symm

set_option maxHeartbeats 1200000 in
theorem vectorSpectralMeasure_add_le (x y : H) :
    vectorSpectralMeasure U (x + y) ≤ (2 : ℝ≥0∞) • (vectorSpectralMeasure U x + vectorSpectralMeasure U y) := by
  let μ := vectorSpectralMeasure U x + vectorSpectralMeasure U y
  have : IsFiniteMeasure ((2 : ℝ≥0∞) • μ) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top μ _)
  apply measure_le_of_integral_nonnegative
  intro f hf
  rw [integral_smul_measure, integral_add_measure]
  · rw [integral_vectorSpectralMeasure_eq_sqrt_norm U (x + y) f hf,
      integral_vectorSpectralMeasure_eq_sqrt_norm U x f hf,
      integral_vectorSpectralMeasure_eq_sqrt_norm U y f hf]
    simp only [map_add, ENNReal.toReal_ofNat, smul_eq_mul]
    let A := spectralCalculus U (complexify ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩)
    change ‖A x + A y‖ ^ 2 ≤ 2 * (‖A x‖ ^ 2 + ‖A y‖ ^ 2)
    have hTri := norm_add_le (A x) (A y)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hTri 2
    nlinarith only [hsq, sq_nonneg (‖A x‖ - ‖A y‖)]
  all_goals exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem dualVectorSpectralMeasure_add_le (x y : H) :
    dualVectorSpectralMeasure U (x + y) ≤
      (2 : ℝ≥0∞) • (dualVectorSpectralMeasure U x + dualVectorSpectralMeasure U y) := by
  have hf := (spectralPointDual_continuous U).measurable
  have hm := Measure.map_mono (vectorSpectralMeasure_add_le U x y) hf
  rw [Measure.map_smul (2 : ℝ≥0∞) hf.aemeasurable, Measure.map_add _ _ hf] at hm
  exact hm

theorem dualVectorSpectralMeasure_univ (x : H) :
    dualVectorSpectralMeasure U x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  unfold dualVectorSpectralMeasure
  rw [Measure.map_apply (spectralPointDual_continuous U).measurable MeasurableSet.univ, preimage_univ]
  conv_rhs => rw [← vectorSpectralMeasure_mass U x, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem dualVectorSpectralMeasure_map_unitary (g : G) (x : H) :
    dualVectorSpectralMeasure U (U g x) = dualVectorSpectralMeasure U x := by
  apply eq_of_spectralFourier_eq
  intro a
  rw [spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure]
  have hComm : U a (U g x) = U g (U a x) := by
    change (U a * U g) x = (U g * U a) x
    rw [← map_mul, ← map_mul, mul_comm' a g]
  rw [hComm, (U g).inner_map_map]

theorem dualVectorSpectralMeasure_smul (c : ℂ) (x : H) :
    dualVectorSpectralMeasure U (c • x) = ENNReal.ofReal (‖c‖ ^ 2) • dualVectorSpectralMeasure U x := by
  let μ := dualVectorSpectralMeasure U x
  have : IsFiniteMeasure (ENNReal.ofReal (‖c‖ ^ 2) • μ) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_dualVectorSpectralMeasure, (U g).map_smul, inner_smul_left, inner_smul_right]
  unfold spectralFourier
  rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _)]
  change star c * (c * ⟪x, U g x⟫_ℂ) =
    Complex.ofReal (‖c‖ ^ 2) * ∫ χ, (dualEvaluation g χ : ℂ) ∂μ
  rw [← mul_assoc, Complex.star_def, mul_comm (conj c) c, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact congrArg (Complex.ofReal (‖c‖ ^ 2) * ·) (spectralFourier_dualVectorSpectralMeasure U x g).symm

/-- The vectors whose spectral measure is absolutely continuous with respect
to a given measure form an invariant linear subspace. -/
noncomputable def spectralAbsoluteContinuousSubmodule (μ : Measure (DiscreteDual G)) : Submodule ℂ H where
  carrier := {x | dualVectorSpectralMeasure U x ≪ μ}
  zero_mem' := fun A _ => measure_mono_null (Set.subset_univ A) (by simp [dualVectorSpectralMeasure_univ])
  add_mem' := fun {x y} hx hy A hA => by
    apply le_antisymm ((dualVectorSpectralMeasure_add_le U x y) A |>.trans_eq ?_) bot_le
    simp only [smul_apply, add_apply, hx hA, hy hA, add_zero, smul_zero, bot_eq_zero]
  smul_mem' := fun c {x} hx A hA => by
    simp only [dualVectorSpectralMeasure_smul, smul_apply, hx hA, smul_zero]

theorem spectralAbsoluteContinuousSubmodule_invariant
    (μ : Measure (DiscreteDual G)) (g : G) (x : H)
    (hx : x ∈ spectralAbsoluteContinuousSubmodule U μ) :
    U g x ∈ spectralAbsoluteContinuousSubmodule U μ := by
  change dualVectorSpectralMeasure U (U g x) ≪ μ
  rw [dualVectorSpectralMeasure_map_unitary]
  exact hx

theorem spectralAbsoluteContinuousSubmodule_isClosed (μ : Measure (DiscreteDual G)) :
    IsClosed (spectralAbsoluteContinuousSubmodule U μ : Set H) := by
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  intro A hA
  have hbound (n : ℕ) : dualVectorSpectralMeasure U x A ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal (‖x - u n‖ ^ 2) := by
    have h := (dualVectorSpectralMeasure_add_le U (u n) (x - u n)) A
    rw [show u n + (x - u n) = x by abel, smul_apply, add_apply,
      (hu n : dualVectorSpectralMeasure U (u n) ≪ μ) hA, zero_add, smul_eq_mul] at h
    refine h.trans ?_
    gcongr
    exact (measure_mono (Set.subset_univ A)).trans_eq (dualVectorSpectralMeasure_univ U (x - u n))
  have h := (tendsto_const_nhds (x := x)).sub hlim
  rw [sub_self] at h
  have hh : Tendsto (fun n => (2 : ℝ≥0∞) * ENNReal.ofReal (‖x - u n‖ ^ 2)) atTop (𝓝 0) := by
    have h0 := (ENNReal.continuous_ofReal.tendsto _).comp (h.norm.pow 2)
    rw [norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero] at h0
    simpa only [Function.comp_def, mul_zero] using
      ENNReal.Tendsto.const_mul (a := 2) h0 (Or.inr ENNReal.ofNat_ne_top)
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hh hbound) bot_le

end Mixing
