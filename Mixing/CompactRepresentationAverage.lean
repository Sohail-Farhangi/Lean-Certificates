/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure InnerProductSpace Set
open scoped ComplexConjugate InnerProductSpace

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The average of the rank-one operators built from the orbit of a vector
in a strongly continuous unitary representation of a compact group. -/
def compactRepresentationAverage (μ : Measure K) (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    H →L[ℂ] H :=
  ∫ k, rankOne ℂ (ρ k x) (ρ k x) ∂μ

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [CompleteSpace H] in
private theorem continuous_rankOne_orbit (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hρ : Continuous fun k ↦ ρ k x) : Continuous (fun k ↦ rankOne ℂ (ρ k x) (ρ k x)) := by
  exact ((ContinuousLinearMap.smulRightL ℂ H H).continuous.comp
    ((innerSL ℂ).continuous.comp hρ)).clm_apply hρ

omit [IsTopologicalGroup K] [CompleteSpace H] in
private theorem integrable_rankOne_orbit (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    Integrable (fun k ↦ rankOne ℂ (ρ k x) (ρ k x)) μ :=
  (continuous_rankOne_orbit ρ x hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [CompleteSpace H] in
private theorem compact_rankOne_self (x : H) : IsCompactOperator (rankOne ℂ x x) := by
  let a := (1 : ℂ →L[ℂ] ℂ).smulRight x
  have hc : IsCompactOperator a := isCompactOperator_of_locallyCompactSpace_rng a
  have he : rankOne ℂ x x = a.comp (innerSL ℂ x) := by
    ext y
    simp [a]
  rw [he]
  exact hc.comp_clm (innerSL ℂ x)

omit [IsTopologicalGroup K] in
theorem isCompactOperator_compactRepresentationAverage (μ : Measure K) [IsProbabilityMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    IsCompactOperator (compactRepresentationAverage μ ρ x) := by
  let C := (compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ
  have hC : IsClosed (C : Set (H →L[ℂ] H)) := isClosed_setOfPred_isCompactOperator
  exact C.convex.integral_mem hC (ae_of_all _ fun k ↦ compact_rankOne_self (ρ k x))
    (integrable_rankOne_orbit μ ρ x hρ)

omit [IsTopologicalGroup K] in
theorem compactRepresentationAverage_apply (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) (y : H) :
    compactRepresentationAverage μ ρ x y = ∫ k, rankOne ℂ (ρ k x) (ρ k x) y ∂μ := by
  exact ((ContinuousLinearMap.apply ℂ H y).integral_comp_comm
    (integrable_rankOne_orbit μ ρ x hρ)).symm

omit [IsTopologicalGroup K] in
theorem inner_compactRepresentationAverage (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) (y z : H) :
    ⟪y, compactRepresentationAverage μ ρ x z⟫_ℂ =
      ∫ k, ⟪y, rankOne ℂ (ρ k x) (ρ k x) z⟫_ℂ ∂μ := by
  have hi := (ContinuousLinearMap.apply ℂ H z).integrable_comp
    (integrable_rankOne_orbit μ ρ x hρ)
  rw [compactRepresentationAverage_apply μ ρ x hρ]
  exact ((innerSL ℂ y).integral_comp_comm hi).symm

omit [IsTopologicalGroup K] in
theorem isSymmetric_compactRepresentationAverage (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    (compactRepresentationAverage μ ρ x).IsSymmetric := by
  intro y z
  change ⟪compactRepresentationAverage μ ρ x y, z⟫_ℂ =
    ⟪y, compactRepresentationAverage μ ρ x z⟫_ℂ
  rw [← inner_conj_symm (compactRepresentationAverage μ ρ x y) z,
    inner_compactRepresentationAverage μ ρ x hρ, inner_compactRepresentationAverage μ ρ x hρ,
    ← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun k ↦
    (inner_conj_symm (rankOne ℂ (ρ k x) (ρ k x) y) z).trans
      (isSymmetric_rankOne_self (ρ k x) y z)

/-- The compact average commutes with the entire representation. -/
theorem compactRepresentationAverage_commutes (μ : Measure K) [IsFiniteMeasure μ]
    [IsMulLeftInvariant μ] (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hρ : Continuous fun k ↦ ρ k x) (a : K) (y : H) :
    ρ a (compactRepresentationAverage μ ρ x y) =
      compactRepresentationAverage μ ρ x (ρ a y) := by
  let v (k : K) := rankOne ℂ (ρ k x) (ρ k x) y
  let w (k : K) := rankOne ℂ (ρ k x) (ρ k x) (ρ a y)
  have hi := (ContinuousLinearMap.apply ℂ H y).integrable_comp (integrable_rankOne_orbit μ ρ x hρ)
  have hw := (ContinuousLinearMap.apply ℂ H (ρ a y)).integrable_comp
    (integrable_rankOne_orbit μ ρ x hρ)
  have he (k : K) : ρ a (v k) = w (a*k) := by
    simp only [v, w, rankOne_apply, map_mul]
    change ρ a (⟪ρ k x,y⟫_ℂ • ρ k x) =
      ⟪ρ a (ρ k x),ρ a y⟫_ℂ • ρ a (ρ k x)
    rw [map_smul, LinearIsometryEquiv.inner_map_map]
  rw [compactRepresentationAverage_apply μ ρ x hρ, compactRepresentationAverage_apply μ ρ x hρ]
  change ρ a (∫ k, v k ∂μ) = ∫ k, w k ∂μ
  calc
    _ = ∫ k, ρ a (v k) ∂μ :=
      ((ρ a).toLinearIsometry.toContinuousLinearMap.integral_comp_comm hi).symm
    _ = ∫ k, w (a*k) ∂μ := integral_congr_ae (ae_of_all _ he)
    _ = _ := by
      have ht := measurePreserving_mul_left μ a
      have hW : AEStronglyMeasurable w (μ.map (fun k ↦ a*k)) := by
        change AEStronglyMeasurable w (μ.map (a * ·))
        rw [ht.map_eq]
        exact hw.aestronglyMeasurable
      have he' := integral_map ht.aemeasurable hW
      rw [ht.map_eq] at he'
      exact he'.symm

omit [IsTopologicalGroup K] in
theorem compactRepresentationAverage_ne_zero (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (ρ : K →* (H ≃ₗᵢ[ℂ] H)) {x : H}
    (hx : x ≠ 0) (hρ : Continuous fun k ↦ ρ k x) :
    compactRepresentationAverage μ ρ x ≠ 0 := by
  let v (k : K) := ‖⟪ρ k x,x⟫_ℂ‖ ^ 2
  have hc : Continuous v := (hρ.inner continuous_const).norm.pow _
  have he : v 1 ≠ 0 := by
    have hOne : ρ 1 x = x := by rw [map_one]; rfl
    change ‖⟪ρ 1 x,x⟫_ℂ‖ ^ 2 ≠ 0
    rw [hOne]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (fun h ↦ hx (inner_self_eq_zero.mp h)))
  have hp : 0 < ∫ k, v k ∂μ :=
    hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (HasCompactSupport.of_compactSpace _)
      (fun _ ↦ sq_nonneg _) he
  have hi : Integrable (fun k ↦ ⟪x,rankOne ℂ (ρ k x) (ρ k x) x⟫_ℂ) μ :=
    (innerSL ℂ x).integrable_comp ((ContinuousLinearMap.apply ℂ H x).integrable_comp
      (integrable_rankOne_orbit μ ρ x hρ))
  have hReal : (⟪x, compactRepresentationAverage μ ρ x x⟫_ℂ).re = ∫ k, v k ∂μ := by
    change RCLike.re (⟪x, compactRepresentationAverage μ ρ x x⟫_ℂ) = _
    rw [inner_compactRepresentationAverage μ ρ x hρ, ← integral_re hi]
    apply integral_congr_ae
    refine ae_of_all _ fun k ↦ ?_
    change (⟪x, rankOne ℂ (ρ k x) (ρ k x) x⟫_ℂ).re = v k
    rw [rankOne_apply, inner_smul_right, mul_comm, ← inner_conj_symm (ρ k x) x, Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq, Complex.ofReal_re, norm_inner_symm]
  intro hz
  rw [hz, zero_apply, inner_zero_right, Complex.zero_re] at hReal
  exact hp.ne' hReal.symm

end Mixing
