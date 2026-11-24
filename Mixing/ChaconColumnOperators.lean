/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconPrefixDensity
public import Mixing.ChaconSubHeight
public import Mixing.ChaconHeightConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory Set
open scoped Classical ComplexConjugate ENNReal Topology InnerProductSpace

local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

theorem ae_chaconHeightObservable_zero (m : ℕ)
    (v : meanZero chaconTowerSystem.measure) {f : ChaconOdometer × Bool → ℂ}
    (hv : (v : Lp ℂ 2 chaconTowerSystem.measure) =ᵐ[chaconTowerSystem.measure] f) :
    (chaconHeightPolynomialOperatorZero m v : Lp ℂ 2 chaconTowerSystem.measure)
      =ᵐ[chaconTowerSystem.measure] chaconHeightObservable m f := by
  let S := chaconTowerSystem
  let w (k : ℕ) : Lp ℂ 2 S.measure := S.koopmanRep (Multiplicative.ofAdd (-(k : ℤ))) v
  have he : (chaconHeightPolynomialOperatorZero m v : Lp ℂ 2 S.measure) =
      ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • w k := by
    let V := (meanZero S.measure).subtypeL
    change V (chaconHeightPolynomialOperatorZero m v) = _
    simp only [chaconHeightPolynomialOperatorZero, sum_apply, smul_apply, map_sum,
      ContinuousLinearMap.map_smul_of_tower]
    rfl
  rw [he]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have h (k : ℕ) : ↑↑(chaconSpacerProbability m k • w k) =ᵐ[S.measure]
      fun x ↦ chaconSpacerProbability m k • f (S.act (Multiplicative.ofAdd (-(k : ℤ))) x) := by
    let t := Multiplicative.ofAdd (-(k : ℤ))
    have hT := (Lp.coeFn_compMeasurePreserving (v : Lp ℂ 2 S.measure) (S.preserves t)).trans
      ((S.preserves t).quasiMeasurePreserving.ae_eq_comp hv)
    filter_upwards [Lp.coeFn_smul (chaconSpacerProbability m k) (w k), hT] with x hx hy
    change w k x = f (S.act t x) at hy
    rw [hx, Pi.smul_apply, hy]
  filter_upwards [ae_all_iff.mpr h] with x hx
  rw [Finset.sum_apply, chaconHeightObservable]
  exact Finset.sum_congr rfl fun k _ ↦ hx k

theorem integral_norm_chaconHeightObservable_le (m : ℕ)
    (v : meanZero chaconTowerSystem.measure) {f : ChaconOdometer × Bool → ℂ}
    (hv : (v : Lp ℂ 2 chaconTowerSystem.measure) =ᵐ[chaconTowerSystem.measure] f) :
    (∫ x, ‖chaconHeightObservable m f x‖ ∂chaconTowerSystem.measure) ≤
      ‖chaconHeightPolynomialOperatorZero m v‖ := by
  let μ := chaconTowerSystem.measure
  let z := (chaconHeightPolynomialOperatorZero m v : Lp ℂ 2 μ)
  have he : (∫ x, ‖chaconHeightObservable m f x‖ ∂μ) = ∫ x, ‖z x‖ ∂μ :=
    integral_congr_ae ((ae_chaconHeightObservable_zero m v hv).symm.mono fun x hx ↦ congrArg norm hx)
  rw [he, integral_norm_eq_lintegral_eNorm (Lp.aestronglyMeasurable z),
    ← eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable z)]
  change _ ≤ ‖z‖
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp z).eLpNorm_lt_top.ne
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

theorem chaconCentered_prefix_coeff (t : Multiplicative ℤ) (X Y : ChaconPrefixObservable) :
    ⟪center chaconTowerSystem.measure (X.val.l2 chaconTowerSystem.measure),
      chaconTowerSystem.koopmanZeroRep t
        (center chaconTowerSystem.measure (Y.val.l2 chaconTowerSystem.measure))⟫_ℂ =
      ∫ x, (chaconCenteredObservable X).conjugate x *
        chaconCenteredObservable Y (chaconTowerSystem.act t x) ∂chaconTowerSystem.measure := by
  let S := chaconTowerSystem
  let μ := S.measure
  let x := center μ (X.val.l2 μ)
  let y := center μ (Y.val.l2 μ)
  have hy := (Lp.coeFn_compMeasurePreserving (y : Lp ℂ 2 μ) (S.preserves t)).trans
    ((S.preserves t).quasiMeasurePreserving.ae_eq_comp (ae_center_chaconPrefixObservable Y))
  change ⟪(x : Lp ℂ 2 μ), S.koopmanRep t y⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_center_chaconPrefixObservable X, hy] with w hX hY
  change (x : Lp ℂ 2 μ) w = _ at hX
  change S.koopmanRep t y w = _ at hY
  rw [hX, hY, RCLike.inner_apply', BoundedObservable.conjugate_apply]
  rfl

set_option maxHeartbeats 1000000 in
/-- The two adjacent height polynomials control every centered cylinder
coefficient for a sub-height remainder. -/
theorem norm_chaconCentered_subHeight_coeff_le (X Y : ChaconPrefixObservable) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m q : ℕ, q < chaconTowerHeight n →
      ‖⟪center chaconTowerSystem.measure (X.val.l2 chaconTowerSystem.measure),
        chaconTowerSystem.koopmanZeroRep (Multiplicative.ofAdd
          ((m * chaconTowerHeight n + q : ℕ) : ℤ))
          (center chaconTowerSystem.measure (Y.val.l2 chaconTowerSystem.measure))⟫_ℂ‖ ≤
      (chaconCenteredObservable X).conjugate.bound *
        (‖chaconHeightPolynomialOperatorZero m
          (center chaconTowerSystem.measure (Y.val.l2 chaconTowerSystem.measure))‖ +
         ‖chaconHeightPolynomialOperatorZero (m+1)
          (center chaconTowerSystem.measure (Y.val.l2 chaconTowerSystem.measure))‖) +
        chaconColumnWeight n * (2*m+2 : ℝ) *
          ((chaconCenteredObservable X).conjugate.bound * (chaconCenteredObservable Y).bound) := by
  obtain ⟨K, hK⟩ := chaconCenteredObservable_prefix X
  obtain ⟨N, hN⟩ := chaconCenteredObservable_prefix Y
  let f := chaconCenteredObservable Y
  let g := (chaconCenteredObservable X).conjugate
  have hg : IsChaconPrefixTest K g := fun x b ↦
    congrArg (starRingEnd ℂ) (hK x b)
  refine ⟨max K N, fun n hn m q hq ↦ ?_⟩
  rw [chaconCentered_prefix_coeff]
  refine (norm_chaconTower_subHeight_correlation_le n m q hq hn
    (hN.mono (le_max_right _ _)) (hg.mono (le_max_left _ _))
    f.measurable g.measurable f.norm_le g.norm_le).trans ?_
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add
    (integral_norm_chaconHeightObservable_le m _ (ae_center_chaconPrefixObservable Y))
    (integral_norm_chaconHeightObservable_le (m+1) _ (ae_center_chaconPrefixObservable Y)))
    g.bound_nonneg) le_rfl

set_option maxHeartbeats 1000000 in
/-- In the non-triadic branch of scale extraction, strong decay of the
adjacent column polynomials forces a zero limit on mean-zero L². -/
theorem chaconUltrafilter_zero_of_subHeight_decompositions
    {I : Type*} (p : Ultrafilter I) (t : I → ℕ) (m : ℕ → ℕ) (n q : ℕ → I → ℕ)
    (hn : ∀ r, Tendsto (n r) (p : Filter I) atTop)
    (hQ : ∀ r, ∀ᶠ j in (p : Filter I), q r j < chaconTowerHeight (n r j) ∧
      t j = m r * chaconTowerHeight (n r j) + q r j)
    (hDecay : ∀ v : meanZero chaconTowerSystem.measure,
      (Tendsto (fun r ↦ chaconHeightPolynomialOperatorZero (m r) v) atTop (𝓝 0)) ∧
      (Tendsto (fun r ↦ chaconHeightPolynomialOperatorZero (m r+1) v) atTop (𝓝 0))) :
    ultrafilterOperator chaconTowerSystem.koopmanZeroRep
      (p.map fun j ↦ Multiplicative.ofAdd (t j : ℤ)) = 0 := by
  let S := chaconTowerSystem
  let M := meanZero S.measure
  let U := S.koopmanZeroRep
  let f (j : I) := Multiplicative.ofAdd (t j : ℤ)
  let L := ultrafilterOperator U (p.map f)
  have hD (X Y : ChaconPrefixObservable) :
      ⟪center S.measure (X.val.l2 S.measure), L (center S.measure (Y.val.l2 S.measure))⟫_ℂ = 0 := by
    let x := center S.measure (X.val.l2 S.measure)
    let y := center S.measure (Y.val.l2 S.measure)
    let B := (chaconCenteredObservable X).conjugate.bound
    let C := (chaconCenteredObservable Y).bound
    obtain ⟨N, hN⟩ := norm_chaconCentered_subHeight_coeff_le X Y
    have hlim : Tendsto (fun j ↦ ‖⟪x, U (f j) y⟫_ℂ‖) (p : Filter I) (𝓝 ‖⟪x, L y⟫_ℂ‖) :=
      ((tendsto_ultrafilterOperator_coeff U (p.map f) x y).comp
        (show Tendsto f (p : Filter I) (p.map f : Filter _) from le_rfl)).norm
    have h (r : ℕ) : ‖⟪x, L y⟫_ℂ‖ ≤ B *
        (‖chaconHeightPolynomialOperatorZero (m r) y‖ + ‖chaconHeightPolynomialOperatorZero (m r+1) y‖) := by
      let z := B * (‖chaconHeightPolynomialOperatorZero (m r) y‖ +
        ‖chaconHeightPolynomialOperatorZero (m r+1) y‖)
      have hr := (((tendsto_chaconColumnWeight.comp (hn r)).mul_const (2*m r+2 : ℝ)).mul_const (B*C)).const_add z
      apply le_of_tendsto_of_tendsto hlim (by simpa only [zero_mul, add_zero] using hr)
      filter_upwards [hQ r, (hn r) (eventually_ge_atTop N)] with j hj hnj
      change ‖⟪x, U (f j) y⟫_ℂ‖ ≤ z + chaconColumnWeight (n r j) * (2*m r+2 : ℝ) * (B*C)
      have he : f j = Multiplicative.ofAdd ((m r * chaconTowerHeight (n r j) + q r j : ℕ) : ℤ) := by
        change Multiplicative.ofAdd (t j : ℤ) = _
        rw [hj.2]
      rw [he]
      exact hN (n r j) hnj (m r) (q r j) hj.1
    have hz : Tendsto (fun r ↦ B * (‖chaconHeightPolynomialOperatorZero (m r) y‖ +
        ‖chaconHeightPolynomialOperatorZero (m r+1) y‖)) atTop (𝓝 0) := by
      simpa only [norm_zero, zero_add, mul_zero] using
        (((hDecay y).1.norm.add (hDecay y).2.norm).const_mul B)
    exact norm_eq_zero.mp (le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hz h) (norm_nonneg _))
  apply ContinuousLinearMap.ext
  intro y
  apply (ext_iff_inner_left ℂ).2
  intro x
  rw [zero_apply, inner_zero_right]
  exact denseRange_center_chaconPrefixObservable.induction_on₂
    (isClosed_eq (continuous_fst.inner (L.continuous.comp continuous_snd)) continuous_const) hD x y

end Mixing
