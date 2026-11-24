/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconColumnOperators
public import Mixing.ChaconMovingRemainders

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory
open scoped Classical InnerProductSpace Topology

local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

/-- The coefficient error for a height multiple and a moving remainder,
before taking the weak limit. -/
def chaconRemainderError (m n : ℕ) (r : ℤ)
    (f g : ChaconOdometer × Bool → ℂ) : ℂ :=
  let S := chaconTowerSystem
  (∫ x, g x * f (S.act (Multiplicative.ofAdd ((m*chaconTowerHeight n : ℕ) + r)) x) ∂S.measure) -
    ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
      ∫ x, g x * f (S.act (Multiplicative.ofAdd (-(k : ℤ)+r)) x) ∂S.measure

/-- A vanishing moving-remainder error for finite-prefix tests gives the
operator identity on all of mean-zero L². -/
theorem chaconUltrafilter_factor_of_prefix_error
    {I : Type*} (p : Ultrafilter I) (m : ℕ) (n : I → ℕ) (r : I → ℤ)
    (hErr : ∀ f g : ChaconPrefixObservable,
      Tendsto (fun j ↦ chaconRemainderError m (n j) (r j)
        (chaconCenteredObservable f) (chaconCenteredObservable g).conjugate)
        (p : Filter I) (𝓝 0)) :
    ultrafilterOperator chaconTowerSystem.koopmanZeroRep
      (p.map fun j ↦ Multiplicative.ofAdd ((m*chaconTowerHeight (n j) : ℕ) + r j)) =
      chaconHeightPolynomialOperatorZero m *
        ultrafilterOperator chaconTowerSystem.koopmanZeroRep (p.map (Multiplicative.ofAdd ∘ r)) := by
  let S := chaconTowerSystem
  let U := S.koopmanZeroRep
  let M := meanZero S.measure
  let s (j : I) := Multiplicative.ofAdd (r j)
  let t (j : I) := Multiplicative.ofAdd ((m*chaconTowerHeight (n j) : ℕ) + r j)
  let L := ultrafilterOperator U (p.map t)
  let R := ultrafilterOperator U (p.map s)
  let P := chaconHeightPolynomialOperatorZero m
  have h (X Y : ChaconPrefixObservable) :
      ⟪center S.measure (X.val.l2 S.measure), L (center S.measure (Y.val.l2 S.measure))⟫_ℂ =
        ⟪center S.measure (X.val.l2 S.measure), (P*R) (center S.measure (Y.val.l2 S.measure))⟫_ℂ := by
    let x := center S.measure (X.val.l2 S.measure)
    let y := center S.measure (Y.val.l2 S.measure)
    have hL : Tendsto (fun j ↦ ⟪x, U (t j) y⟫_ℂ) (p : Filter I) (𝓝 ⟪x, L y⟫_ℂ) :=
      (tendsto_ultrafilterOperator_coeff U (p.map t) x y).comp
        (show Tendsto t (p : Filter I) (p.map t : Filter _) from le_rfl)
    have hShift (k : ℕ) (v : M) :
        ⟪x, U (Multiplicative.ofAdd (-(k : ℤ))) v⟫_ℂ =
        ⟪U (Multiplicative.ofAdd (k : ℤ)) x, v⟫_ℂ := by
      let a := Multiplicative.ofAdd (k : ℤ)
      have he : U a (U a⁻¹ v) = v := by
        change (U a * U a⁻¹) v = v
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl
      change ⟪x, U a⁻¹ v⟫_ℂ = _
      exact ((U a).inner_map_map x (U a⁻¹ v)).symm.trans
        (congrArg (fun z ↦ ⟪U a x, z⟫_ℂ) he)
    have hR (k : ℕ) :
        Tendsto (fun j ↦ ⟪x, U (Multiplicative.ofAdd (-(k : ℤ)+r j)) y⟫_ℂ)
          (p : Filter I) (𝓝 ⟪x, U (Multiplicative.ofAdd (-(k : ℤ))) (R y)⟫_ℂ) := by
      have he (j : I) : U (Multiplicative.ofAdd (-(k : ℤ)+r j)) y =
          U (Multiplicative.ofAdd (-(k : ℤ))) (U (s j) y) := by
        change U ((Multiplicative.ofAdd (-(k : ℤ))) * s j) y = _
        rw [map_mul]
        rfl
      simp_rw [he, hShift]
      exact (tendsto_ultrafilterOperator_coeff U (p.map s)
        (U (Multiplicative.ofAdd (k : ℤ)) x) y).comp
          (show Tendsto s (p : Filter I) (p.map s : Filter _) from le_rfl)
    let A (j : I) := ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
      ⟪x, U (Multiplicative.ofAdd (-(k : ℤ)+r j)) y⟫_ℂ
    have hP : Tendsto A (p : Filter I) (𝓝 ⟪x, (P*R) y⟫_ℂ) := by
      have hh := tendsto_finsetSum (Finset.range (m+1)) (fun k _ ↦
        (tendsto_const_nhds (x := chaconSpacerProbability m k)).smul (hR k))
      change Tendsto A _ (𝓝 _) at hh
      change Tendsto A _ (𝓝 ⟪x, P (R y)⟫_ℂ)
      convert hh using 2
      simp only [P, chaconHeightPolynomialOperatorZero, sum_apply, smul_apply, inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact inner_smul_right_eq_smul (𝕜 := ℂ) x (U (Multiplicative.ofAdd (-(k : ℤ))) (R y))
        (chaconSpacerProbability m k)
    have hE : Tendsto (fun j ↦ ⟪x, U (t j) y⟫_ℂ - A j) (p : Filter I) (𝓝 0) := by
      unfold A
      simp only [x, y, S, U, t, chaconCentered_prefix_coeff]
      exact hErr Y X
    have hc : Tendsto (fun j ↦ ⟪x, U (t j) y⟫_ℂ) (p : Filter I) (𝓝 ⟪x, (P*R) y⟫_ℂ) := by
      simpa only [sub_add_cancel, zero_add] using hE.add hP
    exact tendsto_nhds_unique hL hc
  apply ContinuousLinearMap.ext
  intro y
  apply (ext_iff_inner_left ℂ).2
  intro x
  exact denseRange_center_chaconPrefixObservable.induction_on₂
    (isClosed_eq (continuous_fst.inner (L.continuous.comp continuous_snd))
      (continuous_fst.inner ((P*R).continuous.comp continuous_snd))) h x y

end Mixing
