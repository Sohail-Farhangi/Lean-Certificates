/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconHeightConsequences

/-! # Injectivity at every positive multiple of a Chacon tower height -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

/-- The inverse Koopman generator on the mean-zero subspace. -/
noncomputable def chaconInverseGeneratorZero :
    meanZero chaconTowerSystem.measure →L[ℂ] meanZero chaconTowerSystem.measure :=
  chaconTowerSystem.koopmanZeroRep (Multiplicative.ofAdd (-1))

private theorem chaconInverseGeneratorZero_pow (k : ℕ) :
    chaconInverseGeneratorZero^k =
      (chaconTowerSystem.koopmanZeroRep (Multiplicative.ofAdd (-(k : ℤ))) : _ →L[ℂ] _) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, neg_zero, show Multiplicative.ofAdd (0 : ℤ) = 1 by rfl,
      map_one]
    rfl
  | succ k hk =>
    rw [pow_succ, hk, chaconInverseGeneratorZero, Nat.cast_succ, neg_add,
      show Multiplicative.ofAdd (-(k : ℤ) + -1) =
        Multiplicative.ofAdd (-(k : ℤ)) * Multiplicative.ofAdd (-1) by rfl, map_mul]
    rfl

theorem chaconHeightPolynomialOperatorZero_eq_aeval (m : ℕ) :
    chaconHeightPolynomialOperatorZero m =
      Polynomial.aeval chaconInverseGeneratorZero ((chaconPolynomial m).map (algebraMap ℝ ℂ)) := by
  simp only [chaconHeightPolynomialOperatorZero, chaconPolynomial, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_sum, map_mul,
    map_pow, Polynomial.aeval_C, Polynomial.aeval_X, chaconInverseGeneratorZero_pow,
    chaconSpacerProbability]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  apply ContinuousLinearMap.ext
  intro v
  rw [smul_apply, mul_apply_eq_comp, ContinuousLinearMap.algebraMap_apply,
    IsScalarTower.algebraMap_smul ℂ]

private theorem chaconInverseGeneratorZero_sub_scalar_injective (z : ℂ) :
    Function.Injective (fun v : meanZero chaconTowerSystem.measure ↦
      chaconInverseGeneratorZero v - z • v) := by
  let U := chaconTowerSystem.koopmanZeroRep
  have hinv (v : meanZero chaconTowerSystem.measure) :
      U (Multiplicative.ofAdd 1) (U (Multiplicative.ofAdd (-1)) v) = v := by
    change (U (Multiplicative.ofAdd 1) * U (Multiplicative.ofAdd (-1))) v = _
    rw [← map_mul, show Multiplicative.ofAdd (1 : ℤ) * Multiplicative.ofAdd (-1) = 1 by rfl, map_one]
    rfl
  intro v w h
  change U (Multiplicative.ofAdd (-1)) v - z • v = U (Multiplicative.ofAdd (-1)) w - z • w at h
  by_cases hz : z = 0
  · simp only [hz, zero_smul, sub_zero] at h
    exact (U (Multiplicative.ofAdd (-1))).injective h
  · have hv := congrArg (U (Multiplicative.ofAdd 1)) h
    simp only [map_sub, map_smul, hinv] at hv
    have hw := congrArg (fun x : meanZero chaconTowerSystem.measure ↦ (-z⁻¹) • x) hv
    simp only [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hz, neg_smul, one_smul,
      sub_neg_eq_add] at hw
    apply generator_sub_scalar_injective_of_weaklyMixing U chaconTower_isWeaklyMixing z⁻¹
    change U (Multiplicative.ofAdd 1) v - z⁻¹ • v = U (Multiplicative.ofAdd 1) w - z⁻¹ • w
    simpa only [sub_eq_add_neg, add_comm] using hw

/-- All the height-multiple limit polynomials are injective on mean-zero L². -/
theorem chaconHeightPolynomialOperatorZero_injective (m : ℕ) :
    Function.Injective (chaconHeightPolynomialOperatorZero m) := by
  rw [chaconHeightPolynomialOperatorZero_eq_aeval]
  refine aeval_injective_of_no_eigenvectors _ (fun z ↦ ?_) ?_
  · exact chaconInverseGeneratorZero_sub_scalar_injective z
  intro h
  have hm := (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp h
  exact chaconPolynomial_ne_zero m hm

/-- Positive multiples of the tower heights escape every finite subset of the group. -/
theorem tendsto_chaconHeightTime_cofinite (m : ℕ) (hm : 0 < m) :
    Tendsto (chaconHeightTime m) atTop cofinite := by
  have ht : StrictMono chaconTowerHeight := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [chaconTowerHeight]
    omega
  have hInj : Function.Injective (chaconHeightTime m) := by
    intro n k h
    apply ht.injective
    have he := congrArg Multiplicative.toAdd h
    change (↑(m * chaconTowerHeight n) : ℤ) = ↑(m * chaconTowerHeight k) at he
    exact Nat.eq_of_mul_eq_mul_left hm (Int.ofNat_inj.mp he)
  simpa only [Nat.cofinite_eq_atTop] using hInj.tendsto_cofinite

theorem chaconHeightTime_map_mem_free (m : ℕ) (hm : 0 < m) (q : Ultrafilter ℕ)
    (hq : (q : Filter ℕ) ≤ atTop) : q.map (chaconHeightTime m) ∈ freeUltrafilters (Multiplicative ℤ) :=
  (tendsto_chaconHeightTime_cofinite m hm).mono_left hq

/-- The Example 2 polynomial branch applies along any ultrafilter limit of
fixed multiples of the tower heights. -/
theorem example2_chaconTower_all_height_ultrafilters
    (m : ℕ) (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop) :
    let p := q.map (chaconHeightTime m)
    chaconTowerSystem.generatedSigma {p} = (inferInstance : MeasurableSpace (ChaconOdometer × Bool)) ∧
    ∀ {Y : Type*} [MeasurableSpace Y] (T : System (Multiplicative ℤ) Y), T.IsUMixing {p} →
      SpectrallyDisjoint chaconTowerSystem.koopmanZeroRep T.koopmanZeroRep := by
  dsimp only
  refine chaconTowerSystem.generated_and_spectrallyDisjoint_of_injective_limit _ ?_
  rw [ultrafilterOperator_chaconHeight_zero m q hq]
  exact chaconHeightPolynomialOperatorZero_injective m

end Mixing
