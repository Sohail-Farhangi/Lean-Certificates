/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconKoopmanHeightLimits
public import Mixing.ChaconPolynomialApplication

/-! # A concrete free ultrafilter for the polynomial case of Example 2 -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

/-- The polynomial variable records the integer spacer count. -/
theorem chaconPolynomial_coeff (m k : ℕ) (hk : k ≤ m) :
    (chaconPolynomial m).coeff k = chaconSpacerProbability m k := by
  simp only [chaconPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk), ite_true, chaconSpacerProbability]

theorem chaconSpacerProbability_one_zero : chaconSpacerProbability 1 0 = 1/2 := by
  rw [← chaconPolynomial_coeff 1 0 (by decide), chaconPolynomial_one, Polynomial.coeff_C_mul]
  norm_num

theorem chaconSpacerProbability_one_one : chaconSpacerProbability 1 1 = 1/2 := by
  rw [← chaconPolynomial_coeff 1 1 (by decide), chaconPolynomial_one, Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

/-- The polynomial height limit restricted to the mean-zero Koopman subspace. -/
noncomputable def chaconHeightPolynomialOperatorZero (m : ℕ) :
    meanZero chaconTowerSystem.measure →L[ℂ] meanZero chaconTowerSystem.measure :=
  ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
    (chaconTowerSystem.koopmanZeroRep (Multiplicative.ofAdd (-(k : ℤ))) : _ →L[ℂ] _)

theorem ultrafilterOperator_chaconHeight_zero (m : ℕ) (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    ultrafilterOperator chaconTowerSystem.koopmanZeroRep (p.map (chaconHeightTime m)) =
      chaconHeightPolynomialOperatorZero m := by
  let S := chaconTowerSystem
  let V := (meanZero S.measure).subtypeL
  have hsub : Intertwines S.koopmanZeroRep S.koopmanRep V := fun _ _ ↦ rfl
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  change V (ultrafilterOperator S.koopmanZeroRep (p.map (chaconHeightTime m)) w) =
    V (chaconHeightPolynomialOperatorZero m w)
  rw [hsub.ultrafilter, ultrafilterOperator_chaconHeight m p hp]
  simp only [chaconHeightPolynomialOperator, chaconHeightPolynomialOperatorZero, sum_apply,
    smul_apply, map_sum, ContinuousLinearMap.map_smul_of_tower]
  rfl

private theorem injective_chaconHeightPolynomialOperatorZero_one :
    Function.Injective (chaconHeightPolynomialOperatorZero 1) := by
  let U := chaconTowerSystem.koopmanZeroRep
  have hGen := generator_sub_scalar_injective_of_weaklyMixing U chaconTower_isWeaklyMixing (-1)
  have hVal (v : meanZero chaconTowerSystem.measure) :
      chaconHeightPolynomialOperatorZero 1 v =
        (1/2 : ℝ) • (v + U (Multiplicative.ofAdd (-1)) v) := by
    simp only [chaconHeightPolynomialOperatorZero, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, add_apply, smul_apply, chaconSpacerProbability_one_zero, chaconSpacerProbability_one_one,
      Nat.cast_zero, Nat.cast_one, neg_zero, show Multiplicative.ofAdd (0 : ℤ) = 1 by rfl,
      map_one, smul_add, U]
    rfl
  have hmul (v : meanZero chaconTowerSystem.measure) :
      U (Multiplicative.ofAdd 1) (U (Multiplicative.ofAdd (-1)) v) = v := by
    change (U (Multiplicative.ofAdd 1) * U (Multiplicative.ofAdd (-1))) v = _
    rw [← map_mul, show Multiplicative.ofAdd (1 : ℤ) * Multiplicative.ofAdd (-1) = 1 by rfl,
      map_one]
    rfl
  intro v w h
  rw [hVal, hVal] at h
  have hh := congrArg (fun z : meanZero chaconTowerSystem.measure ↦ (2 : ℝ) • z) h
  simp only [smul_smul, show (2 : ℝ) * (1/2) = 1 by norm_num, one_smul] at hh
  have he := congrArg (U (Multiplicative.ofAdd 1)) hh
  rw [map_add, map_add, hmul, hmul] at he
  apply hGen
  simp only [sub_apply, ContinuousLinearMap.algebraMap_apply, neg_smul, one_smul, sub_neg_eq_add]
  exact he

private theorem injective_chaconHeightTime_one : Function.Injective (chaconHeightTime 1) := by
  have ht : StrictMono chaconTowerHeight := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [chaconTowerHeight]
    omega
  intro n k h
  apply ht.injective
  have he := congrArg Multiplicative.toAdd h
  change (↑(1 * chaconTowerHeight n) : ℤ) = ↑(1 * chaconTowerHeight k) at he
  simp only [one_mul] at he
  exact Int.ofNat_inj.mp he

/-- The height sequence for `m = 1` realizes an injective free-ultrafilter
limit of the concrete Chacon system. -/
theorem chaconTower_exists_free_injective_limit :
    ∃ p ∈ freeUltrafilters (Multiplicative ℤ),
      Function.Injective (ultrafilterOperator chaconTowerSystem.koopmanZeroRep p) := by
  let q : Ultrafilter ℕ := Ultrafilter.of atTop
  let p := q.map (chaconHeightTime 1)
  have hq : (q : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  refine ⟨p, ?_, ?_⟩
  · change (p : Filter (Multiplicative ℤ)) ≤ cofinite
    refine (Filter.map_mono hq).trans ?_
    change Tendsto (chaconHeightTime 1) atTop cofinite
    simpa only [Nat.cofinite_eq_atTop] using injective_chaconHeightTime_one.tendsto_cofinite
  · rw [show p = q.map (chaconHeightTime 1) by rfl, ultrafilterOperator_chaconHeight_zero 1 q hq]
    exact injective_chaconHeightPolynomialOperatorZero_one

/-- Example 2's generation and spectral-disjointness conclusion is attained
along a specific free ultrafilter of the actual Chacon system. -/
theorem example2_chaconTower_height_ultrafilter :
    ∃ p ∈ freeUltrafilters (Multiplicative ℤ),
      chaconTowerSystem.generatedSigma {p} = (inferInstance : MeasurableSpace (ChaconOdometer × Bool)) ∧
      ∀ {Y : Type*} [MeasurableSpace Y] (T : System (Multiplicative ℤ) Y), T.IsUMixing {p} →
        SpectrallyDisjoint chaconTowerSystem.koopmanZeroRep T.koopmanZeroRep := by
  obtain ⟨p, hp, hinj⟩ := chaconTower_exists_free_injective_limit
  exact ⟨p, hp, chaconTowerSystem.generated_and_spectrallyDisjoint_of_injective_limit p hinj⟩

/-- Chacon's system is spectrally disjoint from every strongly mixing system. -/
theorem example2_chaconTower_spectrallyDisjoint_stronglyMixing
    {Y : Type*} [MeasurableSpace Y] (T : System (Multiplicative ℤ) Y)
    (hT : IsStronglyMixing T.koopmanZeroRep) :
    SpectrallyDisjoint chaconTowerSystem.koopmanZeroRep T.koopmanZeroRep := by
  obtain ⟨p, hp, _, hdis⟩ := example2_chaconTower_height_ultrafilter
  have hm := (isStronglyMixing_iff_isUMixing_free T.koopmanZeroRep).mp hT
  exact hdis T (fun q hq ↦ hm q (Set.mem_singleton_iff.mp hq ▸ hp))

end Mixing
