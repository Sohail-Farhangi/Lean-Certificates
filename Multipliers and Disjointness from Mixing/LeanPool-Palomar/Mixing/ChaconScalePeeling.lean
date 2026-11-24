/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconScaleUltrafilters

/-! # Extracting a signed height polynomial from a nonzero free limit -/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

/-- The approximation for an integral scale ratio needed to peel off
one height polynomial. -/
def ChaconSmallRemainderFactorization : Prop :=
  ∀ (q : Ultrafilter ℕ) (m : ℕ) (n : ℕ → ℕ) (s : ℕ → ℤ), Tendsto n q atTop →
    Tendsto (fun j ↦ ((s j).natAbs : ℝ) / chaconTowerHeight (n j)) q (𝓝 0) →
    let U := chaconTowerSystem.koopmanZeroRep
    ultrafilterOperator U (q.map (fun j ↦
      Multiplicative.ofAdd ((m * chaconTowerHeight (n j) : ℕ) + s j))) =
      chaconHeightPolynomialOperatorZero m *
        ultrafilterOperator U (q.map (Multiplicative.ofAdd ∘ s))

/-- The limiting operator is zero in the branch where no normalized
height ratio is integral. -/
def ChaconNonintegralScaleDecay : Prop :=
  ∀ (q : Ultrafilter ℕ), (q : Filter ℕ) ≤ atTop →
    ∀ τ ∈ Icc (1 : ℝ) 3, (∀ r m : ℕ, τ * 3 ^ r ≠ (m : ℝ)) →
      (∀ r : ℕ, Tendsto (chaconScaleLevel r) q atTop ∧
        ∀ᶠ j in (q : Filter ℕ), j / chaconTowerHeight (chaconScaleLevel r j) =
          chaconScaleCoefficient τ r) →
      ultrafilterOperator chaconTowerSystem.koopmanZeroRep (q.map chaconNaturalTime) = 0

/-- The integral branch factors through a positive height polynomial,
while the nonintegral branch vanishes under the decay estimate. -/
theorem chaconNaturalTime_zero_or_height_factor
    (hSmall : ChaconSmallRemainderFactorization) (hDecay : ChaconNonintegralScaleDecay)
    (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop) :
    let U := chaconTowerSystem.koopmanZeroRep
    ultrafilterOperator U (q.map chaconNaturalTime) = 0 ∨
      ∃ (m : ℕ) (p' : Ultrafilter (Multiplicative ℤ)), 0 < m ∧
        ultrafilterOperator U (q.map chaconNaturalTime) =
          chaconHeightPolynomialOperatorZero m * ultrafilterOperator U p' := by
  rcases chaconNaturalTime_scale_dichotomy q hq with
    ⟨m, n, s, hm, hn, hs, htime⟩ | ⟨τ, hτ, hNon, hProfile⟩
  · have h := hSmall q m n s hn hs
    have he : (fun j ↦ Multiplicative.ofAdd ((m * chaconTowerHeight (n j) : ℕ) + s j)) =
        chaconNaturalTime := by
      funext j
      exact congrArg Multiplicative.ofAdd (htime j).symm
    simp only [he] at h
    exact Or.inr ⟨m, q.map (Multiplicative.ofAdd ∘ s), hm, h⟩
  · exact Or.inl (hDecay q hq τ hτ hNon hProfile)

/-- The sign indicates whether to take the adjoint of the polynomial
limit along positive heights. -/
noncomputable def chaconSignedHeightPolynomialOperatorZero (b : Bool) (m : ℕ) :
    meanZero chaconTowerSystem.measure →L[ℂ] meanZero chaconTowerSystem.measure :=
  if b then (chaconHeightPolynomialOperatorZero m).adjoint
  else chaconHeightPolynomialOperatorZero m

/-- A height polynomial commutes with every weak limit of powers. -/
theorem chaconHeightPolynomialOperatorZero_commute (m : ℕ) (p : Ultrafilter (Multiplicative ℤ)) :
    Commute (chaconHeightPolynomialOperatorZero m)
      (ultrafilterOperator chaconTowerSystem.koopmanZeroRep p) := by
  let q : Ultrafilter ℕ := Ultrafilter.of atTop
  have hq : (q : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  rw [← ultrafilterOperator_chaconHeight_zero m q hq]
  exact ultrafilterOperator_commute_pair _ _ _

/-- The positive and negative cases of the scale analysis give a signed
height factor for every nonzero free weak limit. -/
theorem chaconFree_zero_or_signed_height_factor
    (hSmall : ChaconSmallRemainderFactorization) (hDecay : ChaconNonintegralScaleDecay)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    let U := chaconTowerSystem.koopmanZeroRep
    ultrafilterOperator U p = 0 ∨
      ∃ (b : Bool) (m : ℕ) (p' : Ultrafilter (Multiplicative ℤ)), 0 < m ∧
        ultrafilterOperator U p =
          chaconSignedHeightPolynomialOperatorZero b m * ultrafilterOperator U p' := by
  let U := chaconTowerSystem.koopmanZeroRep
  obtain ⟨q, hq, hqLift⟩ := chaconNaturalTime_lift_or_inverse p hp
  have h := chaconNaturalTime_zero_or_height_factor hSmall hDecay q hq
  dsimp only at h
  rcases hqLift with he | he
  · rw [he] at h
    rcases h with hz | ⟨m, p', hm, hp'⟩
    · exact Or.inl hz
    · exact Or.inr ⟨false, m, p', hm,
        by simpa only [chaconSignedHeightPolynomialOperatorZero, Bool.false_eq_true, ite_false]
          using hp'⟩
  · rw [he, ultrafilterOperator_inverse] at h
    rcases h with hz | ⟨m, p', hm, hp'⟩
    · left
      have hs := congrArg star hz
      change star (star (ultrafilterOperator U p)) = star (0 : _ →L[ℂ] _) at hs
      simpa only [star_star, star_zero] using hs
    · right
      refine ⟨true, m, inverseUltrafilter p', hm, ?_⟩
      have hComm := chaconHeightPolynomialOperatorZero_commute m p'
      rw [hComm.eq] at hp'
      have hs := congrArg star hp'
      change star (star (ultrafilterOperator U p)) =
        star (ultrafilterOperator U p' * chaconHeightPolynomialOperatorZero m) at hs
      simpa only [star_star, star_mul, chaconSignedHeightPolynomialOperatorZero,
        ite_true, ultrafilterOperator_inverse, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_adjoint] using hs

end Mixing
