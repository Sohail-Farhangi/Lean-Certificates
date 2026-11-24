/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconScaleSignedFactor
public import Mixing.ChaconDecayConvex

/-! # Exhausting all free limits of the concrete Chacon transformation -/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

/-- At a nonintegral normalized limit, the adjacent polynomials decay
and the sub-height column bound forces the weak limit to vanish. -/
theorem chaconNonintegralScaleDecay_verified : ChaconNonintegralScaleDecay := by
  intro q _ τ hτ hNon hProfile
  have hτ₀ : 0 ≤ τ := zero_le_one.trans hτ.1
  let m := chaconScaleCoefficient τ
  let n := chaconScaleLevel
  let e (r j : ℕ) := j % chaconTowerHeight (n r j)
  have he (r : ℕ) : ∀ᶠ j in (q : Filter ℕ),
      e r j < chaconTowerHeight (n r j) ∧ j = m r * chaconTowerHeight (n r j) + e r j := by
    filter_upwards [(hProfile r).2] with j hj
    refine ⟨Nat.mod_lt _ (chaconTowerHeight_pos _), ?_⟩
    calc
      j = chaconTowerHeight (n r j) * (j / chaconTowerHeight (n r j)) + e r j :=
        (Nat.div_add_mod _ _).symm
      _ = m r * chaconTowerHeight (n r j) + e r j := by
        rw [show j / chaconTowerHeight (n r j) = m r from hj, Nat.mul_comm]
  let d (r : ℕ) : Fin 3 :=
    ⟨chaconScaleDigit τ r, Nat.lt_succ_of_le (chaconScaleDigit_le_two τ r hτ₀)⟩
  have hd (r : ℕ) : m (r + 1) = 3 * m r + (d r).val :=
    chaconScaleCoefficient_succ τ r hτ₀
  have h0 : ¬ ∃ N, ∀ r ≥ N, d r = 0 := by
    rintro ⟨N, hN⟩
    refine (chaconScaleDigit_frequently_ne hτ₀ hNon (Or.inl rfl)) ?_
    filter_upwards [eventually_ge_atTop N] with r hr
    exact fun hn ↦ hn (congrArg Fin.val (hN r hr))
  have h2 : ¬ ∃ N, ∀ r ≥ N, d r = 2 := by
    rintro ⟨N, hN⟩
    refine (chaconScaleDigit_frequently_ne hτ₀ hNon (Or.inr rfl)) ?_
    filter_upwards [eventually_ge_atTop N] with r hr
    exact fun hn ↦ hn (congrArg Fin.val (hN r hr))
  refine chaconUltrafilter_zero_of_subHeight_decompositions q id m n e
    (fun r ↦ (hProfile r).1) he fun v ↦ ?_
  exact ⟨tendsto_chaconDecayOperator_ternary_prefix_zero m d hd h0 h2 false false v,
    tendsto_chaconDecayOperator_ternary_prefix_zero m d hd h0 h2 true false v⟩

/-- Every free, nonzero Chacon weak limit splits off a positive-height
polynomial or its adjoint. -/
theorem chaconHeightExtraction_verified (p : Ultrafilter (Multiplicative ℤ))
    (hp : p ∈ freeUltrafilters (Multiplicative ℤ))
    (hNZ : ultrafilterOperator chaconTowerSystem.koopmanZeroRep p ≠ 0) :
    ∃ (reverse : Bool) (m : ℕ) (q : Ultrafilter (Multiplicative ℤ)), 0 < m ∧
      ultrafilterOperator chaconTowerSystem.koopmanZeroRep p =
        chaconDecayOperator reverse m * ultrafilterOperator chaconTowerSystem.koopmanZeroRep q := by
  rcases chaconFree_zero_or_signed_height_factor chaconSmallRemainderFactorization_verified
      chaconNonintegralScaleDecay_verified p hp with hz | ⟨b, m, q, hm, he⟩
  · exact (hNZ hz).elim
  · exact ⟨b, m, q, hm,
      by simpa only [chaconSignedHeightPolynomialOperatorZero, chaconDecayOperator,
        ContinuousLinearMap.star_eq_adjoint] using he⟩

/-- The concrete Chacon system satisfies the mixing-or-generation
dichotomy and the accompanying spectral disjointness statement. -/
theorem example2_chaconTower (p : Ultrafilter (Multiplicative ℤ)) :
    chaconTowerSystem.IsUMixing {p} ∨
      (chaconTowerSystem.generatedSigma {p} = (inferInstance : MeasurableSpace (ChaconOdometer × Bool)) ∧
        ∀ {Y : Type*} [MeasurableSpace Y] (T : System (Multiplicative ℤ) Y), T.IsUMixing {p} →
          SpectrallyDisjoint chaconTowerSystem.koopmanZeroRep T.koopmanZeroRep) :=
  example2_chaconTower_of_height_extraction chaconHeightExtraction_verified p

/-- Every full Koopman weak limit of powers of Chacon's transformation is
the projection onto constants or a finite convex combination of powers. -/
theorem chaconTower_weakLimit_convex_powers (p : Ultrafilter (Multiplicative ℤ)) :
    let S := chaconTowerSystem
    ultrafilterOperator S.koopmanRep p =
      InnerProductSpace.rankOne ℂ (constantOne S.measure) (constantOne S.measure) ∨
      ∃ l, ChaconConvexWeights l ∧
        ultrafilterOperator S.koopmanRep p = chaconWeightedPowerSum S.koopmanRep l :=
  chaconDecay_convex_full_of_extraction chaconHeightExtraction_verified p

end Mixing
