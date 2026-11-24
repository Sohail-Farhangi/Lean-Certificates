/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconDecayTermination

/-! # The finite convex combination in the Chacon example -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

local notation "𝓗" => meanZero chaconTowerSystem.measure
local notation "𝓤" => chaconTowerSystem.koopmanZeroRep
local notation "ℤₘ" => Multiplicative ℤ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A finite weighted sum of powers, with signed exponents. -/
noncomputable def chaconWeightedPowerSum (U : ℤₘ →* (H ≃ₗᵢ[ℂ] H))
    (l : List (ℝ × ℤ)) : H →L[ℂ] H :=
  (l.map fun w ↦ w.1 • linearRepresentation U (Multiplicative.ofAdd w.2)).sum

/-- The weights in a convex list of powers are nonnegative and add to one. -/
def ChaconConvexWeights (l : List (ℝ × ℤ)) : Prop :=
  (∀ w ∈ l, 0 ≤ w.1) ∧ (l.map Prod.fst).sum = 1

private def chaconConvolutionTerms (a b : List (ℝ × ℤ)) : List (ℝ × ℤ) :=
  a.flatMap fun x ↦ b.map fun y ↦ (x.1 * y.1, x.2 + y.2)

private theorem chaconConvolutionTerms_convex {a b : List (ℝ × ℤ)}
    (ha : ChaconConvexWeights a) (hb : ChaconConvexWeights b) :
    ChaconConvexWeights (chaconConvolutionTerms a b) := by
  constructor
  · intro w hw
    obtain ⟨u, hu, hmap⟩ := List.mem_flatMap.mp hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hmap
    exact mul_nonneg (ha.1 u hu) (hb.1 v hv)
  · have h (u : ℝ × ℤ) (b : List (ℝ × ℤ)) :
        ((b.map fun v ↦ (u.1 * v.1, u.2 + v.2)).map Prod.fst).sum =
          u.1 * (b.map Prod.fst).sum := by
      induction b with
      | nil => simp
      | cons v vs ih => simpa only [List.map_cons, List.sum_cons, mul_add] using congrArg (u.1 * v.1 + ·) ih
    have hsum (a : List (ℝ × ℤ)) :
        ((chaconConvolutionTerms a b).map Prod.fst).sum = (a.map Prod.fst).sum * (b.map Prod.fst).sum := by
      induction a with
      | nil => simp [chaconConvolutionTerms]
      | cons u us ih =>
        change (((b.map fun v ↦ (u.1 * v.1, u.2 + v.2)) ++ chaconConvolutionTerms us b).map
          Prod.fst).sum = _
        rw [List.map_append, List.sum_append, h, ih, List.map_cons, List.sum_cons, add_mul]
    rw [hsum, ha.2, hb.2, one_mul]

private theorem chaconWeightedPowerSum_convolution (U : ℤₘ →* (H ≃ₗᵢ[ℂ] H))
    (a b : List (ℝ × ℤ)) :
    chaconWeightedPowerSum U (chaconConvolutionTerms a b) =
      chaconWeightedPowerSum U a * chaconWeightedPowerSum U b := by
  have h (u : ℝ × ℤ) (b : List (ℝ × ℤ)) :
      chaconWeightedPowerSum U (b.map fun v ↦ (u.1 * v.1, u.2 + v.2)) =
        (u.1 • linearRepresentation U (Multiplicative.ofAdd u.2)) * chaconWeightedPowerSum U b := by
    induction b with
    | nil => simp [chaconWeightedPowerSum]
    | cons v vs ih =>
      change (u.1 * v.1) • linearRepresentation U (Multiplicative.ofAdd (u.2 + v.2)) +
        chaconWeightedPowerSum U (vs.map fun v ↦ (u.1 * v.1, u.2 + v.2)) =
        (u.1 • linearRepresentation U (Multiplicative.ofAdd u.2)) *
          (v.1 • linearRepresentation U (Multiplicative.ofAdd v.2) + chaconWeightedPowerSum U vs)
      rw [ih, mul_add, show Multiplicative.ofAdd (u.2 + v.2) =
        Multiplicative.ofAdd u.2 * Multiplicative.ofAdd v.2 from rfl, map_mul]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm v.1 u.1]
  induction a with
  | nil => simp [chaconConvolutionTerms, chaconWeightedPowerSum]
  | cons u us ih =>
    change chaconWeightedPowerSum U ((b.map fun v ↦ (u.1 * v.1, u.2 + v.2)) ++
      chaconConvolutionTerms us b) =
      (u.1 • linearRepresentation U (Multiplicative.ofAdd u.2) + chaconWeightedPowerSum U us) *
        chaconWeightedPowerSum U b
    have happ (l₁ l₂ : List (ℝ × ℤ)) :
        chaconWeightedPowerSum U (l₁ ++ l₂) = chaconWeightedPowerSum U l₁ +
          chaconWeightedPowerSum U l₂ := by simp [chaconWeightedPowerSum]
    rw [happ, h, ih, add_mul]

private noncomputable def chaconHeightTerms (reverse : Bool) (m : ℕ) : List (ℝ × ℤ) :=
  (Finset.range (m+1)).toList.map fun k ↦
    (chaconSpacerProbability m k, if reverse then (k : ℤ) else -(k : ℤ))

private theorem chaconHeightTerms_convex (reverse : Bool) (m : ℕ) :
    ChaconConvexWeights (chaconHeightTerms reverse m) := by
  constructor
  · intro w hw
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw
    exact measureReal_nonneg
  · simp only [chaconHeightTerms, List.map_map, Function.comp_apply, Finset.sum_map_toList]
    simpa only [chaconPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one, chaconSpacerProbability] using
      chaconPolynomial_eval_one m

private theorem chaconWeightedPowerSum_height (reverse : Bool) (m : ℕ) :
    chaconWeightedPowerSum 𝓤 (chaconHeightTerms reverse m) = chaconDecayOperator reverse m := by
  cases reverse
  · simp only [chaconWeightedPowerSum, chaconHeightTerms, Bool.false_eq_true, ite_false, List.map_map,
      Function.comp_apply, Finset.sum_map_toList, chaconDecayOperator, chaconHeightPolynomialOperatorZero]
    rfl
  · simp only [chaconWeightedPowerSum, chaconHeightTerms, ite_true, List.map_map,
      Function.comp_apply, Finset.sum_map_toList, chaconDecayOperator, chaconHeightPolynomialOperatorZero]
    change _ = star (∑ k ∈ Finset.range (m+1),
      chaconSpacerProbability m k • linearRepresentation 𝓤 (Multiplicative.ofAdd (-(k : ℤ))))
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hReal (r : ℝ) (A : 𝓗 →L[ℂ] 𝓗) : star (r • A) = r • star A := by
      rw [← IsScalarTower.algebraMap_smul ℂ r A, star_smul]
      change conj (r : ℂ) • star A = r • star A
      rw [Complex.conj_ofReal]
      exact IsScalarTower.algebraMap_smul ℂ r (star A)
    rw [hReal, linearRepresentation_star]
    have hx : (Multiplicative.ofAdd (-(k : ℤ)))⁻¹ = Multiplicative.ofAdd (k : ℤ) := by
      change -(-(k : ℤ)) = (k : ℤ)
      rw [neg_neg]
    rw [hx]
    rfl

private theorem chaconDecayProduct_convex (indices : List (Bool × ℕ)) (g : ℤₘ) :
    ∃ l, ChaconConvexWeights l ∧
      chaconWeightedPowerSum 𝓤 l = chaconDecayProduct indices * linearRepresentation 𝓤 g := by
  induction indices with
  | nil =>
    refine ⟨[(1, g.toAdd)], by simp [ChaconConvexWeights], ?_⟩
    change (1 : ℝ) • linearRepresentation 𝓤 g + 0 = 1 * linearRepresentation 𝓤 g
    rw [one_smul, add_zero, one_mul]
  | cons j js ih =>
    obtain ⟨l, hl, he⟩ := ih
    refine ⟨chaconConvolutionTerms (chaconHeightTerms j.1 j.2) l,
      chaconConvolutionTerms_convex (chaconHeightTerms_convex j.1 j.2) hl, ?_⟩
    rw [chaconWeightedPowerSum_convolution, chaconWeightedPowerSum_height, he]
    change chaconDecayOperator j.1 j.2 * (chaconDecayProduct js * _) =
      (chaconDecayOperator j.1 j.2 * chaconDecayProduct js) * _
    rw [mul_assoc]

/-- The finite convex combination of powers in Example 2 on mean-zero L². -/
theorem chaconDecay_convex_of_extraction
    (hstep : ∀ p : Ultrafilter ℤₘ, p ∈ freeUltrafilters ℤₘ →
      ultrafilterOperator 𝓤 p ≠ 0 →
        ∃ (reverse : Bool) (m : ℕ) (q : Ultrafilter ℤₘ), 0 < m ∧
          ultrafilterOperator 𝓤 p = chaconDecayOperator reverse m * ultrafilterOperator 𝓤 q)
    (p : Ultrafilter ℤₘ) :
    ultrafilterOperator 𝓤 p = 0 ∨
      ∃ l, ChaconConvexWeights l ∧ ultrafilterOperator 𝓤 p = chaconWeightedPowerSum 𝓤 l := by
  rcases chaconDecay_classification_of_extraction hstep p with h | ⟨l, g, _, h⟩
  · exact Or.inl h
  · obtain ⟨a, ha, hA⟩ := chaconDecayProduct_convex l g
    exact Or.inr ⟨a, ha, h.trans hA.symm⟩

private theorem chaconWeightedPowerSum_meanZero (l : List (ℝ × ℤ)) (v : 𝓗) :
    chaconWeightedPowerSum chaconTowerSystem.koopmanRep l v =
      (chaconWeightedPowerSum 𝓤 l v : 𝓗) := by
  induction l with
  | nil => rfl
  | cons j js ih =>
    change j.1 • chaconTowerSystem.koopmanRep (Multiplicative.ofAdd j.2) (v : Lp ℂ 2 _) +
      chaconWeightedPowerSum chaconTowerSystem.koopmanRep js v =
        ((j.1 • 𝓤 (Multiplicative.ofAdd j.2) v + chaconWeightedPowerSum 𝓤 js v : 𝓗) :
          Lp ℂ 2 chaconTowerSystem.measure)
    rw [ih]
    rfl

private theorem chaconWeightedPowerSum_constantOne (l : List (ℝ × ℤ)) :
    chaconWeightedPowerSum chaconTowerSystem.koopmanRep l (constantOne chaconTowerSystem.measure) =
      (l.map Prod.fst).sum • constantOne chaconTowerSystem.measure := by
  induction l with
  | nil => simp [chaconWeightedPowerSum]
  | cons j js ih =>
    change j.1 • chaconTowerSystem.koopmanRep (Multiplicative.ofAdd j.2)
        (constantOne chaconTowerSystem.measure) +
      chaconWeightedPowerSum chaconTowerSystem.koopmanRep js (constantOne chaconTowerSystem.measure) =
        (j.1 + (js.map Prod.fst).sum) • constantOne chaconTowerSystem.measure
    have h := chaconTowerSystem.koopman_constantOne (Multiplicative.ofAdd j.2)
    change chaconTowerSystem.koopmanRep (Multiplicative.ofAdd j.2)
      (constantOne chaconTowerSystem.measure) = _ at h
    rw [h, ih, add_smul]

/-- The precise alternative in Example 2 on the full Koopman space:
the orthogonal projector onto constants or a finite convex combination of powers. -/
theorem chaconDecay_convex_full_of_extraction
    (hstep : ∀ p : Ultrafilter ℤₘ, p ∈ freeUltrafilters ℤₘ →
      ultrafilterOperator 𝓤 p ≠ 0 →
        ∃ (reverse : Bool) (m : ℕ) (q : Ultrafilter ℤₘ), 0 < m ∧
          ultrafilterOperator 𝓤 p = chaconDecayOperator reverse m * ultrafilterOperator 𝓤 q)
    (p : Ultrafilter ℤₘ) :
    let S := chaconTowerSystem
    ultrafilterOperator S.koopmanRep p =
      InnerProductSpace.rankOne ℂ (constantOne S.measure) (constantOne S.measure) ∨
      ∃ l, ChaconConvexWeights l ∧
        ultrafilterOperator S.koopmanRep p = chaconWeightedPowerSum S.koopmanRep l := by
  let S := chaconTowerSystem
  let A := ultrafilterOperator S.koopmanRep p
  let c := constantOne S.measure
  have hU : Intertwines 𝓤 S.koopmanRep (meanZero S.measure).subtypeL := fun _ _ ↦ rfl
  have hV (v : 𝓗) : A v = (ultrafilterOperator 𝓤 p v : 𝓗) := (hU.ultrafilter p v).symm
  have hC : A c = c := S.ultrafilterOperator_constantOne p
  rcases chaconDecay_convex_of_extraction hstep p with h | ⟨l, hl, h⟩
  · left
    apply ContinuousLinearMap.ext
    intro f
    let v := center S.measure f
    let t := inner ℂ c f
    have he : f = (v : Lp ℂ 2 S.measure) + t • c := eq_center_add S.measure f
    change A f = _
    rw [InnerProductSpace.rankOne_apply]
    change A f = t • c
    rw [he, map_add, map_smul, hC, hV, h]
    simp
  · right
    refine ⟨l, hl, ?_⟩
    apply ContinuousLinearMap.ext
    intro f
    let v := center S.measure f
    let t := inner ℂ c f
    let B := chaconWeightedPowerSum S.koopmanRep l
    have he : f = (v : Lp ℂ 2 S.measure) + t • c := eq_center_add S.measure f
    have hBc : B c = c := by
      rw [chaconWeightedPowerSum_constantOne, hl.2, one_smul]
    have hBv : B v = A v := by
      rw [hV, h]
      exact chaconWeightedPowerSum_meanZero l v
    change A f = B f
    rw [he, map_add, map_add, map_smul, map_smul, hC, hBc, hBv]

end Mixing
