/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconDecayOperators

/-! # Termination of the Chacon weak-limit factorization -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Classical ENNReal InnerProductSpace Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

local notation "𝓗" => meanZero chaconTowerSystem.measure
local notation "𝓤" => chaconTowerSystem.koopmanZeroRep
local notation "ℤₘ" => Multiplicative ℤ

private theorem chaconDecay_ultrafilterOperator_pure (g : ℤₘ) :
    ultrafilterOperator 𝓤 (pure g) = linearRepresentation 𝓤 g := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff 𝓤 (pure g) x y)
    (tendsto_pure_nhds _ _)

/-- The polynomial of either signed tower-height limit is injective on
the mean-zero space. -/
theorem chaconDecayOperator_injective (reverse : Bool) (m : ℕ) :
    Function.Injective (chaconDecayOperator reverse m) := by
  cases reverse
  · exact chaconHeightPolynomialOperatorZero_injective m
  · let q : Ultrafilter ℕ := Ultrafilter.of atTop
    have hq : (q : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
    have hN : IsStarNormal (chaconHeightPolynomialOperatorZero m) := by
      rw [← ultrafilterOperator_chaconHeight_zero m q hq]
      exact ultrafilterOperator_normal 𝓤 _
    change Function.Injective (chaconHeightPolynomialOperatorZero m).adjoint
    apply LinearMap.ker_eq_bot.mp
    change (chaconHeightPolynomialOperatorZero m).adjoint.ker = ⊥
    rw [(normal_ker_adjoint_ker_pow _ hN (n := 1) (by decide)).1]
    exact LinearMap.ker_eq_bot.mpr (chaconHeightPolynomialOperatorZero_injective m)

theorem chaconDecayProduct_injective (indices : List (Bool × ℕ)) :
    Function.Injective (chaconDecayProduct indices) := by
  induction indices with
  | nil =>
    change Function.Injective (id : 𝓗 → 𝓗)
    exact Function.injective_id
  | cons j js ih =>
    change Function.Injective (chaconDecayOperator j.1 j.2 ∘ chaconDecayProduct js)
    exact (chaconDecayOperator_injective j.1 j.2).comp ih

/-- If every nonzero free limit splits off one signed positive-height
polynomial, then the weak limit is zero or a finite product followed by a
single power. Iterating indefinitely forces zero by spectral decay. -/
theorem chaconDecay_classification_of_extraction
    (hstep : ∀ p : Ultrafilter ℤₘ, p ∈ freeUltrafilters ℤₘ →
      ultrafilterOperator 𝓤 p ≠ 0 →
        ∃ (reverse : Bool) (m : ℕ) (q : Ultrafilter ℤₘ), 0 < m ∧
          ultrafilterOperator 𝓤 p = chaconDecayOperator reverse m * ultrafilterOperator 𝓤 q)
    (p : Ultrafilter ℤₘ) :
    ultrafilterOperator 𝓤 p = 0 ∨
      ∃ (indices : List (Bool × ℕ)) (g : ℤₘ),
        (∀ j ∈ indices, 0 < j.2) ∧
        ultrafilterOperator 𝓤 p = chaconDecayProduct indices * linearRepresentation 𝓤 g := by
  let FiniteProduct (p : Ultrafilter ℤₘ) := ∃ (indices : List (Bool × ℕ)) (g : ℤₘ),
    (∀ j ∈ indices, 0 < j.2) ∧
    ultrafilterOperator 𝓤 p = chaconDecayProduct indices * linearRepresentation 𝓤 g
  let Bad (p : Ultrafilter ℤₘ) := ultrafilterOperator 𝓤 p ≠ 0 ∧ ¬ FiniteProduct p
  change ultrafilterOperator 𝓤 p = 0 ∨ FiniteProduct p
  by_contra! hp
  have hfree (q : Ultrafilter ℤₘ) (hq : Bad q) : q ∈ freeUltrafilters ℤₘ := by
    rcases q.le_cofinite_or_eq_pure with h | ⟨g, rfl⟩
    · exact h
    · exact (hq.2 ⟨[], g, by simp, by
        rw [chaconDecay_ultrafilterOperator_pure]; simp [chaconDecayProduct]⟩).elim
  have hIter (n : ℕ) (p : Ultrafilter ℤₘ) (hp : Bad p) :
      ∃ (l : List (Bool × ℕ)) (q : Ultrafilter ℤₘ), l.length = n ∧
        (∀ j ∈ l, 0 < j.2) ∧ Bad q ∧
        ultrafilterOperator 𝓤 p = chaconDecayProduct l * ultrafilterOperator 𝓤 q := by
    induction n generalizing p with
    | zero =>
      refine ⟨[], p, rfl, by simp, hp, ?_⟩
      simp [chaconDecayProduct]
    | succ n ih =>
      obtain ⟨b, m, q, hm, he⟩ := hstep p (hfree p hp) hp.1
      have hq : Bad q := by
        refine ⟨fun h ↦ hp.1 (by rw [he, h, mul_zero]), ?_⟩
        rintro ⟨l, a, hl, heq⟩
        refine hp.2 ⟨(b, m) :: l, a, ?_, ?_⟩
        · intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hm
          · exact hl j hj
        · rw [he, heq]
          simp only [chaconDecayProduct, List.map_cons, List.prod_cons, mul_assoc]
      obtain ⟨l, r, hlen, hl, hr, hEq⟩ := ih q hq
      refine ⟨(b, m) :: l, r, by simp [hlen], ?_, hr, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hm
        · exact hl j hj
      · rw [he, hEq]
        simp only [chaconDecayProduct, List.map_cons, List.prod_cons, mul_assoc]
  choose l q hlen hpos hBad hEq using fun n ↦ hIter n p hp
  have hZero : ultrafilterOperator 𝓤 p = 0 := by
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro x
    rw [zero_apply, inner_zero_right]
    have hLimit := (tendsto_chaconDecayProduct_adjoint_zero l hpos
      (by simp only [hlen]; exact tendsto_id) x).norm.mul_const ‖y‖
    simp only [norm_zero, zero_mul] at hLimit
    have hBound (n : ℕ) :
        ‖⟪x, ultrafilterOperator 𝓤 p y⟫_ℂ‖ ≤ ‖(star (chaconDecayProduct (l n))) x‖ * ‖y‖ := by
      rw [hEq n, mul_apply_eq_comp, ← ContinuousLinearMap.adjoint_inner_left]
      apply (norm_inner_le_norm _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (ultrafilterOperator_norm_le_one 𝓤 (q n)))
    exact norm_eq_zero.mp
      (le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hLimit hBound) (norm_nonneg _))
  exact hp.1 hZero

/-- The Chacon conclusion of Example 2, reduced to one signed height
factorization step for the nonzero free limits. -/
theorem example2_chaconTower_of_height_extraction
    (hstep : ∀ p : Ultrafilter ℤₘ, p ∈ freeUltrafilters ℤₘ →
      ultrafilterOperator 𝓤 p ≠ 0 →
        ∃ (reverse : Bool) (m : ℕ) (q : Ultrafilter ℤₘ), 0 < m ∧
          ultrafilterOperator 𝓤 p = chaconDecayOperator reverse m * ultrafilterOperator 𝓤 q)
    (p : Ultrafilter ℤₘ) :
    chaconTowerSystem.IsUMixing {p} ∨
      (chaconTowerSystem.generatedSigma {p} = (inferInstance : MeasurableSpace (ChaconOdometer × Bool)) ∧
        ∀ {Y : Type*} [MeasurableSpace Y] (T : System ℤₘ Y), T.IsUMixing {p} →
          SpectrallyDisjoint 𝓤 T.koopmanZeroRep) := by
  rcases chaconDecay_classification_of_extraction hstep p with h | ⟨l, g, _, h⟩
  · left
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact h
  · right
    apply chaconTowerSystem.generated_and_spectrallyDisjoint_of_injective_limit p
    rw [h]
    exact (chaconDecayProduct_injective l).comp (𝓤 g).injective

end Mixing
