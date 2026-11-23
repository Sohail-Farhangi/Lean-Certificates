/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParityFolner
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# A finite-dimensional realization of the parity example

The span of the indicator and the constant one is invariant under right
translation. On this span the operators are determined by parity, so their
weak-operator closure is compact.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

open scoped ENNReal

local notation "W" => lp (fun _ : Point ↦ ℂ) ∞

/-- On coefficients of the indicator and constant one, an even right
translate retains the sum of the coefficients. -/
noncomputable def evenCyclicOperator : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (0 : (ℂ × ℂ) →L[ℂ] ℂ).prod
    (ContinuousLinearMap.fst ℂ ℂ ℂ + ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- An odd right translate retains only the coefficient of the constant one. -/
noncomputable def oddCyclicOperator : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (0 : (ℂ × ℂ) →L[ℂ] ℂ).prod (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The right translation action on the two-dimensional cyclic span. -/
noncomputable def cyclicRepresentation : Point →ₙ* ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) where
  toFun s := if s.first % 2 = 0 then evenCyclicOperator else oddCyclicOperator
  map_mul' s t := by
    simp only [first_mod_two_mul]
    split_ifs <;> apply ContinuousLinearMap.ext <;> intro x <;>
      apply Prod.ext <;> simp [evenCyclicOperator, oddCyclicOperator]

/-- The coefficient realization of the cyclic span in the bounded functions. -/
noncomputable def cyclicEmbedding : (ℂ × ℂ) →ₗ[ℂ] W where
  toFun x := x.1 • indicator + x.2 • (1 : W)
  map_add' x y := by
    change (x.1 + y.1) • indicator + (x.2 + y.2) • (1 : W) =
      (x.1 • indicator + x.2 • (1 : W)) + (y.1 • indicator + y.2 • (1 : W))
    rw [add_smul, add_smul]
    abel
  map_smul' c x := by
    change (c * x.1) • indicator + (c * x.2) • (1 : W) =
      c • (x.1 • indicator + x.2 • (1 : W))
    rw [mul_smul, mul_smul, smul_add]

private theorem rightTranslation_one (s : Point) : rightTranslation s (1 : W) = 1 := by
  apply lp.ext
  rfl

theorem cyclicEmbedding_intertwines (s : Point) (x : ℂ × ℂ) :
    cyclicEmbedding (cyclicRepresentation s x) =
      rightTranslation s (cyclicEmbedding x) := by
  change cyclicEmbedding ((if s.first % 2 = 0 then evenCyclicOperator else oddCyclicOperator) x)
    = rightTranslation s (x.1 • indicator + x.2 • (1 : W))
  rw [map_add, map_smul, map_smul, rightTranslation_indicator, rightTranslation_one]
  split_ifs
  · change (0 : ℂ) • indicator + (x.1 + x.2) • (1 : W) =
      x.1 • (1 : W) + x.2 • (1 : W)
    rw [zero_smul, zero_add, add_smul]
  · change (0 : ℂ) • indicator + x.2 • (1 : W) =
      x.1 • (0 : W) + x.2 • (1 : W)
    rw [zero_smul, smul_zero]

theorem cyclicEmbedding_injective : Function.Injective cyclicEmbedding := by
  classical
  intro x y h
  have ho := congrArg (fun f : W ↦ f oddPoint) h
  have he := congrArg (fun f : W ↦ f (⟨0, 1⟩ : Point)) h
  have hodd : oddPoint ∉ Set.range (· * evenPoint) := by
    intro hmem
    exact (by decide : oddPoint.first % 2 ≠ 0) ((even_ideal_shape _).1 hmem).1
  have heven : (⟨0, 1⟩ : Point) ∈ Set.range (· * evenPoint) :=
    (even_ideal_shape _).2 (by decide)
  change (x.1 • indicator + x.2 • (1 : W)) oddPoint =
    (y.1 • indicator + y.2 • (1 : W)) oddPoint at ho
  change (x.1 • indicator + x.2 • (1 : W)) (⟨0, 1⟩ : Point) =
    (y.1 • indicator + y.2 • (1 : W)) (⟨0, 1⟩ : Point) at he
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    indicator_apply, ite_eq_right hodd, smul_zero, zero_add] at ho
  change x.2 * (1 : ℂ) = y.2 * 1 at ho
  simp only [mul_one] at ho
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
    indicator_apply, ite_eq_left heven, smul_eq_mul, mul_one] at he
  change x.1 + x.2 * (1 : ℂ) = y.1 + y.2 * 1 at he
  simp only [ho, mul_one] at he
  exact Prod.ext (add_right_cancel he) ho

theorem cyclicRepresentation_weakly_compact :
    IsCompact (weakOperatorClosure cyclicRepresentation : Set ((ℂ × ℂ) →WOT[ℂ] (ℂ × ℂ))) := by
  have hf : (Set.range (weakRepresentation cyclicRepresentation)).Finite :=
    ((Set.finite_singleton (ContinuousLinearMapWOT.ofCLM oddCyclicOperator)).insert
      (ContinuousLinearMapWOT.ofCLM evenCyclicOperator)).subset (by
      rintro _ ⟨s, rfl⟩
      change ContinuousLinearMapWOT.ofCLM
        (if s.first % 2 = 0 then evenCyclicOperator else oddCyclicOperator) ∈ _
      split_ifs <;> simp)
  change IsCompact (closure (Set.range (weakRepresentation cyclicRepresentation)))
  rw [hf.isClosed.closure_eq]
  exact hf.isCompact

theorem cyclic_e0_almost_weakly_stable :
    IsAlmostWeaklyStable (closureAction cyclicRepresentation) ((1, 0) : ℂ × ℂ) :=
  ⟨closureInclusion cyclicRepresentation oddPoint, rfl⟩

end JdLG.PaperExamplesParity
