/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PolynomialShifts
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Complex.Basic

/-! # Polynomial coefficient averages for a weakly mixing unitary vector -/

public section

open Filter Finset Polynomial
open scoped BigOperators Topology Polynomial InnerProductSpace ComplexConjugate

namespace JdLG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private noncomputable def phaseForAbsolute (z : ℂ) : ℂ :=
  if z = 0 then 0 else conj z / (‖z‖ : ℂ)

private theorem phaseForAbsolute_norm_le (z : ℂ) : ‖phaseForAbsolute z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseForAbsolute, hz]
  · simp [phaseForAbsolute, hz]

private theorem phaseForAbsolute_mul (z : ℂ) : phaseForAbsolute z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [phaseForAbsolute, hz]
  · have hNorm : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    simp only [phaseForAbsolute, hz, ite_false, div_mul_eq_mul_div,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    exact (div_eq_iff hNorm).mpr (pow_two _)

private theorem unitaryInt_inner_difference (U : Multiplicative ℤ →* E ≃ₗᵢ[ℂ] E)
    (a b : ℤ) (x : E) :
    inner ℂ (U (Multiplicative.ofAdd a) x) (U (Multiplicative.ofAdd b) x) =
      inner ℂ x (U (Multiplicative.ofAdd (b - a)) x) := by
  let R (a : ℤ) := U (Multiplicative.ofAdd a)
  have hAdd (a b : ℤ) : R a (R b x) = R (a + b) x := by
    change (U (Multiplicative.ofAdd a) * U (Multiplicative.ofAdd b)) x =
      U (Multiplicative.ofAdd (a + b)) x
    rw [← map_mul]
    rfl
  have hZero : R 0 x = x := by change U 1 x = x; rw [map_one]; rfl
  calc
    inner ℂ (R a x) (R b x) = inner ℂ (R (-a) (R a x)) (R (-a) (R b x)) :=
      ((R (-a)).inner_map_map (R a x) (R b x)).symm
    _ = _ := by rw [hAdd, hAdd, neg_add_cancel, hZero, show -a + b = b - a by omega]

private theorem scalarCesaro_abs_coeff_of_shiftDifferences
    (U : Multiplicative ℤ →* E ≃ₗᵢ[ℂ] E) (x y : E) (p : ℤ[X])
    (hc : ∀ h j : ℕ, h ≠ j →
      Tendsto (scalarCesaro fun n ↦ ‖inner ℂ x
        (U (Multiplicative.ofAdd (p.eval (n + j : ℤ) - p.eval (n + h : ℤ))) x)‖)
        atTop (𝓝 0)) :
    Tendsto (scalarCesaro fun n ↦ ‖inner ℂ y (U (Multiplicative.ofAdd (p.eval n)) x)‖)
      atTop (𝓝 0) := by
  let u (n : ℕ) := U (Multiplicative.ofAdd (p.eval n)) x
  let c (n : ℕ) := phaseForAbsolute (inner ℂ y (u n))
  let v (n : ℕ) := c n • u n
  have hPhase (n : ℕ) : ‖c n‖ ≤ 1 := phaseForAbsolute_norm_le _
  have hV (n : ℕ) : ‖v n‖ ≤ ‖x‖ := by
    change ‖c n • u n‖ ≤ ‖x‖
    rw [norm_smul, show ‖u n‖ = ‖x‖ from (U _).norm_map x]
    exact mul_le_of_le_one_left (norm_nonneg _) (hPhase n)
  have hCorr (h j : ℕ) (hh : h ≠ j) :
      Tendsto (scalarCesaro fun n ↦ ‖inner ℂ (v (n + h)) (v (n + j))‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun N ↦ mul_nonneg (by positivity) (sum_nonneg fun n _ ↦ norm_nonneg _))
      (fun N ↦ ?_) (hc h j hh)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro n _
    calc
      _ = ‖c (n + h)‖ * (‖c (n + j)‖ * ‖inner ℂ (u (n + h)) (u (n + j))‖) := by
        simp only [v, inner_smul_left, inner_smul_right, norm_mul, RCLike.norm_conj]
        rw [mul_left_comm]
      _ ≤ 1 * (1 * ‖inner ℂ (u (n + h)) (u (n + j))‖) :=
        mul_le_mul (hPhase _) (mul_le_mul_of_nonneg_right (hPhase _) (norm_nonneg _))
          (by positivity) zero_le_one
      _ = _ := by simp only [one_mul, u, Nat.cast_add, unitaryInt_inner_difference]
  have hVlim := tendsto_vectorCesaro_zero_of_abs_correlations v ‖x‖ hV hCorr
  let ψ := Complex.reCLM.comp ((innerSL ℂ y).restrictScalars ℝ)
  have hψ (a : E) : ψ a = (inner ℂ y a).re := rfl
  have hValue (n : ℕ) : ψ (v n) = ‖inner ℂ y (u n)‖ := by
    rw [hψ, show v n = c n • u n from rfl, inner_smul_right, phaseForAbsolute_mul]
    exact Complex.ofReal_re _
  have hMean (N : ℕ) :
      ψ (vectorCesaro v N) = scalarCesaro (fun n ↦ ‖inner ℂ y (u n)‖) N := by
    rw [vectorCesaro, scalarCesaro, map_smul, map_sum, smul_eq_mul]
    simp only [hValue]
  have hlim := (ψ.continuous.tendsto 0).comp hVlim
  change Tendsto (fun N ↦ ψ (vectorCesaro v N)) atTop (𝓝 (ψ 0)) at hlim
  simpa only [hMean, map_zero, u] using hlim

/-- A unitary weakly mixing self-coefficient stays Cesàro-null along every
nonconstant integer polynomial. -/
theorem tendsto_abs_self_coeff_polynomial
    (U : Multiplicative ℤ →* E ≃ₗᵢ[ℂ] E) (x : E)
    (hlin : Tendsto (scalarCesaro fun n : ℕ ↦ ‖inner ℂ x (U (Multiplicative.ofAdd (n : ℤ)) x)‖)
      atTop (𝓝 0)) (p : ℤ[X]) (hp : 0 < p.natDegree) :
    Tendsto (scalarCesaro fun n ↦ ‖inner ℂ x (U (Multiplicative.ofAdd (p.eval n)) x)‖)
      atTop (𝓝 0) := by
  let f (n : ℤ) := ‖inner ℂ x (U (Multiplicative.ofAdd n) x)‖
  have hzero : U (Multiplicative.ofAdd (0 : ℤ)) x = x := by change U 1 x = x; rw [map_one]; rfl
  have hSym (n : ℤ) : f (-n) = f n := by
    have h := unitaryInt_inner_difference U n 0 x
    rw [hzero, zero_sub] at h
    exact (congrArg norm h).symm.trans (norm_inner_symm _ _)
  have hBound (n : ℤ) : ‖f n‖ ≤ ‖x‖ * ‖x‖ := by
    change ‖‖inner ℂ x (U (Multiplicative.ofAdd n) x)‖‖ ≤ ‖x‖ * ‖x‖
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_inner_le_norm (𝕜 := ℂ) x (U (Multiplicative.ofAdd n) x)).trans_eq
      (congrArg (‖x‖ * ·) ((U (Multiplicative.ofAdd n)).norm_map x))
  have hAll (d : ℕ) : ∀ p : ℤ[X], p.natDegree = d → 0 < d →
      Tendsto (scalarCesaro fun n ↦ f (p.eval n)) atTop (𝓝 0) := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro p hd hPos
      by_cases hOne : d = 1
      · have hdeg : p.natDegree = 1 := hd.trans hOne
        have ha : p.coeff 1 ≠ 0 := by
          rw [← hdeg, coeff_natDegree]
          apply leadingCoeff_ne_zero.mpr
          intro h
          simp [h] at hdeg
        have hpEval (n : ℕ) : p.eval (n : ℤ) = p.coeff 1 * n + p.coeff 0 := by
          conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg.le]
          simp
        simpa only [hpEval] using tendsto_scalarCesaro_int_affine
          (f := f) (fun _ ↦ norm_nonneg _) hSym _ hBound hlin (p.coeff 1) (p.coeff 0) ha
      · apply scalarCesaro_abs_coeff_of_shiftDifferences U x x p
        intro h j hhj
        have hp₂ : 2 ≤ p.natDegree := by omega
        let q := p.taylor (j : ℤ) - p.taylor (h : ℤ)
        have hq : q.natDegree = p.natDegree - 1 :=
          natDegree_shiftDifference p hp₂ (by exact_mod_cast hhj.symm)
        have hEval (n : ℕ) : q.eval (n : ℤ) = p.eval (n + j : ℤ) - p.eval (n + h : ℤ) := by
          simp [q, taylor_eval]
        simpa only [hEval, f] using ih q.natDegree (by omega) q rfl (by omega)
  exact hAll p.natDegree p rfl hp

/-- A unitary operator defines a representation of the additive integers by its
integer powers. -/
@[expose] noncomputable def unitaryIntegerPowers (U : E ≃ₗᵢ[ℂ] E) :
    Multiplicative ℤ →* E ≃ₗᵢ[ℂ] E where
  toFun n := U ^ n.toAdd
  map_one' := zpow_zero _
  map_mul' m n := zpow_add _ m.toAdd n.toAdd

@[simp] theorem unitaryIntegerPowers_ofAdd (U : E ≃ₗᵢ[ℂ] E) (n : ℤ) :
    unitaryIntegerPowers U (Multiplicative.ofAdd n) = U ^ n := rfl

/-- Equation (20). For a unitary vector whose linear absolute self-coefficient
is Cesàro-null, the absolute coefficients against any vector are Cesàro-null
along all power sequences of degree at least two. The sum uses indices 1 through N. -/
theorem tendsto_abs_coeff_perfect_powers (U : E ≃ₗᵢ[ℂ] E) (x y : E)
    (hlin : Tendsto (scalarCesaro fun n : ℕ ↦ ‖inner ℂ x ((U ^ (n : ℤ)) x)‖)
      atTop (𝓝 0)) (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (scalarCesaro fun n ↦ ‖inner ℂ ((U ^ (((n : ℤ) + 1) ^ k)) x) y‖)
      atTop (𝓝 0) := by
  let p : ℤ[X] := (X + C 1) ^ k
  have hp : p.natDegree = k := natDegree_pow_X_add_C _ _
  have hEval (n : ℕ) : p.eval (n : ℤ) = ((n : ℤ) + 1) ^ k := by simp [p]
  have h := scalarCesaro_abs_coeff_of_shiftDifferences (unitaryIntegerPowers U) x y p
    fun a b hab ↦ by
      let q := p.taylor (b : ℤ) - p.taylor (a : ℤ)
      have hq : q.natDegree = p.natDegree - 1 :=
        natDegree_shiftDifference p (hp.symm ▸ hk) (by exact_mod_cast hab.symm)
      have hqEval (n : ℕ) : q.eval (n : ℤ) = p.eval (n + b : ℤ) - p.eval (n + a : ℤ) := by
        simp [q, taylor_eval]
      simpa only [hqEval] using tendsto_abs_self_coeff_polynomial (unitaryIntegerPowers U) x hlin q
        (by omega)
  simpa only [hEval, unitaryIntegerPowers_ofAdd, norm_inner_symm y] using h

end JdLG
