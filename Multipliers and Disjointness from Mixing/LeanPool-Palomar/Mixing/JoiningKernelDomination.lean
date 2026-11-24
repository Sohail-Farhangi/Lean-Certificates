/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.JoiningExtreme
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # Geometric domination from the joining-kernel inequality -/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace Mixing

variable {W G X Y : Type*} [CommGroup G]
variable [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]

private theorem comp_mono_measure (κ : Kernel W W) :
    Monotone (fun μ : Measure W => κ ∘ₘ μ) := by
  intro μ ν hμν
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
  exact lintegral_mono' hμν le_rfl

private theorem tendsto_pow_ENNReal {q : ℝ≥0∞} (hq : q < 1) :
    Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) := by
  have hTop : q ≠ ∞ := (hq.trans ENNReal.one_lt_top).ne
  have hReal : q.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal hTop ENNReal.one_ne_top).2 hq
  have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
    (tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.toReal_nonneg hReal)
  simpa only [Function.comp_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hTop, ENNReal.ofReal_zero] using h

/-- Iterating a contractive upper bound under a stationary Markov kernel eliminates
the probability-measure remainder. -/
theorem le_smul_of_markov_comp_bound
    (κ : Kernel W W) [IsMarkovKernel κ] (μ ν : Measure W) [IsProbabilityMeasure μ]
    (hFix : κ ∘ₘ ν = ν) {A q D : ℝ≥0∞} (hq : q < 1) (hD : A + q * D = D)
    (hStep : μ ≤ A • ν + q • (κ ∘ₘ μ)) : μ ≤ D • ν := by
  let go (n : ℕ) := ((fun η : Measure W => κ ∘ₘ η)^[n]) μ
  have hSucc (n : ℕ) : go (n + 1) = κ ∘ₘ go n := Function.iterate_succ_apply' _ _ _
  have hProb (n : ℕ) : IsProbabilityMeasure (go n) := by
    induction n with
    | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
    | succ n ih =>
      rw [hSucc]
      exact inferInstance
  have hBound (n : ℕ) : μ ≤ D • ν + q ^ n • go n := by
    induction n with
    | zero =>
      change μ ≤ D • ν + q ^ 0 • μ
      rw [pow_zero, one_smul]
      exact Measure.le_iff'.mpr fun s => by rw [add_apply]; exact le_add_self
    | succ n ih =>
      have hApplied := comp_mono_measure κ ih
      change κ ∘ₘ μ ≤ κ ∘ₘ (D • ν + q ^ n • go n) at hApplied
      rw [Measure.comp_add, Measure.comp_smul, Measure.comp_smul, hFix, ← hSucc] at hApplied
      calc
        μ ≤ A • ν + q • (κ ∘ₘ μ) := hStep
        _ ≤ A • ν + q • (D • ν + q ^ n • go (n + 1)) := by gcongr
        _ = (A + q * D) • ν + q ^ (n + 1) • go (n + 1) := by
          rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, pow_succ']
        _ = _ := by rw [hD]
  apply Measure.le_iff'.mpr
  intro s
  have hL := (tendsto_const_nhds (x := (D • ν) s)).add (tendsto_pow_ENNReal hq)
  have hPoint (n : ℕ) : μ s ≤ (D • ν) s + q ^ n := calc
    μ s ≤ (D • ν + q ^ n • go n) s := hBound n s
    _ = (D • ν) s + q ^ n * go n s := by rw [add_apply]; rfl
    _ ≤ (D • ν) s + q ^ n * 1 := by
      let := hProb n
      gcongr
      exact prob_le_one
    _ = _ := by rw [mul_one]
  simpa only [add_zero] using ge_of_tendsto' hL hPoint

private theorem le_smul_of_partial_mix_kernel_bound
    (κ : Kernel W W) [IsMarkovKernel κ] (μ ν : Measure W) [IsProbabilityMeasure μ]
    (hFix : κ ∘ₘ ν = ν) {α β : ℝ} (hα : 0 < α) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hSum : 1 < α + β)
    (hStep : ENNReal.ofReal α • μ ≤
      ENNReal.ofReal β • ν + ENNReal.ofReal (1 - β) • (κ ∘ₘ μ)) :
    μ ≤ ENNReal.ofReal (β / (α + β - 1)) • ν := by
  let A := β / α
  let q := (1 - β) / α
  let D := β / (α + β - 1)
  have hA : 0 ≤ A := div_nonneg hβ₀ hα.le
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hβ₁) hα.le
  have hD : 0 ≤ D := div_nonneg hβ₀ (by linarith)
  have hqLt : q < 1 := (div_lt_one hα).mpr (by linarith)
  have hqLt' : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
    exact hqLt
  have hEq : A + q * D = D := by
    have hPos : 0 < α + β - 1 := by linarith
    dsimp [A, q, D]
    field_simp [hα.ne', hPos.ne']
    ring
  have hEq' : ENNReal.ofReal A + ENNReal.ofReal q * ENNReal.ofReal D = ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_add hA (mul_nonneg hq hD), hEq]
  have hInv : 0 ≤ α⁻¹ := inv_nonneg.mpr hα.le
  have hNorm : μ ≤ ENNReal.ofReal A • ν + ENNReal.ofReal q • (κ ∘ₘ μ) := calc
    μ = ENNReal.ofReal α⁻¹ • (ENNReal.ofReal α • μ) := by
      rw [smul_smul, ← ENNReal.ofReal_mul hInv, inv_mul_cancel₀ hα.ne',
        ENNReal.ofReal_one, one_smul]
    _ ≤ ENNReal.ofReal α⁻¹ • (ENNReal.ofReal β • ν +
        ENNReal.ofReal (1 - β) • (κ ∘ₘ μ)) := by gcongr
    _ = _ := by
      rw [smul_add, smul_smul, smul_smul, ← ENNReal.ofReal_mul hInv, ← ENNReal.ofReal_mul hInv]
      simp only [A, q, div_eq_mul_inv, mul_comm α⁻¹]
  exact le_smul_of_markov_comp_bound κ μ ν hFix hqLt' hEq' hNorm

/-- Theorem 5.1 from the measure inequality implied by equation (14).
The partially mixing coordinate is listed first. Its residual Markov kernel
preserves that coordinate's measure. No decomposition into extreme joinings is needed. -/
theorem theorem5_1_of_joining_kernel_inequality [Countable G]
    {T : System G X} {S : System G Y} (hWeak : IsWeaklyMixing T.koopmanZeroRep)
    (κ : Kernel X X) [IsMarkovKernel κ] (hStationary : κ ∘ₘ T.measure = T.measure)
    {α β : ℝ} (hα : 0 < α) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hSum : 1 < α + β)
    (hStep : ∀ μ, IsJoining T S μ → ENNReal.ofReal α • μ ≤
      ENNReal.ofReal β • T.measure.prod S.measure +
        ENNReal.ofReal (1 - β) • ((κ ∥ₖ Kernel.id) ∘ₘ μ)) :
    Disjoint T S := by
  obtain ⟨p, hp⟩ := System.exists_isUMixing_singleton hWeak
  intro μ hμ
  let := hμ.probability
  have hFix : (κ ∥ₖ Kernel.id) ∘ₘ (T.measure.prod S.measure) = T.measure.prod S.measure := by
    rw [← Measure.prod_comp_left, hStationary]
  have hDom := le_smul_of_partial_mix_kernel_bound (κ ∥ₖ Kernel.id)
    μ (T.measure.prod S.measure) hFix hα hβ₀ hβ₁ hSum (hStep μ hμ)
  exact dominated_joining_eq_prod hμ ENNReal.ofReal_ne_top hDom p hp

/-- Equation (14), when expressed as an equality of joining measures via Markov
kernels, forces disjointness. The kernel on the partly mixing coordinate is stationary. -/
theorem theorem5_1_of_joining_kernel_equation [Countable G]
    {T : System G X} {S : System G Y} (hWeak : IsWeaklyMixing T.koopmanZeroRep)
    (κ : Kernel X X) [IsMarkovKernel κ] (hStationary : κ ∘ₘ T.measure = T.measure)
    (η : Kernel Y Y) [IsMarkovKernel η]
    {α β : ℝ} (hα : 0 < α) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hSum : 1 < α + β)
    (hEquation : ∀ μ, IsJoining T S μ →
      ENNReal.ofReal α • μ + ENNReal.ofReal (1 - α) • ((Kernel.id ∥ₖ η) ∘ₘ μ) =
        ENNReal.ofReal β • T.measure.prod S.measure +
          ENNReal.ofReal (1 - β) • ((κ ∥ₖ Kernel.id) ∘ₘ μ)) :
    Disjoint T S := by
  apply theorem5_1_of_joining_kernel_inequality hWeak κ hStationary hα hβ₀ hβ₁ hSum
  intro μ hμ
  rw [← hEquation μ hμ]
  apply Measure.le_iff'.mpr
  intro a
  rw [add_apply]
  exact le_self_add

end Mixing
