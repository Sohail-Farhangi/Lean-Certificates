/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRigidityPhases
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuous circle-valued rigidity phases

The binary phases yield a continuous injective circle-valued map
whose powers converge uniformly to one along the given lacunary tail.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter
open scoped Topology

theorem continuous_gridNumerator (r : ℕ → ℝ) (n : ℕ) :
    Continuous (fun b : ℕ → Bool ↦ gridNumerator r b n) := by
  induction n with
  | zero =>
    exact (show Continuous binaryDigit from continuous_of_discreteTopology).comp
      (continuous_apply 0)
  | succ n ih =>
    let step (v : ℤ × Bool) : ℤ := ⌊r (n + 1) * ((v.1 : ℝ) / r n)⌋ + binaryDigit v.2
    have hstep : Continuous step := continuous_of_discreteTopology
    exact hstep.comp (ih.prodMk (continuous_apply (n + 1)))

theorem continuous_gridApproximation (r : ℕ → ℝ) (n : ℕ) :
    Continuous (fun b : ℕ → Bool ↦ gridApproximation r b n) := by
  have hcast : Continuous (Int.cast : ℤ → ℝ) := continuous_of_discreteTopology
  exact (hcast.comp (continuous_gridNumerator r n)).div_const _

theorem growth_tendsto_atTop (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) : Tendsto r atTop atTop := by
  have hl : ∀ n : ℕ, r 0 * 2 ^ n ≤ r n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right ih (by norm_num)).trans
        ((show r n * 2 ≤ 8 * r n by linarith [hr n]).trans (hg n))
  exact tendsto_atTop_mono hl (Tendsto.const_mul_atTop (hr 0)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))

theorem continuous_rigidityPhase (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) : Continuous (rigidityPhase r hg hr) := by
  have hu : TendstoUniformly (fun n b ↦ gridApproximation r b n) (rigidityPhase r hg hr)
      atTop := by
    apply Metric.tendstoUniformly_iff.2
    intro ε hε
    have ht : Tendsto (fun n : ℕ ↦ 2 / r (n + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop ((growth_tendsto_atTop r hg hr).comp (tendsto_add_atTop_nat 1))
    filter_upwards [(tendsto_order.1 ht).2 ε hε] with n hn b
    rw [dist_comm]
    exact (rigidityPhase_distance r hg hr b n).trans_lt hn
  exact hu.continuous (Frequently.of_forall (continuous_gridApproximation r))

/-- The Fourier phase corresponding to a binary sequence. -/
noncomputable def circlePhase (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (b : ℕ → Bool) : Circle :=
  Real.fourierChar (rigidityPhase r hg hr b)

theorem continuous_circlePhase (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) : Continuous (circlePhase r hg hr) :=
  Real.continuous_fourierChar.comp (continuous_rigidityPhase r hg hr)

private theorem rigidityPhase_bounded (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (h₀ : 4 ≤ r 0) (b : ℕ → Bool) :
    |rigidityPhase r hg hr b| ≤ 1 / 3 := by
  have hg₀ : 32 ≤ r 1 := by linarith [hg 0]
  have hu : 2 / r 1 ≤ 1 / 16 := by
    apply (div_le_iff₀ (hr 1)).2
    linarith
  have hd := rigidityPhase_distance r hg hr b 0
  rw [dist_comm, Real.dist_eq] at hd
  have h₁ : |gridApproximation r b 0| ≤ 1 / 4 := by
    simp only [gridApproximation, gridNumerator, abs_div]
    rw [abs_of_pos (hr 0), abs_of_nonneg (cast_binaryDigit_bounds (b 0)).1,
      div_le_iff₀ (hr 0)]
    linarith [(cast_binaryDigit_bounds (b 0)).2]
  have hsum := abs_sub (rigidityPhase r hg hr b - gridApproximation r b 0)
    (-gridApproximation r b 0)
  rw [sub_neg_eq_add, sub_add_cancel, abs_neg] at hsum
  linarith

theorem circlePhase_injective (r : ℕ → ℝ) (hg : ∀ n, 8 * r n ≤ r (n + 1))
    (hr : ∀ n, 0 < r n) (h₀ : 4 ≤ r 0) : Function.Injective (circlePhase r hg hr) := by
  intro b c hbc
  have hm (x : ℕ → Bool) :
      2 * Real.pi * rigidityPhase r hg hr x ∈ Set.Ioc (-Real.pi) Real.pi := by
    obtain ⟨hl, hu⟩ := abs_le.1 (rigidityPhase_bounded r hg hr h₀ x)
    constructor <;> nlinarith [Real.pi_pos]
  have hi : Set.InjOn Circle.exp (Set.Ioc (-Real.pi) Real.pi) :=
    Circle.exp_injOn_Ioc (by linarith)
  have heq := hi (hm b) (hm c) hbc
  apply rigidityPhase_injective r hg hr
  exact (mul_left_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0)) heq

private theorem fourierChar_sub_int (x : ℝ) (m : ℤ) :
    Real.fourierChar (x - (m : ℝ)) = Real.fourierChar x := by
  rw [Real.fourierChar_apply', Real.fourierChar_apply', mul_sub, Circle.exp_sub,
    Circle.exp_two_pi_mul_int, div_one]

/-- The powers of the circle phase converge to one uniformly on the binary
parameter space. -/
theorem circlePhase_uniform_rigidity (q : ℕ → ℕ)
    (hg : ∀ n, 8 * (q n : ℝ) ≤ (q (n + 1) : ℝ))
    (hp : ∀ n, 0 < (q n : ℝ))
    (hRatio : Tendsto (fun n ↦ (q (n + 1) : ℝ) / (q n : ℝ)) atTop atTop) :
    TendstoUniformly (fun n b ↦ circlePhase (fun j ↦ (q j : ℝ)) hg hp b ^ q n)
      (fun _ ↦ (1 : Circle)) atTop := by
  let r := fun n ↦ (q n : ℝ)
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  have hc := Real.continuous_fourierChar.continuousAt (x := (0 : ℝ))
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.1 hc ε hε
  have hu : Tendsto (fun n ↦ (2 : ℝ) / (r (n + 1) / r n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hRatio
  filter_upwards [(tendsto_order.1 hu).2 δ hδ] with n hn b
  let d := r n * rigidityPhase r hg hp b - (gridNumerator r b n : ℝ)
  have hd : dist d 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    rw [div_div_eq_mul_div] at hn
    exact (rigidityPhase_error r hg hp b n).trans_lt hn
  have hmul : Real.fourierChar d = circlePhase r hg hp b ^ q n := by
    rw [show d = r n * rigidityPhase r hg hp b - (gridNumerator r b n : ℝ) from rfl,
      fourierChar_sub_int, circlePhase, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hnear' := hnear hd
  rw [hmul, AddChar.map_zero_eq_one, dist_comm] at hnear'
  exact hnear'

end JdLG.PaperExamplesRigid
