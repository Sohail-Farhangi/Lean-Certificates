/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Torus
public import VdC.Permissible
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Linear and quadratic exponential averages needed for the polynomial example. -/

@[expose] public section

open Filter Function MeasureTheory
open scoped ComplexConjugate Topology

namespace VdC

noncomputable section

/-- The exponential character `exp(2πit)`. -/
def phase (t : ℝ) : ℂ := fourier (T := 1) 1 (t : UnitAddCircle)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (a b : ℝ) : phase (a + b) = phase a * phase b := by
  simp only [phase, AddCircle.coe_add, fourier_apply, one_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul]

@[simp] theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  rw [phase, fourier_apply, Circle.norm_coe]

theorem phase_frequency (m : ℤ) (t : ℝ) :
    fourier m (t : UnitAddCircle) = phase ((m : ℝ) * t) := by
  rw [phase, fourier_apply, fourier_apply, one_zsmul, ← zsmul_eq_mul, AddCircle.coe_zsmul]

theorem star_phase (a : ℝ) : star (phase a) = phase (-a) := by
  change conj (fourier 1 (a : UnitAddCircle)) = phase (-a)
  rw [← fourier_neg, phase_frequency, Int.cast_neg, Int.cast_one, neg_one_mul]

theorem phase_sub (a b : ℝ) : phase (a - b) = phase a * star (phase b) := by
  rw [sub_eq_add_neg, phase_add, star_phase]

theorem phase_ne_one_of_irrational {b : ℝ} (hb : Irrational b) : phase b ≠ 1 := by
  intro h
  have hto : AddCircle.toCircle (b : UnitAddCircle) = AddCircle.toCircle (0 : UnitAddCircle) := by
    apply Subtype.ext
    simpa only [phase, fourier_apply, one_zsmul, AddCircle.toCircle_zero, Circle.coe_one] using h
  have h0 := (AddCircle.injective_toCircle (one_ne_zero : (1 : ℝ) ≠ 0)) hto
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
  exact hb.ne_int m (by simpa [zsmul_eq_mul] using hm.symm)

/-- The geometric-sum estimate is uniform in the intercept and prefix length. -/
theorem norm_sum_linear_phase_le {b : ℝ} (hb : phase b ≠ 1) (c : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (b * (n : ℝ) + c)‖ ≤ 2 / ‖phase b - 1‖ := by
  have hstep (n : ℕ) : phase (b * ((n+1 : ℕ) : ℝ) + c) =
      phase b * phase (b * (n : ℝ) + c) := by
    rw [← phase_add]
    congr 1
    push_cast
    ring
  have hsum (L : ℕ) : (phase b - 1) *
      (∑ n ∈ Finset.range L, phase (b * (n : ℝ) + c)) = phase (b * (L : ℝ) + c) - phase c := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, mul_add, ih, hstep]
      ring
  have hd : 0 < ‖phase b - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  rw [le_div_iff₀ hd, mul_comm, ← norm_mul, hsum]
  simpa [one_add_one_eq_two] using norm_sub_le (phase (b * (N : ℝ) + c)) (phase c)

/-- The linear exponential sum tends to zero when its slope is irrational. -/
theorem tendsto_cesaro_linear_phase {b : ℝ} (hb : Irrational b) (c : ℝ) :
    Tendsto (cesaro (fun n : ℕ ↦ phase (b * (n : ℝ) + c))) atTop (𝓝 0) := by
  let u (n : ℕ) := phase (b * (n : ℝ) + c)
  have hU : BoundedSeq u := ⟨1, zero_le_one, fun n ↦ (norm_phase _).le⟩
  have hstep : (fun n ↦ u (n + 1)) = fun n ↦ phase b * u n := by
    funext n
    dsimp only [u]
    rw [← phase_add]
    congr 1
    push_cast
    ring
  have h := tendsto_cesaro_shift_sub_zero hU 1
  rw [hstep] at h
  have he (N : ℕ) : cesaro (fun n ↦ phase b * u n) N - cesaro u N =
      (phase b - 1) * cesaro u N := by rw [cesaro_const_mul, sub_mul, one_mul]
  simp_rw [he] at h
  have hne : phase b - 1 ≠ 0 := sub_ne_zero.mpr (phase_ne_one_of_irrational hb)
  have hdiv := h.const_mul (phase b - 1)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_zero] using hdiv

/-- The quadratic exponential sum tends to zero when its leading coefficient is
irrational. All positive-lag autocorrelations reduce to the linear result. -/
theorem tendsto_cesaro_quadratic_phase {a : ℝ} (ha : Irrational a) (b c : ℝ) :
    Tendsto (cesaro (fun n : ℕ ↦ phase (a * (n : ℝ)^2 + b * (n : ℝ) + c))) atTop (𝓝 0) := by
  let u (n : ℕ) := phase (a * (n : ℝ)^2 + b * (n : ℝ) + c)
  have hU : BoundedSeq u := ⟨1, zero_le_one, fun n ↦ (norm_phase _).le⟩
  apply NearlyOrthogonal.tendsto_cesaro_zero
  apply (nearlyOrthogonal_iff_corr_tendsto_zero hU).2
  intro h hh
  have he : (fun n ↦ u (n + h) * star (u n)) =
      fun n : ℕ ↦ phase ((2 * a * (h : ℝ)) * (n : ℝ) + (a * (h : ℝ)^2 + b * (h : ℝ))) := by
    funext n
    simp only [u, ← phase_sub, Nat.cast_add]
    congr 1
    ring
  have hirr : Irrational (2 * a * (h : ℝ)) := by
    have ha2 : Irrational (2 * a) := by
      simpa only [Int.cast_ofNat] using ha.intCast_mul (m := 2) (by norm_num)
    exact ha2.mul_natCast hh.ne'
  unfold corr
  rw [he]
  exact tendsto_cesaro_linear_phase hirr _

/-- The normalized phase of a nonconstant integer polynomial of degree at most two
vanishes on average when the common factor `α` is irrational. -/
theorem tendsto_cesaro_integer_quadratic_phase {α : ℝ} (hα : Irrational α)
    (a b c : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    Tendsto (cesaro (fun n : ℕ ↦ phase (α * ((a : ℝ) * (n : ℝ)^2 + (b : ℝ) * (n : ℝ) + (c : ℝ)))))
      atTop (𝓝 0) := by
  have he : (fun n : ℕ ↦ phase (α * ((a : ℝ) * (n : ℝ)^2 + (b : ℝ) * (n : ℝ) + (c : ℝ)))) =
      fun n : ℕ ↦ phase ((α * a) * (n : ℝ)^2 + (α * b) * (n : ℝ) + α * c) := by
    funext n
    congr 1
    ring
  rw [he]
  by_cases ha : a = 0
  · subst a
    simpa using tendsto_cesaro_linear_phase (hα.mul_intCast (h.resolve_left (by simp))) (α * c)
  · exact tendsto_cesaro_quadratic_phase (hα.mul_intCast ha) _ _

end

end VdC
