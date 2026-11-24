/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconWeakLimitRecursion

/-! # Pointwise decay bounds for the Chacon height polynomials -/

@[expose] public section

open Polynomial Filter
open scoped Classical Topology

namespace Mixing

/-- The Chacon height polynomial at a complex spectral parameter. -/
noncomputable def chaconDecayValue (z : ℂ) (m : ℕ) : ℂ :=
  (chaconPolynomial m).eval₂ (algebraMap ℝ ℂ) z

/-- The larger of the norms of two consecutive height polynomials. -/
noncomputable def chaconDecayPair (z : ℂ) (m : ℕ) : ℝ :=
  max ‖chaconDecayValue z m‖ ‖chaconDecayValue z (m + 1)‖

/-- The one-digit contraction factor on the unit circle. -/
noncomputable def chaconDecayRatio (z : ℂ) : ℝ := (‖1 + z‖ + 1) / 3

theorem chaconDecayRatio_nonneg (z : ℂ) : 0 ≤ chaconDecayRatio z := by
  unfold chaconDecayRatio
  positivity

theorem chaconDecayRatio_le_one {z : ℂ} (hz : ‖z‖ = 1) : chaconDecayRatio z ≤ 1 := by
  have h := norm_add_le (1 : ℂ) z
  rw [norm_one, hz] at h
  unfold chaconDecayRatio
  linarith

theorem chaconDecayRatio_lt_one {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    chaconDecayRatio z < 1 := by
  have h := norm_add_le (1 : ℂ) z
  rw [norm_one, hz] at h
  have hz' : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      _ = Complex.normSq z := by rw [Complex.normSq_apply]; ring
      _ = ‖z‖ ^ 2 := Complex.sq_norm z |>.symm
      _ = 1 := by simp [hz]
  have hlt : z.re < 1 := by
    have hr := Complex.re_le_norm z
    rw [hz] at hr
    rcases hr.lt_or_eq with ht | he
    · exact ht
    · exfalso
      apply hne
      apply Complex.ext
      · simpa only [Complex.one_re] using he
      · rw [he] at hz'
        simpa only [Complex.one_im] using (sq_eq_zero_iff.mp (by nlinarith : z.im ^ 2 = 0))
  have hsq : ‖1 + z‖ ^ 2 = 2 + 2 * z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
    nlinarith
  unfold chaconDecayRatio
  have hn : ‖1 + z‖ < 2 := lt_of_le_of_ne (by linarith) (by
    intro he
    rw [he] at hsq
    linarith)
  linarith

theorem chaconDecayValue_zero (z : ℂ) : chaconDecayValue z 0 = 1 := by
  simp [chaconDecayValue, chaconPolynomial_zero]

theorem chaconDecayValue_one (z : ℂ) :
    chaconDecayValue z 1 = (2 : ℂ)⁻¹ * (1 + z) := by
  simp [chaconDecayValue, chaconPolynomial_one]

theorem chaconDecayValue_three (z : ℂ) (m : ℕ) :
    chaconDecayValue z (3*m) = z^m * chaconDecayValue z m := by
  simp [chaconDecayValue, chaconPolynomial_three, Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem chaconDecayValue_three_add_one (z : ℂ) (m : ℕ) :
    chaconDecayValue z (3*m+1) =
      (3 : ℂ)⁻¹ * z^m * ((1 + z) * chaconDecayValue z m + chaconDecayValue z (m+1)) := by
  simp [chaconDecayValue, chaconPolynomial_three_add_one, Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem chaconDecayValue_three_add_two (z : ℂ) (m : ℕ) :
    chaconDecayValue z (3*m+2) =
      (3 : ℂ)⁻¹ * z^m * (z * chaconDecayValue z m + (1 + z) * chaconDecayValue z (m+1)) := by
  simp [chaconDecayValue, chaconPolynomial_three_add_two, Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem chaconDecayPair_nonneg (z : ℂ) (m : ℕ) : 0 ≤ chaconDecayPair z m :=
  (norm_nonneg _).trans (le_max_left ..)

theorem chaconDecayValue_norm_three {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    ‖chaconDecayValue z (3*m)‖ = ‖chaconDecayValue z m‖ := by
  rw [chaconDecayValue_three, norm_mul, norm_pow, hz, one_pow, one_mul]

theorem chaconDecayValue_norm_three_add_one {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    ‖chaconDecayValue z (3*m+1)‖ ≤ chaconDecayRatio z * chaconDecayPair z m := by
  rw [chaconDecayValue_three_add_one, norm_mul, norm_mul, norm_pow, hz, one_pow, mul_one]
  have h₁ := norm_add_le ((1 + z) * chaconDecayValue z m) (chaconDecayValue z (m+1))
  rw [norm_mul] at h₁
  have h₂ := mul_le_mul_of_nonneg_left
    (le_max_left ‖chaconDecayValue z m‖ ‖chaconDecayValue z (m+1)‖) (norm_nonneg (1 + z))
  have h₃ : ‖chaconDecayValue z (m+1)‖ ≤ chaconDecayPair z m := le_max_right .. 
  rw [show ‖(3 : ℂ)⁻¹‖ = 1/3 by norm_num]
  unfold chaconDecayRatio chaconDecayPair at *
  nlinarith

theorem chaconDecayValue_norm_three_add_two {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    ‖chaconDecayValue z (3*m+2)‖ ≤ chaconDecayRatio z * chaconDecayPair z m := by
  rw [chaconDecayValue_three_add_two, norm_mul, norm_mul, norm_pow, hz, one_pow, mul_one]
  have h₁ := norm_add_le (z * chaconDecayValue z m) ((1 + z) * chaconDecayValue z (m+1))
  rw [norm_mul, norm_mul, hz, one_mul] at h₁
  have h₂ := mul_le_mul_of_nonneg_left
    (le_max_right ‖chaconDecayValue z m‖ ‖chaconDecayValue z (m+1)‖) (norm_nonneg (1 + z))
  have h₃ : ‖chaconDecayValue z m‖ ≤ chaconDecayPair z m := le_max_left ..
  rw [show ‖(3 : ℂ)⁻¹‖ = 1/3 by norm_num]
  unfold chaconDecayRatio chaconDecayPair at *
  nlinarith

theorem chaconDecayPair_append_one {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    chaconDecayPair z (3*m+1) ≤ chaconDecayRatio z * chaconDecayPair z m :=
  max_le (chaconDecayValue_norm_three_add_one hz m) (chaconDecayValue_norm_three_add_two hz m)

theorem chaconDecayPair_append_le {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) (d : Fin 3) :
    chaconDecayPair z (3*m + d.val) ≤ chaconDecayPair z m := by
  have he : chaconDecayRatio z * chaconDecayPair z m ≤ chaconDecayPair z m :=
    mul_le_of_le_one_left (chaconDecayPair_nonneg z m) (chaconDecayRatio_le_one hz)
  fin_cases d
  · change chaconDecayPair z (3*m+0) ≤ _
    rw [add_zero, chaconDecayPair, chaconDecayValue_norm_three hz]
    exact max_le (le_max_left ..) ((chaconDecayValue_norm_three_add_one hz m).trans he)
  · exact (chaconDecayPair_append_one hz m).trans he
  · change max ‖chaconDecayValue z (3*m+2)‖ ‖chaconDecayValue z (3*m+2+1)‖ ≤ _
    rw [show 3*m+2+1 = 3*(m+1) by omega, chaconDecayValue_norm_three hz]
    exact max_le ((chaconDecayValue_norm_three_add_two hz m).trans he) (le_max_right ..)

/-- A switch from ternary digit 0 to digit 2 contracts the consecutive pair. -/
theorem chaconDecayPair_append_zero_two {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    chaconDecayPair z (3*(3*m)+2) ≤ chaconDecayRatio z * chaconDecayPair z m := by
  refine max_le ?_ ?_
  · exact (chaconDecayValue_norm_three_add_two hz (3*m)).trans
      (mul_le_mul_of_nonneg_left (chaconDecayPair_append_le hz m 0) (chaconDecayRatio_nonneg z))
  · change ‖chaconDecayValue z (3*(3*m)+2+1)‖ ≤ _
    rw [show 3*(3*m)+2+1 = 3*(3*m+1) by omega, chaconDecayValue_norm_three hz]
    exact chaconDecayValue_norm_three_add_one hz m

/-- A switch from ternary digit 2 to digit 0 contracts the consecutive pair. -/
theorem chaconDecayPair_append_two_zero {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    chaconDecayPair z (3*(3*m+2)) ≤ chaconDecayRatio z * chaconDecayPair z m := by
  refine max_le ?_ ?_
  · rw [chaconDecayValue_norm_three hz]
    exact chaconDecayValue_norm_three_add_two hz m
  · exact (chaconDecayValue_norm_three_add_one hz (3*m+2)).trans
      (mul_le_mul_of_nonneg_left (chaconDecayPair_append_le hz m 2) (chaconDecayRatio_nonneg z))

theorem chaconDecayPair_le_one {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) : chaconDecayPair z m ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    by_cases hm : m = 0
    · subst m
      rw [chaconDecayPair, zero_add, chaconDecayValue_zero, norm_one, chaconDecayValue_one,
        norm_mul, show ‖(2 : ℂ)⁻¹‖ = 1/2 by norm_num]
      have ht := norm_add_le (1 : ℂ) z
      rw [norm_one, hz] at ht
      exact max_le le_rfl (by linarith)
    · have hd : m / 3 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by omega)
      let d : Fin 3 := ⟨m % 3, Nat.mod_lt _ (by decide)⟩
      have hEq : 3*(m/3) + d.val = m := by
        dsimp [d]
        omega
      rw [← hEq]
      exact (chaconDecayPair_append_le hz (m/3) d).trans (ih (m/3) hd)

/-- A uniform spectral bound for every positive-height polynomial. -/
theorem chaconDecayValue_norm_le_ratio {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) (hm : 0 < m) :
    ‖chaconDecayValue z m‖ ≤ chaconDecayRatio z := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    let k := m / 3
    have hEq : m = 3*k + m % 3 := by dsimp [k]; omega
    have hk : k < m := Nat.div_lt_self hm (by decide)
    have hn : chaconDecayRatio z * chaconDecayPair z k ≤ chaconDecayRatio z :=
      mul_le_of_le_one_right (chaconDecayRatio_nonneg z) (chaconDecayPair_le_one hz k)
    have hd : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hd with hd | hd | hd
    · have he : m = 3*k := by omega
      rw [he, chaconDecayValue_norm_three hz]
      exact ih k hk (by omega)
    · have he : m = 3*k+1 := by omega
      rw [he]
      exact (chaconDecayValue_norm_three_add_one hz k).trans hn
    · have he : m = 3*k+2 := by omega
      rw [he]
      exact (chaconDecayValue_norm_three_add_two hz k).trans hn

end Mixing
