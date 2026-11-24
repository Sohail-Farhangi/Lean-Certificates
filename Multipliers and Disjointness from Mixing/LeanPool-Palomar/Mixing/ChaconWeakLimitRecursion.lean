/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconReturnDynamics
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The spacer cocycle in the polynomial weak limits of Chacon's automorphism

The identities below use the actual spacer set of `chaconTowerSystem`. The
polynomial recursion is Theorem 3.3 of Janvresse, Prikhod’ko, de la Rue and
Ryzhikov, arXiv:1301.2904.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Polynomial Set
open scoped Classical ENNReal

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The zero-or-one spacer function of the Chacon tower. -/
noncomputable def chaconSpacerBit (x : ChaconOdometer) : ℕ :=
  if x ∈ chaconSpacer then 1 else 0

private theorem chaconSpacer_divides (x : ChaconOdometer) :
    x ∈ chaconSpacer ↔ ∃ n : ℕ, (3 : ChaconOdometer) ^ (n + 1) ∣ x + 1 - 2 * 3^n := by
  simp only [chaconSpacer, mem_iUnion, mem_ofPred_eq]
  refine exists_congr fun n ↦ ?_
  rw [PadicInt.norm_le_pow_iff_mem_span_pow (p := 3) _ (n+1), Ideal.mem_span_singleton, Nat.cast_ofNat]

theorem chaconSpacerBit_three_mul (x : ChaconOdometer) :
    chaconSpacerBit (3*x) = 0 := by
  have hs : (3*x : ChaconOdometer) ∉ chaconSpacer := by
    intro hx
    obtain ⟨n, hn⟩ := (chaconSpacer_divides _).mp hx
    have h := (dvd_pow_self (3 : ChaconOdometer) (by omega : n + 1 ≠ 0)).trans hn
    have hr : PadicInt.toZModPow (p := 3) 1 (3*x + 1 - 2*3^n) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one]
      exact h
    rw [map_sub, map_add, map_mul, map_ofNat, map_one, map_mul, map_ofNat, map_pow, map_ofNat] at hr
    change (0 : ZMod 3) * _ + 1 - 2 * 0^n = 0 at hr
    cases n with
    | zero =>
      simp only [zero_mul, zero_add, pow_zero, mul_one] at hr
      exact (by decide : (1:ZMod 3) - 2 ≠ 0) hr
    | succ n => simp at hr
  exact ite_eq_right_iff.mpr fun h => (hs h).elim

theorem chaconSpacerBit_three_mul_add_one (x : ChaconOdometer) :
    chaconSpacerBit (3*x+1) = 1 := by
  have hs : (3*x + 1 : ChaconOdometer) ∈ chaconSpacer := by
    refine (chaconSpacer_divides _).mpr ⟨0, ?_⟩
    rw [show (3*x+1+1-2*3^0 : ChaconOdometer) = 3*x by ring]
    exact dvd_mul_right _ _
  simp only [chaconSpacerBit, hs, ite_true]

theorem chaconSpacerBit_three_mul_add_two (x : ChaconOdometer) :
    chaconSpacerBit (3*x+2) = chaconSpacerBit x := by
  have hs : (3*x + 2 : ChaconOdometer) ∈ chaconSpacer ↔ x ∈ chaconSpacer := by
    rw [chaconSpacer_divides, chaconSpacer_divides]
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero =>
        have hr : PadicInt.toZModPow (p := 3) 1 (3*x+2+1-2*3^0) = 0 := by
          rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
          exact hn
        simp only [pow_zero, mul_one, map_sub, map_add, map_mul, map_one, map_ofNat] at hr
        change (0 : ZMod 3) * _ + 2 + 1 - 2 = 0 at hr
        norm_num at hr
      | succ n =>
        rw [show (3*x+2+1-2*3^(n+1) : ChaconOdometer) = 3*(x+1-2*3^n) by ring,
          pow_succ' (3 : ChaconOdometer) (n+1)] at hn
        exact ⟨n, (mul_dvd_mul_iff_left (by norm_num : (3 : ChaconOdometer) ≠ 0)).mp hn⟩
    · rintro ⟨n, hn⟩
      refine ⟨n+1, ?_⟩
      rw [show (3*x+2+1-2*3^(n+1) : ChaconOdometer) = 3*(x+1-2*3^n) by ring,
        pow_succ' (3 : ChaconOdometer) (n+1)]
      exact mul_dvd_mul_left _ hn
  unfold chaconSpacerBit
  rw [hs]

/-- The number of spacers crossed in the first `m` odometer steps. -/
noncomputable def chaconSpacerCount (m : ℕ) (x : ChaconOdometer) : ℕ :=
  ∑ j : Fin m, chaconSpacerBit (x + (j.val : ChaconOdometer))

theorem chaconReturnSum_eq_add_spacerCount (m : ℕ) (x : ChaconOdometer) :
    chaconReturnSum m x = m + chaconSpacerCount m x := rfl

theorem chaconSpacerCount_succ (m : ℕ) (x : ChaconOdometer) :
    chaconSpacerCount (m+1) x = chaconSpacerBit x + chaconSpacerCount m (x+1) := by
  rw [chaconSpacerCount, Fin.sum_univ_succ, chaconSpacerCount]
  simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, Nat.cast_add,
    Nat.cast_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem chaconSpacerCount_add (m n : ℕ) (x : ChaconOdometer) :
    chaconSpacerCount (m+n) x = chaconSpacerCount m x +
      chaconSpacerCount n (x + (m : ChaconOdometer)) := by
  induction m generalizing x with
  | zero =>
    rw [zero_add, Nat.cast_zero, add_zero]
    have hzero : chaconSpacerCount 0 x = 0 := by simp [chaconSpacerCount]
    rw [hzero, zero_add]
  | succ m hm =>
    rw [show m+1+n = m+n+1 by omega, chaconSpacerCount_succ, hm,
      chaconSpacerCount_succ]
    rw [show (x+1+(m : ChaconOdometer)) = x + ((m+1 : ℕ) : ChaconOdometer) by
      push_cast
      ring]
    omega

private theorem chaconSpacerCount_three0 (m : ℕ) (x : ChaconOdometer) :
    chaconSpacerCount (3*m) (3*x) = m + chaconSpacerCount m x := by
  induction m generalizing x with
  | zero => simp [chaconSpacerCount]
  | succ m hm =>
    rw [show 3*(m+1) = 3*m+1+1+1 by omega, chaconSpacerCount_succ,
      chaconSpacerCount_succ, chaconSpacerCount_succ, chaconSpacerBit_three_mul,
      chaconSpacerBit_three_mul_add_one,
      show (3*x+1+1 : ChaconOdometer) = 3*x+2 by ring,
      chaconSpacerBit_three_mul_add_two,
      show (3*x+2+1 : ChaconOdometer) = 3*(x+1) by ring, hm,
      chaconSpacerCount_succ]
    omega

private theorem chaconSpacerCount_three1 (m : ℕ) (x : ChaconOdometer) :
    chaconSpacerCount (3*m) (3*x+1) = m + chaconSpacerCount m x := by
  induction m generalizing x with
  | zero => simp [chaconSpacerCount]
  | succ m hm =>
    rw [show 3*(m+1) = 3*m+1+1+1 by omega, chaconSpacerCount_succ,
      chaconSpacerCount_succ, chaconSpacerCount_succ, chaconSpacerBit_three_mul_add_one,
      show (3*x+1+1 : ChaconOdometer) = 3*x+2 by ring,
      chaconSpacerBit_three_mul_add_two,
      show (3*x+2+1 : ChaconOdometer) = 3*(x+1) by ring, chaconSpacerBit_three_mul, hm,
      chaconSpacerCount_succ]
    omega

private theorem chaconSpacerCount_three2 (m : ℕ) (x : ChaconOdometer) :
    chaconSpacerCount (3*m) (3*x+2) = m + chaconSpacerCount m x := by
  induction m generalizing x with
  | zero => simp [chaconSpacerCount]
  | succ m hm =>
    rw [show 3*(m+1) = 3*m+1+1+1 by omega, chaconSpacerCount_succ,
      chaconSpacerCount_succ, chaconSpacerCount_succ, chaconSpacerBit_three_mul_add_two,
      show (3*x+2+1 : ChaconOdometer) = 3*(x+1) by ring,
      chaconSpacerBit_three_mul, chaconSpacerBit_three_mul_add_one,
      show (3*(x+1)+1+1 : ChaconOdometer) = 3*(x+1)+2 by ring,
      hm, chaconSpacerCount_succ]
    omega

/-- In every complete block of three, the two nonrecursive digits contribute one. -/
theorem chaconSpacerCount_three (m : ℕ) (r : Fin 3) (x : ChaconOdometer) :
    chaconSpacerCount (3*m) (3*x+(r.val : ChaconOdometer)) = m + chaconSpacerCount m x := by
  fin_cases r
  · simpa using chaconSpacerCount_three0 m x
  · exact chaconSpacerCount_three1 m x
  · exact chaconSpacerCount_three2 m x

theorem chaconSpacerCount_three_add_one (m : ℕ) (x : ChaconOdometer) :
    chaconSpacerCount (3*m+1) (3*x) = m + chaconSpacerCount m x ∧
      chaconSpacerCount (3*m+1) (3*x+1) = m + 1 + chaconSpacerCount m x ∧
      chaconSpacerCount (3*m+1) (3*x+2) = m + chaconSpacerCount (m+1) x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [chaconSpacerCount_succ, chaconSpacerBit_three_mul, chaconSpacerCount_three1, zero_add]
  · rw [chaconSpacerCount_succ, chaconSpacerBit_three_mul_add_one,
      show (3*x+1+1 : ChaconOdometer) = 3*x+2 by ring, chaconSpacerCount_three2]
    omega
  · rw [chaconSpacerCount_succ, chaconSpacerBit_three_mul_add_two,
      show (3*x+2+1 : ChaconOdometer) = 3*(x+1) by ring, chaconSpacerCount_three0,
      chaconSpacerCount_succ]
    omega

theorem chaconSpacerCount_three_add_two (m : ℕ) (x : ChaconOdometer) :
    chaconSpacerCount (3*m+2) (3*x) = m + 1 + chaconSpacerCount m x ∧
      chaconSpacerCount (3*m+2) (3*x+1) = m + 1 + chaconSpacerCount (m+1) x ∧
      chaconSpacerCount (3*m+2) (3*x+2) = m + chaconSpacerCount (m+1) x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [chaconSpacerCount_succ, chaconSpacerBit_three_mul, (chaconSpacerCount_three_add_one m x).2.1,
      zero_add]
  · rw [chaconSpacerCount_succ, chaconSpacerBit_three_mul_add_one,
      show (3*x+1+1 : ChaconOdometer) = 3*x+2 by ring, (chaconSpacerCount_three_add_one m x).2.2]
    omega
  · rw [chaconSpacerCount_succ, chaconSpacerBit_three_mul_add_two,
      show (3*x+2+1 : ChaconOdometer) = 3*(x+1) by ring, (chaconSpacerCount_three_add_one m (x+1)).1,
      chaconSpacerCount_succ]
    omega

/-- The three affine digit branches prepend 0, 1, or 2 to an odometer tail. -/
noncomputable def chaconDigitBranch (r : ℕ) (x : ChaconOdometer) : ChaconOdometer := 3*x+r

theorem measurable_chaconDigitBranch (r : ℕ) : Measurable (chaconDigitBranch r) := by
  unfold chaconDigitBranch
  fun_prop

private theorem exists_chaconDigitBranch (a : ChaconOdometer) :
    ∃ (r : Fin 3) (x : ChaconOdometer), chaconDigitBranch r.val x = a := by
  let z : ZMod 3 := PadicInt.toZModPow (p := 3) 1 a
  have h : PadicInt.toZModPow (p := 3) 1 (a - (z.val : ChaconOdometer)) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one] at h
  have h₃ : (3 : ChaconOdometer) ∣ a - (z.val : ChaconOdometer) := by simpa using h
  obtain ⟨x, hx⟩ := h₃
  exact ⟨⟨z.val, ZMod.val_lt z⟩, x, (eq_sub_iff_add_eq.mp hx.symm)⟩

private theorem map_chaconDigitBranch_translate (r s : ℕ) (x : ChaconOdometer) :
    ((chaconOdometerMeasure.map (chaconDigitBranch r)).map
      (fun y ↦ chaconDigitBranch s x + y)) = chaconOdometerMeasure.map (chaconDigitBranch (r+s)) := by
  have hmeas : Measurable (fun y ↦ chaconDigitBranch s x + y) := measurable_const.add measurable_id
  rw [Measure.map_map hmeas (measurable_chaconDigitBranch r)]
  have hx := chaconOdometer_translate_preserving x
  nth_rw 2 [← hx.map_eq]
  rw [Measure.map_map (measurable_chaconDigitBranch _) hx.measurable]
  congr 1
  funext y
  simp only [Function.comp_apply, chaconDigitBranch, Nat.cast_add]
  ring

private theorem map_chaconDigitBranch_add_three (r : ℕ) :
    chaconOdometerMeasure.map (chaconDigitBranch (r+3)) =
      chaconOdometerMeasure.map (chaconDigitBranch r) := by
  have hx := chaconOdometer_translate_preserving 1
  nth_rw 2 [← hx.map_eq]
  rw [Measure.map_map (measurable_chaconDigitBranch _) hx.measurable]
  congr 1
  funext y
  simp only [Function.comp_apply, chaconDigitBranch, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Prepending an independent uniform ternary digit to a Haar-distributed tail
leaves Haar probability unchanged. -/
theorem chaconOdometerMeasure_digitBranch_decomposition :
    chaconOdometerMeasure = (1/3 : ℝ≥0∞) •
      (chaconOdometerMeasure.map (chaconDigitBranch 0) +
       chaconOdometerMeasure.map (chaconDigitBranch 1) +
       chaconOdometerMeasure.map (chaconDigitBranch 2)) := by
  let D r := chaconOdometerMeasure.map (chaconDigitBranch r)
  let ν : Measure ChaconOdometer := (1/3 : ℝ≥0∞) • (D 0 + D 1 + D 2)
  change _ = ν
  have hu (r : ℕ) : D r univ = 1 := by
    simp [D, Measure.map_apply (measurable_chaconDigitBranch r) MeasurableSet.univ]
  have hν : IsProbabilityMeasure ν := by
    constructor
    change (1/3 : ℝ≥0∞) * (D 0 univ + D 1 univ + D 2 univ) = 1
    simp only [hu]
    rw [show (1+1+1 : ℝ≥0∞) = 3 by norm_num, one_div,
      ENNReal.inv_mul_cancel (by norm_num) (by simp)]
  have hInv : IsAddLeftInvariant ν := by
    constructor
    intro a
    obtain ⟨r, x, rfl⟩ := exists_chaconDigitBranch a
    have hmeas : Measurable (fun y ↦ chaconDigitBranch r.val x + y) := measurable_const.add measurable_id
    have hmaps (s : ℕ) : (D s).map (fun y ↦ chaconDigitBranch r.val x + y) = D (s+r.val) :=
      map_chaconDigitBranch_translate s r.val x
    have hrec (s : ℕ) : D (s+3) = D s := map_chaconDigitBranch_add_three s
    unfold ν
    rw [Measure.map_smul (1/3 : ℝ≥0∞) hmeas.aemeasurable, Measure.map_add _ _ hmeas,
      Measure.map_add _ _ hmeas, hmaps, hmaps, hmaps]
    congr 1
    fin_cases r
    · rfl
    · change D 1 + D 2 + D (0+3) = _
      rw [hrec]
      ac_rfl
    · change D 2 + D (0+3) + D (1+3) = _
      rw [hrec, hrec]
      ac_rfl
  let : IsAddHaarMeasure ν := isAddHaarMeasure_of_isCompact_nonempty_interior ν univ
    isCompact_univ (by simp) (by simp) (by simp)
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem measurable_chaconSpacerCount (m : ℕ) : Measurable (chaconSpacerCount m) := by
  have hbit : Measurable chaconSpacerBit :=
    measurable_const.piecewise chaconSpacer_measurable measurable_const
  exact Finset.measurable_sum _ fun j _ ↦ hbit.comp (measurable_id.add measurable_const)

theorem chaconSpacerCount_le (m : ℕ) (x : ChaconOdometer) : chaconSpacerCount m x ≤ m := by
  calc
    chaconSpacerCount m x ≤ ∑ _ : Fin m, (1 : ℕ) :=
      Finset.sum_le_sum fun j _ ↦ by unfold chaconSpacerBit; split <;> omega
    _ = m := by simp

/-- The Chacon polynomial whose coefficient at `k` is the probability of
crossing `k` spacers in `m` successive odometer steps. -/
noncomputable def chaconPolynomial (m : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1),
    C (chaconOdometerMeasure.real {x | chaconSpacerCount m x = k}) * X^k

private theorem spacerWeight_eq_sum (m : ℕ) (z : ℝ) :
    (fun x ↦ z ^ chaconSpacerCount m x) = fun x ↦
      ∑ k ∈ Finset.range (m+1), {y | chaconSpacerCount m y = k}.indicator (fun _ ↦ z^k) x := by
  funext x
  have h := chaconSpacerCount_le m x
  simp only [Set.indicator, mem_ofPred_eq, Finset.sum_ite_eq (a := chaconSpacerCount m x),
    Finset.mem_range, Nat.lt_succ_iff.mpr h, ite_true]

private theorem integrable_spacerWeight (m : ℕ) (z : ℝ) (μ : Measure ChaconOdometer)
    [IsFiniteMeasure μ] : Integrable (fun x ↦ z ^ chaconSpacerCount m x) μ := by
  rw [spacerWeight_eq_sum]
  exact integrable_finsetSum _ fun k _ ↦ (integrable_const (z^k)).indicator
    ((measurable_chaconSpacerCount m) (measurableSet_singleton k))

theorem chaconPolynomial_eval (m : ℕ) (z : ℝ) :
    (chaconPolynomial m).eval z = ∫ x, z ^ chaconSpacerCount m x ∂chaconOdometerMeasure := by
  rw [spacerWeight_eq_sum, integral_finsetSum]
  · simp only [chaconPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.sum_congr rfl fun k _ ↦
      (integral_indicator_const _ ((measurable_chaconSpacerCount m) (measurableSet_singleton k))).symm
  · exact fun k _ ↦ (integrable_const (z^k)).indicator
      ((measurable_chaconSpacerCount m) (measurableSet_singleton k))

private theorem chaconPolynomial_eval_digit_split (m : ℕ) (z : ℝ) :
    (chaconPolynomial m).eval z = (1/3) *
      ((∫ x, z ^ chaconSpacerCount m (chaconDigitBranch 0 x) ∂chaconOdometerMeasure) +
       (∫ x, z ^ chaconSpacerCount m (chaconDigitBranch 1 x) ∂chaconOdometerMeasure) +
       (∫ x, z ^ chaconSpacerCount m (chaconDigitBranch 2 x) ∂chaconOdometerMeasure)) := by
  let f (x : ChaconOdometer) := z ^ chaconSpacerCount m x
  let D r := chaconOdometerMeasure.map (chaconDigitBranch r)
  rw [chaconPolynomial_eval]
  change (∫ x, f x ∂chaconOdometerMeasure) = _
  conv_lhs => rw [chaconOdometerMeasure_digitBranch_decomposition]
  rw [integral_smul_measure]
  have hg (r : ℕ) : Integrable f (D r) := integrable_spacerWeight m z (D r)
  change ((1/3 : ℝ≥0∞).toReal) * (∫ x, f x ∂(D 0 + D 1 + D 2)) = _
  rw [integral_add_measure ((hg 0).add_measure (hg 1)) (hg 2), integral_add_measure (hg 0) (hg 1)]
  have hm (r : ℕ) : (∫ x, f x ∂(D r)) =
      ∫ x, f (chaconDigitBranch r x) ∂chaconOdometerMeasure :=
    integral_map (measurable_chaconDigitBranch r).aemeasurable (hg r).aestronglyMeasurable
  rw [hm 0, hm 1, hm 2, ENNReal.toReal_div]
  norm_num [f]

/-- Janvresse–Prikhod’ko–de la Rue–Ryzhikov, Theorem 3.3, first recurrence. -/
theorem chaconPolynomial_three (m : ℕ) : chaconPolynomial (3*m) = X^m * chaconPolynomial m := by
  apply Polynomial.funext
  intro z
  rw [chaconPolynomial_eval_digit_split]
  simp only [chaconDigitBranch, Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat,
    chaconSpacerCount_three0, chaconSpacerCount_three1, chaconSpacerCount_three2, pow_add, integral_const_mul,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, chaconPolynomial_eval]
  ring

/-- Janvresse–Prikhod’ko–de la Rue–Ryzhikov, Theorem 3.3, second recurrence. -/
theorem chaconPolynomial_three_add_one (m : ℕ) :
    chaconPolynomial (3*m+1) =
      C (1/3 : ℝ) * X^m * ((1 + X) * chaconPolynomial m + chaconPolynomial (m+1)) := by
  apply Polynomial.funext
  intro z
  rw [chaconPolynomial_eval_digit_split]
  simp only [chaconDigitBranch, Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat,
    fun x ↦ (chaconSpacerCount_three_add_one m x).1,
    fun x ↦ (chaconSpacerCount_three_add_one m x).2.1,
    fun x ↦ (chaconSpacerCount_three_add_one m x).2.2,
    pow_add, pow_one, integral_const_mul, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_X, chaconPolynomial_eval]
  ring

/-- Janvresse–Prikhod’ko–de la Rue–Ryzhikov, Theorem 3.3, third recurrence. -/
theorem chaconPolynomial_three_add_two (m : ℕ) :
    chaconPolynomial (3*m+2) =
      C (1/3 : ℝ) * X^m * (X * chaconPolynomial m + (1 + X) * chaconPolynomial (m+1)) := by
  apply Polynomial.funext
  intro z
  rw [chaconPolynomial_eval_digit_split]
  simp only [chaconDigitBranch, Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat,
    fun x ↦ (chaconSpacerCount_three_add_two m x).1,
    fun x ↦ (chaconSpacerCount_three_add_two m x).2.1,
    fun x ↦ (chaconSpacerCount_three_add_two m x).2.2,
    pow_add, pow_one, integral_const_mul, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_X, chaconPolynomial_eval]
  ring

theorem chaconPolynomial_eval_one (m : ℕ) : (chaconPolynomial m).eval 1 = 1 := by
  simp [chaconPolynomial_eval]

theorem chaconPolynomial_ne_zero (m : ℕ) : chaconPolynomial m ≠ 0 := by
  intro h
  have he := chaconPolynomial_eval_one m
  rw [h, Polynomial.eval_zero] at he
  exact zero_ne_one he

theorem chaconPolynomial_zero : chaconPolynomial 0 = 1 := by
  apply Polynomial.funext
  intro z
  simp [chaconPolynomial_eval, chaconSpacerCount]

theorem chaconPolynomial_one : chaconPolynomial 1 = C (1/2 : ℝ) * (1 + X) := by
  apply Polynomial.funext
  intro z
  have h := congrArg (Polynomial.eval z) (chaconPolynomial_three_add_one 0)
  norm_num [chaconPolynomial_zero] at h ⊢
  linarith

end Mixing
