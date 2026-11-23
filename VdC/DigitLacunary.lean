/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.DigitCorrelation

/-! # Digit Lacunary -/

@[expose] public section

open Filter
open scoped Topology ComplexConjugate

namespace VdC

noncomputable section

def digitAutocorrelation (r m : ℕ) (hr : 1 < r) (h : ℕ) : ℂ :=
  (digitCorrelation_limit_exists (m := m) hr h).choose

theorem tendsto_digitAutocorrelation {r m : ℕ} (hr : 1 < r) (h : ℕ) :
    Tendsto (corr (digitCharacter r m) (digitCharacter r m) h) atTop (𝓝 (digitAutocorrelation r m hr h)) :=
  (digitCorrelation_limit_exists (m := m) hr h).choose_spec

theorem digitAutocorrelation_zero {r m : ℕ} (hr : 1 < r) : digitAutocorrelation r m hr 0 = 1 :=
  tendsto_nhds_unique (tendsto_digitAutocorrelation hr 0)
    (tendsto_const_nhds.congr' ((eventually_gt_atTop (0 : ℕ)).mono fun _ hN => (digitCorrelation_zero hN).symm))

theorem digitAutocorrelation_one {r m : ℕ} (hr : 1 < r) :
    digitAutocorrelation r m hr 1 = digitFirstCorrelation r m :=
  tendsto_nhds_unique (tendsto_digitAutocorrelation hr 1) (tendsto_digitCorrelation_one hr)

theorem digitAutocorrelation_recursion {r m t : ℕ} (hr : 1 < r) (ht : t < r) (q : ℕ) :
    let a := digitAutocorrelation r m hr
    a (r*q+t) = (digitRoot r ^ m) ^ t *
      (((r-t : ℕ) : ℂ) * a q + (t : ℂ) * a (q+1)) / (r : ℂ) := by
  dsimp only
  have hN : Tendsto (fun N => r * N) atTop atTop :=
    (show StrictMono (fun N => r * N) from fun _ _ h => Nat.mul_lt_mul_of_pos_left h
      (lt_trans Nat.zero_lt_one hr)).tendsto_atTop
  have h := (tendsto_digitAutocorrelation (m := m) hr (r*q+t)).comp hN
  have hu := (tendsto_digitAutocorrelation (m := m) hr q).const_mul ((r-t : ℕ) : ℂ)
  have hv := (tendsto_digitAutocorrelation (m := m) hr (q+1)).const_mul (t : ℂ)
  apply tendsto_nhds_unique h
  refine (((hu.add hv).const_mul ((digitRoot r ^ m) ^ t)).div_const (r : ℂ)).congr fun N => ?_
  exact (digitCorrelation_chunks hr ht q N).symm

theorem digitAutocorrelation_left_mul {r m : ℕ} (hr : 1 < r) (q : ℕ) :
    digitAutocorrelation r m hr (r*q) = digitAutocorrelation r m hr q := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hr).ne'
  have h := digitAutocorrelation_recursion (m := m) hr (t := 0) (lt_trans Nat.zero_lt_one hr) q
  simpa [hc, mul_div_cancel_left₀] using h

theorem digitAutocorrelation_pow_mul {r m : ℕ} (hr : 1 < r) (k q : ℕ) :
    digitAutocorrelation r m hr (r^k*q) = digitAutocorrelation r m hr q := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, digitAutocorrelation_left_mul hr, ih]

theorem digitAutocorrelation_pow {r m : ℕ} (hr : 1 < r) (k : ℕ) :
    digitAutocorrelation r m hr (r^k) = digitFirstCorrelation r m := by
  simpa [digitAutocorrelation_one hr] using digitAutocorrelation_pow_mul (m := m) hr k 1

theorem tendsto_digitAutocorrelation_pow_sub_one {r m : ℕ} (hr : 1 < r) :
    let c := digitFirstCorrelation r m
    Tendsto (fun k => digitAutocorrelation r m hr (r^k-1)) atTop (𝓝 (c * star c)) := by
  dsimp only
  let c := digitFirstCorrelation r m
  let ζ := digitRoot r ^ m
  let α := star ζ / (r : ℂ)
  let s k := digitAutocorrelation r m hr (r^k-1)
  have hr0 : 0 < r := lt_trans Nat.zero_lt_one hr
  have hR : (1 : ℝ) < r := by exact_mod_cast hr
  have hRc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_pow]
  have hζ0 : ζ ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hζpow : ζ ^ r = 1 := by
    change (digitRoot r ^ m) ^ r = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, (digitRoot_primitive hr0).pow_eq_one, one_pow]
  have hunit : ζ * star ζ = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hζ, Complex.ofReal_one, one_pow]
  have hlast : ζ ^ (r-1) = star ζ := by
    apply (mul_right_inj' hζ0).1
    rw [mul_comm ζ (ζ ^ (r-1)), ← pow_succ, Nat.sub_add_cancel hr0, hζpow, hunit]
  have hden : (r : ℂ) - ζ ≠ 0 := by
    intro he
    have ht := congrArg norm (sub_eq_zero.mp he)
    rw [Complex.norm_natCast, hζ] at ht
    exact hR.ne ht.symm
  have hc : c * ((r : ℂ) - ζ) = ((r-1 : ℕ) : ℂ) * ζ := div_mul_cancel₀ _ hden
  have hc' : star c * ((r : ℂ) - star ζ) = ((r-1 : ℕ) : ℂ) * star ζ := by
    have hh := congrArg (starRingEnd ℂ) hc
    simpa only [map_mul, map_sub, map_natCast, starRingEnd_apply] using hh
  have he (k : ℕ) : s (k+1) - c * star c = α * (s k - c * star c) := by
    have hk : 0 < r^k := pow_pos hr0 _
    have hidx : r*(r^k-1)+(r-1) = r^(k+1)-1 := by
      rw [pow_succ', Nat.mul_sub_left_distrib, Nat.mul_one]
      have h := Nat.le_mul_of_pos_right r hk
      omega
    have ht : r-1 < r := by omega
    have hs := digitAutocorrelation_recursion (m := m) hr ht (r^k-1)
    dsimp only at hs
    rw [hidx, Nat.sub_add_cancel hk, show r-(r-1)=1 by omega, digitAutocorrelation_pow hr] at hs
    change digitAutocorrelation r m hr (r^(k+1)-1) - _ = _
    rw [hs, Nat.cast_one, one_mul]
    change ζ^(r-1) * (s k + ((r-1 : ℕ) : ℂ)*c) / (r:ℂ) - c*star c = _
    rw [hlast]
    dsimp [α]
    field_simp
    simp only [Complex.star_def] at hc' ⊢
    linear_combination -c * hc'
  have he' (k : ℕ) : s k - c*star c = α^k * (s 0-c*star c) := by
    induction k with
    | zero => simp
    | succ k ih => rw [he, ih, pow_succ', mul_assoc]
  have hα : ‖α‖ < 1 := by
    change ‖star ζ / (r : ℂ)‖ < 1
    rw [norm_div, norm_star, hζ, Complex.norm_natCast, one_div]
    exact inv_lt_one_of_one_lt₀ hR
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hα).mul_const (s 0-c*star c)
  have hh := ht.congr fun k => (he' k).symm
  have ht' := hh.add (tendsto_const_nhds (x := c*star c))
  simpa only [sub_add_cancel, zero_mul, zero_add, s, c] using ht'

end
end VdC
