/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Permissible
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Orthogonal -/

@[expose] public section

open Filter Finset
open scoped BigOperators ComplexConjugate Topology

namespace VdC

theorem cesaro_add (x y : ℕ → ℂ) (N : ℕ) :
    cesaro (fun n => x n + y n) N = cesaro x N + cesaro y N := by
  simp only [cesaro, sum_add_distrib, add_div]

theorem cesaro_sub (x y : ℕ → ℂ) (N : ℕ) :
    cesaro (fun n => x n - y n) N = cesaro x N - cesaro y N := by
  simp only [cesaro, sum_sub_distrib, sub_div]

theorem cesaro_mul_const (x : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    cesaro (fun n => c * x n) N = c * cesaro x N := by
  rw [cesaro, cesaro, ← Finset.mul_sum, mul_div_assoc]

theorem cesaro_const (c : ℂ) {N : ℕ} (hN : 0 < N) : cesaro (fun _ => c) N = c := by
  rw [cesaro, sum_const, card_range, nsmul_eq_mul, mul_div_cancel_left₀]
  exact_mod_cast hN.ne'

theorem cesaro_tendsto_const (c : ℂ) :
    Tendsto (cesaro fun _ => c) atTop (𝓝 c) :=
  tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun _ h => (cesaro_const c h).symm)

theorem norm_cesaro_sq_le (x : ℕ → ℂ) (N : ℕ) :
    ‖cesaro x N‖ ^ 2 ≤ realCesaro (fun n => ‖x n‖ ^ 2) N := by
  simpa only [one_mul, one_pow, ← star_cesaro, norm_star] using
    norm_cesaro_mul_star_sq_le (fun _ => 1) x zero_le_one (by simp) N

theorem re_corr_zero (x : ℕ → ℂ) (N : ℕ) :
    (corr x x 0 N).re = realCesaro (fun n => ‖x n‖ ^ 2) N := by
  simp only [corr, Nat.add_zero, Complex.star_def, Complex.mul_conj', cesaro, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re,
    realCesaro]

private theorem cesaro_shift_window (x : ℕ → ℂ) (H N : ℕ) :
    cesaro (fun n => cesaro (fun i => x (n + i)) H) N =
      cesaro (fun i => cesaro (fun n => x (n + i)) N) H := by
  simp only [cesaro, div_eq_mul_inv, ← Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm, mul_comm ((H : ℂ)⁻¹)]

private theorem corr_shift_window (x : ℕ → ℂ) (H N : ℕ) :
    let u n := cesaro (fun i => x (n + i)) H
    corr u u 0 N =
      (∑ i ∈ range H, ∑ j ∈ range H, orbitCorr x x i j N) / (H : ℂ) ^ 2 := by
  have hpoint (n : ℕ) : cesaro (fun i => x (n + i)) H * star (cesaro (fun j => x (n + j)) H) =
      (∑ i ∈ range H, ∑ j ∈ range H, x (n + i) * star (x (n + j))) / (H : ℂ) ^ 2 := by
    rw [star_cesaro, cesaro, cesaro, div_mul_div_comm, sq, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp only [corr, orbitCorr, Nat.add_zero, hpoint]
  simp only [cesaro, div_eq_mul_inv, ← Finset.sum_mul, mul_assoc]
  rw [mul_comm (((H : ℂ) ^ 2)⁻¹)]
  congr 1
  rw [Finset.sum_comm (s := range N)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := range N)]

/-- Scalar van der Corput when every positive lag correlation vanishes. -/
theorem NearlyOrthogonal.tendsto_cesaro_zero {x : ℕ → ℂ} (hx : NearlyOrthogonal x) :
    Tendsto (cesaro x) atTop (𝓝 0) := by
  have hb : BoundedSeq (fun _ => (1 : ℂ)) := ⟨1, zero_le_one, by simp⟩
  have htest : ∀ N, corr x (fun _ => 1) 0 N = cesaro x N := by intro N; simp [corr]
  have hfun : cesaro x = corr x (fun _ => 1) 0 := funext fun N => (htest N).symm
  rw [hfun]
  apply tendsto_atTop_of_permissible_refinement hx.1 hb (M := id) strictMono_id
  intro φ hφ hp
  obtain ⟨r, hr⟩ := hp.xx
  obtain ⟨s, hs⟩ := hp.xy
  have hm : Tendsto (fun q => cesaro x (φ q)) atTop (𝓝 (s 0)) := by simpa [htest] using hs 0
  have htest' : ∀ H : ℕ, 0 < H → ‖s 0‖ ^ 2 ≤ (r 0).re / H := by
    intro H hH
    let u n := cesaro (fun i => x (n + i)) H
    have hm' : Tendsto (fun q => cesaro u (φ q)) atTop (𝓝 (s 0)) := by
      simp_rw [u, cesaro_shift_window]
      have hl := tendsto_finsetSum (range H) (fun i _ => tendsto_cesaro_shift hx.1 i hφ hm)
      have hh := hl.div_const (H : ℂ)
      simpa only [sum_const, card_range, nsmul_eq_mul, mul_div_cancel_left₀ _
        (show (H : ℂ) ≠ 0 by exact_mod_cast hH.ne'), cesaro] using hh
    have horb (i j : ℕ) : Tendsto (fun q => orbitCorr x x i j (φ q)) atTop
        (𝓝 (if i = j then r 0 else 0)) := by
      rcases lt_trichotomy i j with hij | rfl | hji
      · have h := (orbitCorr_tendsto_of_le hx.1 hx.1 hφ hr (a := j) (b := i) hij.le).star
        simpa [star_orbitCorr, hij.ne, hx.2 φ r hφ hr _ (Nat.sub_pos_of_lt hij)] using h
      · simpa using orbitCorr_tendsto_of_le hx.1 hx.1 hφ hr (a := i) (b := i) le_rfl
      · simpa [hji.ne', hx.2 φ r hφ hr _ (Nat.sub_pos_of_lt hji)] using
          orbitCorr_tendsto_of_le hx.1 hx.1 hφ hr (a := i) (b := j) hji.le
    have hh := (tendsto_finsetSum (range H) fun i _ =>
      tendsto_finsetSum (range H) fun j _ => horb i j).div_const ((H : ℂ) ^ 2)
    classical
    have hsum : (∑ i ∈ range H, ∑ j ∈ range H, if i = j then r 0 else 0) = H * r 0 := by
      calc
        _ = ∑ _ ∈ range H, r 0 := by
          apply sum_congr rfl
          intro i hi
          simp [hi]
        _ = _ := by simp [nsmul_eq_mul]
    have hcancel : ((H : ℂ) * r 0) / (H : ℂ) ^ 2 = r 0 / (H : ℂ) := by
      have : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
      field_simp
    rw [hsum, hcancel] at hh
    have hl : Tendsto (fun q => corr u u 0 (φ q)) atTop (𝓝 (r 0 / (H : ℂ))) := by
      simpa only [u, corr_shift_window] using hh
    have hr' := Complex.continuous_re.continuousAt.tendsto.comp hl
    simp only [Function.comp_def, re_corr_zero, ← Complex.ofReal_natCast, Complex.div_ofReal_re] at hr'
    exact le_of_tendsto_of_tendsto (hm'.norm.pow 2) hr' (Eventually.of_forall fun q => norm_cesaro_sq_le _ _)
  have hz : ‖s 0‖ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_const_div_atTop_nhds_zero_nat _) <|
    (eventually_ge_atTop 1).mono fun H hH => htest' H hH
  have hs0 : s 0 = 0 := by
    have hh : ‖s 0‖ = 0 := by nlinarith [norm_nonneg (s 0)]
    exact norm_eq_zero.mp hh
  simpa [hs0] using hs 0

end VdC
