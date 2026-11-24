/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconTowerClock
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.Compact

/-! # Scale decomposition for escaping times in Chacon's tower -/

@[expose] public section

open Filter Set
open scoped Topology

namespace Mixing

theorem chaconTowerHeight_pos (n : ℕ) : 0 < chaconTowerHeight n := by
  cases n <;> simp [chaconTowerHeight]

theorem chaconTowerHeight_strictMono : StrictMono chaconTowerHeight := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [chaconTowerHeight]
  omega

theorem le_chaconTowerHeight (n : ℕ) : n ≤ chaconTowerHeight n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => simpa only [Nat.succ_eq_add_one] using
      (Nat.succ_le_of_lt (ih.trans_lt (chaconTowerHeight_strictMono n.lt_succ_self)))

theorem tendsto_chaconTowerHeight_atTop : Tendsto chaconTowerHeight atTop atTop :=
  tendsto_atTop_mono le_chaconTowerHeight tendsto_id

theorem chaconHeightScale_exists (k : ℕ) : ∃ n, k < chaconTowerHeight (n + 1) :=
  ⟨k, k.lt_succ_self.trans_le (le_chaconTowerHeight (k + 1))⟩

/-- The height interval containing a positive time, with zero assigned to scale zero. -/
noncomputable def chaconHeightScale (k : ℕ) : ℕ := Nat.find (chaconHeightScale_exists k)

theorem lt_succ_chaconHeightScale_height (k : ℕ) :
    k < chaconTowerHeight (chaconHeightScale k + 1) :=
  Nat.find_spec (chaconHeightScale_exists k)

theorem chaconHeightScale_height_le {k : ℕ} (hk : 0 < k) :
    chaconTowerHeight (chaconHeightScale k) ≤ k := by
  cases h : chaconHeightScale k with
  | zero => simpa only [chaconTowerHeight] using Nat.succ_le_of_lt hk
  | succ n =>
    have hn : n < chaconHeightScale k := h ▸ n.lt_succ_self
    exact le_of_not_gt (Nat.find_min (chaconHeightScale_exists k) hn)

theorem tendsto_chaconHeightScale_atTop : Tendsto chaconHeightScale atTop atTop := by
  refine tendsto_atTop.2 fun n ↦ ?_
  filter_upwards [eventually_ge_atTop (chaconTowerHeight n)] with k hk
  by_contra! h
  exact (lt_succ_chaconHeightScale_height k).not_ge
    ((chaconTowerHeight_strictMono.monotone (Nat.succ_le_of_lt h)).trans hk)

theorem chaconTowerHeight_add_real (n r : ℕ) :
    (chaconTowerHeight (n + r) : ℝ) =
      3 ^ r * (chaconTowerHeight n : ℝ) + (3 ^ r - 1) / 2 := by
  have h₁ : 2 * (chaconTowerHeight (n + r) : ℝ) + 1 = 3 ^ (n + r + 1) := by
    exact_mod_cast chaconTowerHeight_twice_add_one (n + r)
  have h₂ : 2 * (chaconTowerHeight n : ℝ) + 1 = 3 ^ (n + 1) := by
    exact_mod_cast chaconTowerHeight_twice_add_one n
  rw [show n + r + 1 = r + (n + 1) by omega, pow_add, ← h₂] at h₁
  linarith

/-- A positive time normalized by its containing Chacon tower height. -/
noncomputable def chaconScaleRatio (k : ℕ) : ℝ :=
  (k : ℝ) / (chaconTowerHeight (chaconHeightScale k) : ℝ)

theorem chaconScaleRatio_mem_Icc {k : ℕ} (hk : 0 < k) :
    chaconScaleRatio k ∈ Icc (1 : ℝ) 3 := by
  have hp : 0 < (chaconTowerHeight (chaconHeightScale k) : ℝ) := by
    exact_mod_cast chaconTowerHeight_pos (chaconHeightScale k)
  have hlt := lt_succ_chaconHeightScale_height k
  rw [chaconTowerHeight] at hlt
  unfold chaconScaleRatio
  exact ⟨(le_div_iff₀ hp).2 (by simpa only [one_mul] using
      (show (chaconTowerHeight (chaconHeightScale k) : ℝ) ≤ (k : ℝ) by
        exact_mod_cast chaconHeightScale_height_le hk)),
    (div_le_iff₀ hp).2 (by exact_mod_cast (show k ≤ 3 * chaconTowerHeight (chaconHeightScale k) by
      omega))⟩

/-- A free time filter gives a limit of the positive scale ratios. -/
theorem exists_chaconScaleRatio_tendsto {ι : Type*} (p : Ultrafilter ι) {k : ι → ℕ}
    (hk : Tendsto k p atTop) :
    ∃ τ ∈ Icc (1 : ℝ) 3, Tendsto (fun j ↦ chaconScaleRatio (k j)) p (𝓝 τ) := by
  have hp : ∀ᶠ j in (p : Filter ι), chaconScaleRatio (k j) ∈ Icc (1 : ℝ) 3 :=
    (hk.eventually (eventually_ge_atTop 1)).mono fun _ hj ↦ chaconScaleRatio_mem_Icc hj
  exact isCompact_Icc.ultrafilter_le_nhds (p.map (fun j ↦ chaconScaleRatio (k j)))
    (le_principal_iff.2 hp)

theorem tendsto_chaconScale_index_sub {ι : Type*} {F : Filter ι} {k : ι → ℕ}
    (hk : Tendsto k F atTop) (r : ℕ) :
    Tendsto (fun j ↦ chaconHeightScale (k j) - r) F atTop := by
  refine tendsto_atTop.2 fun n ↦ ?_
  filter_upwards [(tendsto_chaconHeightScale_atTop.comp hk).eventually
    (eventually_ge_atTop (n + r))] with j h
  exact Nat.le_sub_of_add_le h

/-- Descending a fixed number of tower scales multiplies the limiting ratio
by the corresponding power of three. -/
theorem tendsto_chaconScaleRatio_sub {ι : Type*} {F : Filter ι} {k : ι → ℕ}
    (hk : Tendsto k F atTop) {τ : ℝ}
    (hτ : Tendsto (fun j ↦ chaconScaleRatio (k j)) F (𝓝 τ)) (r : ℕ) :
    Tendsto (fun j ↦ (k j : ℝ) /
      (chaconTowerHeight (chaconHeightScale (k j) - r) : ℝ)) F (𝓝 (τ * 3 ^ r)) := by
  let n (j : ι) := chaconHeightScale (k j)
  let h (j : ι) := (chaconTowerHeight (n j - r) : ℝ)
  have hh : Tendsto h F atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_chaconTowerHeight_atTop.comp (tendsto_chaconScale_index_sub hk r))
  have he : Tendsto (fun j ↦ ((3 : ℝ) ^ r - 1) / 2 / h j) F (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hh).const_mul (((3 : ℝ) ^ r - 1) / 2)
  have hc : Tendsto (fun j ↦ 3 ^ r + ((3 : ℝ) ^ r - 1) / 2 / h j) F (𝓝 ((3 : ℝ) ^ r)) := by
    simpa only [add_zero] using he.const_add ((3 : ℝ) ^ r)
  refine (hτ.mul hc).congr' ?_
  filter_upwards [(tendsto_chaconHeightScale_atTop.comp hk).eventually
    (eventually_ge_atTop r)] with j hj
  have hcast : (chaconTowerHeight (n j) : ℝ) =
      3 ^ r * h j + (3 ^ r - 1) / 2 := by
    change r ≤ n j at hj
    have heq := chaconTowerHeight_add_real (n j - r) r
    rw [Nat.sub_add_cancel hj] at heq
    exact heq
  have hn : (chaconTowerHeight (n j) : ℝ) ≠ 0 := by
    exact_mod_cast (chaconTowerHeight_pos (n j)).ne'
  have hd : h j ≠ 0 := by
    unfold h
    exact_mod_cast (chaconTowerHeight_pos (n j - r)).ne'
  change (k j : ℝ) / (chaconTowerHeight (n j) : ℝ) *
    (3 ^ r + (3 ^ r - 1) / 2 / h j) = (k j : ℝ) / h j
  field_simp
  linarith only [congrArg (fun t : ℝ ↦ (k j : ℝ) * t) hcast]

/-- The quotient at a scale whose limiting ratio is strictly between two
consecutive integers eventually equals the integer part of that ratio. -/
theorem eventually_chaconHeight_div_eq {ι : Type*} {F : Filter ι} {k : ι → ℕ}
    (hk : Tendsto k F atTop) {τ : ℝ}
    (hτ : Tendsto (fun j ↦ chaconScaleRatio (k j)) F (𝓝 τ)) {r m : ℕ}
    (hlo : (m : ℝ) < τ * 3 ^ r) (hhi : τ * 3 ^ r < m + 1) :
    ∀ᶠ j in F, k j / chaconTowerHeight (chaconHeightScale (k j) - r) = m := by
  have h := tendsto_chaconScaleRatio_sub hk hτ r
  filter_upwards [h.eventually (eventually_gt_nhds hlo),
    h.eventually (eventually_lt_nhds hhi)] with j h₀ h₁
  let b := chaconTowerHeight (chaconHeightScale (k j) - r)
  have hb : 0 < b := chaconTowerHeight_pos _
  have hbr : 0 < (b : ℝ) := by exact_mod_cast hb
  have h₀' : m * b ≤ k j := by
    have hm : (m : ℝ) * b < k j := (lt_div_iff₀ hbr).mp h₀
    exact le_of_lt (by exact_mod_cast hm)
  have h₁' : k j < (m + 1) * b := by
    have hm : (k j : ℝ) < ((m : ℝ) + 1) * b := (div_lt_iff₀ hbr).mp h₁
    exact_mod_cast hm
  change k j / b = m
  exact le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).2 h₁'))
    ((Nat.le_div_iff_mul_le hb).2 h₀')

/-- At an integral limiting ratio, the signed remainder is sub-height. -/
theorem tendsto_chaconHeight_relative_remainder {ι : Type*} {F : Filter ι} {k : ι → ℕ}
    (hk : Tendsto k F atTop) {τ : ℝ}
    (hτ : Tendsto (fun j ↦ chaconScaleRatio (k j)) F (𝓝 τ)) {r m : ℕ}
    (hm : τ * 3 ^ r = (m : ℝ)) :
    Tendsto (fun j ↦
      (((k j : ℤ) - m * chaconTowerHeight (chaconHeightScale (k j) - r)).natAbs : ℝ) /
        chaconTowerHeight (chaconHeightScale (k j) - r)) F (𝓝 0) := by
  have h := ((tendsto_chaconScaleRatio_sub hk hτ r).sub_const (m : ℝ)).abs
  rw [hm, sub_self, abs_zero] at h
  refine h.congr fun j ↦ ?_
  let b := chaconTowerHeight (chaconHeightScale (k j) - r)
  have hb : 0 < (b : ℝ) := by exact_mod_cast chaconTowerHeight_pos (chaconHeightScale (k j) - r)
  change |(k j : ℝ) / b - m| = (((k j : ℤ) - m * b).natAbs : ℝ) / b
  have he : (k j : ℝ) / b - m = ((k j : ℝ) - m * b) / b := by
    field_simp
  rw [he, abs_div, abs_of_pos hb]
  congr 1
  let z : ℤ := (k j : ℤ) - m * b
  have hcast : ((z.natAbs : ℤ) : ℝ) = |(z : ℝ)| := by
    rw [Int.natCast_natAbs, Int.cast_abs]
  simpa only [z, Int.cast_natCast, Int.cast_sub, Int.cast_mul] using hcast.symm

/-- Integer parts of the limiting normalized time at the successive scales. -/
noncomputable def chaconScaleCoefficient (τ : ℝ) (r : ℕ) : ℕ := ⌊τ * 3 ^ r⌋₊

theorem chaconScaleCoefficient_pos {τ : ℝ} (hτ : 1 ≤ τ) (r : ℕ) :
    0 < chaconScaleCoefficient τ r := by
  unfold chaconScaleCoefficient
  refine (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).2 ?_
  have hpow : (1 : ℝ) ≤ 3 ^ r := one_le_pow₀ (by norm_num)
  simpa only [Nat.cast_one, one_mul] using mul_le_mul hτ hpow
    (by positivity : (0 : ℝ) ≤ 1) (zero_le_one.trans hτ)

theorem eventually_chaconHeight_div_eq_floor {ι : Type*} {F : Filter ι} {k : ι → ℕ}
    (hk : Tendsto k F atTop) {τ : ℝ} (hτ₀ : 0 ≤ τ)
    (hτ : Tendsto (fun j ↦ chaconScaleRatio (k j)) F (𝓝 τ)) (r : ℕ)
    (hn : ∀ m : ℕ, τ * 3 ^ r ≠ (m : ℝ)) :
    ∀ᶠ j in F, k j / chaconTowerHeight (chaconHeightScale (k j) - r) =
      chaconScaleCoefficient τ r := by
  apply eventually_chaconHeight_div_eq hk hτ
  · exact (Nat.floor_le (by positivity)).lt_of_ne (Ne.symm (hn _))
  · exact Nat.lt_floor_add_one _

/-- The next ternary digit read from the scale ratio. -/
noncomputable def chaconScaleDigit (τ : ℝ) (r : ℕ) : ℕ :=
  chaconScaleCoefficient τ (r + 1) - 3 * chaconScaleCoefficient τ r

theorem chaconScaleCoefficient_succ (τ : ℝ) (r : ℕ) (hτ : 0 ≤ τ) :
    chaconScaleCoefficient τ (r + 1) =
      3 * chaconScaleCoefficient τ r + chaconScaleDigit τ r := by
  unfold chaconScaleDigit
  rw [Nat.add_sub_of_le]
  have he : (↑(3 * chaconScaleCoefficient τ r) : ℝ) ≤ τ * 3 ^ (r + 1) := by
    rw [pow_succ]
    push_cast
    have hh : (chaconScaleCoefficient τ r : ℝ) ≤ τ * 3 ^ r :=
      Nat.floor_le (by positivity)
    linarith
  exact Nat.le_floor he

theorem chaconScaleDigit_le_two (τ : ℝ) (r : ℕ) (hτ : 0 ≤ τ) :
    chaconScaleDigit τ r ≤ 2 := by
  have hlt : τ * 3 ^ (r + 1) < (3 * chaconScaleCoefficient τ r + 3 : ℕ) := by
    rw [pow_succ]
    push_cast
    have hh : τ * 3 ^ r < (chaconScaleCoefficient τ r : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have h : chaconScaleCoefficient τ (r + 1) < 3 * chaconScaleCoefficient τ r + 3 :=
    (Nat.floor_lt (by positivity)).2 hlt
  unfold chaconScaleDigit
  omega

/-- A tail consisting entirely of zeros or entirely of twos implies that
the normalized limit is integral at some scale. -/
theorem chaconScale_integral_of_constant_tail {τ : ℝ} (hτ : 0 ≤ τ) {d r : ℕ}
    (hd : d = 0 ∨ d = 2) (hTail : ∀ i ≥ r, chaconScaleDigit τ i = d) :
    ∃ m : ℕ, τ * 3 ^ r = (m : ℝ) := by
  let a := chaconScaleCoefficient τ
  have he (n : ℕ) : (a (r + n) : ℝ) + (d : ℝ) / 2 =
      3 ^ n * ((a r : ℝ) + (d : ℝ) / 2) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := chaconScaleCoefficient_succ τ (r + n) hτ
      rw [hTail (r+n) (by omega)] at h
      have h' : (a (r + (n + 1)) : ℝ) = 3 * (a (r+n) : ℝ) + d := by
        exact_mod_cast h
      rw [h', pow_succ]
      linear_combination 3 * ih
  have hb : (0 : ℝ) ≤ (d : ℝ) / 2 ∧ (d : ℝ) / 2 ≤ 1 := by
    rcases hd with rfl | rfl <;> norm_num
  have hbound (n : ℕ) : |τ * 3 ^ r - ((a r : ℝ) + (d : ℝ) / 2)| ≤
      ((3 : ℝ)^n)⁻¹ := by
    have h₀ : (a (r+n) : ℝ) ≤ τ * (3 : ℝ) ^ (r+n) := Nat.floor_le (by positivity)
    have h₁ : τ * (3 : ℝ) ^ (r+n) < (a (r+n) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h : |τ * (3 : ℝ) ^ (r+n) - ((a (r+n) : ℝ) + (d : ℝ) / 2)| ≤ 1 :=
      abs_le.2 ⟨by linarith [hb.2], by linarith [hb.1]⟩
    rw [he, pow_add, show τ * ((3 : ℝ)^r * 3^n) -
        3^n * ((a r : ℝ) + (d : ℝ) / 2) =
        3^n * (τ * 3^r - ((a r : ℝ) + (d : ℝ) / 2)) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3^n), mul_comm] at h
    rw [← one_div]
    exact (le_div_iff₀ (by positivity)).2 h
  have ht : Tendsto (fun n : ℕ ↦ ((3 : ℝ)^n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3))
  have hzero : |τ * 3 ^ r - ((a r : ℝ) + (d : ℝ) / 2)| = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds ht hbound) (abs_nonneg _)
  have h := sub_eq_zero.mp (abs_eq_zero.mp hzero)
  rcases hd with rfl | rfl
  · exact ⟨a r, by simpa using h⟩
  · exact ⟨a r + 1, by push_cast; norm_num at h; exact h⟩

/-- A ratio which is nonintegral at every scale has arbitrarily late
digits different from zero and arbitrarily late digits different from two. -/
theorem chaconScaleDigit_frequently_ne {τ : ℝ} (hτ : 0 ≤ τ)
    (hn : ∀ r m : ℕ, τ * 3 ^ r ≠ (m : ℝ)) {d : ℕ} (hd : d = 0 ∨ d = 2) :
    ∃ᶠ r : ℕ in atTop, chaconScaleDigit τ r ≠ d := by
  by_contra! hf
  obtain ⟨r, hr⟩ := eventually_atTop.1 hf
  obtain ⟨m, hm⟩ := chaconScale_integral_of_constant_tail hτ hd hr
  exact hn r m hm

end Mixing
