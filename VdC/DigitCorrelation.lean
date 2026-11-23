/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.DigitExamples
public import VdC.ResidueAverages

/-! # Digit Correlation -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

@[simp] theorem norm_digitRoot (r : ℕ) : ‖digitRoot r‖ = 1 := by
  rw [digitRoot, Complex.norm_exp, Complex.div_natCast_re]
  simp [Complex.mul_re]

@[simp] theorem norm_digitCharacter (r m n : ℕ) : ‖digitCharacter r m n‖ = 1 := by
  simp [digitCharacter, norm_pow]

private theorem digitCharacter_step {r m b t : ℕ} (hr : 1 < r) (hb : b < r) (ht : t < r)
    (n q : ℕ) :
    digitCharacter r m (r*n+b+(r*q+t)) * star (digitCharacter r m (r*n+b)) =
      (digitRoot r ^ m) ^ t *
        (digitCharacter r m (n + (if b+t < r then q else q+1)) * star (digitCharacter r m n)) := by
  let ζ := digitRoot r ^ m
  have hζ : ζ ^ r = 1 := by
    change (digitRoot r ^ m) ^ r = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, (digitRoot_primitive (lt_trans Nat.zero_lt_one hr)).pow_eq_one,
      one_pow]
  have hz (j : ℕ) : ζ ^ j * star (ζ ^ j) = 1 := by
    rw [Complex.star_def, Complex.mul_conj']
    simp [ζ, norm_pow]
  rw [digitCharacter_block hr hb n]
  by_cases h : b+t < r
  · rw [ite_eq_left h, show r*n+b+(r*q+t)=r*(n+q)+(b+t) by ring, digitCharacter_block hr h,
      show (digitRoot r ^ m) ^ (b + t) = ζ ^ b * ζ ^ t by rw [pow_add]]
    change digitCharacter r m (n + q) * (ζ ^ b * ζ ^ t) * star (digitCharacter r m n * ζ ^ b) = _
    rw [star_mul]
    calc
      _ = ζ ^ t * (digitCharacter r m (n + q) * star (digitCharacter r m n)) *
          (ζ ^ b * star (ζ ^ b)) := by ring
      _ = _ := by rw [hz, mul_one]
  · have hf : (b+t-r) + r = b+t := by omega
    have ht' : b+t-r < r := by omega
    have he : ζ ^ (b+t-r) = ζ ^ b * ζ ^ t := by
      calc
        _ = ζ ^ (b+t-r) * ζ ^ r := by rw [hζ, mul_one]
        _ = _ := by rw [← pow_add, hf, pow_add]
    rw [ite_eq_right h, show r*n+b+(r*q+t)=r*(n+(q+1))+(b+t-r) by
      rw [Nat.add_comm (r*(n+(q+1))), ← Nat.add_assoc, Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega, digitCharacter_block hr ht']
    change digitCharacter r m (n + (q+1)) * ζ ^ (b+t-r) * star (digitCharacter r m n * ζ ^ b) = _
    rw [he, star_mul]
    calc
      _ = ζ ^ t * (digitCharacter r m (n + (q+1)) * star (digitCharacter r m n)) *
          (ζ ^ b * star (ζ ^ b)) := by ring
      _ = _ := by rw [hz, mul_one]

/-- Exact recursion on complete base-r blocks. The last `t` residues carry
into the next block and the first `r - t` do not. -/
theorem digitCorrelation_chunks {r m t : ℕ} (hr : 1 < r) (ht : t < r) (q N : ℕ) :
    let u := digitCharacter r m
    corr u u (r*q+t) (r*N) = (digitRoot r ^ m) ^ t *
      (((r-t : ℕ) : ℂ) * corr u u q N + (t : ℂ) * corr u u (q+1) N) / (r : ℂ) := by
  dsimp only
  conv_lhs => unfold corr
  rw [cesaro_mul_residue]
  have hs (b : ℕ) (hb : b < r) :
      cesaro (fun n => digitCharacter r m (r*n+b+(r*q+t)) * star (digitCharacter r m (r*n+b))) N =
        (digitRoot r ^ m) ^ t * corr (digitCharacter r m) (digitCharacter r m)
          (if b+t < r then q else q+1) N := by
    simp_rw [digitCharacter_step hr hb ht, cesaro_mul_const, corr]
  congr 1
  calc
    _ = ∑ b ∈ range r, (digitRoot r ^ m) ^ t * corr (digitCharacter r m) (digitCharacter r m)
        (if b+t < r then q else q+1) N := sum_congr rfl fun b hb => hs b (mem_range.mp hb)
    _ = _ := by
      rw [← mul_sum]
      congr 1
      let f b := corr (digitCharacter r m) (digitCharacter r m) (if b+t < r then q else q+1) N
      change (∑ b ∈ range r, f b) = _
      have hsplit : (∑ b ∈ range r, f b) = ∑ b ∈ range ((r-t)+t), f b := by rw [Nat.sub_add_cancel ht.le]
      rw [hsplit, sum_range_add]
      have h₀ : (∑ b ∈ range (r-t), f b) = (r-t : ℕ) • corr (digitCharacter r m) (digitCharacter r m) q N := by
        have he : ∀ b ∈ range (r-t), f b = corr (digitCharacter r m) (digitCharacter r m) q N := by
          intro b hb
          have hb' := mem_range.mp hb
          simp [f, ite_eq_left (by omega : b+t < r)]
        rw [sum_congr rfl he, sum_const, card_range]
      have h₁ : (∑ b ∈ range t, f (r-t+b)) = t • corr (digitCharacter r m) (digitCharacter r m) (q+1) N := by
        have he : ∀ b ∈ range t, f (r-t+b) = corr (digitCharacter r m) (digitCharacter r m) (q+1) N := by
          intro b hb
          simp [f, ite_eq_right (by omega : ¬ r-t+b+t < r)]
        rw [sum_congr rfl he, sum_const, card_range]
      simpa [Nat.sub_add_cancel ht.le, nsmul_eq_mul] using congrArg₂ (· + ·) h₀ h₁

private theorem tendsto_cesaro_of_contraction {u : ℕ → ℂ} {r : ℕ} (hr : 0 < r)
    (hu : BoundedSeq u) (c : ℂ) (d : ℝ) (hd0 : 0 ≤ d) (hd : d < 1)
    (hstep : ∀ᶠ N in atTop, ‖cesaro u (r*N) - c‖ = d * ‖cesaro u N - c‖) :
    Tendsto (cesaro u) atTop (𝓝 c) := by
  obtain ⟨C, hC, hu⟩ := hu
  let a N := ‖cesaro u N - c‖
  let L := limsup a atTop
  have hana (N : ℕ) : 0 ≤ a N := norm_nonneg _
  have hab : atTop.IsBoundedUnder (· ≤ ·) a := isBoundedUnder_of
    ⟨C + ‖c‖, fun N => (norm_sub_le ..).trans (add_le_add (norm_cesaro_le u hC hu N) le_rfl)⟩
  have hL0 : 0 ≤ L := le_limsup_of_frequently_le (Frequently.of_forall hana) hab
  have hfilter : Tendsto (fun N : ℕ => N / r) atTop atTop := by
    refine tendsto_atTop.2 fun b => eventually_atTop.2 ⟨b * r, fun N hN => ?_⟩
    exact (Nat.le_div_iff_mul_le hr).2 hN
  have herr : Tendsto (fun N : ℕ => ‖cesaro u N - cesaro u (r * (N/r))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_const_div_atTop_nhds_zero_nat (2*C*r))
    intro N
    have he := Nat.mod_add_div N r
    have hle : r * (N / r) ≤ N := by omega
    have hrem : N - r * (N / r) ≤ r := by have hm := Nat.mod_lt N hr; omega
    apply (norm_cesaro_sub_prefix_le u hC hu hle).trans
    gcongr
  have hL : L = 0 := by
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm (show L ≠ 0 from hne))
    let ε := (1-d)*L/4
    have hε : 0 < ε := by dsimp [ε]; positivity
    have ha' := hfilter.eventually (eventually_lt_add_pos_of_limsup_le hab (show limsup a atTop ≤ L from le_rfl) hε)
    have hs := hfilter.eventually hstep
    have hh := herr.eventually (gt_mem_nhds hε)
    have hle : L ≤ ε + d*(L+ε) := by
      refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop hana) ?_
      filter_upwards [ha', hs, hh] with N ha hs hh
      have htri : a N ≤ ‖cesaro u N - cesaro u (r * (N/r))‖ +
          ‖cesaro u (r * (N/r)) - c‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (cesaro u N - cesaro u (r * (N/r))) (cesaro u (r * (N/r)) - c)
      rw [hs] at htri
      exact htri.trans (add_le_add hh.le (mul_le_mul_of_nonneg_left ha.le hd0))
    have hprod : d*ε ≤ ε := mul_le_of_le_one_left hε.le hd.le
    dsimp [ε] at hprod hle
    nlinarith only [hprod, hle, mul_pos (sub_pos.mpr hd) hLpos]
  refine Metric.tendsto_nhds.2 (fun ε hε => ?_)
  simpa only [a, dist_eq_norm, hL, zero_add] using
    eventually_lt_add_pos_of_limsup_le hab (show limsup a atTop ≤ 0 from hL.le) hε

theorem digitCorrelation_zero {r m N : ℕ} (hN : 0 < N) :
    corr (digitCharacter r m) (digitCharacter r m) 0 N = 1 := by
  unfold corr
  simp only [Nat.add_zero, Complex.star_def, Complex.mul_conj', norm_digitCharacter, one_pow,
    Complex.ofReal_one]
  exact cesaro_const 1 hN

def digitFirstCorrelation (r m : ℕ) : ℂ :=
  (((r-1 : ℕ) : ℂ) * (digitRoot r ^ m)) / ((r : ℂ) - digitRoot r ^ m)

theorem digitFirstCorrelation_ne_zero {r m : ℕ} (hr : 1 < r) : digitFirstCorrelation r m ≠ 0 := by
  have hden : (r : ℂ) - digitRoot r ^ m ≠ 0 := by
    intro h
    have hh := congrArg norm (sub_eq_zero.mp h)
    simp only [Complex.norm_natCast, norm_pow, norm_digitRoot, one_pow] at hh
    exact (show (1 : ℝ) < r by exact_mod_cast hr).ne hh.symm
  have hnum : ((r-1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show r-1 ≠ 0 by omega)
  exact div_ne_zero (mul_ne_zero hnum (pow_ne_zero _ (Complex.exp_ne_zero _))) hden

theorem tendsto_digitCorrelation_one {r m : ℕ} (hr : 1 < r) :
    Tendsto (corr (digitCharacter r m) (digitCharacter r m) 1) atTop
      (𝓝 (digitFirstCorrelation r m)) := by
  let x := digitCharacter r m
  let ζ := digitRoot r ^ m
  let c := digitFirstCorrelation r m
  let u n := x (n+1) * star (x n)
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hr).ne'
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_pow]
  have hden : (r : ℂ) - ζ ≠ 0 := by
    intro h
    have hh := congrArg norm (sub_eq_zero.mp h)
    simp only [Complex.norm_natCast, hζ] at hh
    exact hrR.ne hh.symm
  have hc : c * ((r : ℂ) - ζ) = ((r-1 : ℕ) : ℂ) * ζ := by
    exact div_mul_cancel₀ _ hden
  change Tendsto (cesaro u) atTop (𝓝 c)
  apply tendsto_cesaro_of_contraction (lt_trans Nat.zero_lt_one hr)
    (⟨1, zero_le_one, fun n => by simp [u, x]⟩ : BoundedSeq u) c
    ((r : ℝ)⁻¹) (by positivity) (inv_lt_one_of_one_lt₀ hrR)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have he := digitCorrelation_chunks (m := m) (t := 1) hr hr 0 N
  simp only [mul_zero, zero_add, pow_one, Nat.cast_one, one_mul, digitCorrelation_zero hN] at he
  have he' : cesaro u (r*N) - c = (ζ / (r : ℂ)) * (cesaro u N - c) := by
    change corr x x 1 (r*N) - c = (ζ / (r : ℂ)) * (corr x x 1 N - c)
    rw [he]
    change ζ * (((r-1 : ℕ) : ℂ) * 1 + corr x x 1 N) / (r:ℂ) - c = _
    field_simp
    linear_combination -hc
  rw [he', norm_mul, norm_div, hζ, Complex.norm_natCast, one_div]

/-- All autocorrelations converge along the full sequence of initial segments. -/
theorem digitCorrelation_limit_exists {r m : ℕ} (hr : 1 < r) (h : ℕ) :
    ∃ c : ℂ, Tendsto (corr (digitCharacter r m) (digitCharacter r m) h) atTop (𝓝 c) := by
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    rcases eq_or_ne h 0 with rfl | h₀
    · exact ⟨1, tendsto_const_nhds.congr' ((eventually_gt_atTop (0 : ℕ)).mono fun N hN =>
        (digitCorrelation_zero hN).symm)⟩
    rcases eq_or_ne h 1 with rfl | h₁
    · exact ⟨_, tendsto_digitCorrelation_one hr⟩
    let q := h / r
    let t := h % r
    have ht : t < r := Nat.mod_lt _ (lt_trans Nat.zero_lt_one hr)
    have hh : r*q+t = h := by dsimp [q, t]; simpa [add_comm] using Nat.mod_add_div h r
    have hq : q < h := Nat.div_lt_self (by omega : 0 < h) hr
    have hmul : 2*q ≤ r*q := Nat.mul_le_mul_right _ (by omega)
    let x := digitCharacter r m
    have hb : BoundedSeq (fun n => x (n+h)*star (x n)) := ⟨1, zero_le_one,
      fun n => by simp [x]⟩
    obtain ⟨a, ha⟩ := ih q hq
    by_cases htz : t = 0
    · refine ⟨a, tendsto_cesaro_of_chunked (lt_trans Nat.zero_lt_one hr) hb ?_⟩
      have he (N : ℕ) : corr x x h (r*N) = corr x x q N := by
        have h := digitCorrelation_chunks (m := m) hr ht q N
        rw [hh, htz] at h
        have hz : (r : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hr).ne'
        simpa [hz, mul_div_cancel_left₀, x] using h
      exact ha.congr fun N => (he N).symm
    · obtain ⟨b, hb'⟩ := ih (q+1) (by omega)
      have hlim := (((ha.const_mul ((r-t : ℕ) : ℂ)).add (hb'.const_mul (t : ℂ))).const_mul
        ((digitRoot r ^ m) ^ t)).div_const (r : ℂ)
      refine ⟨(digitRoot r ^ m) ^ t * (((r-t : ℕ) : ℂ) * a + (t : ℂ) * b) / r,
        tendsto_cesaro_of_chunked (lt_trans Nat.zero_lt_one hr) hb ?_⟩
      refine hlim.congr fun N => ?_
      have he := digitCorrelation_chunks (m := m) hr ht q N
      rw [hh] at he
      exact he.symm

end
end VdC
