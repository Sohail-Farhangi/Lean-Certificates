/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Applications
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Ring.GeomSum

/-! # Digit Examples -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

def digitSum (r n : ℕ) : ℕ := (r.digits n).sum

theorem digitSum_block {r t : ℕ} (hr : 1 < r) (ht : t < r) (a : ℕ) :
    digitSum r (r * a + t) = digitSum r a + t := by
  by_cases h : t ≠ 0 ∨ a ≠ 0
  · rw [digitSum, add_comm, Nat.digits_add r hr t a ht h]
    simp [digitSum, add_comm]
  · push Not at h
    simp [digitSum, h.1, h.2]

def digitResidue (r j : ℕ) : Set ℕ := {n | digitSum r n % r = j}

def residueOffset (r j a : ℕ) : ℕ :=
  let v := digitSum r a % r
  if v ≤ j then j - v else r - (v - j)

theorem residueOffset_lt {r j : ℕ} (hr : 1 < r) (hj : j < r) (a : ℕ) : residueOffset r j a < r := by
  have hv := Nat.mod_lt (digitSum r a) (lt_trans Nat.zero_lt_one hr)
  dsimp [residueOffset]
  split <;> omega

theorem digitResidue_block_iff {r j t : ℕ} (hr : 1 < r) (hj : j < r) (ht : t < r) (a : ℕ) :
    r * a + t ∈ digitResidue r j ↔ t = residueOffset r j a := by
  let v := digitSum r a % r
  have hv : v < r := Nat.mod_lt _ (lt_trans Nat.zero_lt_one hr)
  change digitSum r (r * a + t) % r = j ↔ _
  rw [digitSum_block hr ht, Nat.add_mod, Nat.mod_eq_of_lt ht]
  change (v + t) % r = j ↔ t = if v ≤ j then j-v else r-(v-j)
  by_cases hsum : r ≤ v+t
  · rw [Nat.mod_eq_sub_mod hsum, Nat.mod_eq_of_lt (by omega : v+t-r < r)]
    split <;> omega
  · rw [Nat.mod_eq_of_lt (by omega : v+t < r)]
    split <;> omega

def digitResidueIndex (r j a : ℕ) : ℕ := r * a + residueOffset r j a

theorem strictMono_digitResidueIndex {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    StrictMono (digitResidueIndex r j) := by
  intro a b hab
  have h := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hab)
  have ht := residueOffset_lt hr hj a
  unfold digitResidueIndex
  rw [Nat.mul_succ] at h
  omega

private theorem digitResidue_count_lower {r j : ℕ} (hr : 1 < r) (hj : j < r) (N : ℕ) :
    N / r ≤ initialCount (digitResidue r j) N := by
  classical
  let e : ℕ ↪ ℕ := ⟨digitResidueIndex r j, (strictMono_digitResidueIndex hr hj).injective⟩
  rw [initialCount, ← card_range (N / r), ← card_map e]
  apply card_le_card
  intro n hn
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hn
  have ha' := Nat.succ_le_of_lt (mem_range.mp ha)
  have hb' : r * (N / r) ≤ N := by simpa [mul_comm] using Nat.div_mul_le_self N r
  have hb := (Nat.mul_le_mul_left r ha').trans hb'
  have ht := residueOffset_lt hr hj a
  simp only [Function.Embedding.coeFn_mk, mem_filter, mem_range, e, digitResidueIndex]
  refine ⟨?_, (digitResidue_block_iff hr hj ht a).2 rfl⟩
  rw [Nat.mul_succ] at hb
  omega

theorem digitResidue_positive_lowerDensity {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    HasPositiveLowerDensity (digitResidue r j) := by
  have hR : 0 < (r : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hr
  refine ⟨1 / (2 * (r : ℝ)), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * r)] with N hN
  have hdiv : ((N / r : ℕ) : ℝ) ≤ initialCount (digitResidue r j) N := by
    exact_mod_cast digitResidue_count_lower hr hj N
  apply (le_trans ?_ hdiv)
  have hN' : 2 * (r : ℝ) ≤ N := by exact_mod_cast hN
  have hEq : ((N % r : ℕ) : ℝ) + (r : ℝ) * ((N / r : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.mod_add_div N r
  have hrem : ((N % r : ℕ) : ℝ) < r := by
    exact_mod_cast Nat.mod_lt N (lt_trans Nat.zero_lt_one hr)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith only [hN', hEq, hrem]

theorem range_digitResidueIndex {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    Set.range (digitResidueIndex r j) = digitResidue r j := by
  ext n
  constructor
  · rintro ⟨a, rfl⟩
    exact (digitResidue_block_iff hr hj (residueOffset_lt hr hj a) a).2 rfl
  · intro hn
    have ht := Nat.mod_lt n (lt_trans Nat.zero_lt_one hr)
    have he : r * (n / r) + n % r = n := by simpa [add_comm, mul_comm] using Nat.mod_add_div n r
    have hmem : r * (n / r) + n % r ∈ digitResidue r j := by rw [he]; exact hn
    have ho := (digitResidue_block_iff hr hj ht (n / r)).1 hmem
    exact ⟨n / r, by simpa [digitResidueIndex, ← ho] using he⟩

private theorem digitResidue_count_upper {r j : ℕ} (hr : 1 < r) (hj : j < r) (N : ℕ) :
    initialCount (digitResidue r j) N ≤ N/r + 1 := by
  classical
  rw [initialCount, ← card_range (N/r+1)]
  apply card_le_card_of_injOn (fun n => n/r)
  · intro n hn
    change n ∈ (range N).filter (· ∈ digitResidue r j) at hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hn).1).le))
  · intro n hn k hk h
    have hnorm (s : ℕ) (hs : s ∈ digitResidue r j) : s = digitResidueIndex r j (s/r) := by
      have he : r * (s/r) + s%r = s := by simpa [add_comm] using Nat.mod_add_div s r
      have hmem : r*(s/r)+s%r ∈ digitResidue r j := by rwa [he]
      have hm := (digitResidue_block_iff hr hj (Nat.mod_lt _ (lt_trans Nat.zero_lt_one hr)) (s/r)).1 hmem
      simpa [digitResidueIndex, ← hm] using he.symm
    exact (hnorm n (mem_filter.mp hn).2).trans ((congrArg (digitResidueIndex r j) h).trans
      (hnorm k (mem_filter.mp hk).2).symm)

/-- Each digit-sum residue has natural density exactly `1/r`. -/
theorem tendsto_digitResidue_density {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    Tendsto (fun N : ℕ => (initialCount (digitResidue r j) N : ℝ) / (N : ℝ)) atTop (𝓝 ((r : ℝ)⁻¹)) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hr
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually (gt_mem_nhds hε)
  filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with N hsmall hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let L : ℝ := (initialCount (digitResidue r j) N : ℝ)
  let Q : ℝ := ((N/r : ℕ) : ℝ)
  have hlo : Q ≤ L := by dsimp [Q, L]; exact_mod_cast digitResidue_count_lower hr hj N
  have hhi : L ≤ Q+1 := by dsimp [Q, L]; exact_mod_cast digitResidue_count_upper hr hj N
  have hEq : ((N%r : ℕ) : ℝ) + (r : ℝ) * Q = N := by dsimp [Q]; exact_mod_cast Nat.mod_add_div N r
  have hrem : ((N%r : ℕ) : ℝ) < r := by exact_mod_cast Nat.mod_lt N (lt_trans Nat.zero_lt_one hr)
  have hrem0 : 0 ≤ ((N%r : ℕ) : ℝ) := by positivity
  have hb₁ := mul_le_mul_of_nonneg_right hlo hrR.le
  have hb₂ := mul_le_mul_of_nonneg_right hhi hrR.le
  have hbound : |L * r - N| ≤ (r : ℝ) := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  change dist (L / N) ((r : ℝ)⁻¹) < ε
  rw [Real.dist_eq, show L/(N : ℝ) - (r : ℝ)⁻¹ = (L*r-N)/(N*r) by field_simp,
    abs_div, abs_of_pos (mul_pos hNr hrR)]
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right hbound (by positivity))
  rwa [show (r : ℝ)/(N*r) = 1/N by field_simp]

noncomputable section

def digitRoot (r : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / r)

theorem digitRoot_primitive {r : ℕ} (hr : 0 < r) : IsPrimitiveRoot (digitRoot r) r :=
  Complex.isPrimitiveRoot_exp _ hr.ne'

/-- The m-th additive digit character, before shifting by the selected residue. -/
def digitCharacter (r m n : ℕ) : ℂ := (digitRoot r ^ m) ^ digitSum r n

theorem digitCharacter_block {r m t : ℕ} (hr : 1 < r) (ht : t < r) (a : ℕ) :
    digitCharacter r m (r * a + t) = digitCharacter r m a * (digitRoot r ^ m) ^ t := by
  simp [digitCharacter, digitSum_block hr ht, pow_add]

/-- The roots-of-unity filter for a base-r digit-sum residue. -/
theorem digitResidue_indicator_fourier {r j : ℕ} (hr : 1 < r) (hj : j < r) (n : ℕ) :
    selectionWeight (digitResidue r j) n = (∑ m ∈ range r,
      ((digitRoot r ^ j)⁻¹) ^ m * digitCharacter r m n) / r := by
  classical
  let z := digitRoot r
  have hz := digitRoot_primitive (lt_trans Nat.zero_lt_one hr)
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  let w := (z ^ j)⁻¹ * z ^ digitSum r n
  have hw (m : ℕ) : w ^ m = ((z ^ j)⁻¹) ^ m * digitCharacter r m n := by
    change ((z ^ j)⁻¹ * z ^ digitSum r n) ^ m = _
    rw [mul_pow, digitCharacter]
    change _ = ((z ^ j)⁻¹) ^ m * (z ^ m) ^ digitSum r n
    rw [← pow_mul, ← pow_mul, Nat.mul_comm (digitSum r n) m]
  have hsums : (∑ m ∈ range r, ((digitRoot r ^ j)⁻¹) ^ m * digitCharacter r m n) =
      ∑ m ∈ range r, w ^ m := sum_congr rfl fun m _ => (hw m).symm
  rw [hsums]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hr).ne'
  have htest : w = 1 ↔ n ∈ digitResidue r j := by
    change (z ^ j)⁻¹ * z ^ digitSum r n = 1 ↔ digitSum r n % r = j
    have hz' : IsPrimitiveRoot z r := hz
    rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero j hz0), mul_one,
      (hz'.isOfFinOrder (lt_trans Nat.zero_lt_one hr).ne').pow_inj_mod,
      ← hz'.eq_orderOf, Nat.mod_eq_of_lt hj]
  by_cases hh : w = 1
  · simp [selectionWeight, htest.1 hh, hh, nsmul_eq_mul, hrC]
  · have hwr : w ^ r = 1 := by
      have hpow (k : ℕ) : (z ^ k) ^ r = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
      simp [w, mul_pow, inv_pow, hpow]
    have hs := geom_sum_mul w r
    rw [hwr, sub_self, mul_eq_zero] at hs
    have hn : n ∉ digitResidue r j := fun hm => hh (htest.2 hm)
    simp [selectionWeight, hn, hs.resolve_right (sub_ne_zero.mpr hh)]

private theorem spectrallySingular_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℂ)
    (hf : ∀ i ∈ s, SpectrallySingular (f i)) : SpectrallySingular (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using spectrallySingular_zero
  | insert a s ha ih =>
    simpa only [sum_insert ha] using
      (hf a (mem_insert_self ..)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

/-- The digit-sum example with the cited spectral input stated explicitly. -/
theorem spectrallySingular_digitResidue_of_characters {r j : ℕ} (hr : 1 < r) (hj : j < r)
    (hS : ∀ m : ℕ, 0 < m → m < r → SpectrallySingular (digitCharacter r m)) :
    SpectrallySingular (selectionWeight (digitResidue r j)) := by
  have hc (m : ℕ) (hm : m ∈ range r) : SpectrallySingular (digitCharacter r m) := by
    by_cases hm0 : m = 0
    · subst m
      have he : digitCharacter r 0 = fun _ => 1 := by funext n; simp [digitCharacter]
      rw [he]
      exact spectrallySingular_one
    · exact hS m (Nat.pos_of_ne_zero hm0) (mem_range.mp hm)
  have hf := (spectrallySingular_finset_sum (range r)
    (fun m n => ((digitRoot r ^ j)⁻¹) ^ m * digitCharacter r m n)
    (fun m hm => (hc m hm).const_mul _)).const_mul ((r : ℂ)⁻¹)
  convert hf using 1
  ext n
  rw [digitResidue_indicator_fourier hr hj, div_eq_inv_mul]

end
end VdC
