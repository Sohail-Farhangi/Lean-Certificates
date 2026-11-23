/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PolynomialVdC
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Polynomial differences and the linear subsequence case -/

public section

open Filter Finset Polynomial
open scoped BigOperators Topology Polynomial

namespace JdLG

/-- The degree of the difference of distinct shifts drops by one, and the
difference stays nonconstant when the original integer polynomial has degree at least two. -/
theorem natDegree_shiftDifference (p : ℤ[X]) (hp : 2 ≤ p.natDegree) {a b : ℤ} (hab : a ≠ b) :
    (p.taylor a - p.taylor b).natDegree = p.natDegree - 1 := by
  let d := p.natDegree - 1
  have hd : 1 + d = p.natDegree := by dsimp [d]; omega
  have hTop : (p.taylor a - p.taylor b).natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases hEq : i = p.natDegree
    · subst i
      simp
    · have hlt : p.natDegree < i := by omega
      have ha := coeff_eq_zero_of_natDegree_lt
        (p := p.taylor a) (by simpa only [natDegree_taylor] using hlt)
      have hb := coeff_eq_zero_of_natDegree_lt
        (p := p.taylor b) (by simpa only [natDegree_taylor] using hlt)
      rw [coeff_sub, ha, hb, sub_self]
  refine le_antisymm hTop (le_natDegree_of_ne_zero ?_)
  let q := p.hasseDeriv d
  have hqDeg : q.natDegree ≤ 1 := by
    refine (natDegree_hasseDeriv_le p d).trans ?_
    omega
  have hqA : q.coeff 1 = ((p.natDegree : ℕ) : ℤ) * p.leadingCoeff := by
    change (p.hasseDeriv d).coeff 1 = _
    rw [hasseDeriv_coeff, show (1 + d).choose d = p.natDegree by
      rw [Nat.add_comm 1 d, Nat.choose_succ_self_right, Nat.add_comm d 1, hd],
      hd, coeff_natDegree]
  have hqNZ : q.coeff 1 ≠ 0 :=
    hqA ▸ mul_ne_zero (by exact_mod_cast (show p.natDegree ≠ 0 by omega))
      (leadingCoeff_ne_zero.mpr (by intro h; simp [h] at hp))
  rw [coeff_sub, taylor_coeff, taylor_coeff]
  change q.eval a - q.eval b ≠ 0
  conv_lhs =>
    rw [eq_X_add_C_of_natDegree_le_one hqDeg]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  rw [add_sub_add_right_eq_sub, ← mul_sub]
  exact mul_ne_zero hqNZ (sub_ne_zero.mpr hab)

private theorem tendsto_scalarCesaro_nat_affine {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hlim : Tendsto (scalarCesaro f) atTop (𝓝 0)) (a b : ℕ) (ha : 0 < a) :
    Tendsto (scalarCesaro (fun n ↦ f (a * n + b))) atTop (𝓝 0) := by
  let C := a + b + 1
  have hC : 0 < C := by dsimp [C]; omega
  have hMap : Tendsto (fun N : ℕ ↦ C * N) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_mul_of_pos_left _ hC) tendsto_id
  have hUpper : Tendsto (fun N ↦ (C : ℝ) * scalarCesaro f (C * N)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (hlim.comp hMap).const_mul (C : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ ?_) ?_ hUpper
  · exact mul_nonneg (by positivity) (sum_nonneg fun n _ ↦ hf _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hSub : (range N).image (fun n ↦ a * n + b) ⊆ range (C * N) := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
      apply mem_range.mpr
      have hB : b ≤ b * N := by
        simpa only [mul_one] using Nat.mul_le_mul_left b (show 1 ≤ N from hN)
      calc
        _ ≤ a * N + b * N :=
          Nat.add_le_add (Nat.mul_le_mul_left a (Nat.le_of_lt (mem_range.mp hn))) hB
        _ < _ := by dsimp [C]; rw [Nat.add_mul, Nat.add_mul, one_mul]; omega
    have hSum : (∑ n ∈ range N, f (a * n + b)) ≤ ∑ m ∈ range (C * N), f m := by
      rw [← sum_image (s := range N) (f := f) (g := fun n ↦ a * n + b)
        (fun n _ m _ h ↦ Nat.eq_of_mul_eq_mul_left ha (Nat.add_right_cancel h))]
      exact sum_le_sum_of_subset_of_nonneg hSub (fun i _ _ ↦ hf i)
    unfold scalarCesaro
    refine (mul_le_mul_of_nonneg_left hSum (by positivity)).trans_eq ?_
    push_cast
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
    field_simp

/-- Passage from the ordinary Cesàro limit to any affine integral subsequence
for a symmetric, nonnegative, bounded sequence indexed by the integers. -/
theorem tendsto_scalarCesaro_int_affine {f : ℤ → ℝ} (hpos : ∀ n, 0 ≤ f n)
    (hsym : ∀ n, f (-n) = f n) (M : ℝ) (hBound : ∀ n, ‖f n‖ ≤ M)
    (hlim : Tendsto (scalarCesaro fun n : ℕ ↦ f n) atTop (𝓝 0))
    (a b : ℤ) (ha : a ≠ 0) :
    Tendsto (scalarCesaro fun n ↦ f (a * n + b)) atTop (𝓝 0) := by
  have hPositive (a b : ℤ) (ha : 0 < a) :
      Tendsto (scalarCesaro fun n ↦ f (a * n + b)) atTop (𝓝 0) := by
    let t := (-b).toNat
    let c := a * (t : ℤ) + b
    have hC : 0 ≤ c := by
      have ht : -b ≤ (t : ℤ) := by dsimp [t]; omega
      have hAP : (t : ℤ) ≤ a * (t : ℤ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ a by omega)
          (Int.natCast_nonneg t)
      dsimp [c]
      linarith
    apply tendsto_scalarCesaro_of_shift M (fun n ↦ hBound _) t
    have hA : 0 < a.toNat := by omega
    have hlim' := tendsto_scalarCesaro_nat_affine (f := fun n : ℕ ↦ f n) (fun n ↦ hpos n)
      hlim a.toNat c.toNat hA
    refine hlim'.congr fun N ↦ ?_
    unfold scalarCesaro
    congr 1
    apply sum_congr rfl
    intro n _
    simp only [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hC]
    congr 1
    dsimp [c]
    ring
  by_cases ha' : 0 < a
  · exact hPositive a b ha'
  · refine (hPositive (-a) (-b) (by omega)).congr fun N ↦ ?_
    unfold scalarCesaro
    congr 1
    apply sum_congr rfl
    intro n _
    change f (-a * (n : ℤ) + -b) = f (a * (n : ℤ) + b)
    rw [neg_mul, ← neg_add, hsym]

end JdLG
