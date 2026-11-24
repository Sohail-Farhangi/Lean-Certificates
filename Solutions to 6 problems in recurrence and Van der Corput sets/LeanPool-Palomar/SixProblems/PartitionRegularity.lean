/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.PositiveDefinite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.Ring

@[expose] public section

namespace SixProblems

variable {G : Type*} [Group G]

namespace RealPositiveDefinite

theorem const {c : ℝ} (hc : 0 ≤ c) : RealPositiveDefinite (fun _ : G ↦ c) := by
  intro I
  have h := (Matrix.posSemidef_vecMulVec_self_star (fun _ : I ↦ (1 : ℝ))).smul hc
  convert h using 1
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.smul_apply]

theorem add {φ ψ : G → ℝ} (hφ : RealPositiveDefinite φ) (hψ : RealPositiveDefinite ψ) :
    RealPositiveDefinite (fun g ↦ φ g + ψ g) :=
  fun I ↦ (hφ I).add (hψ I)

theorem mul {φ ψ : G → ℝ} (hφ : RealPositiveDefinite φ) (hψ : RealPositiveDefinite ψ) :
    RealPositiveDefinite (fun g ↦ φ g * ψ g) := by
  classical
  exact fun I ↦ (hφ I).hadamard (hψ I)

theorem smul {φ : G → ℝ} (hφ : RealPositiveDefinite φ) {c : ℝ} (hc : 0 ≤ c) :
    RealPositiveDefinite (fun g ↦ c * φ g) := by
  intro I
  exact (hφ I).smul hc

theorem pow {φ : G → ℝ} (hφ : RealPositiveDefinite φ) (n : ℕ) :
    RealPositiveDefinite (fun g ↦ φ g ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const (G := G) zero_le_one
  | succ k ih => simpa only [pow_succ] using ih.mul hφ

theorem finset_prod {I : Type*} (s : Finset I) (F : I → G → ℝ)
    (hF : ∀ i ∈ s, RealPositiveDefinite (F i)) :
    RealPositiveDefinite (fun g ↦ ∏ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using const (G := G) zero_le_one
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).mul (ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)))

theorem finset_sum {I : Type*} (s : Finset I) (F : I → G → ℝ)
    (hF : ∀ i ∈ s, RealPositiveDefinite (F i)) :
    RealPositiveDefinite (fun g ↦ ∑ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const (G := G) (le_refl (0 : ℝ))
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add (ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)))

end RealPositiveDefinite

/-- Lemma 3.1. A polynomial with nonnegative coefficients preserves real
positive definiteness under pointwise evaluation. The two-variable statement
uses `I = Fin 2`. -/
theorem lemma3_1 {I : Type*} (F : I → G → ℝ) (hF : ∀ i, RealPositiveDefinite (F i))
    (p : MvPolynomial I ℝ) (hp : ∀ d, 0 ≤ p.coeff d) :
    RealPositiveDefinite (fun g ↦ MvPolynomial.eval (fun i ↦ F i g) p) := by
  simp_rw [MvPolynomial.eval_eq]
  apply RealPositiveDefinite.finset_sum
  intro d _
  apply RealPositiveDefinite.smul _ (hp d)
  exact RealPositiveDefinite.finset_prod d.support _ (fun i _ ↦ (hF i).pow (d i))

/-- Lemma 3.2. The polynomial barrier is strictly negative by a uniform
amount when either input lies below `-ε`. -/
theorem lemma3_2 {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M) :
    ∃ δ > 0, ∃ K : ℕ, ∀ x y : ℝ, x ∈ Set.Icc (-M) M → y ∈ Set.Icc (-M) M →
      (x < -ε ∨ y < -ε) → x * (2 * M + y) ^ K + y * (2 * M + x) ^ K ≤ -δ := by
  have hM : 0 < M := hε.trans hεM
  have htwoM : 0 < 2 * M := by linarith
  have hsmall : 0 < 2 * M - ε := by linarith
  let q := (2 * M - ε) / (2 * M)
  have hq : q < 1 := (div_lt_one htwoM).mpr (by linarith)
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (x := ε / 2 / M) (by positivity) hq
  have hK' : M * (2 * M - ε) ^ K ≤ (ε / 2) * (2 * M) ^ K := by
    simp only [q, div_pow] at hK
    have h := (div_lt_div_iff₀ (pow_pos htwoM K) hM).mp hK
    simpa only [mul_comm] using h.le
  let δ := (ε / 2) * M ^ K
  have hδ : 0 < δ := mul_pos (half_pos hε) (pow_pos hM K)
  refine ⟨δ, hδ, K, fun x y hx hy hneg ↦ ?_⟩
  have hfirst (a b : ℝ) (ha : a ∈ Set.Icc (-M) M) (hb : b ∈ Set.Icc (-M) M)
      (haneg : a < -ε) : a * (2 * M + b) ^ K + b * (2 * M + a) ^ K ≤ -δ := by
    have hbase_a : M ≤ 2 * M + a := by linarith [ha.1]
    have hbase_b : M ≤ 2 * M + b := by linarith [hb.1]
    have ha_pow : 0 ≤ (2 * M + a) ^ K := pow_nonneg (hM.le.trans hbase_a) _
    have hb_pow : 0 ≤ (2 * M + b) ^ K := pow_nonneg (hM.le.trans hbase_b) _
    have hpow_small : (2 * M + a) ^ K ≤ (2 * M - ε) ^ K :=
      pow_le_pow_left₀ (hM.le.trans hbase_a) (by linarith) K
    by_cases hb0 : b ≤ 0
    · have hb_term : b * (2 * M + a) ^ K ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 ha_pow
      calc
        _ ≤ (-ε) * (2 * M + b) ^ K := by
          linarith [mul_le_mul_of_nonneg_right haneg.le hb_pow]
        _ ≤ (-ε) * M ^ K := mul_le_mul_of_nonpos_left
          (pow_le_pow_left₀ hM.le hbase_b K) (neg_nonpos.mpr hε.le)
        _ ≤ -δ := by
          dsimp [δ]
          linarith [mul_le_mul_of_nonneg_right (show -ε ≤ -(ε / 2) by linarith)
            (pow_nonneg hM.le K)]
    · have hb_bound : (2 * M) ^ K ≤ (2 * M + b) ^ K :=
        pow_le_pow_left₀ htwoM.le (by linarith) K
      have hmain : a * (2 * M + b) ^ K ≤ (-ε) * (2 * M) ^ K :=
        (mul_le_mul_of_nonneg_right haneg.le hb_pow).trans
          (mul_le_mul_of_nonpos_left hb_bound (neg_nonpos.mpr hε.le))
      have hother : b * (2 * M + a) ^ K ≤ (ε / 2) * (2 * M) ^ K :=
        (mul_le_mul_of_nonneg_right hb.2 ha_pow).trans
          ((mul_le_mul_of_nonneg_left hpow_small hM.le).trans hK')
      have hwide : M ^ K ≤ (2 * M) ^ K := pow_le_pow_left₀ hM.le (by linarith) K
      calc
        _ ≤ -(ε / 2) * (2 * M) ^ K := by linarith
        _ ≤ -δ := by
          dsimp [δ]
          linarith [mul_le_mul_of_nonpos_left hwide (show -(ε / 2) ≤ 0 by linarith)]
  rcases hneg with hxneg | hyneg
  · exact hfirst x y hx hy hxneg
  · rw [add_comm]
    exact hfirst y x hy hx hyneg

/-- Failure of the nonnegative-supremum criterion gives a uniform
negative positive-definite witness on the set. -/
theorem not_nonnegativeOnPositiveDefinite_iff {R : Set G} :
    ¬NonnegativeOnPositiveDefinite R ↔
      ∃ φ : G → ℝ, RealPositiveDefinite φ ∧ ∃ ε > 0, ∀ g ∈ R, φ g < -ε := by
  unfold NonnegativeOnPositiveDefinite
  push Not
  rfl

/-- Theorem 3.3 in the positive-definite characterization from Theorem 2.2(d).
The nonnegative-supremum criterion is partition regular. -/
theorem theorem3_3_positiveDefinite {A B : Set G}
    (hA : ¬NonnegativeOnPositiveDefinite A) (hB : ¬NonnegativeOnPositiveDefinite B) :
    ¬NonnegativeOnPositiveDefinite (A ∪ B) := by
  obtain ⟨φ, hφ, ε₁, hε₁, hφneg⟩ := not_nonnegativeOnPositiveDefinite_iff.mp hA
  obtain ⟨ψ, hψ, ε₂, hε₂, hψneg⟩ := not_nonnegativeOnPositiveDefinite_iff.mp hB
  let ε := min ε₁ ε₂
  let M := max (max (φ 1) (ψ 1)) ε + 1
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hεM : ε < M := by dsimp [M]; linarith [le_max_right (max (φ 1) (ψ 1)) ε]
  have hM : 0 ≤ M := (hε.trans hεM).le
  have hφM : φ 1 ≤ M := by dsimp [M]; linarith [
    (le_max_left (φ 1) (ψ 1)).trans (le_max_left (max (φ 1) (ψ 1)) ε)]
  have hψM : ψ 1 ≤ M := by dsimp [M]; linarith [
    (le_max_right (φ 1) (ψ 1)).trans (le_max_left (max (φ 1) (ψ 1)) ε)]
  obtain ⟨δ, hδ, K, hbound⟩ := lemma3_2 hε hεM
  let χ (g : G) := φ g * (2 * M + ψ g) ^ K + ψ g * (2 * M + φ g) ^ K
  have hconst : RealPositiveDefinite (fun _ : G ↦ 2 * M) :=
    RealPositiveDefinite.const (mul_nonneg (by norm_num) hM)
  have hχ : RealPositiveDefinite χ :=
    (hφ.mul ((hconst.add hψ).pow K)).add (hψ.mul ((hconst.add hφ).pow K))
  refine not_nonnegativeOnPositiveDefinite_iff.mpr ⟨χ, hχ, δ / 2, half_pos hδ, fun g hg ↦ ?_⟩
  have hφg := abs_le.mp ((hφ.abs_le_one g).trans hφM)
  have hψg := abs_le.mp ((hψ.abs_le_one g).trans hψM)
  have hneg : φ g < -ε ∨ ψ g < -ε := by
    rcases hg with hg | hg
    · exact Or.inl ((hφneg g hg).trans_le (neg_le_neg (min_le_left ε₁ ε₂)))
    · exact Or.inr ((hψneg g hg).trans_le (neg_le_neg (min_le_right ε₁ ε₂)))
  exact (hbound (φ g) (ψ g) hφg hψg hneg).trans_lt (by linarith)

/-- Corollary 3.4 in the positive-definite characterization. -/
theorem corollary3_4_positiveDefinite {I : Type*} (s : Finset I) (D : I → Set G)
    (hD : NonnegativeOnPositiveDefinite (⋃ i ∈ s, D i)) :
    ∃ i ∈ s, NonnegativeOnPositiveDefinite (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨g, hg, _⟩ := hD (fun _ ↦ 0) (RealPositiveDefinite.const le_rfl) 1 zero_lt_one
    simp at hg
  | insert i s hi ih =>
    change NonnegativeOnPositiveDefinite (⋃ j ∈ (↑(insert i s) : Set I), D j) at hD
    rw [Finset.coe_insert, Set.biUnion_insert] at hD
    by_cases hDi : NonnegativeOnPositiveDefinite (D i)
    · exact ⟨i, Finset.mem_insert_self _ _, hDi⟩
    · have hrest : NonnegativeOnPositiveDefinite (⋃ j ∈ s, D j) := by
        by_contra hrest
        exact theorem3_3_positiveDefinite hDi hrest hD
      obtain ⟨j, hj, hDj⟩ := ih hrest
      exact ⟨j, Finset.mem_insert_of_mem hj, hDj⟩

end SixProblems
