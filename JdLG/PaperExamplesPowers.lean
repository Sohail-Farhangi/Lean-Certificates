/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Data.Int.Interval

/-!
# Perfect powers in Example 5.4

The supports are the positive perfect powers, in the literal translation
representation on bounded functions on the integers.
-/

@[expose] public section

namespace JdLG.PaperExamplesPowers

open Filter
open scoped ENNReal Topology

local notation "W" => lp (fun _ : ℤ ↦ ℂ) ∞

/-- The positive perfect `k`th powers, viewed as a subset of the integers. -/
def perfectPowers (k : ℕ) : Set ℤ :=
  Set.range (fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ) ^ k)

/-- The support of the left translate by `a`. -/
def translateSupport (k : ℕ) (a : ℤ) : Set ℤ :=
  {t | a + t ∈ perfectPowers k}

/-- Beyond the square powers, consecutive perfect powers are separated by
at least one more than the lower base. -/
theorem power_gap {m n k : ℕ} (hk : 2 ≤ k) (hm : 0 < m) (hmn : m < n) :
    m ^ k + (m + 1) ≤ n ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
  have hj : 1 ≤ m ^ j := Nat.pow_pos hm
  have hsq : m ^ 2 + (m + 1) ≤ (m + 1) ^ 2 := by nlinarith
  have hmul : m + 1 ≤ m ^ j * (m + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (m + 1) hj
  calc
    m ^ (j + 2) + (m + 1) ≤ m ^ j * (m ^ 2 + (m + 1)) := by
      rw [pow_add, mul_add]
      exact Nat.add_le_add_left hmul _
    _ ≤ (m + 1) ^ j * (m + 1) ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) j) hsq
    _ ≤ n ^ (j + 2) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_left (by omega) _

private theorem lower_base_bound {k m n : ℕ} (hk : 2 ≤ k) (hm : 0 < m) (hmn : m < n)
    (a b t : ℤ) (ha : a + t = (m : ℤ) ^ k) (hb : b + t = (n : ℤ) ^ k) :
    m ≤ (a - b).natAbs := by
  have lab := power_gap hk hm hmn
  have hcast : (m : ℤ) ^ k + ((m : ℤ) + 1) ≤ (n : ℤ) ^ k := by exact_mod_cast lab
  have hab : b - a ≤ ((a - b).natAbs : ℤ) := by
    rw [Int.natCast_natAbs, abs_sub_comm]
    exact le_abs_self _
  exact_mod_cast (show (m : ℤ) ≤ ((a - b).natAbs : ℤ) by omega)

/-- Distinct translates of the powers indicator have finite intersection. -/
theorem finite_inter_translateSupport {k : ℕ} (hk : 2 ≤ k) {a b : ℤ} (hab : a ≠ b) :
    (translateSupport k a ∩ translateSupport k b).Finite := by
  let D := ((a - b).natAbs : ℤ) ^ k
  refine (Set.finite_Icc (a := min (-a) (-b)) (b := max (D - a) (D - b))).subset ?_
  intro t ht
  rcases ht with ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
  have hm' : a + t = ((m + 1 : ℕ) : ℤ) ^ k := hm.symm
  have hn' : b + t = ((n + 1 : ℕ) : ℤ) ^ k := hn.symm
  have hlo : min (-a) (-b) ≤ t := by
    have hp : 0 ≤ ((m + 1 : ℕ) : ℤ) ^ k := by positivity
    exact (min_le_left _ _).trans (by omega)
  refine ⟨hlo, ?_⟩
  have hmn : m ≠ n := by
    intro h
    rw [h] at hm'
    exact hab (by omega)
  rcases lt_or_gt_of_ne hmn with h | h
  · have hmD := lower_base_bound hk (by omega) (Nat.succ_lt_succ h) a b t hm' hn'
    have hD : ((m + 1 : ℕ) : ℤ) ^ k ≤ D := by
      dsimp [D]
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hmD) _
    exact (show t ≤ D - a by omega).trans (le_max_left _ _)
  · have hnD := lower_base_bound hk (by omega) (Nat.succ_lt_succ h) b a t hn' hm'
    have hD : ((n + 1 : ℕ) : ℤ) ^ k ≤ D := by
      dsimp [D]
      rw [← Int.natAbs_neg (a - b), neg_sub]
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hnD) _
    exact (show t ≤ D - b by omega).trans (le_max_right _ _)

open Classical in
/-- An indicator in the bounded complex function space. -/
noncomputable def boundedIndicator (A : Set ℤ) : W :=
  ⟨fun t ↦ if t ∈ A then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨t, rfl⟩
    change ‖(if t ∈ A then 1 else 0 : ℂ)‖ ≤ 1
    split_ifs <;> simp⟩⟩

open Classical in
@[simp] theorem boundedIndicator_apply (A : Set ℤ) (t : ℤ) :
    boundedIndicator A t = if t ∈ A then 1 else 0 := rfl

/-- The bounded indicator used in Example 5.4. -/
noncomputable def powersIndicator (k : ℕ) : W := boundedIndicator (perfectPowers k)

/-- Precomposition with integer translation, as a linear map. -/
noncomputable def translateLinear (a : ℤ) : W →ₗ[ℂ] W where
  toFun f := ⟨fun t ↦ f (a + t), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨t, rfl⟩
    exact lp.norm_apply_le_norm (by simp) f (a + t)⟩⟩
  map_add' f g := lp.ext (funext fun _ ↦ rfl)
  map_smul' z f := lp.ext (funext fun _ ↦ rfl)

/-- The literal translation representation of the additive integers. -/
noncomputable def translation : Multiplicative ℤ →ₙ* (W →L[ℂ] W) where
  toFun a := (translateLinear a.toAdd).mkContinuous 1 fun f ↦ by
    simp only [one_mul]
    apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro t
    exact lp.norm_apply_le_norm (by simp) f (a.toAdd + t)
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext t
    change f (a.toAdd + b.toAdd + t) = f (b.toAdd + (a.toAdd + t))
    rw [show a.toAdd + b.toAdd + t = b.toAdd + (a.toAdd + t) by omega]

theorem translation_powersIndicator (k : ℕ) (a : ℤ) :
    translation (Multiplicative.ofAdd a) (powersIndicator k) =
      boundedIndicator (translateSupport k a) := rfl

/-- Evaluation at zero is one at each polynomial time in the example. -/
theorem polynomial_coefficient (k : ℕ) (n : ℕ) (hn : 0 < n) :
    translation (Multiplicative.ofAdd ((n : ℤ) ^ k)) (powersIndicator k) 0 = 1 := by
  classical
  rw [translation_powersIndicator, boundedIndicator_apply]
  apply ite_eq_left
  refine ⟨n - 1, ?_⟩
  change ((n - 1 + 1 : ℕ) : ℤ) ^ k = (n : ℤ) ^ k + 0
  rw [Nat.sub_add_cancel (by omega), add_zero]

/-- The polynomial coefficient averages in the powers example are constantly
one, for every nonempty initial interval of positive integers. -/
theorem polynomial_coefficient_average (k N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.range N,
      ‖translation (Multiplicative.ofAdd (((n + 1 : ℕ) : ℤ) ^ k)) (powersIndicator k) 0‖) /
        (N : ℝ) = 1 := by
  have hsum : (∑ n ∈ Finset.range N,
      ‖translation (Multiplicative.ofAdd (((n + 1 : ℕ) : ℤ) ^ k)) (powersIndicator k) 0‖) =
      ∑ _n ∈ Finset.range N, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [polynomial_coefficient k (n + 1) (Nat.succ_pos _), norm_one]
  rw [hsum]
  simp [hN.ne']

end JdLG.PaperExamplesPowers
