/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Rectangles
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-! Long blocks with duplicated halves give the lower discrepancy bound in the
example motivating permissible pairs. Every positive lag is used infinitely often. -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

noncomputable section

def duplicationLag (q : ℕ) : ℕ := (Nat.unpair q).1 + 1

theorem duplicationLag_pos (q : ℕ) : 0 < duplicationLag q := Nat.succ_pos _

@[simp] theorem duplicationLag_pair (h k : ℕ) : duplicationLag (Nat.pair h k) = h + 1 := by
  simp [duplicationLag]

/-- The start of a block. The parameter `request` permits extra growth at each step. -/
def duplicationStart (request : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 =>
    let A := duplicationStart request q
    A + (2 * duplicationLag q) * ((q + 1) * (A + 1) + request (q + 1))

def duplicationGroups (request : ℕ → ℕ) (q : ℕ) : ℕ :=
  (q + 1) * (duplicationStart request q + 1) + request (q + 1)

theorem duplicationStart_succ (request : ℕ → ℕ) (q : ℕ) : duplicationStart request (q + 1) =
    duplicationStart request q + (2 * duplicationLag q) * duplicationGroups request q := rfl

theorem duplicationGroups_pos (request : ℕ → ℕ) (q : ℕ) : 0 < duplicationGroups request q := by
  unfold duplicationGroups
  positivity

theorem duplicationStart_strictMono (request : ℕ → ℕ) : StrictMono (duplicationStart request) := by
  apply strictMono_nat_of_lt_succ
  intro q
  rw [duplicationStart_succ]
  apply Nat.lt_add_of_pos_right
  exact Nat.mul_pos (Nat.mul_pos (by decide) (duplicationLag_pos q)) (duplicationGroups_pos request q)

theorem le_duplicationStart (request : ℕ → ℕ) (q : ℕ) : q ≤ duplicationStart request q :=
  (duplicationStart_strictMono request).le_apply

theorem exists_duplicationBlock (request : ℕ → ℕ) (n : ℕ) :
    ∃ q, n < duplicationStart request (q + 1) :=
  ⟨n, (Nat.lt_succ_self n).trans_le (le_duplicationStart request (n + 1))⟩

def duplicationBlock (request : ℕ → ℕ) (n : ℕ) : ℕ := Nat.find (exists_duplicationBlock request n)

theorem duplicationBlock_eq {request : ℕ → ℕ} {n q : ℕ}
    (hlo : duplicationStart request q ≤ n) (hhi : n < duplicationStart request (q + 1)) :
    duplicationBlock request n = q := by
  unfold duplicationBlock
  apply (Nat.find_eq_iff _).mpr
  refine ⟨hhi, fun j hj ↦ ?_⟩
  exact not_lt_of_ge (((duplicationStart_strictMono request).monotone (by omega : j+1 ≤ q)).trans hlo)

/-- Replace the second half of each group by a copy of its first half. -/
def duplicationIndex (request : ℕ → ℕ) (n : ℕ) : ℕ :=
  let q := duplicationBlock request n
  let p := duplicationLag q
  if (n - duplicationStart request q) % (2 * p) < p then n else n - p

/-- The doubled-square sequence on the one-dimensional torus. -/
def duplicationSequence (request : ℕ → ℕ) (α : ℝ) (n : ℕ) : Torus 1 :=
  fun _ ↦ ((α * (duplicationIndex request n : ℝ)^2 : ℝ) : UnitAddCircle)

theorem duplicationIndex_first_half (request : ℕ → ℕ) (q k t : ℕ)
    (hk : k < duplicationGroups request q) (ht : t < duplicationLag q) :
    let A := duplicationStart request q
    let p := duplicationLag q
    let n := A + (2 * p) * k + t
    duplicationIndex request n = n ∧ duplicationIndex request (n + p) = n := by
  let A := duplicationStart request q
  let p := duplicationLag q
  let n := A + (2 * p) * k + t
  have hupper := Nat.mul_le_mul_left (2 * p) (show k + 1 ≤ duplicationGroups request q by omega)
  rw [Nat.mul_succ] at hupper
  have hbefore : n + p < duplicationStart request (q + 1) := by
    rw [duplicationStart_succ]
    dsimp [n, A, p] at *
    omega
  have hlo : A ≤ n := by dsimp [n]; omega
  have hq := duplicationBlock_eq hlo (show n < duplicationStart request (q + 1) by omega)
  have hq' := duplicationBlock_eq (show A ≤ n + p by omega) hbefore
  have hsub : n - A = (2 * p) * k + t := by dsimp [n]; omega
  have hsub' : n + p - A = (2 * p) * k + (t + p) := by dsimp [n]; omega
  have hres : (n - A) % (2 * p) = t := by
    rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hres' : (n + p - A) % (2 * p) = t + p := by
    rw [hsub', Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  change duplicationIndex request n = n ∧ duplicationIndex request (n + p) = n
  constructor
  · unfold duplicationIndex
    rw [hq]
    change (if (n - A) % (2 * p) < p then n else n - p) = n
    rw [hres, ite_eq_left ht]
  · unfold duplicationIndex
    rw [hq']
    change (if (n + p - A) % (2 * p) < p then n+p else n+p-p) = n
    rw [hres', ite_eq_right (by omega), Nat.add_sub_cancel]

private theorem unitRepresentative_zero_value : (unitRepresentative 0 : ℝ) = 0 := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  change (AddCircle.equivIco (1 : ℝ) 0 0 : ℝ) = 0
  have h := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := (0 : ℝ)) (by norm_num)
  simpa using congrArg Subtype.val h

private theorem stage_count_lower (request : ℕ → ℕ) (α : ℝ) (q : ℕ) :
    (duplicationGroups request q : ℝ) * (duplicationLag q : ℝ) /
        (duplicationStart request (q + 1) : ℝ) ≤
      differenceDiscrepancy (duplicationSequence request α) (duplicationLag q - 1)
        (duplicationStart request (q + 1)) := by
  classical
  let A := duplicationStart request q
  let B := duplicationStart request (q + 1)
  let p := duplicationLag q
  let M := duplicationGroups request q
  let u (n : ℕ) (i : Fin 1) := unitRepresentative
    (duplicationSequence request α (n + ((p - 1) + 1)) i - duplicationSequence request α n i)
  let z : Fin 1 → UnitInterval := fun _ ↦ ⟨0, by simp⟩
  let coords := (range M) ×ˢ (range p)
  let f (kt : ℕ × ℕ) := A + (2 * p) * kt.1 + kt.2
  let good := (range B).filter fun n ↦ ∀ i, (z i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ z i
  have hp : 0 < p := duplicationLag_pos q
  have hgood : Set.MapsTo f (coords : Set (ℕ × ℕ)) (good : Set ℕ) := by
    rintro ⟨k,t⟩ hkt
    have hkt' := Finset.mem_product.1 hkt
    have hk : k < M := mem_range.1 hkt'.1
    have ht : t < p := mem_range.1 hkt'.2
    have hn : f (k,t) < B := by
      have hmul := Nat.mul_le_mul_left (2 * p) (by omega : k+1 ≤ M)
      rw [Nat.mul_succ] at hmul
      dsimp [B, f]
      rw [duplicationStart_succ]
      change A + (2 * p) * k + t < A + (2 * p) * M
      omega
    have hd := duplicationIndex_first_half request q k t hk ht
    have hcopy : duplicationSequence request α (f (k,t) + p) = duplicationSequence request α (f (k,t)) := by
      unfold duplicationSequence
      change duplicationIndex request (f (k,t)) = f (k,t) ∧
        duplicationIndex request (f (k,t) + p) = f (k,t) at hd
      rw [hd.1, hd.2]
    apply Finset.mem_filter.2 ⟨Finset.mem_range.2 hn, ?_⟩
    intro i
    have hu : (u (f (k,t)) i : ℝ) = 0 := by
      dsimp only [u]
      rw [Nat.sub_add_cancel hp, hcopy, sub_self, unitRepresentative_zero_value]
    simp [z, hu]
  have hinj : (coords : Set (ℕ × ℕ)).InjOn f := by
    rintro ⟨k,t⟩ hkt ⟨k',t'⟩ hkt' he
    have ht : t < p := mem_range.1 (Finset.mem_product.1 hkt).2
    have ht' : t' < p := mem_range.1 (Finset.mem_product.1 hkt').2
    have hs : k = k' := by
      rcases lt_trichotomy k k' with hl | hh | hl
      · have hmul := Nat.mul_le_mul_left (2 * p) (by omega : k+1 ≤ k')
        rw [Nat.mul_succ] at hmul
        dsimp only [f] at he
        omega
      · exact hh
      · have hmul := Nat.mul_le_mul_left (2 * p) (by omega : k'+1 ≤ k)
        rw [Nat.mul_succ] at hmul
        dsimp only [f] at he
        omega
    subst k'
    have hst : t = t' := by dsimp only [f] at he; omega
    rw [hst]
  have hc : M * p ≤ good.card := by
    simpa [coords] using Finset.card_le_card_of_injOn f hgood hinj
  have hV : rectangleVolume z z = 0 := by simp [rectangleVolume]
  have hFr : rectangleFrequency u B z z = (good.card : ℝ) / (B : ℝ) := rfl
  have hb := rectangle_deviation_le_discrepancy u B z z
  rw [hV, sub_zero, hFr, abs_of_nonneg (by positivity)] at hb
  change (M : ℝ) * (p : ℝ) / (B : ℝ) ≤ rectangleDiscrepancy u B
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)).trans hb

theorem duplicationStage_discrepancy_lower (request : ℕ → ℕ) (α : ℝ) (q : ℕ) :
    1 / 2 - 1 / ((q : ℝ) + 1) ≤ differenceDiscrepancy (duplicationSequence request α)
      (duplicationLag q - 1) (duplicationStart request (q + 1)) := by
  let A := duplicationStart request q
  let B := duplicationStart request (q+1)
  let p := duplicationLag q
  let M := duplicationGroups request q
  have hBe : B = A + 2 * p * M := duplicationStart_succ request q
  have hB : 0 < (B : ℝ) := by
    exact_mod_cast (Nat.succ_pos q).trans_le (le_duplicationStart request (q + 1))
  have hQ : 0 < (q : ℝ) + 1 := by positivity
  have hA : (A : ℝ) / (B : ℝ) ≤ 1 / ((q : ℝ) + 1) := by
    rw [div_le_div_iff₀ hB hQ, one_mul]
    have hM : A * (q+1) ≤ M := by
      unfold M duplicationGroups
      change A * (q+1) ≤ (q+1)*(A+1) + request (q+1)
      rw [Nat.mul_comm A (q+1)]
      exact (Nat.mul_le_mul_left _ (Nat.le_succ _)).trans (Nat.le_add_right _ _)
    have hp : 1 ≤ 2*p := by have := duplicationLag_pos q; dsimp [p]; omega
    have hM' : M ≤ 2*p*M := by simpa only [one_mul] using Nat.mul_le_mul_right M hp
    have : A*(q+1) ≤ B := (hM.trans hM').trans (by rw [hBe]; omega)
    exact_mod_cast this
  have he : (M : ℝ) * (p : ℝ) / (B : ℝ) = (1 - (A : ℝ)/(B : ℝ))/2 := by
    have hBe' : (B : ℝ) = (A : ℝ) + 2 * (p : ℝ) * (M : ℝ) := by exact_mod_cast hBe
    field_simp
    linarith only [hBe']
  have hg := stage_count_lower request α q
  change (M : ℝ) * (p : ℝ) / (B : ℝ) ≤ _ at hg
  rw [he] at hg
  exact (show 1/2 - 1/((q : ℝ)+1) ≤ (1-(A : ℝ)/(B : ℝ))/2 by
    linarith only [hA, one_div_nonneg.mpr hQ.le]).trans hg

/-- The duplicated-block construction has upper discrepancy at least `1/2` at every
positive lag. The parameter `h` corresponds to the positive lag `h+1`. -/
theorem duplication_upper_discrepancy_ge_half (request : ℕ → ℕ) (α : ℝ) (h : ℕ) :
    (1 : ℝ)/2 ≤ upperDifferenceDiscrepancy (duplicationSequence request α) h := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := differenceDiscrepancy (duplicationSequence request α) h
  have hb : atTop.IsBoundedUnder (· ≤ ·) d := by
    refine ⟨1, ?_⟩
    exact Filter.eventually_map.2 (Eventually.of_forall fun N ↦ (rectangleDiscrepancy_mem_Icc _ _).2)
  have hf : ∃ᶠ N in atTop, (1 : ℝ)/2 - ε ≤ d N := by
    apply frequently_atTop.2
    intro n
    obtain ⟨k, hk⟩ := exists_nat_gt (1/ε)
    let q := Nat.pair h (max n k)
    have hq : max n k ≤ q := by
      simpa only [q, Nat.unpair_pair] using Nat.unpair_right_le q
    have hqk : (k : ℝ) ≤ q := by exact_mod_cast (le_max_right n k).trans hq
    have hεq : 1/((q : ℝ)+1) ≤ ε := by
      rw [div_le_iff₀ (by positivity : 0 < (q : ℝ)+1)]
      have hp : 1 < (k : ℝ)*ε := (div_lt_iff₀ hε).1 hk
      have hm := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ (q : ℝ)+1 by linarith) hε.le
      nlinarith only [hp, hm]
    refine ⟨duplicationStart request (q+1), ?_, ?_⟩
    · exact ((le_max_left n k).trans hq).trans ((Nat.le_succ q).trans (le_duplicationStart request _))
    have he : duplicationLag q - 1 = h := by simp [q]
    have hg := duplicationStage_discrepancy_lower request α q
    rw [he] at hg
    exact (sub_le_sub_left hεq _).trans hg
  have hfreq := le_limsup_of_frequently_le hf hb
  change (1 : ℝ)/2 ≤ limsup d atTop + ε
  linarith

end

end VdC
