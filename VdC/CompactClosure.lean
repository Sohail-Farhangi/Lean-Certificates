/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Permissible

/-! # Compact Closure -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

private def lag (x : ℕ → ℂ) (m : ℕ) : ℕ → ℂ := fun n => x (n + (m+1))

private noncomputable def meanSq (x y : ℕ → ℂ) (N : ℕ) : ℝ :=
  realCesaro (fun n => ‖x n - y n‖^2) N

private theorem meanSq_comm (x y : ℕ → ℂ) (N : ℕ) : meanSq x y N = meanSq y x N := by
  simp only [meanSq, norm_sub_rev]

private theorem sq_norm_add_bound (a b : ℂ) : ‖a+b‖^2 ≤ 2 * (‖a‖^2 + ‖b‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

private theorem meanSq_triangle (x y z : ℕ → ℂ) (N : ℕ) :
    meanSq x z N ≤ 2 * (meanSq x y N + meanSq y z N) := by
  unfold meanSq
  rw [← realCesaro_add, ← realCesaro_const_mul]
  apply realCesaro_mono _ N
  intro n
  rw [show x n - z n = (x n - y n) + (y n - z n) by ring]
  exact sq_norm_add_bound _ _

private theorem meanSq_add_const_mul (x x' y y' : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    meanSq (fun n => x n + c*y n) (fun n => x' n + c*y' n) N ≤
      2 * (meanSq x x' N + ‖c‖^2 * meanSq y y' N) := by
  unfold meanSq
  rw [← realCesaro_const_mul, ← realCesaro_add, ← realCesaro_const_mul]
  apply realCesaro_mono _ N
  intro n
  rw [show x n + c*y n - (x' n + c*y' n) = (x n - x' n) + c*(y n-y' n) by ring]
  have hh := sq_norm_add_bound (x n-x' n) (c*(y n-y' n))
  rwa [norm_mul, mul_pow] at hh

private theorem exists_meanSq_lag_limit {x : ℕ → ℂ} {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hx : BoundedSeq x) (hN : StrictMono N) (hr : CorrLimits x x N r) (m k : ℕ) :
    ∃ e : ℝ, Tendsto (fun q => meanSq (lag x m) (lag x k) (N q)) atTop (𝓝 e) := by
  by_cases h : k ≤ m
  · exact ⟨_, tendsto_realCesaro_shift_dist_sq hx hN hr (a := m+1) (b := k+1) (by omega)⟩
  · exact ⟨_, by simpa only [meanSq, lag, norm_sub_rev (x (_ + (k+1)))] using
      tendsto_realCesaro_shift_dist_sq hx hN hr (a := k+1) (b := m+1) (by omega)⟩

/-- The compact case of scalar linear closure in `ClosedUnderLinearClosureLemma`.
Each shift is assigned a pair of cover centers, and each occupied pair gets
one actual shift representative common to the two sequences. -/
theorem CompactAlong.add_const_mul {x y : ℕ → ℂ} {M : ℕ → ℕ}
    (hx : CompactAlong x M) (hy : CompactAlong y M) (c : ℂ) :
    CompactAlong (fun n => x n + c * y n) M := by
  classical
  let z (n : ℕ) := x n + c * y n
  have hz : BoundedSeq z := boundedSeq_add_const_mul hx.1 hy.1 c
  refine ⟨hz, hx.2.1, ?_⟩
  intro σ r hσ hr ε hε
  let δ := ε / (16 * (1 + ‖c‖^2))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hx.1 hy.1 (hx.2.1.comp hσ)
  obtain ⟨rx, hrx⟩ := hp.xx
  obtain ⟨ry, hry⟩ := hp.yy
  obtain ⟨Kx, hKx⟩ := hx.2.2 (σ ∘ φ) rx (hσ.comp hφ) hrx δ hδ
  obtain ⟨Ky, hKy⟩ := hy.2.2 (σ ∘ φ) ry (hσ.comp hφ) hry δ hδ
  choose ax hax ex hex hX using hKx
  choose ay hay ey hey hY using hKy
  let L := Fin (Kx+1) × Fin (Ky+1)
  let label (m : ℕ) : L := (⟨ax m, Nat.lt_succ_of_le (hax m)⟩, ⟨ay m, Nat.lt_succ_of_le (hay m)⟩)
  let rep (l : L) : ℕ := if h : ∃ m, label m = l then Classical.choose h else 0
  have hrep (m : ℕ) : label (rep (label m)) = label m := by
    have h : ∃ k, label k = label m := ⟨m, rfl⟩
    simpa only [rep, dite_eq_left h] using Classical.choose_spec h
  let K := Finset.univ.sup rep
  refine ⟨K, fun m => ?_⟩
  let k := rep (label m)
  have hk : k ≤ K := Finset.le_sup (s := (Finset.univ : Finset L)) (f := rep) (Finset.mem_univ (label m))
  have hkx : ax k = ax m := congrArg (fun l : L => l.1.val) (hrep m)
  have hky : ay k = ay m := congrArg (fun l : L => l.2.val) (hrep m)
  obtain ⟨ez, hez⟩ := exists_meanSq_lag_limit hz (hx.2.1.comp hσ) hr m k
  have hR : ∀ᶠ q : ℕ in atTop,
      meanSq (lag z m) (lag z k) ((M ∘ (σ ∘ φ)) q) ≤ ε/2 := by
    have hXm := (hX m).eventually (gt_mem_nhds (hex m))
    have hXk := (hX k).eventually (gt_mem_nhds (hex k))
    have hYm := (hY m).eventually (gt_mem_nhds (hey m))
    have hYk := (hY k).eventually (gt_mem_nhds (hey k))
    filter_upwards [hXm, hXk, hYm, hYk] with q hxm hxk hym hyk
    let N := (M ∘ (σ ∘ φ)) q
    change meanSq (lag x m) (lag x (ax m)) N < δ at hxm
    change meanSq (lag x k) (lag x (ax k)) N < δ at hxk
    change meanSq (lag y m) (lag y (ay m)) N < δ at hym
    change meanSq (lag y k) (lag y (ay k)) N < δ at hyk
    rw [hkx] at hxk
    rw [hky] at hyk
    have hxTri := meanSq_triangle (lag x m) (lag x (ax m)) (lag x k) N
    rw [meanSq_comm (lag x (ax m)) (lag x k)] at hxTri
    have hyTri := meanSq_triangle (lag y m) (lag y (ay m)) (lag y k) N
    rw [meanSq_comm (lag y (ay m)) (lag y k)] at hyTri
    have hxb : meanSq (lag x m) (lag x k) N ≤ 4*δ := by linarith only [hxTri, hxm, hxk]
    have hyb : meanSq (lag y m) (lag y k) N ≤ 4*δ := by linarith only [hyTri, hym, hyk]
    change meanSq (fun n => lag x m n + c*lag y m n) (fun n => lag x k n + c*lag y k n) N ≤ _
    refine (meanSq_add_const_mul _ _ _ _ c N).trans ?_
    refine (mul_le_mul_of_nonneg_left (add_le_add hxb (mul_le_mul_of_nonneg_left hyb (sq_nonneg _))) (by norm_num)).trans_eq ?_
    dsimp [δ]
    field_simp [show (1 + ‖c‖^2) ≠ 0 by positivity]
    ring
  have hE : ez ≤ ε/2 := le_of_tendsto (hez.comp hφ.tendsto_atTop) hR
  exact ⟨k, hk, ez, hE.trans_lt (by linarith only [hε]), hez⟩

theorem CompactAlong.const_mul {x : ℕ → ℂ} {M : ℕ → ℕ}
    (hx : CompactAlong x M) (c : ℂ) : CompactAlong (fun n => c*x n) M := by
  simpa only [zero_add] using (compactAlong_const 0 hx.2.1).add_const_mul hx c

theorem CompactAlong.add {x y : ℕ → ℂ} {M : ℕ → ℕ}
    (hx : CompactAlong x M) (hy : CompactAlong y M) : CompactAlong (fun n => x n+y n) M := by
  simpa only [one_mul] using hx.add_const_mul hy 1

theorem compactAlong_finset_sum {ι : Type*} {M : ℕ → ℕ} (hM : StrictMono M)
    (s : Finset ι) (x : ι → ℕ → ℂ) (h : ∀ i ∈ s, CompactAlong (x i) M) :
    CompactAlong (fun n => ∑ i ∈ s, x i n) M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using compactAlong_const 0 hM
  | insert a s ha IH =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Compactness is preserved under Cesàro-L² approximation along common averaging lengths. -/
theorem compactAlong_of_meanSquare_approximation {x : ℕ → ℂ} {M : ℕ → ℕ}
    (hx : BoundedSeq x) (hM : StrictMono M)
    (hApprox : ∀ ε : ℝ, 0 < ε → ∃ z : ℕ → ℂ, CompactAlong z M ∧
      ∀ᶠ N : ℕ in atTop, realCesaro (fun n => ‖x n-z n‖^2) N ≤ ε) :
    CompactAlong x M := by
  refine ⟨hx, hM, ?_⟩
  intro σ r hσ hr ε hε
  let δ := ε/20
  have hd : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨z, hz, hApproxZ⟩ := hApprox (δ/2) (by positivity)
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hz.1 hz.1 (hM.comp hσ)
  obtain ⟨rz, hrz⟩ := hp.xx
  obtain ⟨K, hK⟩ := hz.2.2 (σ ∘ φ) rz (hσ.comp hφ) hrz δ hd
  obtain ⟨C, hC, hX⟩ := hx
  obtain ⟨D, hD, hZ⟩ := hz.1
  let u (n : ℕ) := ‖x n-z n‖^2
  have hU (n : ℕ) : |u n| ≤ (C+D)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hX n) (hZ n))) 2
  have hClose (j : ℕ) : ∀ᶠ n : ℕ in atTop, meanSq (lag x j) (lag z j) n ≤ δ := by
    have hShift := tendsto_realCesaro_shift_sub_zero (by positivity) hU (j+1)
    filter_upwards [hApproxZ, hShift.eventually (gt_mem_nhds (show 0 < δ/2 by positivity))] with N hN hN'
    change realCesaro (fun n => u (n+(j+1))) N ≤ δ
    linarith only [hN, hN']
  refine ⟨K, fun m => ?_⟩
  obtain ⟨k, hk, ez, hez, hzlim⟩ := hK m
  obtain ⟨e, he⟩ := exists_meanSq_lag_limit ⟨C, hC, hX⟩ (hM.comp hσ) hr m k
  have hBound : ∀ᶠ q : ℕ in atTop, meanSq (lag x m) (lag x k) ((M ∘ (σ ∘ φ)) q) ≤ ε/2 := by
    filter_upwards [hp.strictMono.tendsto_atTop.eventually (hClose m),
      hp.strictMono.tendsto_atTop.eventually (hClose k), hzlim.eventually (gt_mem_nhds hez)] with q hm hk' hzk
    let N := (M ∘ (σ ∘ φ)) q
    change meanSq (lag x m) (lag z m) N ≤ δ at hm
    change meanSq (lag x k) (lag z k) N ≤ δ at hk'
    change meanSq (lag z m) (lag z k) N < δ at hzk
    change meanSq (lag x m) (lag x k) N ≤ ε/2
    have hTri := meanSq_triangle (lag x m) (lag z m) (lag x k) N
    have hTri' := meanSq_triangle (lag z m) (lag z k) (lag x k) N
    rw [meanSq_comm (lag z k) (lag x k)] at hTri'
    dsimp [δ] at *
    linarith only [hm, hk', hzk, hTri, hTri']
  have he' : e ≤ ε/2 := le_of_tendsto (he.comp hφ.tendsto_atTop) hBound
  exact ⟨k, hk, e, he'.trans_lt (by linarith only [hε]), he⟩

theorem compactAlong_of_limsup_square_approximation {x : ℕ → ℂ} {M : ℕ → ℕ}
    (hx : BoundedSeq x) (hM : StrictMono M) (z : ℕ → ℕ → ℂ) (hz : ∀ k, CompactAlong (z k) M)
    (hlim : Tendsto (fun k => limsup (fun N => realCesaro (fun n => ‖z k n - x n‖^2) N) atTop)
      atTop (𝓝 0)) : CompactAlong x M := by
  apply compactAlong_of_meanSquare_approximation hx hM
  intro ε hε
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨z k, hz k, ?_⟩
  obtain ⟨Cx, _, hX⟩ := hx
  obtain ⟨Cz, _, hZ⟩ := (hz k).1
  have hb : atTop.IsBoundedUnder (· ≤ ·) (fun N : ℕ => realCesaro (fun n => ‖z k n - x n‖^2) N) := by
    apply isBoundedUnder_of_eventually_le (a := (Cz + Cx)^2)
    apply Eventually.of_forall
    intro N
    by_cases hN : N = 0
    · simp [realCesaro, hN, sq_nonneg]
    have hh : ∀ n, ‖z k n - x n‖^2 ≤ (Cz + Cx)^2 := fun n =>
      pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hZ n) (hX n))) 2
    exact (realCesaro_mono hh N).trans_eq (realCesaro_const_pos _ (Nat.pos_of_ne_zero hN))
  filter_upwards [eventually_lt_of_limsup_lt hk hb] with N hN
  simpa only [norm_sub_rev] using hN.le

end VdC
