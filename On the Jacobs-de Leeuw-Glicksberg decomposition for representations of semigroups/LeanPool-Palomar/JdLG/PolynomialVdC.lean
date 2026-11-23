/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! # A Hilbert-space van der Corput estimate -/

@[expose] public section

open Filter Finset
open scoped BigOperators Topology ComplexConjugate InnerProductSpace

namespace JdLG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The initial-segment Cesàro average of a real sequence. -/
noncomputable def scalarCesaro (f : ℕ → ℝ) (N : ℕ) : ℝ := (N : ℝ)⁻¹ * ∑ n ∈ range N, f n

/-- The initial-segment Cesàro average of a vector sequence. -/
noncomputable def vectorCesaro (v : ℕ → E) (N : ℕ) : E := (N : ℝ)⁻¹ • ∑ n ∈ range N, v n

private theorem tendsto_natCast_inv : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem tendsto_zero_finsetSum {I A : Type*} [AddCommMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] (s : Finset I) {f : I → ℕ → A}
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∑ i ∈ s, f i N) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using tendsto_const_nhds
  | @insert i s hi ih =>
    simpa only [sum_insert hi, zero_add] using
      (hf i (mem_insert_self _ _)).add (ih fun j hj ↦ hf j (mem_insert_of_mem hj))

omit [InnerProductSpace ℂ E] in
private theorem norm_shift_sum_sub_le (v : ℕ → E) (M : ℝ) (hv : ∀ n, ‖v n‖ ≤ M) (N h : ℕ) :
    ‖(∑ n ∈ range N, v (n + h)) - ∑ n ∈ range N, v n‖ ≤ (h : ℝ) * M + (h : ℝ) * M := by
  have hShift : (∑ n ∈ range N, v (n + h)) - ∑ n ∈ range N, v n =
      (∑ n ∈ range h, v (n + N)) - ∑ n ∈ range h, v n := by
    have hSum := (Finset.sum_range_add v h N).symm.trans
      (Nat.add_comm h N ▸ Finset.sum_range_add v N h)
    calc
      _ = ((∑ n ∈ range h, v n) + ∑ n ∈ range N, v (n + h)) -
          (∑ n ∈ range h, v n) - ∑ n ∈ range N, v n := by abel
      _ = _ := by
        simp_rw [Nat.add_comm h _, Nat.add_comm N _] at hSum
        rw [hSum]
        abel
  rw [hShift]
  have hBound (f : ℕ → ℕ) : ‖∑ n ∈ range h, v (f n)‖ ≤ (h : ℝ) * M := by
    refine (norm_sum_le _ _).trans ?_
    simpa only [sum_const, card_range, nsmul_eq_mul] using
      (sum_le_sum fun n (_ : n ∈ range h) ↦ hv (f n))
  exact (norm_sub_le _ _).trans (add_le_add (hBound (· + N)) (hBound id))

private theorem tendsto_vectorCesaro_shift_sub (v : ℕ → E) (M : ℝ) (hv : ∀ n, ‖v n‖ ≤ M)
    (h : ℕ) :
    Tendsto (fun N ↦ vectorCesaro (fun n ↦ v (n + h)) N - vectorCesaro v N) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * ((h : ℝ) * M + (h : ℝ) * M)) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_natCast_inv.mul tendsto_const_nhds
  apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hlim
  intro N
  rw [vectorCesaro, vectorCesaro, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_shift_sum_sub_le v M hv N h) (by positivity)

/-- The scalar Cesàro shift error is bounded by the two end segments. -/
theorem norm_scalarCesaro_shift_sub_le (v : ℕ → ℝ) (M : ℝ) (hv : ∀ n, ‖v n‖ ≤ M)
    (N h : ℕ) :
    ‖scalarCesaro (fun n ↦ v (n + h)) N - scalarCesaro v N‖ ≤
      (N : ℝ)⁻¹ * ((h : ℝ) * M + (h : ℝ) * M) := by
  rw [scalarCesaro, scalarCesaro, ← mul_sub, norm_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_shift_sum_sub_le v M hv N h) (by positivity)

/-- A fixed shift of a bounded scalar sequence does not change its Cesàro limit. -/
theorem tendsto_scalarCesaro_of_shift {v : ℕ → ℝ} (M : ℝ) (hv : ∀ n, ‖v n‖ ≤ M)
    (h : ℕ) {c : ℝ} (hc : Tendsto (scalarCesaro fun n ↦ v (n + h)) atTop (𝓝 c)) :
    Tendsto (scalarCesaro v) atTop (𝓝 c) := by
  have hErr : Tendsto (fun N ↦ scalarCesaro (fun n ↦ v (n + h)) N - scalarCesaro v N)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ * ((h : ℝ) * M + (h : ℝ) * M))
        atTop (𝓝 0) := by
      simpa only [zero_mul] using tendsto_natCast_inv.mul tendsto_const_nhds
    exact squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun N ↦ norm_scalarCesaro_shift_sub_le v M hv N h) hlim
  simpa only [sub_sub_cancel, sub_zero] using hc.sub hErr

private theorem norm_sq_vectorCesaro_le (v : ℕ → E) {N : ℕ} (hN : 0 < N) :
    ‖vectorCesaro v N‖ ^ 2 ≤ scalarCesaro (fun n ↦ ‖v n‖ ^ 2) N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hJ : ‖∑ n ∈ range N, v n‖ ^ 2 ≤
      (N : ℝ) * ∑ n ∈ range N, ‖v n‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _).trans
      (by simpa only [card_range] using
        sq_sum_le_card_mul_sum_sq (s := range N) (f := fun n ↦ ‖v n‖))
  rw [vectorCesaro, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hN'.le), mul_pow]
  refine (mul_le_mul_of_nonneg_left hJ (sq_nonneg _)).trans_eq ?_
  unfold scalarCesaro
  field_simp

private theorem norm_sq_block_le (v : ℕ → E) (n H : ℕ) :
    ‖∑ h ∈ range H, v (n + h)‖ ^ 2 ≤
      ∑ h ∈ range H, ∑ j ∈ range H, ‖inner ℂ (v (n + h)) (v (n + j))‖ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner]
  simp only [inner_sum, map_sum]
  exact sum_le_sum fun h _ ↦ sum_le_sum fun j _ ↦ Complex.re_le_norm _

private theorem scalarCesaro_le_const {f : ℕ → ℝ} {M : ℝ} (h : ∀ n, f n ≤ M)
    {N : ℕ} (hN : 0 < N) : scalarCesaro f N ≤ M := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold scalarCesaro
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ _ ∈ range N, M :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun n _ ↦ h n) (inv_nonneg.mpr hN'.le)
    _ = M := by
      rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN'.ne', one_mul]

/-- Van der Corput for a bounded Hilbert-space sequence with vanishing Cesàro averages
of absolute off-diagonal coefficients. -/
theorem tendsto_vectorCesaro_zero_of_abs_correlations (v : ℕ → E) (M : ℝ)
    (hv : ∀ n, ‖v n‖ ≤ M)
    (hc : ∀ h j : ℕ, h ≠ j → Tendsto
      (scalarCesaro (fun n ↦ ‖inner ℂ (v (n + h)) (v (n + j))‖)) atTop (𝓝 0)) :
    Tendsto (vectorCesaro v) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let d := (ε / 2) ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨H, hH⟩ := exists_nat_gt ((M ^ 2 + 1) / d + 1)
  have hH1 : (1 : ℝ) ≤ H := by
    linarith [div_nonneg (by positivity : 0 ≤ M ^ 2 + 1) hd.le]
  have hHp : (0 : ℝ) < H := by linarith
  have hGoal : (H : ℝ) * M ^ 2 + 1 < ((H : ℝ) * (ε / 2)) ^ 2 := by
    have hHd : M ^ 2 + 1 < (H : ℝ) * d := (div_lt_iff₀ hd).mp (by linarith)
    calc
      _ ≤ (H : ℝ) * (M ^ 2 + 1) := by nlinarith
      _ < (H : ℝ) * ((H : ℝ) * d) := mul_lt_mul_of_pos_left hHd hHp
      _ = _ := by dsimp [d]; ring
  let B (n : ℕ) := ∑ h ∈ range H, v (n + h)
  let corr (h j : ℕ) (N : ℕ) := scalarCesaro (fun n ↦ ‖inner ℂ (v (n + h)) (v (n + j))‖) N
  let diag (N : ℕ) := ∑ h ∈ range H, corr h h N
  let off (N : ℕ) := ∑ h ∈ range H, ∑ j ∈ (range H).erase h, corr h j N
  have hOff : Tendsto off atTop (𝓝 0) := by
    simpa only [off] using
      tendsto_zero_finsetSum (range H) fun h _ ↦
        tendsto_zero_finsetSum ((range H).erase h) fun j hj ↦
          hc h j (Finset.ne_of_mem_erase hj).symm
  have hErr : Tendsto (fun N ↦ vectorCesaro B N - (H : ℝ) • vectorCesaro v N) atTop (𝓝 0) := by
    have hSplit (N : ℕ) : vectorCesaro B N - (H : ℝ) • vectorCesaro v N =
        ∑ h ∈ range H, (vectorCesaro (fun n ↦ v (n + h)) N - vectorCesaro v N) := by
      rw [sum_sub_distrib, sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ]
      unfold vectorCesaro B
      rw [Finset.sum_comm (s := range N) (t := range H), smul_sum]
    simpa only [hSplit] using tendsto_zero_finsetSum (range H) fun h _ ↦
      tendsto_vectorCesaro_shift_sub v M hv h
  have hPos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  have hOff' : ∀ᶠ N in atTop, off N < 1 := hOff.eventually (gt_mem_nhds (by norm_num))
  have hErr' : ∀ᶠ N in atTop, ‖vectorCesaro B N - (H : ℝ) • vectorCesaro v N‖ < ε / 2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hErr) (ε / 2) (half_pos hε)
  filter_upwards [hPos, hOff', hErr'] with N hN hOffN hErrN
  have hDiag : diag N ≤ (H : ℝ) * M ^ 2 := by
    apply (sum_le_sum (fun h (_ : h ∈ range H) ↦ scalarCesaro_le_const ?_ hN)).trans
    · rw [sum_const, card_range, nsmul_eq_mul]
    · intro n
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hv _) _
  have hSplitCorr : ∑ h ∈ range H, ∑ j ∈ range H, corr h j N = diag N + off N := by
    unfold diag off
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro h hh
    exact (add_sum_erase _ _ hh).symm
  have hJ : ‖vectorCesaro B N‖ ^ 2 ≤ diag N + off N := by
    apply (norm_sq_vectorCesaro_le B hN).trans
    unfold scalarCesaro
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, ∑ h ∈ range H, ∑ j ∈ range H,
          ‖inner ℂ (v (n + h)) (v (n + j))‖ :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun n _ ↦ norm_sq_block_le v n H)
          (by positivity)
      _ = _ := by
        rw [← hSplitCorr]
        unfold corr scalarCesaro
        rw [Finset.sum_comm (s := range N) (t := range H), mul_sum]
        apply sum_congr rfl
        intro h _
        rw [Finset.sum_comm (s := range N) (t := range H), mul_sum]
  have hB : ‖vectorCesaro B N‖ < (H : ℝ) * (ε / 2) := by
    have hSq := ((hJ.trans (add_le_add hDiag hOffN.le)).trans_lt hGoal)
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hSq
  have hTriangle : ‖(H : ℝ) • vectorCesaro v N‖ ≤
      ‖vectorCesaro B N‖ + ‖vectorCesaro B N - (H : ℝ) • vectorCesaro v N‖ := by
    nth_rewrite 1 [show (H : ℝ) • vectorCesaro v N =
      vectorCesaro B N - (vectorCesaro B N - (H : ℝ) • vectorCesaro v N) by abel]
    exact norm_sub_le _ _
  rw [norm_smul, Real.norm_of_nonneg hHp.le] at hTriangle
  rw [dist_zero_right]
  apply (lt_of_mul_lt_mul_left ?_ hHp.le)
  calc
    _ ≤ _ := hTriangle
    _ < (H : ℝ) * (ε / 2) + ε / 2 := add_lt_add hB hErrN
    _ ≤ (H : ℝ) * ε := by nlinarith

end JdLG
