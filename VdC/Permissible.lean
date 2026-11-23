/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Permissible -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators ComplexConjugate

namespace VdC

theorem norm_cesaro_le (x : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) (hx : ∀ n, ‖x n‖ ≤ C)
    (N : ℕ) : ‖cesaro x N‖ ≤ C := by
  by_cases hN : N = 0
  · simpa [cesaro, hN] using hC
  have hN' : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [cesaro, norm_div, Complex.norm_natCast, div_le_iff₀ hN']
  calc
    _ ≤ ∑ n ∈ range N, ‖x n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range N, C := sum_le_sum fun n _ => hx n
    _ = C * N := by simp [mul_comm]

theorem norm_corr_le {x y : ℕ → ℂ} {Cx Cy : ℝ} (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy)
    (hx : ∀ n, ‖x n‖ ≤ Cx) (hy : ∀ n, ‖y n‖ ≤ Cy) (h N : ℕ) :
    ‖corr x y h N‖ ≤ Cx * Cy := by
  apply norm_cesaro_le _ (mul_nonneg hCx hCy)
  intro n
  rw [norm_mul, norm_star]
  exact mul_le_mul (hx _) (hy _) (norm_nonneg _) hCx

/-- Countably many bounded complex sequences admit a common convergent subsequence.
The proof applies sequential compactness to the product of the closed discs. -/
theorem exists_common_subsequence {ι : Type*} [Countable ι] (u : ℕ → ι → ℂ)
    (hu : ∀ i, BoundedSeq (fun n => u n i)) :
    ∃ (φ : ℕ → ℕ) (a : ι → ℂ), StrictMono φ ∧
      ∀ i, Tendsto (fun n => u (φ n) i) atTop (𝓝 (a i)) := by
  classical
  choose C hC hB using hu
  let A : Set (ι → ℂ) := Set.pi Set.univ fun i => Metric.closedBall 0 (C i)
  have hA : IsCompact A := isCompact_univ_pi fun i => isCompact_closedBall _ _
  have huA (n : ℕ) : u n ∈ A := by
    intro i _
    simpa only [Metric.mem_closedBall, dist_zero_right] using hB i n
  obtain ⟨a, _, φ, hφ, hlim⟩ := hA.tendsto_subseq huA
  exact ⟨φ, a, hφ, fun i => (continuous_apply i).continuousAt.tendsto.comp hlim⟩

/-- Every increasing sequence of averaging lengths has a refinement giving
a permissible triple, using one extraction for all four correlations and all lags. -/
theorem exists_permissible_refinement {x y : ℕ → ℂ} (hx : BoundedSeq x) (hy : BoundedSeq y)
    {M : ℕ → ℕ} (hM : StrictMono M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ PermissibleTriple x y (M ∘ φ) := by
  classical
  let v (b : Bool) : ℕ → ℂ := if b then y else x
  let u (q : ℕ) (i : Bool × Bool × ℕ) := corr (v i.1) (v i.2.1) i.2.2 (M q)
  have hB (b : Bool) : BoundedSeq (v b) := by
    cases b
    · exact hx
    · exact hy
  have hu (i : Bool × Bool × ℕ) : BoundedSeq (fun q => u q i) := by
    obtain ⟨Cx, hCx, hx'⟩ := hB i.1
    obtain ⟨Cy, hCy, hy'⟩ := hB i.2.1
    exact ⟨Cx * Cy, mul_nonneg hCx hCy, fun q => norm_corr_le hCx hCy hx' hy' _ _⟩
  obtain ⟨φ, a, hφ, hlim⟩ := exists_common_subsequence u hu
  refine ⟨φ, hφ, ⟨hx, hy, hM.comp hφ, ?_, ?_, ?_, ?_⟩⟩
  · exact ⟨fun h => a (false, false, h), fun h => by simpa [u, v] using hlim (false, false, h)⟩
  · exact ⟨fun h => a (false, true, h), fun h => by simpa [u, v] using hlim (false, true, h)⟩
  · exact ⟨fun h => a (true, false, h), fun h => by simpa [u, v] using hlim (true, false, h)⟩
  · exact ⟨fun h => a (true, true, h), fun h => by simpa [u, v] using hlim (true, true, h)⟩

/-- The cutoff error from changing the starting point by a fixed shift. -/
theorem norm_cesaro_shift_sub_le (x : ℕ → ℂ) {C : ℝ} (hx : ∀ n, ‖x n‖ ≤ C)
    (k N : ℕ) : ‖cesaro (fun n => x (n + k)) N - cesaro x N‖ ≤ (2 * k * C) / N := by
  have hsum (a b : ℕ) : ∑ n ∈ range (a + b), x n =
      (∑ n ∈ range a, x n) + ∑ n ∈ range b, x (n + a) := by
    simpa [add_comm] using Finset.sum_range_add x a b
  have hdiff : (∑ n ∈ range N, x (n + k)) - (∑ n ∈ range N, x n) =
      (∑ n ∈ range k, x (n + N)) - (∑ n ∈ range k, x n) := by
    have h := (hsum k N).symm.trans ((congrArg (fun a => ∑ n ∈ range a, x n) (Nat.add_comm k N)).trans (hsum N k))
    linear_combination h
  have hbound (a : ℕ) : ‖∑ n ∈ range k, x (n + a)‖ ≤ k * C := by
    calc
      _ ≤ ∑ n ∈ range k, ‖x (n + a)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range k, C := sum_le_sum fun n _ => hx _
      _ = _ := by simp
  have hbound0 : ‖∑ n ∈ range k, x n‖ ≤ k * C := by simpa using hbound 0
  rw [cesaro, cesaro, ← sub_div, hdiff, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have htri := (norm_sub_le _ _).trans (add_le_add (hbound N) hbound0)
  linarith only [htri]

theorem tendsto_cesaro_shift_sub_zero {x : ℕ → ℂ} (hx : BoundedSeq x) (k : ℕ) :
    Tendsto (fun N => cesaro (fun n => x (n + k)) N - cesaro x N) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := hx
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (norm_cesaro_shift_sub_le x hC k)
    (tendsto_const_div_atTop_nhds_zero_nat _)

theorem tendsto_cesaro_shift {x : ℕ → ℂ} (hx : BoundedSeq x) (k : ℕ) {M : ℕ → ℕ}
    (hM : StrictMono M) {L : ℂ} (h : Tendsto (fun q => cesaro x (M q)) atTop (𝓝 L)) :
    Tendsto (fun q => cesaro (fun n => x (n + k)) (M q)) atTop (𝓝 L) := by
  have hh := ((tendsto_cesaro_shift_sub_zero hx k).comp hM.tendsto_atTop).add h
  simpa [Function.comp_def] using hh

theorem tendsto_atTop_of_permissible_refinement {x y : ℕ → ℂ}
    (hx : BoundedSeq x) (hy : BoundedSeq y) {M : ℕ → ℕ} (hM : StrictMono M)
    {h : ℕ} {L : ℂ}
    (hlimit : ∀ φ : ℕ → ℕ, StrictMono φ → PermissibleTriple x y (M ∘ φ) →
      Tendsto (fun q => corr x y h (M (φ q))) atTop (𝓝 L)) :
    Tendsto (fun q => corr x y h (M q)) atTop (𝓝 L) := by
  by_contra H
  rw [Metric.tendsto_nhds] at H
  push Not at H
  obtain ⟨ε, hε, hbad⟩ := H
  obtain ⟨ψ, hψ, hb⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨φ, hφ, hperm⟩ := exists_permissible_refinement hx hy (hM.comp hψ)
  have ht := hlimit (ψ ∘ φ) (hψ.comp hφ) hperm
  have ht' := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨q, hq, hq'⟩ := (ht'.and (Eventually.of_forall (fun q => hb (φ q)))).exists
  exact hq'.not_gt hq

theorem nearlyOrthogonal_iff_corr_tendsto_zero {x : ℕ → ℂ} (hx : BoundedSeq x) :
    NearlyOrthogonal x ↔ ∀ h : ℕ, 0 < h → Tendsto (corr x x h) atTop (𝓝 0) := by
  constructor
  · intro ho h hh
    apply tendsto_atTop_of_permissible_refinement hx hx (M := id) strictMono_id
    intro φ hφ hp
    obtain ⟨r, hr⟩ := hp.xx
    have hz := ho.2 (id ∘ φ) r hp.strictMono hr h hh
    simpa [hz] using hr h
  · intro h
    refine ⟨hx, fun N r hN hr k hk => ?_⟩
    exact tendsto_nhds_unique (hr k) ((h k hk).comp hN.tendsto_atTop)

theorem bounded_corr_product {x y : ℕ → ℂ} (hx : BoundedSeq x) (hy : BoundedSeq y) (a b : ℕ) :
    BoundedSeq (fun n => x (n + a) * star (y (n + b))) := by
  obtain ⟨Cx, h0x, hCx⟩ := hx
  obtain ⟨Cy, h0y, hCy⟩ := hy
  refine ⟨Cx * Cy, mul_nonneg h0x h0y, fun n => ?_⟩
  rw [norm_mul, norm_star]
  exact mul_le_mul (hCx _) (hCy _) (norm_nonneg _) h0x

/-- Correlation of two terms of the shift orbit, at possibly different lags. -/
noncomputable def orbitCorr (x y : ℕ → ℂ) (a b N : ℕ) : ℂ :=
  cesaro (fun n => x (n + a) * star (y (n + b))) N

theorem orbitCorr_tendsto_of_le {x y : ℕ → ℂ} (hx : BoundedSeq x) (hy : BoundedSeq y)
    {M : ℕ → ℕ} (hM : StrictMono M) {r : ℕ → ℂ} (hr : CorrLimits x y M r) {a b : ℕ}
    (hab : b ≤ a) : Tendsto (fun q => orbitCorr x y a b (M q)) atTop (𝓝 (r (a - b))) := by
  have hsum : b + (a - b) = a := by omega
  have h := tendsto_cesaro_shift (bounded_corr_product hx hy (a - b) 0) b hM (hr (a - b))
  simpa only [orbitCorr, Nat.add_assoc, hsum, Nat.add_zero] using h

theorem star_cesaro (u : ℕ → ℂ) (N : ℕ) :
    star (cesaro u N) = cesaro (fun n => star (u n)) N := by
  change (starRingEnd ℂ) ((∑ n ∈ range N, u n) / (N : ℂ)) = _
  rw [map_div₀, map_sum, map_natCast]
  rfl

theorem star_orbitCorr (x y : ℕ → ℂ) (a b N : ℕ) :
    star (orbitCorr x y a b N) = orbitCorr y x b a N := by
  unfold orbitCorr
  rw [star_cesaro]
  simp only [star_mul, star_star]

theorem exists_orbitCorr_limit {x y : ℕ → ℂ} {M : ℕ → ℕ} (h : PermissibleTriple x y M)
    (a b : ℕ) : ∃ L : ℂ, Tendsto (fun q => orbitCorr x y a b (M q)) atTop (𝓝 L) := by
  by_cases hab : b ≤ a
  · obtain ⟨r, hr⟩ := h.xy
    exact ⟨r (a - b), orbitCorr_tendsto_of_le h.boundedX h.boundedY h.strictMono hr hab⟩
  · obtain ⟨r, hr⟩ := h.yx
    have hlim := orbitCorr_tendsto_of_le h.boundedY h.boundedX h.strictMono hr (a := b) (b := a) (by omega)
    exact ⟨star (r (b - a)), by simpa only [star_orbitCorr] using hlim.star⟩

theorem PermissibleTriple.self_right {x y : ℕ → ℂ} {M : ℕ → ℕ} (h : PermissibleTriple x y M) :
    PermissibleTriple y y M := ⟨h.boundedY, h.boundedY, h.strictMono, h.yy, h.yy, h.yy, h.yy⟩

theorem PermissibleTriple.shift_right {x y : ℕ → ℂ} {M : ℕ → ℕ} (hp : PermissibleTriple x y M)
    (k : ℕ) : PermissibleTriple x (fun n => y (n + k)) M := by
  classical
  obtain ⟨Cy, hCy, hy⟩ := hp.boundedY
  have hy' : BoundedSeq (fun n => y (n + k)) := ⟨Cy, hCy, fun n => hy _⟩
  refine ⟨hp.boundedX, hy', hp.strictMono, hp.xx, ?_, ?_, ?_⟩
  · choose r hr using fun h => exists_orbitCorr_limit hp h k
    exact ⟨r, fun h => by simpa only [orbitCorr, corr] using hr h⟩
  · obtain ⟨r, hr⟩ := hp.yx
    exact ⟨fun h => r (h + k), fun h => by simpa only [corr, Nat.add_assoc] using hr (h + k)⟩
  · obtain ⟨r, hr⟩ := hp.yy
    refine ⟨r, fun h => ?_⟩
    have hlim : Tendsto (fun q => orbitCorr y y (h + k) k (M q)) atTop (𝓝 (r ((h + k) - k))) :=
      orbitCorr_tendsto_of_le hp.boundedY hp.boundedY hp.strictMono hr (by omega)
    simpa only [orbitCorr, corr, Nat.add_assoc, Nat.add_sub_cancel] using hlim

theorem realCesaro_const_pos (a : ℝ) {N : ℕ} (hN : 0 < N) :
    realCesaro (fun _ => a) N = a := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp [realCesaro, nsmul_eq_mul, hn]

theorem realCesaro_const_tendsto (a : ℝ) :
    Tendsto (realCesaro (fun _ => a)) atTop (𝓝 a) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (realCesaro_const_pos a hN).symm

theorem realCesaro_mono {x y : ℕ → ℝ} (h : ∀ n, x n ≤ y n) (N : ℕ) :
    realCesaro x N ≤ realCesaro y N := by
  exact div_le_div_of_nonneg_right (sum_le_sum fun n _ => h n) (by positivity)

theorem realCesaro_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ) (N : ℕ) :
    realCesaro (fun n => ∑ i ∈ s, a i n) N = ∑ i ∈ s, realCesaro (a i) N := by
  unfold realCesaro
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- The elementary finite-average Cauchy–Schwarz bound used to test compact shifts. -/
theorem norm_cesaro_mul_star_sq_le (x y : ℕ → ℂ) {C : ℝ} (_hC : 0 ≤ C)
    (hx : ∀ n, ‖x n‖ ≤ C) (N : ℕ) :
    ‖cesaro (fun n => x n * star (y n)) N‖ ^ 2 ≤
      C^2 * realCesaro (fun n => ‖y n‖^2) N := by
  by_cases hN : N = 0
  · simp [hN, cesaro, realCesaro]
  have hn : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  let S := ∑ n ∈ range N, ‖y n‖
  let Q := ∑ n ∈ range N, ‖y n‖^2
  have hnorm : ‖∑ n ∈ range N, x n * star (y n)‖ ≤ C * S := calc
    _ ≤ ∑ n ∈ range N, ‖x n * star (y n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range N, C * ‖y n‖ := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right (hx n) (norm_nonneg _)
    _ = _ := by simp only [S, Finset.mul_sum]
  have hCS : S^2 ≤ (N : ℝ) * Q := by
    simpa [S, Q, nsmul_eq_mul] using
      (Finset.sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1 : ℝ)) (fun n => ‖y n‖))
  rw [cesaro, norm_div, Complex.norm_natCast, div_pow]
  change ‖∑ n ∈ range N, x n * star (y n)‖ ^ 2 / (N : ℝ)^2 ≤ C^2 * (Q / N)
  calc
    _ ≤ (C * S)^2 / (N : ℝ)^2 := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hnorm 2) (sq_nonneg _)
    _ ≤ C^2 * ((N : ℝ) * Q) / (N : ℝ)^2 := by
      rw [mul_pow]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hCS (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by field_simp [hn.ne']

theorem orbitCorr_sub_eq {x y : ℕ → ℂ} (a b c N : ℕ) :
    orbitCorr x y a b N - orbitCorr x y a c N =
      cesaro (fun n => x (n + a) * star (y (n + b) - y (n + c))) N := by
  simp only [orbitCorr, cesaro, ← sub_div, ← Finset.sum_sub_distrib, star_sub, mul_sub]

/-- Weakly mixing sequences are asymptotically orthogonal along the cutoffs on
which the testing sequence is compact (`WeakMixingPerpCompact`). -/
theorem nearlyWeakMixing_corr_compact {x y : ℕ → ℂ} {M : ℕ → ℕ}
    (hx : NearlyWeakMixing x) (hy : CompactAlong y M) :
    Tendsto (fun q => corr x y 0 (M q)) atTop (𝓝 0) := by
  classical
  apply tendsto_atTop_of_permissible_refinement hx.1 hy.1 hy.2.1
  intro φ hφ hp
  obtain ⟨r, hr⟩ := hp.xy
  suffices hr0 : r 0 = 0 by simpa [hr0, Function.comp_def] using hr 0
  by_contra hne
  obtain ⟨Cx, hCx0, hCx⟩ := hx.1
  let A := ‖r 0‖
  have hA : 0 < A := norm_pos_iff.mpr hne
  let ε := (A / (2 * (Cx + 1)))^2
  have he : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨ry, hry⟩ := hp.yy
  obtain ⟨K, hcover⟩ := hy.2.2 φ ry hφ hry ε he
  have hshift (k : ℕ) := hp.shift_right (k + 1)
  choose R hR using fun k => (hshift k).xy
  have hmean (k : ℕ) : Tendsto (realCesaro (fun h => ‖R k (h + 1)‖)) atTop (𝓝 0) :=
    hx.2 _ _ _ (hshift k) (hR k)
  have hdiff (m : ℕ) : ∃ k ≤ K, ‖r 0 - R k (m + 1)‖ ≤ A / 2 := by
    obtain ⟨k, hk, e, hee, hdist⟩ := hcover m
    refine ⟨k, hk, ?_⟩
    have hself := orbitCorr_tendsto_of_le hx.1 hy.1 hp.strictMono hr
      (le_refl (m + 1))
    rw [Nat.sub_self] at hself
    have htest : Tendsto (fun q => orbitCorr x y (m + 1) (k + 1) ((M ∘ φ) q)) atTop
        (𝓝 (R k (m + 1))) := hR k (m + 1)
    have hlim := ((hself.sub htest).norm).pow 2
    have hineq : ∀ q, ‖orbitCorr x y (m + 1) (m + 1) ((M ∘ φ) q) -
        orbitCorr x y (m + 1) (k + 1) ((M ∘ φ) q)‖ ^ 2 ≤ Cx^2 *
          realCesaro (fun n => ‖y (n + (m + 1)) - y (n + (k + 1))‖^2) ((M ∘ φ) q) := by
      intro q
      rw [orbitCorr_sub_eq]
      exact norm_cesaro_mul_star_sq_le _ _ hCx0 (fun n => hCx _) _
    have hb : ‖r 0 - R k (m + 1)‖ ^ 2 ≤ Cx^2 * e :=
      le_of_tendsto_of_tendsto hlim (hdist.const_mul _) (Eventually.of_forall hineq)
    have hbound : Cx^2 * ε ≤ (A / 2)^2 := by
      dsimp only [ε]
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity) _ 2
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * (Cx + 1))]
      nlinarith only [hA]
    have hsq := hb.trans ((mul_le_mul_of_nonneg_left hee.le (sq_nonneg _)).trans hbound)
    by_contra! H
    nlinarith only [hsq, mul_pos (sub_pos.mpr H) (show 0 < ‖r 0 - R k (m + 1)‖ + A/2 by positivity)]
  have hpoint (m : ℕ) : A / 2 ≤ ∑ k ∈ range (K + 1), ‖R k (m + 1)‖ := by
    obtain ⟨k, hk, hclose⟩ := hdiff m
    have htri := norm_sub_le (r 0 - R k (m + 1)) (-R k (m + 1))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
    have hk' : k ∈ range (K + 1) := mem_range.mpr (by omega)
    have hsum := single_le_sum (fun j _ => norm_nonneg (R j (m + 1))) hk'
    change ‖r 0‖ / 2 ≤ _
    linarith only [htri, hclose, hsum]
  have htotal : Tendsto (realCesaro (fun m => ∑ k ∈ range (K + 1), ‖R k (m + 1)‖)) atTop (𝓝 0) := by
    have ht : Tendsto (fun N => ∑ k ∈ range (K + 1), realCesaro (fun m => ‖R k (m + 1)‖) N)
        atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using (tendsto_finsetSum (range (K + 1)) fun k _ => hmean k)
    exact ht.congr' (Eventually.of_forall fun N => (realCesaro_sum _ _ N).symm)
  have hzero := le_of_tendsto_of_tendsto (realCesaro_const_tendsto (A/2)) htotal
    (Eventually.of_forall fun N => realCesaro_mono hpoint N)
  linarith only [hA, hzero]

theorem corr_star_star (x y : ℕ → ℂ) (h N : ℕ) :
    corr (fun n => star (x n)) (fun n => star (y n)) h N = star (corr x y h N) := by
  simp only [corr, star_cesaro, star_mul, star_star, mul_comm]

theorem CompactAlong.conjugate {y : ℕ → ℂ} {M : ℕ → ℕ} (hy : CompactAlong y M) :
    CompactAlong (fun n => star (y n)) M := by
  obtain ⟨Cy, hCy, hnorm⟩ := hy.1
  refine ⟨⟨Cy, hCy, fun n => by simpa only [norm_star] using hnorm n⟩, hy.2.1, ?_⟩
  intro φ r hφ hr ε he
  have hconj : CorrLimits y y (M ∘ φ) (fun h => star (r h)) := by
    intro h
    simpa only [corr_star_star, star_star] using (hr h).star
  obtain ⟨K, hK⟩ := hy.2.2 φ _ hφ hconj ε he
  refine ⟨K, fun m => ?_⟩
  obtain ⟨k, hk, e, hlt, hlim⟩ := hK m
  exact ⟨k, hk, e, hlt, by simpa only [← star_sub, norm_star] using hlim⟩

theorem nearlyWeakMixing_mul_compact {x y : ℕ → ℂ} {M : ℕ → ℕ}
    (hx : NearlyWeakMixing x) (hy : CompactAlong y M) :
    Tendsto (fun q => cesaro (fun n => x n * y n) (M q)) atTop (𝓝 0) := by
  simpa only [corr, Nat.add_zero, star_star] using nearlyWeakMixing_corr_compact hx hy.conjugate

theorem compactAlong_const (c : ℂ) {M : ℕ → ℕ} (hM : StrictMono M) :
    CompactAlong (fun _ => c) M := by
  refine ⟨⟨‖c‖, norm_nonneg _, fun _ => le_rfl⟩, hM, fun _ _ _ _ ε he => ?_⟩
  refine ⟨0, fun m => ⟨0, le_rfl, 0, he, ?_⟩⟩
  simp [realCesaro]

theorem NearlyWeakMixing.cesaro_zero {x : ℕ → ℂ} (hx : NearlyWeakMixing x) :
    Tendsto (cesaro x) atTop (𝓝 0) := by
  simpa only [id_eq, mul_one] using nearlyWeakMixing_mul_compact hx (compactAlong_const 1 strictMono_id)

theorem realCesaro_re (u : ℕ → ℂ) (N : ℕ) :
    realCesaro (fun n => (u n).re) N = (cesaro u N).re := by
  unfold cesaro realCesaro
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum]

theorem norm_sub_sq_complex (a b : ℂ) : ‖a - b‖^2 =
    (a * star a).re + (b * star b).re - 2 * (a * star b).re := by
  change ‖a - b‖^2 = (a * conj a).re + (b * conj b).re - 2 * (a * conj b).re
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem realCesaro_shift_dist_sq (y : ℕ → ℂ) (a b N : ℕ) :
    realCesaro (fun n => ‖y (n + a) - y (n + b)‖^2) N =
      (orbitCorr y y a a N).re + (orbitCorr y y b b N).re - 2 * (orbitCorr y y a b N).re := by
  calc
    _ = realCesaro (fun n => (y (n + a) * star (y (n + a))).re) N +
      realCesaro (fun n => (y (n + b) * star (y (n + b))).re) N -
      2 * realCesaro (fun n => (y (n + a) * star (y (n + b))).re) N := by
      simp only [norm_sub_sq_complex, realCesaro, sum_sub_distrib, sum_add_distrib, ← mul_sum]
      ring
    _ = _ := by simp only [realCesaro_re, orbitCorr]

theorem tendsto_realCesaro_shift_dist_sq {y : ℕ → ℂ} {M : ℕ → ℕ} {r : ℕ → ℂ}
    (hy : BoundedSeq y) (hM : StrictMono M) (hr : CorrLimits y y M r) {a b : ℕ} (hab : b ≤ a) :
    Tendsto (fun q => realCesaro (fun n => ‖y (n + a) - y (n + b)‖^2) (M q)) atTop
      (𝓝 (2 * ((r 0).re - (r (a-b)).re))) := by
  have haa := orbitCorr_tendsto_of_le hy hy hM hr (le_refl a)
  have hbb := orbitCorr_tendsto_of_le hy hy hM hr (le_refl b)
  rw [Nat.sub_self] at haa hbb
  have hab' := orbitCorr_tendsto_of_le hy hy hM hr hab
  have hae := Complex.continuous_re.continuousAt.tendsto.comp haa
  have hbe := Complex.continuous_re.continuousAt.tendsto.comp hbb
  have habe := Complex.continuous_re.continuousAt.tendsto.comp hab'
  have H := (hae.add hbe).sub (habe.const_mul 2)
  rw [show 2 * ((r 0).re - (r (a-b)).re) = (r 0).re + (r 0).re - 2 * (r (a-b)).re by ring]
  exact H.congr' (Eventually.of_forall fun q => (realCesaro_shift_dist_sq y a b (M q)).symm)

theorem compactAlong_returns {M φ : ℕ → ℕ} {y : ℕ → ℂ} {r : ℕ → ℂ}
    (hy : CompactAlong y M) (hφ : StrictMono φ) (hr : CorrLimits y y (M ∘ φ) r) :
    ∀ ε : ℝ, 0 < ε → ∀ L : ℕ, ∃ h ≥ L, 2 * ((r 0).re - (r h).re) < ε := by
  intro ε hε L
  obtain ⟨K, hK⟩ := hy.2.2 φ r hφ hr ε hε
  obtain ⟨k, hk, e, he, hlim⟩ := hK (L + K)
  let h := (L + K + 1) - (k + 1)
  have hr' := tendsto_realCesaro_shift_dist_sq hy.1 (hy.2.1.comp hφ) hr
    (a := L + K + 1) (b := k + 1) (by omega)
  have heq := tendsto_nhds_unique hr' hlim
  exact ⟨h, by dsimp [h]; omega, heq.trans_lt he⟩

private theorem cesaro_add_wm (x y : ℕ → ℂ) (N : ℕ) :
    cesaro (fun n => x n + y n) N = cesaro x N + cesaro y N := by
  simp only [cesaro, Finset.sum_add_distrib, add_div]

theorem cesaro_const_mul (c : ℂ) (x : ℕ → ℂ) (N : ℕ) :
    cesaro (fun n => c * x n) N = c * cesaro x N := by
  simp only [cesaro, ← Finset.mul_sum, mul_div_assoc]

theorem cesaro_finset_sum {ι : Type*} (s : Finset ι) (x : ι → ℕ → ℂ) (N : ℕ) :
    cesaro (fun n => ∑ i ∈ s, x i n) N = ∑ i ∈ s, cesaro (x i) N := by
  unfold cesaro
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem realCesaro_add (x y : ℕ → ℝ) (N : ℕ) :
    realCesaro (fun n => x n + y n) N = realCesaro x N + realCesaro y N := by
  simp only [realCesaro, Finset.sum_add_distrib, add_div]

theorem realCesaro_const_mul (c : ℝ) (x : ℕ → ℝ) (N : ℕ) :
    realCesaro (fun n => c * x n) N = c * realCesaro x N := by
  simp only [realCesaro, ← Finset.mul_sum, mul_div_assoc]

theorem realCesaro_nonneg {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) (N : ℕ) :
    0 ≤ realCesaro x N := div_nonneg (sum_nonneg fun n _ => hx n) (by positivity)

theorem corr_add_const_mul (x y z : ℕ → ℂ) (c : ℂ) (h N : ℕ) :
    corr (fun n => x n + c * y n) z h N = corr x z h N + c * corr y z h N := by
  simp only [corr, add_mul, mul_assoc, cesaro_add_wm, cesaro_const_mul]

theorem boundedSeq_add_const_mul {x y : ℕ → ℂ} (hx : BoundedSeq x) (hy : BoundedSeq y)
    (c : ℂ) : BoundedSeq (fun n => x n + c * y n) := by
  obtain ⟨Cx, hCx, hX⟩ := hx
  obtain ⟨Cy, hCy, hY⟩ := hy
  refine ⟨Cx + ‖c‖ * Cy, by positivity, fun n => ?_⟩
  have htri := norm_add_le (x n) (c * y n)
  rw [norm_mul] at htri
  exact htri.trans (add_le_add (hX n) (mul_le_mul_of_nonneg_left (hY n) (norm_nonneg _)))

/-- The linear closure part of `ClosedUnderLinearClosureLemma` for nearly weakly mixing sequences. -/
theorem NearlyWeakMixing.add_const_mul {x y : ℕ → ℂ} (hx : NearlyWeakMixing x)
    (hy : NearlyWeakMixing y) (c : ℂ) : NearlyWeakMixing (fun n => x n + c * y n) := by
  refine ⟨boundedSeq_add_const_mul hx.1 hy.1 c, ?_⟩
  intro z N r hp hr
  obtain ⟨φ, hφ, hp1⟩ := exists_permissible_refinement hx.1 hp.boundedY hp.strictMono
  obtain ⟨ψ, hψ, hp2⟩ := exists_permissible_refinement hy.1 hp.boundedY hp1.strictMono
  obtain ⟨rx, hX⟩ := hp1.xy
  obtain ⟨ry, hY⟩ := hp2.xy
  have hsum (h : ℕ) : r h = rx h + c * ry h := by
    have hr' := (hr h).comp (hφ.comp hψ).tendsto_atTop
    have hh := ((hX h).comp hψ.tendsto_atTop).add ((hY h).const_mul c)
    exact tendsto_nhds_unique hr' (by simpa only [corr_add_const_mul, Function.comp_def] using hh)
  have hX' := hx.2 _ _ _ hp1 hX
  have hY' := hy.2 _ _ _ hp2 hY
  have hup := hX'.add (hY'.const_mul ‖c‖)
  have hup' : Tendsto (fun H => realCesaro (fun h => ‖rx (h+1)‖ + ‖c‖ * ‖ry (h+1)‖) H) atTop (𝓝 0) := by
    simpa only [realCesaro_add, realCesaro_const_mul, mul_zero, add_zero] using hup
  refine squeeze_zero (realCesaro_nonneg fun _ => norm_nonneg _) (fun H => realCesaro_mono ?_ H) hup'
  intro h
  rw [hsum, ← norm_mul]
  exact norm_add_le _ _

theorem nearlyWeakMixing_zero : NearlyWeakMixing (fun _ => 0) := by
  refine ⟨⟨0, le_rfl, by simp⟩, ?_⟩
  intro y N r hp hr
  have h (k : ℕ) : r k = 0 := tendsto_nhds_unique (hr k) (by simp [corr, cesaro])
  simpa only [h, norm_zero] using realCesaro_const_tendsto 0

theorem NearlyWeakMixing.const_mul {x : ℕ → ℂ} (hx : NearlyWeakMixing x) (c : ℂ) :
    NearlyWeakMixing (fun n => c * x n) := by
  simpa only [zero_add] using nearlyWeakMixing_zero.add_const_mul hx c

theorem NearlyWeakMixing.add {x y : ℕ → ℂ} (hx : NearlyWeakMixing x) (hy : NearlyWeakMixing y) :
    NearlyWeakMixing (fun n => x n + y n) := by
  simpa only [one_mul] using hx.add_const_mul hy 1

theorem nearlyWeakMixing_finset_sum {ι : Type*} (s : Finset ι) (x : ι → ℕ → ℂ)
    (h : ∀ j ∈ s, NearlyWeakMixing (x j)) : NearlyWeakMixing (fun n => ∑ j ∈ s, x j n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using nearlyWeakMixing_zero
  | insert a s ha IH =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem norm_cesaro_mul_star_sq_le_right (x y : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hy : ∀ n, ‖y n‖ ≤ C) (N : ℕ) :
    ‖cesaro (fun n => x n * star (y n)) N‖ ^ 2 ≤
      C^2 * realCesaro (fun n => ‖x n‖^2) N := by
  rw [← norm_star (cesaro (fun n => x n * star (y n)) N), star_cesaro]
  simpa only [star_mul, star_star] using norm_cesaro_mul_star_sq_le y x hC hy N

theorem corr_sub_left (x z y : ℕ → ℂ) (h N : ℕ) :
    corr x y h N - corr z y h N = corr (fun n => x n - z n) y h N := by
  simp only [corr, cesaro, ← sub_div, ← Finset.sum_sub_distrib, sub_mul]

theorem tendsto_realCesaro_shift_sub_zero {u : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ n, |u n| ≤ C) (h : ℕ) :
    Tendsto (fun N => realCesaro (fun n => u (n+h)) N - realCesaro u N) atTop (𝓝 0) := by
  let v : ℕ → ℂ := fun n => (u n : ℂ)
  have hv : BoundedSeq v := ⟨C, hC, fun n => by simpa [v] using hu n⟩
  have hh := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_cesaro_shift_sub_zero hv h)
  simpa only [Function.comp_def, Complex.sub_re, Complex.zero_re, ← realCesaro_re,
    v, Complex.ofReal_re] using hh

/-- Quantitative Cesàro-L² closure in the nearly weakly mixing case. -/
theorem nearlyWeakMixing_of_cesaro_l2_approx {x : ℕ → ℂ} (hx : BoundedSeq x)
    (hApprox : ∀ ε : ℝ, 0 < ε → ∃ z : ℕ → ℂ, NearlyWeakMixing z ∧
      ∀ᶠ N : ℕ in atTop, realCesaro (fun n => ‖x n - z n‖^2) N ≤ ε) :
    NearlyWeakMixing x := by
  refine ⟨hx, ?_⟩
  intro y N r hp hr
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Cy, hCy, hY⟩ := hp.boundedY
  let δ := (ε / (2 * (Cy + 1)))^2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨z, hz, hApproxZ⟩ := hApprox (δ/2) (by positivity)
  obtain ⟨φ, hφ, hperm⟩ := exists_permissible_refinement hz.1 hp.boundedY hp.strictMono
  obtain ⟨s, hs⟩ := hperm.xy
  obtain ⟨Cx, hCx, hX⟩ := hx
  obtain ⟨Cz, hCz, hZ⟩ := hz.1
  let D (n : ℕ) := ‖x n - z n‖^2
  have hD0 (n : ℕ) : 0 ≤ D n := sq_nonneg _
  have hD (n : ℕ) : |D n| ≤ (Cx + Cz)^2 := by
    rw [abs_of_nonneg (hD0 n)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hX n) (hZ n))) 2
  have hdiff (h : ℕ) : ‖r h - s h‖ ≤ ε / 2 := by
    have hsq_shift := tendsto_realCesaro_shift_sub_zero (by positivity) hD h
    have hev : ∀ᶠ j : ℕ in atTop, realCesaro (fun n => D (n+h)) j ≤ δ := by
      filter_upwards [hApproxZ, hsq_shift.eventually (gt_mem_nhds (show 0 < δ/2 by positivity))] with j hj hj'
      linarith only [hj, hj']
    have hn := ((hr h).comp hφ.tendsto_atTop).sub (hs h)
    have hn2 := hn.norm.pow 2
    have hbound : ∀ᶠ q : ℕ in atTop,
        ‖corr x y h (N (φ q)) - corr z y h (N (φ q))‖ ^ 2 ≤ Cy^2 * δ := by
      filter_upwards [hperm.strictMono.tendsto_atTop.eventually hev] with q hq
      rw [corr_sub_left]
      have hcs := norm_cesaro_mul_star_sq_le_right (fun n => x (n+h) - z (n+h)) y hCy hY (N (φ q))
      exact hcs.trans (mul_le_mul_of_nonneg_left hq (sq_nonneg Cy))
    have hn3 : ‖r h - s h‖^2 ≤ Cy^2 * δ := le_of_tendsto hn2 hbound
    have hb : Cy^2 * δ ≤ (ε/2)^2 := by
      dsimp only [δ]
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity) _ 2
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * (Cy+1))]
      nlinarith only [hε]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hn3.trans hb)
  have hpoint (h : ℕ) : ‖r (h+1)‖ ≤ ‖s (h+1)‖ + ε/2 := by
    calc
      _ = ‖(r (h+1) - s (h+1)) + s (h+1)‖ := by rw [sub_add_cancel]
      _ ≤ ‖r (h+1) - s (h+1)‖ + ‖s (h+1)‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [hdiff (h+1)]
  have hmean := hz.2 _ _ _ hperm hs
  filter_upwards [hmean.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity)),
    eventually_gt_atTop (0 : ℕ)] with H hH Hpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (realCesaro_nonneg (fun _ => norm_nonneg _) _)]
  have hpnt := realCesaro_mono hpoint H
  rw [realCesaro_add, realCesaro_const_pos _ Hpos] at hpnt
  linarith only [hpnt, hH]

/-- The limsup formulation of the L² closure in `ClosedUnderLinearClosureLemma`. -/
theorem nearlyWeakMixing_of_limsup_l2 {x : ℕ → ℂ} (hx : BoundedSeq x)
    (z : ℕ → ℕ → ℂ) (hz : ∀ k, NearlyWeakMixing (z k))
    (hlim : Tendsto (fun k => limsup (fun N => realCesaro (fun n => ‖z k n - x n‖^2) N) atTop)
      atTop (𝓝 0)) : NearlyWeakMixing x := by
  apply nearlyWeakMixing_of_cesaro_l2_approx hx
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

private noncomputable def phaseWeight (z : ℂ) : ℂ := star z / (‖z‖ : ℂ)

private theorem norm_phaseWeight_le (z : ℂ) : ‖phaseWeight z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [phaseWeight, hz]
  have hp := norm_pos_iff.mpr hz
  simp [phaseWeight, hp.ne']

private theorem phaseWeight_mul (z : ℂ) : phaseWeight z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [phaseWeight, hz]
  have hp := norm_pos_iff.mpr hz
  have ho : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold phaseWeight
  rw [div_mul_eq_mul_div, mul_comm (star z), show z * star z = (‖z‖ : ℂ)^2 from Complex.mul_conj' z]
  field_simp [ho]

private noncomputable def weightedShift (x : ℕ → ℂ) (w : ℕ → ℂ) (H n : ℕ) : ℂ :=
  ∑ j ∈ range H, w j * x (n + (j + 1))

private theorem cesaro_weightedShift_mul_star (x y w : ℕ → ℂ) (H N : ℕ) :
    cesaro (fun n => weightedShift x w H n * star (y n)) N =
      ∑ j ∈ range H, w j * corr x y (j+1) N := by
  simp only [weightedShift, Finset.sum_mul, mul_assoc, cesaro_finset_sum, cesaro_const_mul, corr]

private theorem energy_weightedShift (x w : ℕ → ℂ) (H N : ℕ) :
    realCesaro (fun n => ‖weightedShift x w H n‖^2) N =
      (∑ j ∈ range H, ∑ k ∈ range H, w j * star (w k) *
        orbitCorr x x (j+1) (k+1) N).re := by
  have hpoint (n : ℕ) : ‖weightedShift x w H n‖^2 =
      (∑ j ∈ range H, ∑ k ∈ range H, w j * star (w k) *
        (x (n+(j+1)) * star (x (n+(k+1))))).re := by
    let p := weightedShift x w H n
    have hp : (p * star p).re = ‖p‖^2 := by rw [show p * star p = (‖p‖ : ℂ)^2 from Complex.mul_conj' p]; norm_cast
    rw [← hp]
    apply congrArg Complex.re
    change (∑ j ∈ range H, w j * x (n+(j+1))) *
      (starRingEnd ℂ) (∑ k ∈ range H, w k * x (n+(k+1))) = _
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul]
    change w j * x (n+(j+1)) * (star (w k) * star (x (n+(k+1)))) = _
    ring
  simp only [hpoint, realCesaro_re, cesaro_finset_sum, cesaro_const_mul, orbitCorr]

private theorem weightedShift_energy_le (x w : ℕ → ℂ) (hw : ∀ k, ‖w k‖ ≤ 1) (H N : ℕ) :
    realCesaro (fun n => ‖weightedShift x w H n‖^2) N ≤
      ∑ j ∈ range H, ∑ k ∈ range H, ‖orbitCorr x x (j+1) (k+1) N‖ := by
  rw [energy_weightedShift]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  apply Finset.sum_le_sum
  intro j _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, norm_mul, norm_star]
  have hb := mul_le_mul (hw j) (hw k) (norm_nonneg _) zero_le_one
  exact mul_le_of_le_one_left (norm_nonneg _) (by simpa only [one_mul] using hb)

private theorem tendsto_norm_orbitCorr_self {x : ℕ → ℂ} (hx : BoundedSeq x)
    {M : ℕ → ℕ} (hM : StrictMono M) {r : ℕ → ℂ} (hr : CorrLimits x x M r) (j k : ℕ) :
    Tendsto (fun q => ‖orbitCorr x x (j+1) (k+1) (M q)‖) atTop (𝓝 ‖r (j-k + (k-j))‖) := by
  by_cases h : k ≤ j
  · have hh : (j+1) - (k+1) = j-k+(k-j) := by omega
    exact hh ▸ (orbitCorr_tendsto_of_le hx hx hM hr (a := j+1) (b := k+1) (by omega)).norm
  · have hh : (k+1) - (j+1) = j-k+(k-j) := by omega
    have ht := (orbitCorr_tendsto_of_le hx hx hM hr (a := k+1) (b := j+1) (by omega)).star.norm
    simpa only [star_orbitCorr, norm_star, hh] using ht

private theorem toeplitz_row_bound (c : ℕ → ℝ) (hc : ∀ h, 0 ≤ c h) {H j : ℕ} (hj : j < H) :
    (∑ k ∈ range H, c (j-k+(k-j))) ≤ 2 * ∑ k ∈ range H, c k := by
  rw [← Finset.sum_filter_add_sum_filter_not (range H) (fun k => k ≤ j)]
  have hle : (∑ k ∈ (range H).filter (· ≤ j), c (j-k+(k-j))) ≤ ∑ k ∈ range H, c k := by
    apply Finset.sum_le_sum_of_injOn (fun k : ℕ => j-k)
    · intro a ha b hb he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
      change j - a = j - b at he
      omega
    · intro u hu
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
      apply Finset.mem_range.mpr
      omega
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      simp [Nat.sub_eq_zero_of_le hk']
    · exact fun a _ _ => hc a
  have hge : (∑ k ∈ (range H).filter (fun k => ¬ k ≤ j), c (j-k+(k-j))) ≤ ∑ k ∈ range H, c k := by
    apply Finset.sum_le_sum_of_injOn (fun k : ℕ => k-j)
    · intro a ha b hb he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
      change a - j = b - j at he
      omega
    · intro u hu
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
      have hk' := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      apply Finset.mem_range.mpr
      omega
    · intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      simp [Nat.sub_eq_zero_of_le (show j ≤ k by omega)]
    · exact fun a _ _ => hc a
  linarith only [hle, hge]

theorem double_toeplitz_bound (c : ℕ → ℝ) (hc : ∀ h, 0 ≤ c h) (H : ℕ) :
    (∑ j ∈ range H, ∑ k ∈ range H, c (j-k+(k-j))) ≤
      (H : ℝ) * (2 * (c 0 + ∑ k ∈ range H, c (k+1))) := by
  have hsum : (∑ k ∈ range H, c k) ≤ c 0 + ∑ k ∈ range H, c (k+1) := by
    rw [add_comm (c 0), ← Finset.sum_range_succ']
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ H)) (fun k _ _ => hc k)
  calc
    _ ≤ ∑ j ∈ range H, 2 * (c 0 + ∑ k ∈ range H, c (k+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (toeplitz_row_bound c hc (Finset.mem_range.mp hj)).trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ = _ := by simp

/-- A self-correlation criterion for nearly weak mixing, using a finite phase
choice and Cesàro Cauchy–Schwarz. -/
theorem nearlyWeakMixing_of_self_mean {x : ℕ → ℂ} (hx : BoundedSeq x)
    (hself : ∀ M r, StrictMono M → CorrLimits x x M r →
      Tendsto (realCesaro (fun h => ‖r (h+1)‖)) atTop (𝓝 0)) : NearlyWeakMixing x := by
  refine ⟨hx, ?_⟩
  intro y M r hp hr
  obtain ⟨u, hu⟩ := hp.xx
  obtain ⟨C, hC, hy⟩ := hp.boundedY
  let c (h : ℕ) := ‖u h‖
  let w (h : ℕ) := phaseWeight (r (h+1))
  have hw (h : ℕ) : ‖w h‖ ≤ 1 := norm_phaseWeight_le _
  have hsum (H : ℕ) : (∑ j ∈ range H, ‖r (j+1)‖)^2 ≤
      C^2 * (∑ j ∈ range H, ∑ k ∈ range H, c (j-k+(k-j))) := by
    have hCcs (q : ℕ) : ‖∑ j ∈ range H, w j * corr x y (j+1) (M q)‖ ^ 2 ≤
        C^2 * (∑ j ∈ range H, ∑ k ∈ range H, ‖orbitCorr x x (j+1) (k+1) (M q)‖) := by
      rw [← cesaro_weightedShift_mul_star]
      exact (norm_cesaro_mul_star_sq_le_right (weightedShift x w H) y hC hy (M q)).trans
        (mul_le_mul_of_nonneg_left (weightedShift_energy_le x w hw H (M q)) (sq_nonneg _))
    have hlimL := (tendsto_finsetSum (range H) (fun j _ => (hr (j+1)).const_mul (w j))).norm.pow 2
    have heq : ‖∑ j ∈ range H, w j * r (j+1)‖ = ∑ j ∈ range H, ‖r (j+1)‖ := by
      simp only [w, phaseWeight_mul, ← Complex.ofReal_sum, Complex.norm_real]
      exact abs_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg _))
    rw [heq] at hlimL
    have hlimR := (tendsto_finsetSum (range H) (fun j _ => tendsto_finsetSum (range H)
      (fun k _ => tendsto_norm_orbitCorr_self hx hp.strictMono hu j k))).const_mul (C^2)
    exact le_of_tendsto_of_tendsto hlimL hlimR (Eventually.of_forall hCcs)
  have hmean := hself M u hp.strictMono hu
  have hupper0 := (tendsto_const_div_atTop_nhds_zero_nat (c 0)).add hmean
  have hupper : Tendsto (fun H : ℕ => C^2 * (2 * (c 0 / (H : ℝ) + realCesaro (fun k => c (k+1)) H)))
      atTop (𝓝 0) := by
    simpa only [c, add_zero, mul_zero] using (hupper0.const_mul 2).const_mul (C^2)
  have hsq : Tendsto (fun H => (realCesaro (fun h => ‖r (h+1)‖) H)^2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ hupper
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
    have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hH
    have h1 := (hsum H).trans (mul_le_mul_of_nonneg_left (double_toeplitz_bound c (fun _ => norm_nonneg _) H) (sq_nonneg _))
    rw [realCesaro, div_pow]
    have h2 := div_le_div_of_nonneg_right h1 (sq_nonneg (H : ℝ))
    refine h2.trans_eq ?_
    unfold realCesaro
    field_simp [hH0]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (realCesaro_nonneg (fun _ => norm_nonneg _) _)] using hh

/-- Lemma `CreatingSpectrallyLebesgue/NWMSequences` (ii). -/
theorem nearlyWeakMixing_of_upper_corr {x : ℕ → ℂ} (hx : BoundedSeq x)
    (h : Tendsto (realCesaro (fun k => limsup (fun N => ‖corr x x (k+1) N‖) atTop)) atTop (𝓝 0)) :
    NearlyWeakMixing x := by
  apply nearlyWeakMixing_of_self_mean hx
  intro M r hM hr
  obtain ⟨C, hC, hX⟩ := hx
  have hb (k : ℕ) : ‖r k‖ ≤ limsup (fun N => ‖corr x x k N‖) atTop := by
    have hu := (hr k).norm.limsup_eq
    rw [← hu]
    exact hM.tendsto_atTop.limsup_comp_le_limsup
      (isCoboundedUnder_le_of_le _ (fun _ => norm_nonneg _))
      (isBoundedUnder_of_eventually_le (Eventually.of_forall fun N => norm_corr_le hC hC hX hX k N))
  exact squeeze_zero (realCesaro_nonneg (fun _ => norm_nonneg _)) (fun H => realCesaro_mono (fun k => hb (k+1)) H) h

theorem NearlyOrthogonal.nearlyWeakMixing {x : ℕ → ℂ} (hx : NearlyOrthogonal x) : NearlyWeakMixing x := by
  apply nearlyWeakMixing_of_self_mean hx.1
  intro M r hM hr
  have hz (k : ℕ) : r (k+1) = 0 := hx.2 M r hM hr (k+1) (Nat.succ_pos k)
  simpa only [hz, norm_zero] using realCesaro_const_tendsto 0

/-- Nearly weak mixing also controls the cross-correlations with the lag on
the second sequence. A common finite shift reverses the lag order while the
Toeplitz estimate still uses just the self-correlations of the first sequence. -/
theorem NearlyWeakMixing.reverse_corr {x y : ℕ → ℂ} (hx : NearlyWeakMixing x)
    {M : ℕ → ℕ} {r : ℕ → ℂ} (hp : PermissibleTriple x y M)
    (hr : CorrLimits y x M r) :
    Tendsto (realCesaro (fun h => ‖r (h+1)‖)) atTop (𝓝 0) := by
  obtain ⟨u, hu⟩ := hp.xx
  obtain ⟨C, hC, hy⟩ := hp.boundedY
  let c (h : ℕ) := ‖u h‖
  have hself : PermissibleTriple x x M :=
    ⟨hx.1, hx.1, hp.strictMono, hp.xx, hp.xx, hp.xx, hp.xx⟩
  have hsum (H : ℕ) : (∑ j ∈ range H, ‖r (j+1)‖)^2 ≤
      C^2 * (∑ j ∈ range H, ∑ k ∈ range H, c (j-k+(k-j))) := by
    let w (j : ℕ) := phaseWeight (star (r (H-j)))
    have hw (j : ℕ) : ‖w j‖ ≤ 1 := norm_phaseWeight_le _
    have ht (j : ℕ) (hj : j ∈ range H) :
        Tendsto (fun q => orbitCorr x y (j+1) (H+1) (M q)) atTop (𝓝 (star (r (H-j)))) := by
      have hle : j+1 ≤ H+1 := by have := Finset.mem_range.mp hj; omega
      have ht := (orbitCorr_tendsto_of_le hp.boundedY hp.boundedX hp.strictMono hr hle).star
      simpa only [star_orbitCorr, Nat.add_sub_add_right] using ht
    have hCcs (q : ℕ) : ‖∑ j ∈ range H, w j * orbitCorr x y (j+1) (H+1) (M q)‖ ^ 2 ≤
        C^2 * (∑ j ∈ range H, ∑ k ∈ range H, ‖orbitCorr x x (j+1) (k+1) (M q)‖) := by
      have heq : (∑ j ∈ range H, w j * orbitCorr x y (j+1) (H+1) (M q)) =
          cesaro (fun n => weightedShift x w H n * star (y (n+(H+1)))) (M q) := by
        simp only [weightedShift, Finset.sum_mul, mul_assoc, cesaro_finset_sum, cesaro_const_mul, orbitCorr]
      rw [heq]
      exact (norm_cesaro_mul_star_sq_le_right (weightedShift x w H) (fun n => y (n+(H+1)))
        hC (fun n => hy _) (M q)).trans
        (mul_le_mul_of_nonneg_left (weightedShift_energy_le x w hw H (M q)) (sq_nonneg _))
    have hlimL := (tendsto_finsetSum (range H) (fun j hj => (ht j hj).const_mul (w j))).norm.pow 2
    have heq : ‖∑ j ∈ range H, w j * star (r (H-j))‖ = ∑ j ∈ range H, ‖r (j+1)‖ := by
      simp only [w, phaseWeight_mul, norm_star, ← Complex.ofReal_sum, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg _))]
      rw [← Finset.sum_range_reflect (fun j => ‖r (j+1)‖) H]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      have := Finset.mem_range.mp hj
      omega
    rw [heq] at hlimL
    have hlimR := (tendsto_finsetSum (range H) (fun j _ => tendsto_finsetSum (range H)
      (fun k _ => tendsto_norm_orbitCorr_self hx.1 hp.strictMono hu j k))).const_mul (C^2)
    exact le_of_tendsto_of_tendsto hlimL hlimR (Eventually.of_forall hCcs)
  have hmean := hx.2 x M u hself hu
  have hupper0 := (tendsto_const_div_atTop_nhds_zero_nat (c 0)).add hmean
  have hupper : Tendsto (fun H : ℕ => C^2 * (2 * (c 0 / (H : ℝ) + realCesaro (fun k => c (k+1)) H)))
      atTop (𝓝 0) := by
    simpa only [c, add_zero, mul_zero] using (hupper0.const_mul 2).const_mul (C^2)
  have hsq : Tendsto (fun H => (realCesaro (fun h => ‖r (h+1)‖) H)^2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) ?_ hupper
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
    have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hH
    have h1 := (hsum H).trans (mul_le_mul_of_nonneg_left
      (double_toeplitz_bound c (fun _ => norm_nonneg _) H) (sq_nonneg _))
    rw [realCesaro, div_pow]
    have h2 := div_le_div_of_nonneg_right h1 (sq_nonneg (H : ℝ))
    refine h2.trans_eq ?_
    unfold realCesaro
    field_simp [hH0]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq
    (realCesaro_nonneg (fun _ => norm_nonneg _) _)] using hh

/-- The Cesàro mean of a nonnegative sequence tending to zero tends to zero. -/
theorem realCesaro_tendsto_zero_of_tendsto_zero {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hlim : Tendsto u atTop (𝓝 0)) : Tendsto (realCesaro u) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (show 0 < ε/2 by positivity)))
  let S := ∑ n ∈ range K, u n
  have hvanish : Tendsto (fun N : ℕ => S / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [eventually_ge_atTop K, eventually_gt_atTop (0 : ℕ),
    hvanish.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with N hNK hN hsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (realCesaro_nonneg hu N)]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hEq : (∑ n ∈ range N, u n) = S + ∑ n ∈ range (N-K), u (n+K) := by
    have h := Finset.sum_range_add u K (N-K)
    have hk : K + (N-K) = N := by omega
    rw [hk] at h
    simpa only [S, Nat.add_comm] using h
  have hle : ∑ n ∈ range (N-K), u (n+K) ≤ (N : ℝ) * (ε/2) := by
    calc
      _ ≤ ∑ _n ∈ range (N-K), ε/2 := by
        apply Finset.sum_le_sum
        intro n _
        have hn := hK (n+K) (by omega)
        exact hn.le
      _ = ((N-K : ℕ) : ℝ) * (ε/2) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N K) (by positivity)
  unfold realCesaro
  rw [hEq, add_div]
  have hle' := (div_le_iff₀ hNpos).mpr (show ∑ n ∈ range (N-K), u (n+K) ≤ ε/2 * N by
    simpa only [mul_comm] using hle)
  linarith only [hsmall, hle']

end VdC
