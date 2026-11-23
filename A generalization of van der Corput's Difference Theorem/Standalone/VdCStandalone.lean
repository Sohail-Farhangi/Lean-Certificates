/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.NormNum
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.Tactic.FinCases
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Data.Nat.Pairing
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Tactic.IntervalCases

/-! # A generalization of van der Corput's Difference Theorem

Consolidated proof sources for arXiv:2106.01123v6. The companion
PAPER_GUIDE.txt maps the formal statements to the paper.
-/

/- Source: VdC/Basic.lean -/
section VdC_Basic_Module

/-! # Basic -/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace VdC

def BoundedSeq (x : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖x n‖ ≤ C

noncomputable def cesaro (x : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, x n) / (N : ℂ)

noncomputable def realCesaro (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, x n) / (N : ℝ)

noncomputable def corr (x y : ℕ → ℂ) (h N : ℕ) : ℂ :=
  cesaro (fun n => x (n + h) * star (y n)) N

def CorrLimits (x y : ℕ → ℂ) (N : ℕ → ℕ) (r : ℕ → ℂ) : Prop :=
  ∀ h, Tendsto (fun q => corr x y h (N q)) atTop (𝓝 (r h))

structure PermissibleTriple (x y : ℕ → ℂ) (N : ℕ → ℕ) : Prop where
  boundedX : BoundedSeq x
  boundedY : BoundedSeq y
  strictMono : StrictMono N
  xx : ∃ r, CorrLimits x x N r
  xy : ∃ r, CorrLimits x y N r
  yx : ∃ r, CorrLimits y x N r
  yy : ∃ r, CorrLimits y y N r

def NearlyOrthogonal (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r → ∀ h, 0 < h → r h = 0

def NearlyWeakMixing (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ y N r, PermissibleTriple x y N → CorrLimits x y N r →
    Tendsto (realCesaro (fun h => ‖r (h + 1)‖)) atTop (𝓝 0)

def CompactAlong (x : ℕ → ℂ) (M : ℕ → ℕ) : Prop :=
  BoundedSeq x ∧ StrictMono M ∧ ∀ σ r, StrictMono σ → CorrLimits x x (M ∘ σ) r →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m : ℕ, ∃ k ≤ K, ∃ e : ℝ, e < ε ∧
      Tendsto (fun q => realCesaro (fun n => ‖x (n + (m + 1)) - x (n + (k + 1))‖ ^ 2)
        ((M ∘ σ) q)) atTop (𝓝 e)

def CompactSeq (x : ℕ → ℂ) : Prop := CompactAlong x id

end VdC

end

end VdC_Basic_Module

/- Source: VdC/Permissible.lean -/
section VdC_Permissible_Module

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

end

end VdC_Permissible_Module

/- Source: VdC/Orthogonal.lean -/
section VdC_Orthogonal_Module

/-! # Orthogonal -/

@[expose] public section

open Filter Finset
open scoped BigOperators ComplexConjugate Topology

namespace VdC

theorem cesaro_add (x y : ℕ → ℂ) (N : ℕ) :
    cesaro (fun n => x n + y n) N = cesaro x N + cesaro y N := by
  simp only [cesaro, sum_add_distrib, add_div]

theorem cesaro_sub (x y : ℕ → ℂ) (N : ℕ) :
    cesaro (fun n => x n - y n) N = cesaro x N - cesaro y N := by
  simp only [cesaro, sum_sub_distrib, sub_div]

theorem cesaro_mul_const (x : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    cesaro (fun n => c * x n) N = c * cesaro x N := by
  rw [cesaro, cesaro, ← Finset.mul_sum, mul_div_assoc]

theorem cesaro_const (c : ℂ) {N : ℕ} (hN : 0 < N) : cesaro (fun _ => c) N = c := by
  rw [cesaro, sum_const, card_range, nsmul_eq_mul, mul_div_cancel_left₀]
  exact_mod_cast hN.ne'

theorem cesaro_tendsto_const (c : ℂ) :
    Tendsto (cesaro fun _ => c) atTop (𝓝 c) :=
  tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun _ h => (cesaro_const c h).symm)

theorem norm_cesaro_sq_le (x : ℕ → ℂ) (N : ℕ) :
    ‖cesaro x N‖ ^ 2 ≤ realCesaro (fun n => ‖x n‖ ^ 2) N := by
  simpa only [one_mul, one_pow, ← star_cesaro, norm_star] using
    norm_cesaro_mul_star_sq_le (fun _ => 1) x zero_le_one (by simp) N

theorem re_corr_zero (x : ℕ → ℂ) (N : ℕ) :
    (corr x x 0 N).re = realCesaro (fun n => ‖x n‖ ^ 2) N := by
  simp only [corr, Nat.add_zero, Complex.star_def, Complex.mul_conj', cesaro, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re,
    realCesaro]

private theorem cesaro_shift_window (x : ℕ → ℂ) (H N : ℕ) :
    cesaro (fun n => cesaro (fun i => x (n + i)) H) N =
      cesaro (fun i => cesaro (fun n => x (n + i)) N) H := by
  simp only [cesaro, div_eq_mul_inv, ← Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm, mul_comm ((H : ℂ)⁻¹)]

private theorem corr_shift_window (x : ℕ → ℂ) (H N : ℕ) :
    let u n := cesaro (fun i => x (n + i)) H
    corr u u 0 N =
      (∑ i ∈ range H, ∑ j ∈ range H, orbitCorr x x i j N) / (H : ℂ) ^ 2 := by
  have hpoint (n : ℕ) : cesaro (fun i => x (n + i)) H * star (cesaro (fun j => x (n + j)) H) =
      (∑ i ∈ range H, ∑ j ∈ range H, x (n + i) * star (x (n + j))) / (H : ℂ) ^ 2 := by
    rw [star_cesaro, cesaro, cesaro, div_mul_div_comm, sq, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  simp only [corr, orbitCorr, Nat.add_zero, hpoint]
  simp only [cesaro, div_eq_mul_inv, ← Finset.sum_mul, mul_assoc]
  rw [mul_comm (((H : ℂ) ^ 2)⁻¹)]
  congr 1
  rw [Finset.sum_comm (s := range N)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm (s := range N)]

/-- Scalar van der Corput when every positive lag correlation vanishes. -/
theorem NearlyOrthogonal.tendsto_cesaro_zero {x : ℕ → ℂ} (hx : NearlyOrthogonal x) :
    Tendsto (cesaro x) atTop (𝓝 0) := by
  have hb : BoundedSeq (fun _ => (1 : ℂ)) := ⟨1, zero_le_one, by simp⟩
  have htest : ∀ N, corr x (fun _ => 1) 0 N = cesaro x N := by intro N; simp [corr]
  have hfun : cesaro x = corr x (fun _ => 1) 0 := funext fun N => (htest N).symm
  rw [hfun]
  apply tendsto_atTop_of_permissible_refinement hx.1 hb (M := id) strictMono_id
  intro φ hφ hp
  obtain ⟨r, hr⟩ := hp.xx
  obtain ⟨s, hs⟩ := hp.xy
  have hm : Tendsto (fun q => cesaro x (φ q)) atTop (𝓝 (s 0)) := by simpa [htest] using hs 0
  have htest' : ∀ H : ℕ, 0 < H → ‖s 0‖ ^ 2 ≤ (r 0).re / H := by
    intro H hH
    let u n := cesaro (fun i => x (n + i)) H
    have hm' : Tendsto (fun q => cesaro u (φ q)) atTop (𝓝 (s 0)) := by
      simp_rw [u, cesaro_shift_window]
      have hl := tendsto_finsetSum (range H) (fun i _ => tendsto_cesaro_shift hx.1 i hφ hm)
      have hh := hl.div_const (H : ℂ)
      simpa only [sum_const, card_range, nsmul_eq_mul, mul_div_cancel_left₀ _
        (show (H : ℂ) ≠ 0 by exact_mod_cast hH.ne'), cesaro] using hh
    have horb (i j : ℕ) : Tendsto (fun q => orbitCorr x x i j (φ q)) atTop
        (𝓝 (if i = j then r 0 else 0)) := by
      rcases lt_trichotomy i j with hij | rfl | hji
      · have h := (orbitCorr_tendsto_of_le hx.1 hx.1 hφ hr (a := j) (b := i) hij.le).star
        simpa [star_orbitCorr, hij.ne, hx.2 φ r hφ hr _ (Nat.sub_pos_of_lt hij)] using h
      · simpa using orbitCorr_tendsto_of_le hx.1 hx.1 hφ hr (a := i) (b := i) le_rfl
      · simpa [hji.ne', hx.2 φ r hφ hr _ (Nat.sub_pos_of_lt hji)] using
          orbitCorr_tendsto_of_le hx.1 hx.1 hφ hr (a := i) (b := j) hji.le
    have hh := (tendsto_finsetSum (range H) fun i _ =>
      tendsto_finsetSum (range H) fun j _ => horb i j).div_const ((H : ℂ) ^ 2)
    classical
    have hsum : (∑ i ∈ range H, ∑ j ∈ range H, if i = j then r 0 else 0) = H * r 0 := by
      calc
        _ = ∑ _ ∈ range H, r 0 := by
          apply sum_congr rfl
          intro i hi
          simp [hi]
        _ = _ := by simp [nsmul_eq_mul]
    have hcancel : ((H : ℂ) * r 0) / (H : ℂ) ^ 2 = r 0 / (H : ℂ) := by
      have : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
      field_simp
    rw [hsum, hcancel] at hh
    have hl : Tendsto (fun q => corr u u 0 (φ q)) atTop (𝓝 (r 0 / (H : ℂ))) := by
      simpa only [u, corr_shift_window] using hh
    have hr' := Complex.continuous_re.continuousAt.tendsto.comp hl
    simp only [Function.comp_def, re_corr_zero, ← Complex.ofReal_natCast, Complex.div_ofReal_re] at hr'
    exact le_of_tendsto_of_tendsto (hm'.norm.pow 2) hr' (Eventually.of_forall fun q => norm_cesaro_sq_le _ _)
  have hz : ‖s 0‖ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds (tendsto_const_div_atTop_nhds_zero_nat _) <|
    (eventually_ge_atTop 1).mono fun H hH => htest' H hH
  have hs0 : s 0 = 0 := by
    have hh : ‖s 0‖ = 0 := by nlinarith [norm_nonneg (s 0)]
    exact norm_eq_zero.mp hh
  simpa [hs0] using hs 0

end VdC

end

end VdC_Orthogonal_Module

/- Source: VdC/Distribution.lean -/
section VdC_Distribution_Module

/-! # Distribution -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped BigOperators ComplexConjugate Topology

namespace VdC

section CompactSpace

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

noncomputable def testMean (μ : Measure X) (f : C(X, ℂ)) : ℂ := ∫ x, f x ∂μ

def Equidistributed (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f))

def OrthogonalDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → NearlyOrthogonal (fun n => f (x n))

omit [MeasurableSpace X] [BorelSpace X] in
theorem bounded_test (f : C(X, ℂ)) (x : ℕ → X) : BoundedSeq (fun n => f (x n)) :=
  ⟨‖f‖, norm_nonneg _, fun n => ContinuousMap.norm_coe_le_norm f (x n)⟩

theorem test_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall fun a => ContinuousMap.norm_coe_le_norm f a)

theorem testMean_add (μ : Measure X) [IsFiniteMeasure μ] (f g : C(X, ℂ)) :
    testMean μ (f + g) = testMean μ f + testMean μ g :=
  integral_add (test_integrable μ f) (test_integrable μ g)

theorem testMean_sub (μ : Measure X) [IsFiniteMeasure μ] (f g : C(X, ℂ)) :
    testMean μ (f - g) = testMean μ f - testMean μ g :=
  integral_sub (test_integrable μ f) (test_integrable μ g)

omit [BorelSpace X] [CompactSpace X] in
theorem testMean_smul (μ : Measure X) (c : ℂ) (f : C(X, ℂ)) :
    testMean μ (c • f) = c * testMean μ f := integral_const_mul _ _

omit [BorelSpace X] [CompactSpace X] in
theorem testMean_const (μ : Measure X) [IsProbabilityMeasure μ] (c : ℂ) :
    testMean μ (ContinuousMap.const X c) = c := by simp [testMean]

omit [BorelSpace X] [CompactSpace X] in
theorem testMean_star (μ : Measure X) (f : C(X, ℂ)) :
    testMean μ (star f) = star (testMean μ f) := integral_conj

private noncomputable def testError (μ : Measure X) (x : ℕ → X) (f : C(X, ℂ)) (N : ℕ) :=
  cesaro (fun n => f (x n)) N - testMean μ f

private theorem norm_error_difference (μ : Measure X) [IsProbabilityMeasure μ] (x : ℕ → X)
    (f g : C(X, ℂ)) (N : ℕ) : ‖testError μ x f N - testError μ x g N‖ ≤ 2 * ‖f - g‖ := by
  have hf : ‖cesaro (fun n => (f - g) (x n)) N‖ ≤ ‖f - g‖ :=
    norm_cesaro_le _ (norm_nonneg _) (fun n => ContinuousMap.norm_coe_le_norm _ _) _
  have hg : ‖testMean μ (f - g)‖ ≤ ‖f - g‖ :=
    by simpa [testMean] using
      (norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall fun a => ContinuousMap.norm_coe_le_norm (f - g) a))
  have he : testError μ x f N - testError μ x g N = testError μ x (f - g) N := by
    unfold testError
    rw [testMean_sub]
    change _ = cesaro (fun n => f (x n) - g (x n)) N - _
    rw [cesaro_sub]
    abel
  rw [he, testError]
  linarith only [(norm_sub_le _ _).trans (add_le_add hf hg)]

omit [BorelSpace X] [CompactSpace X] in
private theorem tendency_testError_iff (μ : Measure X) (x : ℕ → X) (f : C(X, ℂ)) :
    Tendsto (testError μ x f) atTop (𝓝 0) ↔
    Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f)) := by
  constructor
  · intro h
    simpa [testError] using h.add (tendsto_const_nhds (x := testMean μ f))
  · intro h
    unfold testError
    simpa only [sub_self] using h.sub (tendsto_const_nhds (x := testMean μ f))

noncomputable def convergenceTests (μ : Measure X) [IsProbabilityMeasure μ] (x : ℕ → X) :
    Submodule ℂ C(X, ℂ) where
  carrier := {f | Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f))}
  zero_mem' := by
    change Tendsto (cesaro fun _ => 0) atTop (𝓝 (testMean μ (0 : C(X, ℂ))))
    simpa only [testMean, ContinuousMap.zero_apply, integral_zero] using cesaro_tendsto_const 0
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun N => cesaro (fun n => f (x n) + g (x n)) N) atTop (𝓝 (testMean μ (f + g)))
    simp only [cesaro_add, testMean_add]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (fun N => cesaro (fun n => c * f (x n)) N) atTop (𝓝 (testMean μ (c • f)))
    simp only [cesaro_mul_const, testMean_smul]
    exact tendsto_const_nhds.mul hf

theorem equidistributed_of_dense_tests (μ : Measure X) [IsProbabilityMeasure μ] (x : ℕ → X)
    (s : Set C(X, ℂ)) (hd : (Submodule.span ℂ s).topologicalClosure = ⊤)
    (hs : ∀ f ∈ s, Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f))) :
    Equidistributed μ x := by
  intro f
  apply (tendency_testError_iff μ x f).1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hf : f ∈ closure (↑(Submodule.span ℂ s) : Set C(X, ℂ)) := by
    change f ∈ (Submodule.span ℂ s).topologicalClosure
    rw [hd]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf (ε / 4) (by positivity)
  have hh : g ∈ convergenceTests μ x :=
    (Submodule.span_le.2 (fun u hu => hs u hu)) hg
  have ht := (Metric.tendsto_nhds.mp ((tendency_testError_iff μ x g).2 hh)) (ε / 2) (by positivity)
  filter_upwards [ht] with N hN
  rw [dist_zero_right] at hN ⊢
  rw [dist_eq_norm] at hdist
  have htri : ‖testError μ x f N‖ ≤ ‖testError μ x f N - testError μ x g N‖ + ‖testError μ x g N‖ := by
    simpa only [sub_add_cancel] using norm_add_le (testError μ x f N - testError μ x g N) (testError μ x g N)
  linarith only [hN, hdist, htri, norm_error_difference μ x f g N]

def productTest (f : C(X, ℂ)) (g : C(Y, ℂ)) : C(X × Y, ℂ) :=
  ⟨fun p => f p.1 * g p.2, (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
@[simp] theorem productTest_apply (f : C(X, ℂ)) (g : C(Y, ℂ)) (p : X × Y) :
    productTest f g p = f p.1 * g p.2 := rfl

private def productTests : Set C(X × Y, ℂ) := {u | ∃ f g, productTest f g = u}

private noncomputable def productAlgebra : StarSubalgebra ℂ C(X × Y, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (productTests (X := X) (Y := Y))
  star_mem' := by
    change Algebra.adjoin ℂ (productTests (X := X) (Y := Y)) ≤
      star (Algebra.adjoin ℂ (productTests (X := X) (Y := Y)))
    apply Algebra.adjoin_le
    rintro _ ⟨f, g, rfl⟩
    change star (productTest f g) ∈ Algebra.adjoin ℂ productTests
    apply Algebra.subset_adjoin
    exact ⟨star f, star g, by ext p; simp⟩

variable [T2Space X] [T2Space Y]

private theorem complex_test_separates {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    {a b : Z} (h : a ≠ b) : ∃ f : C(Z, ℂ), f a ≠ f b := by
  obtain ⟨f, ha, hb, _⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := a)) (isClosed_singleton (x := b))
    (Set.disjoint_singleton.2 h)
  refine ⟨⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩, ?_⟩
  change (f a : ℂ) ≠ (f b : ℂ)
  simp [ha (Set.mem_singleton a), hb (Set.mem_singleton b)]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
private theorem productTests_dense : (Submodule.span ℂ (productTests (X := X) (Y := Y))).topologicalClosure = ⊤ := by
  have hsep : (productAlgebra (X := X) (Y := Y)).SeparatesPoints := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    by_cases hac : a = c
    · have hbd : b ≠ d := by intro he; exact h (Prod.ext hac he)
      obtain ⟨g, hg⟩ := complex_test_separates hbd
      refine ⟨_, ⟨productTest 1 g, Algebra.subset_adjoin ⟨1, g, rfl⟩, rfl⟩, ?_⟩
      simpa using hg
    · obtain ⟨f, hf⟩ := complex_test_separates hac
      refine ⟨_, ⟨productTest f 1, Algebra.subset_adjoin ⟨f, 1, rfl⟩, rfl⟩, ?_⟩
      simpa using hf
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have had : (productAlgebra (X := X) (Y := Y)).toSubalgebra.toSubmodule = Submodule.span ℂ productTests := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans ?_ Submodule.subset_span
    intro x hx
    refine Submonoid.closure_induction (fun _ h => h) ⟨1, 1, ?_⟩ ?_ hx
    · ext p; simp
    · rintro _ _ - - ⟨f, g, rfl⟩ ⟨f', g', rfl⟩
      exact ⟨f * f', g * g', by ext p; simp; ring⟩
  rw [← had]
  exact congrArg (fun A : StarSubalgebra ℂ C(X × Y, ℂ) => A.toSubalgebra.toSubmodule) hd

theorem equidistributed_prod_iff [SecondCountableTopology X] [SecondCountableTopology Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : ℕ → X) (y : ℕ → Y) :
    Equidistributed (μ.prod ν) (fun n => (x n, y n)) ↔ ∀ (f : C(X, ℂ)) (g : C(Y, ℂ)),
      Tendsto (cesaro fun n => f (x n) * g (y n)) atTop (𝓝 (testMean μ f * testMean ν g)) := by
  have hp (f : C(X, ℂ)) (g : C(Y, ℂ)) :
      testMean (μ.prod ν) (productTest f g) = testMean μ f * testMean ν g := integral_prod_mul _ _
  constructor
  · intro h f g
    simpa only [hp, productTest_apply] using h (productTest f g)
  · intro h
    apply equidistributed_of_dense_tests _ _ productTests productTests_dense
    rintro _ ⟨f, g, rfl⟩
    simpa only [hp, productTest_apply] using h f g

end CompactSpace

end VdC

end

end VdC_Distribution_Module

/- Source: VdC/LagPairs.lean -/
section VdC_LagPairs_Module

/-! # Lag Pairs -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace VdC

/-- The two polarization identities are valid even when the lagged correlation
form fails to be Hermitian. -/
theorem corr_polarization (u v : ℕ → ℂ) (h N : ℕ) :
    let a n := u n + v n
    let b n := u n + Complex.I * v n
    corr u v h N = ((corr a a h N - corr u u h N - corr v v h N) +
      Complex.I * (corr b b h N - corr u u h N - corr v v h N)) / 2 := by
  have h₁ : ∀ n, (u (n + h) + v (n + h)) * star (u n + v n) =
      u (n + h) * star (u n) + v (n + h) * star (v n) +
        (u (n + h) * star (v n) + v (n + h) * star (u n)) := by
    intro n
    simp only [star_add]
    ring
  have h₂ : ∀ n, (u (n + h) + Complex.I * v (n + h)) * star (u n + Complex.I * v n) =
      u (n + h) * star (u n) + v (n + h) * star (v n) +
        ((-Complex.I) * (u (n + h) * star (v n)) + Complex.I * (v (n + h) * star (u n))) := by
    intro n
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I]
    linear_combination -(v (n + h) * conj (v n)) * Complex.I_sq
  dsimp only
  simp only [corr, h₁, h₂, cesaro_add, cesaro_mul_const]
  linear_combination (cesaro (fun n => u (n + h) * star (v n)) N -
    cesaro (fun n => v (n + h) * star (u n)) N) / 2 * Complex.I_sq

section CompactSpace

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def center (f : C(X, ℂ)) : C(X, ℂ) := f - ContinuousMap.const X (testMean μ f)

@[simp] theorem testMean_center (f : C(X, ℂ)) : testMean μ (center μ f) = 0 := by
  rw [center, testMean_sub, testMean_const, sub_self]

theorem equidistributed_of_centered_tests (x : ℕ → X)
    (h : ∀ f : C(X, ℂ), testMean μ f = 0 →
      Tendsto (cesaro fun n => f (x n)) atTop (𝓝 0)) : Equidistributed μ x := by
  intro f
  have hh := (h (center μ f) (testMean_center μ f)).add (cesaro_tendsto_const (testMean μ f))
  simp only [zero_add] at hh
  convert hh using 1
  ext1 N
  rw [← cesaro_add]
  congr 1
  ext1 n
  simp [center]

theorem OrthogonalDistribution.equidistributed {x : ℕ → X} (hx : OrthogonalDistribution μ x) :
    Equidistributed μ x :=
  equidistributed_of_centered_tests μ x fun f hf => (hx f hf).tendsto_cesaro_zero

theorem OrthogonalDistribution.mixed_corr_zero {x : ℕ → X} (hx : OrthogonalDistribution μ x)
    (f g : C(X, ℂ)) (hf : testMean μ f = 0) (hg : testMean μ g = 0) {h : ℕ} (hh : 0 < h) :
    Tendsto (corr (fun n => f (x n)) (fun n => g (x n)) h) atTop (𝓝 0) := by
  have hf' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test f x)).1 (hx f hf) h hh
  have hg' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test g x)).1 (hx g hg) h hh
  have h₁ : testMean μ (f + g) = 0 := by simp [testMean_add, hf, hg]
  have h₂ : testMean μ (f + Complex.I • g) = 0 := by simp [testMean_add, testMean_smul, hf, hg]
  have h₁' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test (f + g) x)).1 (hx _ h₁) h hh
  have h₂' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test (f + Complex.I • g) x)).1 (hx _ h₂) h hh
  have hl := (((h₁'.sub hf').sub hg').add
    (((h₂'.sub hf').sub hg').const_mul Complex.I)).div_const (2 : ℂ)
  simp only [sub_zero, mul_zero, add_zero, zero_div] at hl
  exact hl.congr fun N => (corr_polarization (fun n => f (x n)) (fun n => g (x n)) h N).symm

theorem product_means_of_centered_tests (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (σ : Measure Y) [IsProbabilityMeasure σ] (x : ℕ → X) (y : ℕ → Y)
    (hx : Equidistributed ν x) (hy : Equidistributed σ y)
    (h : ∀ (f : C(X, ℂ)) (g : C(Y, ℂ)), testMean ν f = 0 → testMean σ g = 0 →
      Tendsto (cesaro fun n => f (x n) * g (y n)) atTop (𝓝 0))
    (f : C(X, ℂ)) (g : C(Y, ℂ)) :
    Tendsto (cesaro fun n => f (x n) * g (y n)) atTop (𝓝 (testMean ν f * testMean σ g)) := by
  let a := testMean ν f
  let b := testMean σ g
  have h₀ := h (center ν f) (center σ g) (testMean_center ν f) (testMean_center σ g)
  have h₁ := (tendsto_const_nhds (x := b)).mul (hx (center ν f))
  have h₂ := (tendsto_const_nhds (x := a)).mul (hy (center σ g))
  have hsum := (((h₀.add h₁).add h₂).add (cesaro_tendsto_const (a * b)))
  simp only [testMean_center, mul_zero, add_zero, zero_add] at hsum
  refine hsum.congr fun N => ?_
  rw [← cesaro_mul_const, ← cesaro_mul_const, ← cesaro_add, ← cesaro_add, ← cesaro_add]
  congr 1
  ext1 n
  simp only [center, ContinuousMap.sub_apply, ContinuousMap.const_apply, a, b]
  ring

/-- CharacterizationOfOsequences, with an arbitrary compact probability space
in place of the cube and uniform distribution tested by continuous functions. -/
theorem orthogonalDistribution_iff_lag_pairs [T2Space X] [SecondCountableTopology X]
    (x : ℕ → X) : OrthogonalDistribution μ x ↔ ∀ h : ℕ, 0 < h →
      Equidistributed (μ.prod μ) (fun n => (x n, x (n + h))) := by
  constructor
  · intro hx h hh
    apply (equidistributed_prod_iff μ μ _ _).2
    have hs : Equidistributed μ (fun n => x (n + h)) := fun f =>
      tendsto_cesaro_shift (bounded_test f x) h strictMono_id (hx.equidistributed μ f)
    apply product_means_of_centered_tests μ μ x _ (hx.equidistributed μ) hs
    intro f g hf hg
    refine (hx.mixed_corr_zero μ g (star f) hg (by simp [testMean_star, hf]) hh).congr ?_
    intro N
    simp [corr, mul_comm]
  · intro hx f hf
    apply (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test f x)).2
    intro h hh
    have hl := (equidistributed_prod_iff μ μ _ _).1 (hx h hh) (star f) f
    have hl' : Tendsto (cesaro fun n => star (f (x n)) * f (x (n + h))) atTop (𝓝 0) := by
      simpa [testMean_star, hf] using hl
    exact hl'.congr fun N => by simp [corr, mul_comm]

end CompactSpace

end VdC

end

end VdC_LagPairs_Module

/- Source: VdC/Selection.lean -/
section VdC_Selection_Module

/-! # Selection -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

noncomputable def selectionWeight (A : Set ℕ) (n : ℕ) : ℂ := A.indicator (fun _ => 1) n

noncomputable def initialCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter (· ∈ A)).card

/-- An eventual positive lower bound for the initial-segment densities. -/
def HasPositiveLowerDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ (N : ℕ) in atTop, δ * (N : ℝ) ≤ initialCount A N

noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (initialCount A N : ℝ) / (N : ℝ)) atTop

theorem hasPositiveLowerDensity_iff (A : Set ℕ) : HasPositiveLowerDensity A ↔ 0 < lowerDensity A := by
  have hnonneg (N : ℕ) : 0 ≤ (initialCount A N : ℝ) / (N : ℝ) := by positivity
  have hupper (N : ℕ) : (initialCount A N : ℝ) / (N : ℝ) ≤ 1 := by
    by_cases hN : 0 < N
    · have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
      rw [div_le_iff₀ hNr, one_mul]
      classical
      exact_mod_cast (card_filter_le _ _).trans_eq (card_range N)
    · simp [Nat.eq_zero_of_not_pos hN]
  constructor
  · rintro ⟨δ, hδ, hd⟩
    refine hδ.trans_le (le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hupper) ?_)
    filter_upwards [hd, eventually_gt_atTop (0 : ℕ)] with N hD hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    exact (le_div_iff₀ hNr).2 hD
  · intro h
    obtain ⟨δ, hδ, hδ'⟩ := exists_between h
    refine ⟨δ, hδ, ?_⟩
    have hh := eventually_lt_of_lt_liminf hδ' (isBoundedUnder_of ⟨0, hnonneg⟩)
    filter_upwards [hh, eventually_gt_atTop (0 : ℕ)] with N hD hN
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    exact (lt_div_iff₀ hNr).1 hD |>.le

private theorem range_filter_eq_map (σ : ℕ → ℕ) (hσ : StrictMono σ) (K : ℕ) :
    letI := Classical.decPred (· ∈ Set.range σ)
    (range (σ K + 1)).filter (· ∈ Set.range σ) = (range (K + 1)).map ⟨σ, hσ.injective⟩ := by
  classical
  ext n
  simp only [mem_filter, mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hn, k, rfl⟩
    exact ⟨k, Nat.lt_succ_of_le (hσ.le_iff_le.mp (Nat.le_of_lt_succ hn)), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Nat.lt_succ_of_le (hσ.monotone (Nat.le_of_lt_succ hk)), ⟨k, rfl⟩⟩

theorem initialCount_at_selection {σ : ℕ → ℕ} (hσ : StrictMono σ) (K : ℕ) :
    initialCount (Set.range σ) (σ K + 1) = K + 1 := by
  classical
  rw [initialCount, range_filter_eq_map σ hσ K, card_map, card_range]

private theorem selection_sum (u : ℕ → ℂ) {σ : ℕ → ℕ} (hσ : StrictMono σ) (K : ℕ) :
    ∑ n ∈ range (σ K + 1), u n * selectionWeight (Set.range σ) n =
      ∑ k ∈ range (K + 1), u (σ k) := by
  classical
  calc
    _ = ∑ n ∈ (range (σ K + 1)).filter (· ∈ Set.range σ), u n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n ∈ Set.range σ <;> simp [selectionWeight, hn]
    _ = _ := by rw [range_filter_eq_map σ hσ K, Finset.sum_map]; rfl

theorem tendsto_cesaro_selected_zero (u : ℕ → ℂ) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hd : HasPositiveLowerDensity (Set.range σ))
    (h : Tendsto (cesaro fun n => u n * selectionWeight (Set.range σ) n) atTop (𝓝 0)) :
    Tendsto (cesaro fun k => u (σ k)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hden⟩ := hd
  have hσ' : Tendsto (fun K => σ K + 1) atTop atTop :=
    (show StrictMono (fun K => σ K + 1) from fun _ _ h => Nat.add_lt_add_right (hσ h) _).tendsto_atTop
  have hb : ∀ᶠ K in atTop, δ * ((σ K + 1 : ℕ) : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    simpa only [initialCount_at_selection hσ] using hσ'.eventually hden
  have hn := (h.comp hσ').norm
  have hbound : ∀ᶠ K in atTop,
      ‖cesaro (fun k => u (σ k)) (K + 1)‖ ≤
        δ⁻¹ * ‖cesaro (fun n => u n * selectionWeight (Set.range σ) n) (σ K + 1)‖ := by
    filter_upwards [hb] with K hK
    simp only [cesaro, selection_sum u hσ, norm_div, Complex.norm_natCast]
    have hratio : ((σ K + 1 : ℕ) : ℝ) ≤ δ⁻¹ * ((K + 1 : ℕ) : ℝ) := by
      rwa [inv_mul_eq_div, le_div_iff₀ hδ, mul_comm]
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hratio (norm_nonneg (∑ k ∈ range (K + 1), u (σ k)))
  have ht := squeeze_zero' (Eventually.of_forall fun K => norm_nonneg (cesaro (fun k => u (σ k)) (K + 1)))
    hbound (by simpa using tendsto_const_nhds.mul hn (a := δ⁻¹))
  exact (tendsto_add_atTop_iff_nat 1).1 (tendsto_zero_iff_norm_tendsto_zero.mpr ht)

end VdC

end

end VdC_Selection_Module

/- Source: VdC/Spectrum.lean -/
section VdC_Spectrum_Module

/-! # Spectral measures on the circle -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Haar probability measure on the unit circle. -/
def circleHaar : Measure UnitAddCircle := AddCircle.haarAddCircle

instance circleHaar_probability : IsProbabilityMeasure circleHaar := by
  unfold circleHaar
  infer_instance

/-- Fourier coefficient, with the manuscript's sign convention. -/
def measureFourier (μ : Measure UnitAddCircle) (n : ℤ) : ℂ :=
  ∫ x, fourier (-n) x ∂μ

/-- Realization of the nonnegative-lag correlation sequence by a positive finite measure. -/
def HasSpectrum (r : ℕ → ℂ) (μ : FiniteMeasure UnitAddCircle) : Prop :=
  ∀ h : ℕ, measureFourier μ (h : ℤ) = r h

theorem measureFourier_neg (μ : Measure UnitAddCircle) (n : ℤ) :
    measureFourier μ (-n) = conj (measureFourier μ n) := by
  simp only [measureFourier, ← integral_conj, ← fourier_neg, neg_neg]

theorem measureFourier_zero (μ : Measure UnitAddCircle) :
    measureFourier μ 0 = (μ.real Set.univ : ℂ) := by
  simp only [measureFourier, neg_zero, fourier_zero, integral_const, Complex.real_smul,
    mul_one]

theorem measureFourier_dirac_zero (n : ℤ) :
    measureFourier (Measure.dirac (0 : UnitAddCircle)) n = 1 := by
  rw [measureFourier, integral_dirac, fourier_eval_zero]

theorem measureFourier_add (μ ν : Measure UnitAddCircle) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (n : ℤ) :
    measureFourier (μ + ν) n = measureFourier μ n + measureFourier ν n := by
  have hint (ρ : Measure UnitAddCircle) [IsFiniteMeasure ρ] :
      Integrable (fourier (T := 1) (-n)) ρ :=
    (fourier (-n)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_add_measure (hint μ) (hint ν)

theorem measureFourier_smul (μ : Measure UnitAddCircle) (c : ℝ≥0∞) (n : ℤ) :
    measureFourier (c • μ) n = (c.toReal : ℂ) * measureFourier μ n := by
  rw [measureFourier, integral_smul_measure]
  rfl

private def integrationFunctional (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] :
    C(UnitAddCircle, ℂ) →L[ℂ] ℂ := by
  have hint (f : C(UnitAddCircle, ℂ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let I : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := fun f g => integral_add (hint f) (hint g)
      map_smul' := fun a f => integral_smul a f }
  exact I.mkContinuous (μ.real Set.univ) fun f => by
    change ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖
    simpa [mul_comm] using norm_integral_le_of_norm_le_const
      (ae_of_all (μ := μ) fun x => f.norm_coe_le_norm x)

private theorem integrationFunctional_apply (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (f : C(UnitAddCircle, ℂ)) :
    integrationFunctional μ f = ∫ x, f x ∂μ := rfl

/-- A positive finite circle measure is determined by its Fourier coefficients. -/
theorem measure_eq_of_fourier {μ ν : Measure UnitAddCircle} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a, measureFourier μ a = measureFourier ν a) : μ = ν := by
  let Δ := integrationFunctional μ - integrationFunctional ν
  let K := LinearMap.ker Δ.toLinearMap
  have hK : IsClosed (K : Set C(UnitAddCircle, ℂ)) := isClosed_eq Δ.continuous continuous_const
  have he : Submodule.span ℂ (Set.range (@fourier 1)) ≤ K := by
    apply Submodule.span_le.2
    rintro f ⟨a, rfl⟩
    change integrationFunctional μ (fourier a) - integrationFunctional ν (fourier a) = 0
    rw [sub_eq_zero, integrationFunctional_apply, integrationFunctional_apply]
    simpa [measureFourier] using h (-a)
  have htop := (Submodule.span ℂ (Set.range (@fourier 1))).topologicalClosure_minimal he hK
  rw [span_fourier_closure_eq_top] at htop
  have hh (f : C(UnitAddCircle, ℂ)) : integrationFunctional μ f = integrationFunctional ν f := by
    have hk : f ∈ K := htop (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ C(UnitAddCircle, ℂ)))
    change integrationFunctional μ f - integrationFunctional ν f = 0 at hk
    exact sub_eq_zero.mp hk
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : C(UnitAddCircle, ℂ) := ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hEq := hh g
  simp only [integrationFunctional_apply, g, ContinuousMap.coe_mk] at hEq
  exact Complex.ofReal_injective (by simpa only [integral_complex_ofReal] using hEq)

/-- Nonnegative-lag Fourier data already determine a positive finite measure. -/
theorem measure_eq_of_fourier_nat {μ ν : Measure UnitAddCircle} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ a : ℕ, measureFourier μ (a : ℤ) = measureFourier ν (a : ℤ)) : μ = ν := by
  apply measure_eq_of_fourier
  intro n
  cases n with
  | ofNat a => exact h a
  | negSucc a =>
    change measureFourier μ (-((a + 1 : ℕ) : ℤ)) = measureFourier ν (-((a + 1 : ℕ) : ℤ))
    rw [measureFourier_neg, measureFourier_neg, h]

end

end VdC

end

end VdC_Spectrum_Module

/- Source: VdC/Torus.lean -/
section VdC_Torus_Module

/-! # Torus -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev Torus (d : ℕ) := Fin d → UnitAddCircle

def torusHaar (d : ℕ) : Measure (Torus d) := Measure.pi fun _ => circleHaar

instance torusHaar_probability (d : ℕ) : IsProbabilityMeasure (torusHaar d) := by
  unfold torusHaar
  infer_instance

def torusCharacter {d : ℕ} (m : Fin d → ℤ) : C(Torus d, ℂ) :=
  ⟨fun x => ∏ i, fourier (m i) (x i), continuous_finsetProd _ fun i _ =>
    (fourier (m i)).continuous.comp (continuous_apply i)⟩

@[simp] theorem torusCharacter_apply {d : ℕ} (m : Fin d → ℤ) (x : Torus d) :
    torusCharacter m x = ∏ i, fourier (m i) (x i) := rfl

@[simp] theorem torusCharacter_zero (d : ℕ) : torusCharacter (0 : Fin d → ℤ) = 1 := by
  ext x
  simp

theorem torusCharacter_mul {d : ℕ} (m k : Fin d → ℤ) :
    torusCharacter (m + k) = torusCharacter m * torusCharacter k := by
  ext x
  simp only [torusCharacter_apply, Pi.add_apply, fourier_add, Finset.prod_mul_distrib, ContinuousMap.mul_apply]

theorem torusCharacter_neg {d : ℕ} (m : Fin d → ℤ) :
    torusCharacter (-m) = star (torusCharacter m) := by
  ext x
  simp only [torusCharacter_apply, Pi.neg_apply, fourier_neg, ContinuousMap.star_apply, Complex.star_def, map_prod]

theorem torusCharacter_norm {d : ℕ} (m : Fin d → ℤ) (x : Torus d) :
    ‖torusCharacter m x‖ = 1 := by
  simp [fourier_apply]

theorem torusCharacter_point_add {d : ℕ} (m : Fin d → ℤ) (x y : Torus d) :
    torusCharacter m (x + y) = torusCharacter m x * torusCharacter m y := by
  simp [fourier_apply, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem torusCharacter_point_sub {d : ℕ} (m : Fin d → ℤ) (x y : Torus d) :
    torusCharacter m (x - y) = torusCharacter m x * star (torusCharacter m y) := by
  rw [sub_eq_add_neg, torusCharacter_point_add]
  congr 1
  simp only [torusCharacter_apply, Pi.neg_apply, fourier_apply, zsmul_neg, fourier_neg',
    Complex.star_def, map_prod]

private def torusCharacterAlgebra (d : ℕ) : StarSubalgebra ℂ C(Torus d, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (torusCharacter (d := d)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (torusCharacter (d := d))) ≤ star (Algebra.adjoin ℂ _)
    apply Algebra.adjoin_le
    rintro _ ⟨m, rfl⟩
    exact Algebra.subset_adjoin ⟨-m, torusCharacter_neg m⟩

theorem torusCharacter_single {d : ℕ} (i : Fin d) (u : Torus d) :
    torusCharacter (Pi.single i (1 : ℤ)) u = fourier 1 (u i) := by
  classical
  rw [torusCharacter_apply, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem torusCharacters_dense (d : ℕ) :
    (Submodule.span ℂ (Set.range (torusCharacter (d := d)))).topologicalClosure = ⊤ := by
  have hsep : (torusCharacterAlgebra d).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by contrapose! hxy; exact funext hxy
    refine ⟨_, ⟨torusCharacter (Pi.single i 1), Algebra.subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
    change torusCharacter (Pi.single i 1) x ≠ torusCharacter (Pi.single i 1) y
    rw [torusCharacter_single, torusCharacter_single, fourier_one, fourier_one]
    exact fun h => hi (AddCircle.injective_toCircle one_ne_zero (Subtype.coe_injective h))
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have had : (torusCharacterAlgebra d).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (torusCharacter (d := d))) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans ?_ Submodule.subset_span
    intro u hu
    refine Submonoid.closure_induction (fun _ => id) ⟨0, torusCharacter_zero d⟩ ?_ hu
    rintro _ _ - - ⟨m, rfl⟩ ⟨k, rfl⟩
    exact ⟨m + k, torusCharacter_mul m k⟩
  rw [← had]
  exact congrArg (fun A : StarSubalgebra ℂ C(Torus d, ℂ) => A.toSubalgebra.toSubmodule) hd

theorem testMean_circle_character (m : ℤ) :
    testMean circleHaar (fourier (T := 1) m) = if m = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) m) 0
  simpa [testMean, circleHaar, fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

theorem testMean_torusCharacter {d : ℕ} (m : Fin d → ℤ) :
    testMean (torusHaar d) (torusCharacter m) = if m = 0 then 1 else 0 := by
  classical
  simp only [testMean, torusHaar, torusCharacter_apply, integral_fintype_prod_eq_prod]
  change (∏ i, testMean circleHaar (fourier (m i))) = _
  by_cases hm : m = 0
  · subst m
    simp [testMean_circle_character]
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by contrapose! hm; exact funext hm
    rw [ite_eq_right hm]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [testMean_circle_character, hi])

/-- Weyl's criterion on the d-dimensional torus. -/
theorem equidistributed_torus_iff {d : ℕ} (x : ℕ → Torus d) :
    Equidistributed (torusHaar d) x ↔
      ∀ m : Fin d → ℤ, m ≠ 0 → Tendsto (cesaro fun n => torusCharacter m (x n)) atTop (𝓝 0) := by
  constructor
  · intro h m hm
    simpa only [testMean_torusCharacter, ite_eq_right hm] using h (torusCharacter m)
  · intro h
    apply equidistributed_of_dense_tests _ _ _ (torusCharacters_dense d)
    rintro _ ⟨m, rfl⟩
    by_cases hm : m = 0
    · subst m
      rw [testMean_torusCharacter, ite_eq_left rfl, torusCharacter_zero]
      exact cesaro_tendsto_const 1
    · simpa only [testMean_torusCharacter, ite_eq_right hm] using h m hm

end
end VdC

end

end VdC_Torus_Module

/- Source: VdC/Periodogram.lean -/
section VdC_Periodogram_Module

/-! The finite Fourier measures of bounded complex sequences. -/

@[expose] public section

namespace VdC

open Filter Finset MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal NNReal Topology

noncomputable section

abbrev periodogramHaar : Measure UnitAddCircle := AddCircle.haarAddCircle

def windowPolynomial (u : ℕ → ℂ) (N : ℕ) : C(UnitAddCircle, ℂ) :=
  ∑ i ∈ range N, u i • _root_.fourier (i : ℤ)

private theorem windowPolynomial_apply (u : ℕ → ℂ) (N : ℕ) (t : UnitAddCircle) :
    windowPolynomial u N t = ∑ i ∈ range N, u i * _root_.fourier (i : ℤ) t := by
  simp [windowPolynomial, ContinuousMap.sum_apply, smul_eq_mul]

def windowDensity (u : ℕ → ℂ) (N : ℕ) (t : UnitAddCircle) : ℝ :=
  ‖windowPolynomial u N t‖ ^ 2 / (N : ℝ)

theorem windowDensity_nonneg (u : ℕ → ℂ) (N : ℕ) (t : UnitAddCircle) :
    0 ≤ windowDensity u N t := by unfold windowDensity; positivity

private theorem continuous_windowDensity (u : ℕ → ℂ) (N : ℕ) :
    Continuous (windowDensity u N) := by
  unfold windowDensity
  exact ((windowPolynomial u N).continuous.norm.pow 2).div_const _

theorem integral_density (u : ℕ → ℂ) (N : ℕ) : Integrable (windowDensity u N) periodogramHaar :=
  (continuous_windowDensity u N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The positive finite measure of density `|∑_{j<N} u_j e(jt)|²/N`. -/
def periodogram (u : ℕ → ℂ) (N : ℕ) : FiniteMeasure UnitAddCircle := by
  let f := windowDensity u N
  refine ⟨periodogramHaar.withDensity (fun x ↦ ENNReal.ofReal (f x)), ⟨?_⟩⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integral_density u N)
      (ae_of_all _ fun x ↦ windowDensity_nonneg u N x)]
  exact ENNReal.ofReal_lt_top

private theorem density_expand (u : ℕ → ℂ) (N : ℕ) :
    (fun t : UnitAddCircle ↦ (windowDensity u N t : ℂ)) =
      ∑ i ∈ range N, ∑ j ∈ range N, fun t : UnitAddCircle ↦
        (u i * conj (u j) / (N : ℂ)) * _root_.fourier ((i : ℤ) - (j : ℤ)) t := by
  funext t
  simp only [windowDensity, Complex.ofReal_div, Complex.ofReal_natCast, ← Complex.normSq_eq_norm_sq,
    ← Complex.mul_conj,
    windowPolynomial_apply, Finset.sum_apply, map_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, ← fourier_neg, sub_eq_add_neg, fourier_add]
  ring

private theorem periodogram_fourier_eq_double_sum (u : ℕ → ℂ) (N : ℕ) (h : ℤ) :
    (∫ t, _root_.fourier (-h) t ∂((periodogram u N : FiniteMeasure UnitAddCircle) : Measure UnitAddCircle)) =
    ∑ i ∈ range N, ∑ j ∈ range N, if (i : ℤ) - (j : ℤ) = h then u i * conj (u j) / (N : ℂ) else 0 := by
  let f := windowDensity u N
  have hm : Measurable fun x ↦ (f x).toNNReal :=
    (continuous_real_toNNReal.comp (continuous_windowDensity u N)).measurable
  have hfourier : (∫ t, _root_.fourier (-h) t ∂((periodogram u N : FiniteMeasure UnitAddCircle) : Measure UnitAddCircle)) =
      fourierCoeff (fun t : UnitAddCircle ↦ (windowDensity u N t : ℂ)) h := by
    change (∫ t, _root_.fourier (-h) t ∂periodogramHaar.withDensity (fun x ↦ ENNReal.ofReal (f x))) = _
    rw [show (fun x ↦ ENNReal.ofReal (f x)) = fun x ↦ (Real.toNNReal (f x) : ℝ≥0∞) by rfl,
      integral_withDensity_eq_integral_smul hm (fun x ↦ _root_.fourier (-h) x)]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      change ((↑(Real.toNNReal (f x)) : ℝ) : ℂ) * _root_.fourier (-h) x =
        _root_.fourier (-h) x * (f x : ℂ)
      rw [Real.coe_toNNReal _ (windowDensity_nonneg u N x), mul_comm]
  rw [hfourier, density_expand]
  let term (i j : ℕ) (t : UnitAddCircle) :=
    (u i * conj (u j) / (N : ℂ)) * _root_.fourier ((i : ℤ) - (j : ℤ)) t
  have hint (i j : ℕ) : Integrable (term i j) periodogramHaar :=
    (continuous_const.mul (_root_.fourier ((i : ℤ) - (j : ℤ))).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change fourierCoeff (∑ i ∈ range N, ∑ j ∈ range N, term i j) h = _
  rw [fourierCoeff.sum _ _ (fun i _ ↦ integrable_finsetSum' _ (fun j _ ↦ hint i j)), Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fourierCoeff.sum _ _ (fun j _ ↦ hint i j), Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [term]
  rw [fourierCoeff.const_mul, fourierCoeff_fourier]
  by_cases hij : (i : ℤ) - (j : ℤ) = h
  · rw [ite_eq_left hij, hij, Pi.single_eq_same, mul_one]
  · rw [ite_eq_right hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero]

/-- The Fourier coefficients of the finite periodogram are the truncated correlations. -/
theorem periodogram_fourier (u : ℕ → ℂ) (N h : ℕ) :
    (∫ t, _root_.fourier (-(h : ℤ)) t ∂((periodogram u N : FiniteMeasure UnitAddCircle) : Measure UnitAddCircle)) =
      (∑ j ∈ range (N - h), u (j + h) * conj (u j)) / (N : ℂ) := by
  rw [periodogram_fourier_eq_double_sum, Finset.sum_comm]
  have innerSum (j : ℕ) :
      (∑ i ∈ range N, if (i : ℤ) - (j : ℤ) = (h : ℤ) then u i * conj (u j) / (N : ℂ) else 0) =
        if j + h ∈ range N then u (j + h) * conj (u j) / (N : ℂ) else 0 := by
    simp only [show ∀ i : ℕ, (i : ℤ) - (j : ℤ) = (h : ℤ) ↔ i = j + h by intro i; omega]
    exact Finset.sum_ite_eq' _ _ _
  simp_rw [innerSum, ← Finset.sum_filter]
  have heq : (range N).filter (fun j ↦ j + h ∈ range N) = range (N - h) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [heq, Finset.sum_div]

theorem periodogram_mass_le (u : ℕ → ℂ) (N : ℕ) (C : ℝ≥0)
    (hC : ∀ k, ‖u k‖ ≤ C) : (periodogram u N).mass ≤ C ^ 2 := by
  have hzero := periodogram_fourier u N 0
  simp only [Nat.cast_zero, neg_zero, fourier_zero, integral_const, Complex.real_smul,
    mul_one, FiniteMeasure.measureReal_eq_coe_coeFn, Nat.sub_zero, add_zero] at hzero
  change (((periodogram u N).mass : ℝ) : ℂ) =
      (∑ j ∈ range N, u j * conj (u j)) / (N : ℂ) at hzero
  have he : ((periodogram u N).mass : ℝ) =
      ‖(∑ j ∈ range N, u j * conj (u j)) / (N : ℂ)‖ := by
    rw [← hzero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change ((periodogram u N).mass : ℝ) ≤ ((C ^ 2 : ℝ≥0) : ℝ)
  rw [he, NNReal.coe_pow, norm_div, Complex.norm_natCast]
  by_cases hN : N = 0
  · simp [hN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [div_le_iff₀ hN', mul_comm]
  calc
    _ ≤ ∑ j ∈ range N, ‖u j * conj (u j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range N, (C : ℝ) ^ 2 := Finset.sum_le_sum fun j _ ↦ by
      rw [norm_mul, Complex.norm_conj, sq]
      exact mul_le_mul (hC j) (hC j) (norm_nonneg _) C.coe_nonneg
    _ = _ := by simp

/-- Removing the last `h` terms changes a normalized bounded average by at most `h C / N`. -/
theorem norm_truncated_average_sub (u : ℕ → ℂ) (N h : ℕ) (C : ℝ)
    (hC₀ : 0 ≤ C) (hC : ∀ k, ‖u k‖ ≤ C) :
    ‖(∑ k ∈ range (N - h), u k) / (N : ℂ) - (∑ k ∈ range N, u k) / (N : ℂ)‖ ≤
      (h : ℝ) * C / (N : ℝ) := by
  rw [← sub_div, norm_div, Complex.norm_natCast, norm_sub_rev,
    ← Finset.sum_Ico_eq_sub _ (Nat.sub_le N h)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ k ∈ Ico (N - h) N, ‖u k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Ico (N - h) N, C := Finset.sum_le_sum fun k _ ↦ hC k
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show N - (N - h) ≤ h by omega)) hC₀

/-- Integration of a continuous complex function depends continuously on a finite measure. -/
theorem continuous_finiteMeasure_integral (g : C(UnitAddCircle, ℂ)) :
    Continuous fun μ : FiniteMeasure UnitAddCircle ↦ ∫ x, g x ∂(μ : Measure UnitAddCircle) := by
  let gr : C(UnitAddCircle, ℝ) := ⟨fun x ↦ (g x).re, Complex.continuous_re.comp g.continuous⟩
  let gi : C(UnitAddCircle, ℝ) := ⟨fun x ↦ (g x).im, Complex.continuous_im.comp g.continuous⟩
  have hr := FiniteMeasure.continuous_integral_continuousMap gr
  have hi := FiniteMeasure.continuous_integral_continuousMap gi
  have h : (fun μ : FiniteMeasure UnitAddCircle ↦ ∫ x, g x ∂(μ : Measure UnitAddCircle)) =
    fun μ : FiniteMeasure UnitAddCircle ↦
      Complex.ofReal (∫ x, gr x ∂(μ : Measure UnitAddCircle)) +
        Complex.ofReal (∫ x, gi x ∂(μ : Measure UnitAddCircle)) * Complex.I := by
    funext μ
    have hg : Integrable g (μ : Measure UnitAddCircle) :=
      g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    apply Complex.ext
    · simpa [Complex.add_re, Complex.mul_re, gr] using (integral_re (𝕜 := ℂ) hg).symm
    · simpa [Complex.add_im, Complex.mul_im, gi] using (integral_im (𝕜 := ℂ) hg).symm
  rw [h]
  exact (Complex.continuous_ofReal.comp hr).add ((Complex.continuous_ofReal.comp hi).mul continuous_const)

end

end VdC

end

end VdC_Periodogram_Module

/- Source: VdC/Realization.lean -/
section VdC_Realization_Module

/-! Positive spectral measures for permissible correlations. The finite
periodograms are compact in the weak topology at bounded mass. -/

@[expose] public section

open Filter Finset Function MeasureTheory Set
open scoped BigOperators ComplexConjugate NNReal Topology

namespace VdC

noncomputable section

theorem tendsto_periodogram_fourier {u : ℕ → ℂ} {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hu : BoundedSeq u) (hN : StrictMono N) (hr : CorrLimits u u N r) (h : ℕ) :
    Tendsto (fun q : ℕ ↦ measureFourier (periodogram u (N q)) (h : ℤ)) atTop (𝓝 (r h)) := by
  obtain ⟨C, hC₀, hC⟩ := hu
  have hbounded (k : ℕ) : ‖u (k + h) * conj (u k)‖ ≤ C * C := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC₀
  have hdiff (q : ℕ) :
      ‖measureFourier (periodogram u (N q)) (h : ℤ) - corr u u h (N q)‖ ≤
        (h : ℝ) * (C * C) / (N q : ℝ) := by
    rw [measureFourier, periodogram_fourier]
    exact norm_truncated_average_sub _ _ _ _ (mul_nonneg hC₀ hC₀) hbounded
  have hbound : Tendsto (fun q ↦ (h : ℝ) * (C * C) / (N q : ℝ)) atTop (𝓝 0) := by
    have hcast := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hN.tendsto_atTop
    simpa only [div_eq_mul_inv, mul_zero, comp_def] using
      (tendsto_inv_atTop_zero.comp hcast).const_mul ((h : ℝ) * (C * C))
  have hnorm : Tendsto (fun q ↦
      ‖measureFourier (periodogram u (N q)) (h : ℤ) - corr u u h (N q)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) hdiff hbound
  have hzero : Tendsto (fun q ↦
      measureFourier (periodogram u (N q)) (h : ℤ) - corr u u h (N q)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [zero_add, sub_add_cancel] using hzero.add (hr h)

/-- A positive circle spectrum for every limiting self-correlation. -/
theorem exists_corr_spectrum {u : ℕ → ℂ} {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hu : BoundedSeq u) (hN : StrictMono N) (hr : CorrLimits u u N r) :
    ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ := by
  obtain ⟨C, hC₀, hC⟩ := hu
  let C₀ : ℝ≥0 := ⟨C, hC₀⟩
  let seq (q : ℕ) := periodogram u (N q)
  have hmass (q : ℕ) : (seq q).mass ≤ C₀ ^ 2 := periodogram_mass_le u (N q) C₀ hC
  let l : Ultrafilter ℕ := Ultrafilter.of atTop
  have hl : (l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hc := isCompact_setOfPred_finiteMeasure_le_of_compactSpace UnitAddCircle (C₀ ^ 2)
  obtain ⟨μ, -, hμ⟩ := hc.ultrafilter_le_nhds' (l.map seq) (by
    change {q | (seq q).mass ≤ C₀ ^ 2} ∈ l
    exact Ultrafilter.mem_coe.1 (Eventually.of_forall hmass))
  have ht : Tendsto seq (l : Filter ℕ) (𝓝 μ) := hμ
  refine ⟨μ, fun h ↦ ?_⟩
  have htest : Continuous fun ν : FiniteMeasure UnitAddCircle ↦ measureFourier ν (h : ℤ) :=
    continuous_finiteMeasure_integral (_root_.fourier (-(h : ℤ)))
  exact tendsto_nhds_unique (htest.continuousAt.tendsto.comp ht)
    ((tendsto_periodogram_fourier ⟨C, hC₀, hC⟩ hN hr h).mono_left hl)

/-- A finite linear combination of sequences. -/
def sequenceCombination {I : Type*} [Fintype I] (u : I → ℕ → ℂ) (z : I → ℂ) (n : ℕ) : ℂ :=
  ∑ i, z i * u i n

theorem bounded_sequenceCombination {I : Type*} [Fintype I] (u : I → ℕ → ℂ) (z : I → ℂ)
    (hu : ∀ i, BoundedSeq (u i)) : BoundedSeq (sequenceCombination u z) := by
  choose C hC₀ hC using hu
  refine ⟨∑ i, ‖z i‖ * C i, Finset.sum_nonneg (fun i _ ↦ mul_nonneg (norm_nonneg _) (hC₀ i)), fun n ↦ ?_⟩
  unfold sequenceCombination
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC i n) (norm_nonneg _))

private theorem cesaro_sum {I : Type*} [Fintype I] (u : I → ℕ → ℂ) (N : ℕ) :
    cesaro (fun n ↦ ∑ i, u i n) N = ∑ i, cesaro (u i) N := by
  simp only [cesaro, ← Finset.sum_div]
  rw [Finset.sum_comm]

private theorem cesaro_mul (u : ℕ → ℂ) (a : ℂ) (N : ℕ) :
    cesaro (fun n ↦ a * u n) N = a * cesaro u N := by
  simp only [cesaro, ← mul_div_assoc, Finset.mul_sum]

theorem corr_sequenceCombination {I : Type*} [Fintype I] (u : I → ℕ → ℂ) (z : I → ℂ) (h N : ℕ) :
    corr (sequenceCombination u z) (sequenceCombination u z) h N =
      ∑ i, ∑ j, (z i * conj (z j)) * corr (u i) (u j) h N := by
  unfold corr
  have hexpand (n : ℕ) :
      sequenceCombination u z (n + h) * star (sequenceCombination u z n) =
        ∑ i, ∑ j, (z i * conj (z j)) * (u i (n + h) * star (u j n)) := by
    change (∑ i, z i * u i (n + h)) * conj (∑ j, z j * u j n) = _
    rw [map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (z i * u i (n + h)) * (conj (z j) * conj (u j n)) =
      (z i * conj (z j)) * (u i (n + h) * conj (u j n))
    ring
  simp_rw [hexpand, cesaro_sum, cesaro_mul]

theorem corrLimits_sequenceCombination {I : Type*} [Fintype I]
    (u : I → ℕ → ℂ) (z : I → ℂ) (N : ℕ → ℕ) (r : I → I → ℕ → ℂ)
    (hr : ∀ i j, CorrLimits (u i) (u j) N (r i j)) :
    CorrLimits (sequenceCombination u z) (sequenceCombination u z) N
      (fun h ↦ ∑ i, ∑ j, z i * conj (z j) * r i j h) := by
  intro h
  simp_rw [corr_sequenceCombination]
  exact tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ (hr i j h).const_mul _

/-- Extend positive-lag cross-correlations to negative lags using conjugate transpose. -/
def integerCorrelation {I : Type*} (r : I → I → ℕ → ℂ) (i j : I) : ℤ → ℂ
  | .ofNat h => r i j h
  | .negSucc h => conj (r j i (h + 1))

theorem corrLimits_hermitian_zero {I : Type*} (u : I → ℕ → ℂ) (N : ℕ → ℕ)
    (r : I → I → ℕ → ℂ) (hr : ∀ i j, CorrLimits (u i) (u j) N (r i j)) (i j : I) :
    conj (r i j 0) = r j i 0 := by
  have h := (Complex.continuous_conj.tendsto (r i j 0)).comp (hr i j 0)
  have he (q : ℕ) : conj (corr (u i) (u j) 0 (N q)) = corr (u j) (u i) 0 (N q) := by
    simp only [corr, cesaro, add_zero, map_div₀, map_natCast, map_sum, map_mul]
    apply congrArg (· / (N q : ℂ))
    apply Finset.sum_congr rfl
    intro n _
    change conj (u i n) * conj (conj (u j n)) = u j n * conj (u i n)
    simp [mul_comm]
  have h' : Tendsto (fun q : ℕ ↦ corr (u j) (u i) 0 (N q)) atTop (𝓝 (conj (r i j 0))) := by
    simpa only [comp_def, he] using h
  exact tendsto_nhds_unique h' (hr j i 0)

/-- A family of positive spectra for all linear combinations of a finite family
of sequences with common limiting correlations. -/
theorem exists_joint_corr_spectrum {I : Type*} [Fintype I]
    (u : I → ℕ → ℂ) (N : ℕ → ℕ) (r : I → I → ℕ → ℂ)
    (hu : ∀ i, BoundedSeq (u i)) (hN : StrictMono N)
    (hr : ∀ i j, CorrLimits (u i) (u j) N (r i j)) :
    ∃ M : (I → ℂ) → FiniteMeasure UnitAddCircle,
      ∀ z n, measureFourier (M z) n =
        ∑ i, ∑ j, z i * conj (z j) * integerCorrelation r i j n := by
  have hh (z : I → ℂ) := exists_corr_spectrum (bounded_sequenceCombination u z hu) hN
    (corrLimits_sequenceCombination u z N r hr)
  choose M hM using hh
  refine ⟨M, fun z n ↦ ?_⟩
  cases n with
  | ofNat h => exact hM z h
  | negSucc h =>
    change measureFourier (M z) (Int.negSucc h) = ∑ i, ∑ j, z i * conj (z j) * conj (r j i (h + 1))
    rw [show (Int.negSucc h : ℤ) = -((h + 1 : ℕ) : ℤ) by omega, measureFourier_neg, hM z (h + 1)]
    simp only [map_sum, map_mul, starRingEnd_self_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Selecting a single coordinate of the joint spectrum gives its self-correlation spectrum. -/
theorem joint_spectrum_single {I : Type*} [Fintype I] [DecidableEq I]
    (M : (I → ℂ) → FiniteMeasure UnitAddCircle) (r : I → I → ℕ → ℂ)
    (hM : ∀ z n, measureFourier (M z) n = ∑ i, ∑ j, z i * conj (z j) * integerCorrelation r i j n)
    (i : I) : HasSpectrum (r i i) (M (Pi.single i 1)) := by
  intro h
  rw [hM, Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single i]
    · simp [integerCorrelation]
    · intro j hj; simp [hj]
  · intro j hj; simp [hj]

end

end VdC

end

end VdC_Realization_Module

/- Source: VdC/SpectralSequences.lean -/
section VdC_SpectralSequences_Module

/-! # Spectral classes of bounded sequences -/

@[expose] public section

open MeasureTheory

namespace VdC

/-- Every convergent autocorrelation subsequence has an absolutely
continuous positive finite spectral measure. -/
def SpectrallyLebesgue (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r →
    ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧
      (μ : Measure UnitAddCircle) ≪ circleHaar

/-- Every convergent autocorrelation subsequence has a singular
positive finite spectral measure. -/
def SpectrallySingular (x : ℕ → ℂ) : Prop :=
  BoundedSeq x ∧ ∀ N r, StrictMono N → CorrLimits x x N r →
    ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧
      (μ : Measure UnitAddCircle).MutuallySingular circleHaar

end VdC

end

end VdC_SpectralSequences_Module

/- Source: VdC/CompactSpectrum.lean -/
section VdC_CompactSpectrum_Module

/-! Compact sequences have singular spectrum. This uses small return energies
and the Riemann–Lebesgue lemma on the absolutely continuous part. -/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ComplexConjugate ENNReal FourierTransform Topology

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Riemann–Lebesgue for a circle measure absolutely continuous with respect to Haar. -/
theorem tendsto_measureFourier_zero_of_ac (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (hμ : μ ≪ circleHaar) :
    Tendsto (fun n : ℕ ↦ measureFourier μ (n : ℤ)) atTop (𝓝 0) := by
  let ρ := μ.rnDeriv circleHaar
  let f : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator
    (fun x ↦ Complex.ofReal (ρ (x : UnitAddCircle)).toReal)
  have hreal := ((Real.tendsto_integral_exp_smul_cocompact f).mono_left atTop_le_cocompact).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine hreal.congr' (Eventually.of_forall fun n ↦ ?_)
  have : μ.HaveLebesgueDecomposition circleHaar := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hρ : circleHaar.withDensity ρ = μ := Measure.withDensity_rnDeriv_eq μ circleHaar hμ
  change (∫ x : ℝ, 𝐞 (-(x * (n : ℝ))) • f x) = measureFourier μ (n : ℤ)
  rw [measureFourier, ← hρ, integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv _ _) (Measure.rnDeriv_lt_top _ _), circleHaar,
    AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← UnitAddCircle.integral_preimage (0 : ℝ), zero_add, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [f, ρ, circleHaar, indicator_of_mem hx, Circle.smul_def, Real.fourierChar_apply,
      fourier_coe_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Int.cast_neg, Int.cast_natCast, Complex.ofReal_one, div_one]
    ring_nf
  · simp [f, hx]

/-- The squared distance of the character at time `h` from the constant character. -/
def spectralReturnEnergy (μ : Measure UnitAddCircle) (h : ℕ) : ℝ :=
  ∫ t, ‖_root_.fourier (-(h : ℤ)) t - 1‖ ^ 2 ∂μ

theorem spectralReturnEnergy_eq (μ : Measure UnitAddCircle) [IsFiniteMeasure μ] (h : ℕ) :
    spectralReturnEnergy μ h = 2 * (μ.real univ - (measureFourier μ (h : ℤ)).re) := by
  have hpt (z : ℂ) (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
    have hz' : ‖z‖ ^ 2 = 1 := by rw [hz, one_pow]
    rw [Complex.sq_norm, Complex.normSq_apply] at hz'
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero]
    nlinarith only [hz']
  let g : C(UnitAddCircle, ℂ) := _root_.fourier (-(h : ℤ))
  have hg : Integrable g μ :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr : Integrable (fun t ↦ (g t).re) μ :=
    (Complex.continuous_re.comp g.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : ∫ t, (g t).re ∂μ = (measureFourier μ (h : ℤ)).re := by
    change (∫ t, (g t).re ∂μ) = (∫ t, g t ∂μ).re
    simpa only [RCLike.re_to_complex] using (integral_re (𝕜 := ℂ) hg)
  change (∫ t, ‖g t - 1‖ ^ 2 ∂μ) = _
  calc
    _ = ∫ t, 2 * (1 - (g t).re) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun t ↦ hpt (g t) (by simp [g, fourier_apply, Circle.norm_coe])
    _ = _ := by
      rw [integral_const_mul, integral_sub (integrable_const _) hr,
        integral_const, smul_eq_mul, mul_one, he]

theorem spectralReturnEnergy_mono {ν μ : Measure UnitAddCircle} [IsFiniteMeasure μ]
    (hν : ν ≤ μ) (h : ℕ) : spectralReturnEnergy ν h ≤ spectralReturnEnergy μ h := by
  apply integral_mono_measure hν (ae_of_all _ fun _ ↦ sq_nonneg _)
  have hc : Continuous (fun t : UnitAddCircle ↦ ‖_root_.fourier (-(h : ℤ)) t - 1‖ ^ 2) :=
    ((_root_.fourier (-(h : ℤ))).continuous.sub continuous_const).norm.pow 2
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A positive measure with arbitrarily late arbitrarily small returns is singular. -/
theorem mutuallySingular_of_small_spectral_returns (μ : Measure UnitAddCircle)
    [IsFiniteMeasure μ]
    (hsmall : ∀ ε > (0 : ℝ), ∀ L : ℕ, ∃ h ≥ L, spectralReturnEnergy μ h < ε) :
    μ.MutuallySingular circleHaar := by
  let ν := circleHaar.withDensity (μ.rnDeriv circleHaar)
  have : μ.HaveLebesgueDecomposition circleHaar := Measure.haveLebesgueDecomposition_of_finiteMeasure
  have hνle : ν ≤ μ := Measure.withDensity_rnDeriv_le _ _
  have hνac : ν ≪ circleHaar := withDensity_absolutelyContinuous _ _
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνle
  have hl : Tendsto (spectralReturnEnergy ν) atTop (𝓝 (2 * ν.real univ)) := by
    have ht := Complex.continuous_re.tendsto 0 |>.comp (tendsto_measureFourier_zero_of_ac ν hνac)
    have ht' := (tendsto_const_nhds (x := ν.real univ)).sub ht |>.const_mul (2 : ℝ)
    change Tendsto (fun h ↦ spectralReturnEnergy ν h) atTop (𝓝 (2 * ν.real univ))
    simpa only [spectralReturnEnergy_eq, comp_def, Complex.zero_re, sub_zero] using ht'
  apply (Measure.withDensity_rnDeriv_eq_zero μ circleHaar).mp
  change ν = 0
  by_contra hne
  have hpos : 0 < ν.real univ := by
    apply lt_of_le_of_ne measureReal_nonneg
    intro hz
    apply hne
    exact Measure.measure_univ_eq_zero.mp
      ((measureReal_eq_zero_iff (measure_ne_top ν univ)).mp hz.symm)
  have hev : ∀ᶠ h : ℕ in atTop, ν.real univ < spectralReturnEnergy ν h :=
    hl.eventually (lt_mem_nhds (by linarith))
  obtain ⟨L, hL⟩ := eventually_atTop.mp hev
  obtain ⟨h, hh, hsmall'⟩ := hsmall _ hpos L
  exact (hL h hh).not_ge ((spectralReturnEnergy_mono hνle h).trans hsmall'.le)

/-- Compact bounded sequences have singular spectral measures on every permissible subsequence. -/
theorem spectrallySingular_of_compactSeq {y : ℕ → ℂ} (hy : CompactSeq y) :
    SpectrallySingular y := by
  refine ⟨hy.1, fun N r hN hr ↦ ?_⟩
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hy.1 hN hr
  refine ⟨μ, hμ, mutuallySingular_of_small_spectral_returns _ ?_⟩
  intro ε hε L
  obtain ⟨h, hh, hs⟩ := compactAlong_returns hy hN hr ε hε L
  refine ⟨h, hh, ?_⟩
  have hmass := hμ 0
  rw [Nat.cast_zero, measureFourier_zero] at hmass
  have hm := congrArg Complex.re hmass
  rw [Complex.ofReal_re] at hm
  simpa only [spectralReturnEnergy_eq, hμ h, hm] using hs

end

end VdC

end

end VdC_CompactSpectrum_Module

/- Source: VdC/MixingHierarchy.lean -/
section VdC_MixingHierarchy_Module

/-! # Mixing Hierarchy -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

/-- Absolutely continuous spectral measures give vanishing self-correlations by
Riemann–Lebesgue, hence the required Cesàro vanishing for all bounded tests. -/
theorem SpectrallyLebesgue.nearlyWeakMixing {x : ℕ → ℂ} (hx : SpectrallyLebesgue x) :
    NearlyWeakMixing x := by
  apply nearlyWeakMixing_of_self_mean hx.1
  intro M r hM hr
  obtain ⟨μ, hμ, hAc⟩ := hx.2 M r hM hr
  change ∀ h : ℕ, measureFourier (μ : Measure UnitAddCircle) (h : ℤ) = r h at hμ
  have hFourier := tendsto_measureFourier_zero_of_ac (μ : Measure UnitAddCircle) hAc
  have hnorm := (hFourier.comp (tendsto_add_atTop_nat 1)).norm
  apply realCesaro_tendsto_zero_of_tendsto_zero (fun _ => norm_nonneg _)
  simpa only [Function.comp_def, hμ, norm_zero] using hnorm

end VdC

end

end VdC_MixingHierarchy_Module

/- Source: VdC/SpectralScalars.lean -/
section VdC_SpectralScalars_Module

/-! # Scalar spectral classes and conjugation -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem measureFourier_reflect (μ : Measure UnitAddCircle) (n : ℤ) :
    measureFourier (μ.map (fun x => -x)) n = conj (measureFourier μ n) := by
  rw [measureFourier, integral_map measurable_neg.aemeasurable
    (fourier (-n)).continuous.aestronglyMeasurable, measureFourier, ← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp

/-- Only the zeroth Fourier coefficient of normalized Haar measure is nonzero. -/
theorem measureFourier_circleHaar (n : ℤ) :
    measureFourier circleHaar n = if n = 0 then 1 else 0 := by
  have he : measureFourier circleHaar n = fourierCoeff (fourier (T := 1) 0) n := by
    simp only [measureFourier, circleHaar, fourierCoeff, smul_eq_mul, fourier_zero, mul_one]
  rw [he, fourierCoeff_fourier]
  simp [Pi.single_apply]

private theorem circleHaar_reflect : circleHaar.map (fun x => -x) = circleHaar := by
  have : IsFiniteMeasure (circleHaar.map (fun x => -x)) := circleHaar.isFiniteMeasure_map _
  apply measure_eq_of_fourier
  intro n
  rw [measureFourier_reflect, measureFourier_circleHaar]
  split_ifs <;> simp

private theorem circleHaar_singleton_zero : circleHaar {0} = 0 := by
  let f (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have hf (n : ℕ) : f n ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    constructor
    · dsimp [f]
      positivity
    · dsimp [f]
      rw [zero_add, div_lt_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hinj : Function.Injective (fun n => (f n : UnitAddCircle)) := by
    intro m n h
    have h' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hf m) (hf n)).mp h
    simp only [f, one_div, inv_inj] at h'
    exact_mod_cast (add_right_cancel h')
  have : Infinite UnitAddCircle := Infinite.of_injective _ hinj
  by_contra h
  have htop : circleHaar Set.univ = ∞ := Set.infinite_univ.meas_eq_top
    ⟨_, h, fun x _ => by
      have hx : (fun y : UnitAddCircle => -x + y) ⁻¹' {0} = {x} := by
        ext y
        simp [eq_comm]
      have ht := measure_preimage_add (AddCircle.haarAddCircle : Measure UnitAddCircle)
        (-x) ({0} : Set UnitAddCircle)
      rw [hx] at ht
      exact ht.ge⟩
  exact measure_ne_top _ _ htop

theorem corr_conj (x y : ℕ → ℂ) (h N : ℕ) :
    corr (fun n => conj (x n)) (fun n => conj (y n)) h N = conj (corr x y h N) := by
  simp only [corr, cesaro, Complex.star_def, map_div₀, map_natCast, map_sum, map_mul,
    starRingEnd_self_apply]

/-- Conjugation corresponds to reflecting the spectrum on the circle. -/
theorem SpectrallySingular.conj {x : ℕ → ℂ} (hx : SpectrallySingular x) :
    SpectrallySingular (fun n => conj (x n)) := by
  obtain ⟨C, hC, hB⟩ := hx.1
  refine ⟨⟨C, hC, fun n => by simpa using hB n⟩, ?_⟩
  intro N r hN hr
  have hc : CorrLimits x x N (fun h => conj (r h)) := by
    intro h
    simpa only [Function.comp_def, corr_conj, starRingEnd_self_apply] using
      (Complex.continuous_conj.tendsto (r h)).comp (hr h)
  obtain ⟨μ, hμ, hsing⟩ := hx.2 N _ hN hc
  refine ⟨μ.map (fun x => -x), ?_, ?_⟩
  · intro h
    rw [FiniteMeasure.toMeasure_map, measureFourier_reflect, hμ, starRingEnd_self_apply]
  · change ((μ : Measure UnitAddCircle).map fun x => -x).MutuallySingular circleHaar
    simpa only [circleHaar_reflect] using measurableEmbedding_neg.mutuallySingular_map hsing

private theorem corr_const_mul (x : ℕ → ℂ) (c : ℂ) (h N : ℕ) :
    corr (fun n => c * x n) (fun n => c * x n) h N =
      (Complex.normSq c : ℂ) * corr x x h N := by
  unfold corr
  rw [← cesaro_mul_const]
  congr 1
  funext n
  change (c * x (n+h)) * conj (c * x n) = (Complex.normSq c : ℂ) * (x (n+h) * conj (x n))
  rw [map_mul, ← Complex.mul_conj]
  ring

private theorem zeroCorrSpectrum {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hr : CorrLimits (fun _ => 0) (fun _ => 0) N r) :
    HasSpectrum r 0 := by
  intro h
  have he : r h = 0 := tendsto_nhds_unique (hr h) (by simp [corr, cesaro])
  simp [he, measureFourier]

theorem spectrallyLebesgue_zero : SpectrallyLebesgue (fun _ => 0) :=
  ⟨⟨0, le_rfl, by simp⟩, fun _ _ _ hr => ⟨0, zeroCorrSpectrum hr, Measure.AbsolutelyContinuous.zero _⟩⟩

theorem spectrallySingular_zero : SpectrallySingular (fun _ => 0) :=
  ⟨⟨0, le_rfl, by simp⟩, fun _ _ _ hr => ⟨0, zeroCorrSpectrum hr, Measure.MutuallySingular.zero_left⟩⟩

private theorem spectrumClass_const_mul (P : Measure UnitAddCircle → Prop) {x : ℕ → ℂ}
    (hx : BoundedSeq x) (hzero : P 0)
    (hscale : ∀ (b : ℝ≥0) (μ : Measure UnitAddCircle), P μ → P (b • μ))
    (hP : ∀ N r, StrictMono N → CorrLimits x x N r →
      ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧ P μ) (c : ℂ) :
    BoundedSeq (fun n => c * x n) ∧ ∀ N r, StrictMono N →
      CorrLimits (fun n => c * x n) (fun n => c * x n) N r →
      ∃ μ : FiniteMeasure UnitAddCircle, HasSpectrum r μ ∧ P μ := by
  obtain ⟨C, hC, hB⟩ := hx
  refine ⟨⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun n => ?_⟩, ?_⟩
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)
  · intro N r hN hr
    by_cases hc : c = 0
    · subst c
      simp only [zero_mul] at hr
      exact ⟨0, zeroCorrSpectrum hr, hzero⟩
    let a := Complex.normSq c
    have ha : 0 < a := Complex.normSq_pos.mpr hc
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hG : CorrLimits x x N (fun h => (a : ℂ)⁻¹ * r h) := by
      intro h
      have hh := (hr h).const_mul ((a : ℂ)⁻¹)
      simpa [corr_const_mul, a, ← mul_assoc, inv_mul_cancel₀ ha0] using hh
    obtain ⟨μ, hμ, hμP⟩ := hP N _ hN hG
    let b : ℝ≥0 := ⟨a, ha.le⟩
    refine ⟨b • μ, ?_, ?_⟩
    · intro n
      change measureFourier ((b : ℝ≥0∞) • (μ : Measure UnitAddCircle)) (n : ℤ) = r n
      rw [measureFourier_smul, ENNReal.coe_toReal, hμ]
      change (a : ℂ) * ((a : ℂ)⁻¹ * r n) = r n
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    · exact hscale b μ hμP

/-- Closure of spectral Lebesgue sequences under multiplication by a scalar. -/
theorem SpectrallyLebesgue.const_mul {x : ℕ → ℂ} (hx : SpectrallyLebesgue x) (c : ℂ) :
    SpectrallyLebesgue (fun n => c * x n) :=
  spectrumClass_const_mul (· ≪ circleHaar) hx.1 (Measure.AbsolutelyContinuous.zero _)
    (fun b _ h => h.smul_left b) hx.2 c

/-- Closure of spectrally singular sequences under multiplication by a scalar. -/
theorem SpectrallySingular.const_mul {x : ℕ → ℂ} (hx : SpectrallySingular x) (c : ℂ) :
    SpectrallySingular (fun n => c * x n) :=
  spectrumClass_const_mul (·.MutuallySingular circleHaar) hx.1 Measure.MutuallySingular.zero_left
    (fun b _ h => h.smul_nnreal b) hx.2 c

/-- The constant unit sequence has the point mass at frequency zero as
its spectrum on every permissible subsequence. -/
theorem spectrallySingular_one : SpectrallySingular (fun _ => 1) := by
  refine ⟨⟨1, zero_le_one, by simp⟩, ?_⟩
  intro N r hN hr
  let μ : FiniteMeasure UnitAddCircle := ⟨Measure.dirac 0, inferInstance⟩
  refine ⟨μ, ?_, ?_⟩
  · intro h
    change measureFourier (Measure.dirac (0 : UnitAddCircle)) (h : ℤ) = r h
    rw [measureFourier_dirac_zero]
    apply tendsto_nhds_unique _ (hr h)
    simpa [corr, Function.comp_def] using (cesaro_tendsto_const (1 : ℂ)).comp hN.tendsto_atTop
  · refine ⟨{0}ᶜ, (measurableSet_singleton 0).compl, ?_, by
      simpa using circleHaar_singleton_zero⟩
    change Measure.dirac (0 : UnitAddCircle) ({0}ᶜ : Set UnitAddCircle) = 0
    simp

theorem spectrallySingular_const (c : ℂ) : SpectrallySingular (fun _ => c) := by
  simpa only [mul_one] using spectrallySingular_one.const_mul c

end

end VdC

end

end VdC_SpectralScalars_Module

/- Source: VdC/SpectralAC.lean -/
section VdC_SpectralAC_Module

/-! # Absolute continuity from square summability -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- A finite positive absolutely continuous measure has a nonnegative L¹
Radon–Nikodym density. -/
theorem exists_integrable_density (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (hμ : μ ≪ circleHaar) :
    ∃ g : UnitAddCircle → ℝ, Integrable g circleHaar ∧ (∀ x, 0 ≤ g x) ∧
      μ = circleHaar.withDensity (fun x => ENNReal.ofReal (g x)) := by
  let f := μ.rnDeriv circleHaar
  have hf : Measurable f := Measure.measurable_rnDeriv _ _
  have heq : circleHaar.withDensity f = μ := Measure.withDensity_rnDeriv_eq _ _ hμ
  have hfin : (∫⁻ x, f x ∂circleHaar) ≠ ∞ := by
    have he := congrArg (fun ν : Measure UnitAddCircle => ν Set.univ) heq
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
    exact he ▸ measure_ne_top μ Set.univ
  refine ⟨fun x => (f x).toReal, integrable_toReal_of_lintegral_ne_top hf.aemeasurable hfin,
    fun _ => ENNReal.toReal_nonneg, ?_⟩
  rw [← heq]
  symm
  apply withDensity_congr_ae
  refine ofReal_toReal_ae_eq ?_
  exact ae_lt_top hf hfin

private theorem positiveDensity_finite {g : UnitAddCircle → ℝ}
    (hg : Integrable g circleHaar) :
    IsFiniteMeasure (circleHaar.withDensity (fun x => ENNReal.ofReal (g x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := hg.real_toNNReal.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ => NNReal.coe_nonneg _))] at h
  simpa using h

theorem measureFourier_withDensity_ofReal {g : UnitAddCircle → ℝ}
    (hg : Integrable g circleHaar) (n : ℤ) :
    measureFourier (circleHaar.withDensity (fun x => ENNReal.ofReal (g x))) n =
      ∫ x, fourier (-n) x * (↑((g x).toNNReal : ℝ) : ℂ) ∂circleHaar := by
  have hm : AEMeasurable (fun x => (g x).toNNReal) circleHaar :=
    continuous_real_toNNReal.measurable.comp_aemeasurable hg.aemeasurable
  unfold measureFourier
  change (∫ x, fourier (-n) x ∂circleHaar.withDensity (fun x => ((g x).toNNReal : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul₀ hm]
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm _ _

private theorem fourier_translate_integrable {f : UnitAddCircle → ℂ}
    (hf : Integrable f circleHaar) (n : ℤ) :
    Integrable (fun x => fourier n x * f x) circleHaar :=
  hf.fourier_smul n

private theorem fourier_real_part_of_density {g : UnitAddCircle → ℂ}
    (hg : Integrable g circleHaar) (μ : Measure UnitAddCircle)
    (hG : ∀ n, (∫ x, fourier (-n) x * g x ∂circleHaar) = measureFourier μ n) (n : ℤ) :
    (∫ x, fourier (-n) x * (↑(g x).re : ℂ) ∂circleHaar) = measureFourier μ n := by
  have h1 := fourier_translate_integrable hg (-n)
  have hconj : Integrable (fun x => conj (g x)) circleHaar :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hg
  have h2 := fourier_translate_integrable hconj (-n)
  have hG2 : (∫ x, fourier (-n) x * conj (g x) ∂circleHaar) = measureFourier μ n := by
    have hc (x : UnitAddCircle) : fourier (-n) x * conj (g x) = conj (fourier n x * g x) := by
      rw [map_mul, fourier_neg]
    simp_rw [hc, integral_conj]
    simpa only [neg_neg, measureFourier_neg, starRingEnd_apply, star_star] using
      congrArg (fun z : ℂ => conj z) (hG (-n))
  have hpoint (x : UnitAddCircle) : (↑(g x).re : ℂ) =
      (1 / 2 : ℂ) * (g x + conj (g x)) := by
    apply Complex.ext
    · norm_num [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.div_re]
      ring
    · norm_num [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.div_im]
  calc
    _ = ∫ x, (1 / 2 : ℂ) * (fourier (-n) x * g x + fourier (-n) x * conj (g x)) ∂circleHaar := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only; rw [hpoint]; ring
    _ = _ := by
      rw [integral_const_mul, integral_add h1 h2, hG, hG2]
      ring

/-- A circle measure with square-summable Fourier coefficients is absolutely
continuous. The Fourier Hilbert basis constructs an L² density, with the real
part identified as a difference of two finite positive densities. -/
theorem fourier_l2_absolutelyContinuous (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (h : Summable (fun n : ℤ => ‖measureFourier μ n‖ ^ 2)) :
    μ ≪ circleHaar := by
  let c : lp (fun _ : ℤ => ℂ) 2 := ⟨measureFourier μ, memℓp_gen (by simpa using h)⟩
  let g : Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) := (@fourierBasis 1 _).repr.symm c
  have hg : Integrable g circleHaar := (Lp.memLp g).integrable (by norm_num)
  have hG (n : ℤ) : (∫ x, fourier (-n) x * g x ∂circleHaar) = measureFourier μ n := by
    change @fourierCoeff 1 _ _ _ _ g n = _
    exact (fourierBasis_repr g n).symm.trans
      (congrArg (fun r : lp (fun _ : ℤ => ℂ) 2 => r n)
        ((@fourierBasis 1 _).repr.apply_symm_apply c))
  let f : UnitAddCircle → ℝ := fun x => (g x).re
  have hf : Integrable f circleHaar := hg.re
  let ν := circleHaar.withDensity (fun x => ENNReal.ofReal (f x))
  let νneg := circleHaar.withDensity (fun x => ENNReal.ofReal (-f x))
  have : IsFiniteMeasure ν := positiveDensity_finite hf
  have : IsFiniteMeasure νneg := positiveDensity_finite hf.neg
  have hsplit (x : UnitAddCircle) :
      (↑((f x).toNNReal : ℝ) : ℂ) =
        (↑(f x) : ℂ) + (↑((-f x).toNNReal : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]
    congr 1
    rw [Real.coe_toNNReal', Real.coe_toNNReal']
    rcases le_total 0 (f x) with hx | hx
    · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
  have hEq : μ + νneg = ν := by
    apply measure_eq_of_fourier
    intro n
    rw [measureFourier_add, show measureFourier ν n = _ from measureFourier_withDensity_ofReal hf n,
      show measureFourier νneg n = _ from measureFourier_withDensity_ofReal hf.neg n,
      ← fourier_real_part_of_density hg μ hG n]
    simp_rw [hsplit, mul_add]
    exact (integral_add (fourier_translate_integrable hf.ofReal (-n))
      (fourier_translate_integrable hf.neg.real_toNNReal.ofReal (-n))).symm
  have hac : ν ≪ circleHaar := withDensity_absolutelyContinuous _ _
  rw [← hEq] at hac
  intro s hs
  exact le_antisymm ((le_self_add.trans_eq (add_apply _ _ s).symm).trans_eq (hac hs)) bot_le

/-- Positive lags suffice because coefficients at negative lags are conjugates. -/
theorem fourier_positive_l2_absolutelyContinuous (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (h : Summable (fun n : ℕ => ‖measureFourier μ ((n + 1 : ℕ) : ℤ)‖ ^ 2)) :
    μ ≪ circleHaar := by
  apply fourier_l2_absolutelyContinuous
  rw [summable_int_iff_summable_nat_and_neg]
  have hn : Summable (fun n : ℕ => ‖measureFourier μ (n : ℤ)‖ ^ 2) :=
    (summable_nat_add_iff 1).mp h
  exact ⟨hn, by simpa only [measureFourier_neg, Complex.norm_conj] using hn⟩

end

end VdC

end

end VdC_SpectralAC_Module

/- Source: VdC/SpectralOrthogonality.lean -/
section VdC_SpectralOrthogonality_Module

/-! # Orthogonality of mutually singular spectral measures -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate BigOperators

namespace VdC

noncomputable section

/-- The scalar Fourier data for a linear combination of two vectors. -/
def spectralQuadratic (c : Fin 2 → Fin 2 → ℤ → ℂ) (z : Fin 2 → ℂ) (n : ℤ) : ℂ :=
  ∑ i, ∑ j, z i * conj (z j) * c i j n

private theorem measureFourier_finite_smul (μ : FiniteMeasure UnitAddCircle) (t : ℝ≥0)
    (n : ℤ) :
    measureFourier (↑(t • μ) : Measure UnitAddCircle) n =
      ((t : ℝ) : ℂ) * measureFourier μ n := by
  change measureFourier ((t : ℝ≥0∞) • (↑μ : Measure UnitAddCircle)) n = _
  rw [measureFourier_smul, ENNReal.coe_toReal]

variable
  (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
  (c : Fin 2 → Fin 2 → ℤ → ℂ)
  (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic c z n)
include hM

theorem combinationMeasure_neg (w : Fin 2 → ℂ) :
    M (-w) = M w := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp [hM, spectralQuadratic]

private theorem combinationMeasure_parallelogram (v w : Fin 2 → ℂ) :
    M (v+w) + M (v-w) = (2 : ℝ≥0) • M v + (2 : ℝ≥0) • M w := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp only [FiniteMeasure.toMeasure_add, measureFourier_add, measureFourier_finite_smul,
    hM, spectralQuadratic, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, map_add, map_sub,
    NNReal.coe_ofNat, Complex.ofReal_ofNat]
  ring

private theorem combinationMeasure_scale (v w : Fin 2 → ℂ) (k : ℕ) :
    M (v + ((k : ℂ) + 1) • w) + (k : ℝ≥0) • M v =
      ((k : ℝ≥0) + 1) • M (v+w) + (((k : ℝ≥0) + 1) * (k : ℝ≥0)) • M w := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp only [FiniteMeasure.toMeasure_add, measureFourier_add, measureFourier_finite_smul,
    hM, spectralQuadratic, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul, map_natCast, map_one, NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_one, Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_mul]
  ring

private def realMass (A : Set UnitAddCircle) (μ : FiniteMeasure UnitAddCircle) : ℝ :=
  (μ : Measure UnitAddCircle).real A

omit hM in
private theorem realMass_add (A : Set UnitAddCircle) (μ ν : FiniteMeasure UnitAddCircle) :
    realMass A (μ+ν) = realMass A μ + realMass A ν := by
  exact measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)

omit hM in
private theorem realMass_smul (A : Set UnitAddCircle) (s : ℝ≥0)
    (μ : FiniteMeasure UnitAddCircle) :
    realMass A (s • μ) = (s : ℝ) * realMass A μ := by
  simp only [realMass, FiniteMeasure.toMeasure_smul, measureReal_nnreal_smul_apply]

omit hM in
private theorem realMass_nonneg (A : Set UnitAddCircle) (μ : FiniteMeasure UnitAddCircle) :
    0 ≤ realMass A μ := ENNReal.toReal_nonneg

private theorem realMass_add_lower_of_null
    (v w : Fin 2 → ℂ) (A : Set UnitAddCircle) (hw : realMass A (M w) = 0) :
    realMass A (M v) ≤ realMass A (M (v+w)) := by
  have hb (k : ℕ) :
      (k : ℝ) * realMass A (M v) ≤ ((k : ℝ) + 1) * realMass A (M (v+w)) := by
    have h := congrArg (realMass A) (combinationMeasure_scale M c hM v w k)
    simp only [realMass_add, realMass_smul, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_mul,
      NNReal.coe_one, hw, mul_zero, add_zero] at h
    linarith [realMass_nonneg A (M (v + ((k : ℂ) + 1) • w))]
  by_contra! hlt
  have hp := sub_pos.mpr hlt
  obtain ⟨k, hk⟩ := exists_nat_gt (realMass A (M (v+w)) /
    (realMass A (M v) - realMass A (M (v+w))))
  have h := (div_lt_iff₀ hp).mp hk
  nlinarith only [h, hb k]

private theorem realMass_add_of_null
    (v w : Fin 2 → ℂ) (A : Set UnitAddCircle) (hw : realMass A (M w) = 0) :
    realMass A (M (v+w)) = realMass A (M v) := by
  have h₁ := realMass_add_lower_of_null M c hM v w A hw
  have h₂ := realMass_add_lower_of_null M c hM v (-w) A (by
    rw [combinationMeasure_neg M c hM, hw])
  have hpar := congrArg (realMass A) (combinationMeasure_parallelogram M c hM v w)
  simp only [realMass_add, realMass_smul, NNReal.coe_ofNat, hw, mul_zero, add_zero] at hpar
  rw [sub_eq_add_neg] at hpar
  linarith

/-- A summand with vanishing spectral mass on A does not change the
other summand's spectral mass there. -/
theorem combinationMeasure_apply_of_null
    (v w : Fin 2 → ℂ) (A : Set UnitAddCircle) (hw : (M w : Measure UnitAddCircle) A = 0) :
    (M (v+w) : Measure UnitAddCircle) A = (M v : Measure UnitAddCircle) A := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact realMass_add_of_null M c hM v w A (by simp [realMass, Measure.real, hw])

/-- The sum of two absolutely continuous vectors is absolutely continuous. -/
theorem combinationMeasure_add_absolutelyContinuous
    (v w : Fin 2 → ℂ) (ν : Measure UnitAddCircle)
    (hv : (M v : Measure UnitAddCircle) ≪ ν) (hw : (M w : Measure UnitAddCircle) ≪ ν) :
    (M (v+w) : Measure UnitAddCircle) ≪ ν := by
  intro A hA
  rw [combinationMeasure_apply_of_null M c hM v w A (hw hA), hv hA]

private theorem realMass_add_of_mutuallySingular
    (v w : Fin 2 → ℂ)
    (hperp : ((M v) : Measure UnitAddCircle).MutuallySingular (M w)) :
    realMass Set.univ (M (v+w)) = realMass Set.univ (M v) + realMass Set.univ (M w) := by
  obtain ⟨A, hA, hv, hw⟩ := hperp
  have hv' : realMass A (M v) = 0 := by simp [realMass, Measure.real, hv]
  have hw' : realMass Aᶜ (M w) = 0 := by simp [realMass, Measure.real, hw]
  have ha := realMass_add_of_null M c hM w v A hv'
  rw [add_comm w v] at ha
  have hb := realMass_add_of_null M c hM v w Aᶜ hw'
  have hc (z : Fin 2 → ℂ) :
      realMass A (M z) + realMass Aᶜ (M z) = realMass Set.univ (M z) :=
    measureReal_add_measureReal_compl hA
  rw [← hc (v+w), ← hc v, ← hc w, ha, hb, hv', hw']
  ring

theorem combinationMeasure_mul_I (v : Fin 2 → ℂ) :
    M (Complex.I • v) = M v := by
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_fourier
  intro n
  simp only [hM, spectralQuadratic, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, map_mul,
    Complex.conj_I]
  ring_nf
  simp

private theorem quadratic_add_of_mutuallySingular
    (v w : Fin 2 → ℂ)
    (hperp : ((M v) : Measure UnitAddCircle).MutuallySingular (M w)) :
    spectralQuadratic c (v+w) 0 = spectralQuadratic c v 0 + spectralQuadratic c w 0 := by
  simp only [← hM, measureFourier_zero, ← Complex.ofReal_add]
  exact congrArg Complex.ofReal (realMass_add_of_mutuallySingular M c hM v w hperp)

/-- Orthogonality for two vectors whose spectra are mutually singular.
The positive measures for all linear combinations replace a Hilbert-space
quotient, and their Fourier coefficients determine their quadratic mass laws. -/
theorem correlation_measures_orthogonal
    (hsing : ((M (Pi.single (0 : Fin 2) 1)) : Measure UnitAddCircle).MutuallySingular
      (M (Pi.single (1 : Fin 2) 1)))
    (herm : conj (c 0 1 0) = c 1 0 0) :
    c 0 1 0 = 0 := by
  let v : Fin 2 → ℂ := Pi.single 0 1
  let w : Fin 2 → ℂ := Pi.single 1 1
  have hR := quadratic_add_of_mutuallySingular M c hM v w hsing
  have hIsing : ((M v) : Measure UnitAddCircle).MutuallySingular (M (Complex.I • w)) := by
    rw [combinationMeasure_mul_I M c hM]
    exact hsing
  have hI := quadratic_add_of_mutuallySingular M c hM v (Complex.I • w) hIsing
  simp [spectralQuadratic, Fin.sum_univ_two, v, w, Pi.single_apply] at hR
  simp [spectralQuadratic, Fin.sum_univ_two, v, w, Pi.single_apply, Complex.I_mul_I] at hI
  rw [← herm] at hR hI
  apply Complex.ext
  · have h := congrArg Complex.re hR
    simp [Complex.add_re] at h
    rw [Complex.zero_re]
    linarith
  · have h := congrArg Complex.re hI
    simp [Complex.add_re, Complex.mul_re] at h
    rw [Complex.zero_im]
    linarith

end

end VdC

end

end VdC_SpectralOrthogonality_Module

/- Source: VdC/SpectralResults.lean -/
section VdC_SpectralResults_Module

/-! # Spectral consequences for permissible autocorrelation limits -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal ComplexConjugate

namespace VdC

noncomputable section

/-- Lemma `CreatingSpectrallyLebesgue/NWMSequences` (i). -/
theorem spectrallyLebesgue_of_limsup_square_summable {x : ℕ → ℂ} (hx : BoundedSeq x)
    (h : Summable (fun j : ℕ => limsup (fun N => ‖corr x x (j+1) N‖ ^ 2) atTop)) :
    SpectrallyLebesgue x := by
  refine ⟨hx, ?_⟩
  intro N r hN hr
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hx hN hr
  refine ⟨μ, hμ, fourier_positive_l2_absolutelyContinuous μ ?_⟩
  obtain ⟨C, hC, hbound⟩ := hx
  simp_rw [show ∀ a : ℕ, measureFourier μ (a : ℤ) = r a from hμ]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ h
  intro j
  have ht := (hr (j+1)).norm.pow 2
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => ‖corr x x (j+1) n‖ ^ 2) := by
    refine ⟨(C*C)^2, eventually_map.2 (Eventually.of_forall fun n => ?_)⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_corr_le hC hC hbound hbound (j+1) n) 2
  exact le_limsup_of_le hb fun _ he => le_of_tendsto ht (hN.tendsto_atTop.eventually he)

def pairSequences (x y : ℕ → ℂ) : Fin 2 → ℕ → ℂ :=
  fun i => if i = 0 then x else y

theorem exists_pair_spectra {x y : ℕ → ℂ} {N : ℕ → ℕ} (hp : PermissibleTriple x y N) :
    ∃ (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle),
      (∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j)) ∧
      ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n := by
  obtain ⟨xx, hxx⟩ := hp.xx
  obtain ⟨xy, hxy⟩ := hp.xy
  obtain ⟨yx, hyx⟩ := hp.yx
  obtain ⟨yy, hyy⟩ := hp.yy
  let r : Fin 2 → Fin 2 → ℕ → ℂ := fun i j =>
    if i = 0 then (if j = 0 then xx else xy) else (if j = 0 then yx else yy)
  have hr (i j : Fin 2) : CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j) := by
    fin_cases i <;> fin_cases j
    · exact hxx
    · exact hxy
    · exact hyx
    · exact hyy
  have hb (i : Fin 2) : BoundedSeq (pairSequences x y i) := by
    fin_cases i
    · exact hp.boundedX
    · exact hp.boundedY
  obtain ⟨M, hM⟩ := exists_joint_corr_spectrum (pairSequences x y) N r hb hp.strictMono hr
  exact ⟨r, M, hr, hM⟩

def baseVector (i : Fin 2) : Fin 2 → ℂ := Pi.single i 1

private theorem pairSpectrum_basis (r : Fin 2 → Fin 2 → ℕ → ℂ)
    (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (i : Fin 2) :
    HasSpectrum (r i i) (M (baseVector i)) := by
  intro n
  rw [hM]
  fin_cases i <;> simp [spectralQuadratic, baseVector, Pi.single_apply,
    integerCorrelation]

theorem pairSpectrum_ac {x y : ℕ → ℂ} {N : ℕ → ℕ} (hN : StrictMono N)
    (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hr : ∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j))
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (i : Fin 2) (h : SpectrallyLebesgue (pairSequences x y i)) :
    (M (baseVector i) : Measure UnitAddCircle) ≪ circleHaar := by
  obtain ⟨μ, hμ, hac⟩ := h.2 N (r i i) hN (hr i i)
  have he : (M (baseVector i) : Measure UnitAddCircle) = μ :=
    measure_eq_of_fourier_nat (fun n => (pairSpectrum_basis r M hM i n).trans (hμ n).symm)
  rwa [he]

private theorem pairSpectrum_singular {x y : ℕ → ℂ} {N : ℕ → ℕ} (hN : StrictMono N)
    (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hr : ∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j))
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (i : Fin 2) (h : SpectrallySingular (pairSequences x y i)) :
    (M (baseVector i) : Measure UnitAddCircle).MutuallySingular circleHaar := by
  obtain ⟨μ, hμ, hsing⟩ := h.2 N (r i i) hN (hr i i)
  have he : (M (baseVector i) : Measure UnitAddCircle) = μ :=
    measure_eq_of_fourier_nat (fun n => (pairSpectrum_basis r M hM i n).trans (hμ n).symm)
  rwa [he]

/-- The Lebesgue/singular dichotomy on a fixed permissible subsequence. -/
theorem cross_zero_of_ac_singular {x y : ℕ → ℂ} {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hx : SpectrallyLebesgue x) (hy : SpectrallySingular y)
    (hp : PermissibleTriple x y N) (hr : CorrLimits x y N r) :
    r 0 = 0 := by
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hxa := pairSpectrum_ac hp.strictMono c M hc hM 0 hx
  have hys := pairSpectrum_singular hp.strictMono c M hc hM 1 hy
  have hperp := hys.symm.mono_ac hxa Measure.AbsolutelyContinuous.rfl
  have herm := corrLimits_hermitian_zero (pairSequences x y) N c hc 0 1
  have hz := correlation_measures_orthogonal M (integerCorrelation c) hM hperp herm
  exact (tendsto_nhds_unique (hr 0) (hc 0 1 0)).trans hz

/-- Cesàro averages of x times the conjugate of y vanish. -/
theorem corr_tendsto_zero_of_ac_singular {x y : ℕ → ℂ}
    (hx : SpectrallyLebesgue x) (hy : SpectrallySingular y) :
    Tendsto (corr x y 0) atTop (𝓝 0) := by
  apply tendsto_atTop_of_permissible_refinement hx.1 hy.1 (M := id) strictMono_id
  intro φ _ hp
  obtain ⟨r, hr⟩ := hp.xy
  have hz := cross_zero_of_ac_singular hx hy hp hr
  simpa only [hz, Function.comp_def, id_eq] using hr 0

/-- Lemma `ErgodicDichotomyForSequences` (i), written as the ordinary
product in the paper. -/
theorem cesaro_product_tendsto_zero_of_ac_singular {x y : ℕ → ℂ}
    (hx : SpectrallyLebesgue x) (hy : SpectrallySingular y) :
    Tendsto (cesaro (fun n => x n * y n)) atTop (𝓝 0) := by
  convert corr_tendsto_zero_of_ac_singular hx hy.conj using 1
  ext N
  simp only [corr, Nat.add_zero, Complex.star_def, starRingEnd_self_apply]

private theorem pairSequences_combo_add (x y : ℕ → ℂ) :
    sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1) =
      fun n => x n + y n := by
  funext n
  simp [sequenceCombination, Fin.sum_univ_two, pairSequences, baseVector, Pi.single_apply]

private theorem pairSequences_combo_sub (x y : ℕ → ℂ) :
    sequenceCombination (pairSequences x y) (baseVector 0 - baseVector 1) =
      fun n => x n - y n := by
  funext n
  simp [sequenceCombination, Fin.sum_univ_two, pairSequences, baseVector, Pi.single_apply,
    sub_eq_add_neg]

private theorem pairSpectrum_combination {x y : ℕ → ℂ} {N : ℕ → ℕ}
    (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hr : ∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j))
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (z : Fin 2 → ℂ) :
    CorrLimits (sequenceCombination (pairSequences x y) z)
      (sequenceCombination (pairSequences x y) z) N (fun h => measureFourier (M z) (h : ℤ)) := by
  simp_rw [hM, spectralQuadratic]
  exact corrLimits_sequenceCombination (pairSequences x y) z N r hr

/-- Closure of spectral Lebesgue sequences under addition. -/
theorem SpectrallyLebesgue.add {x y : ℕ → ℂ} (hx : SpectrallyLebesgue x)
    (hy : SpectrallyLebesgue y) : SpectrallyLebesgue (fun n => x n + y n) := by
  let z := baseVector 0 + baseVector 1
  have hb (i : Fin 2) : BoundedSeq (pairSequences x y i) := by
    fin_cases i
    · exact hx.1
    · exact hy.1
  refine ⟨pairSequences_combo_add x y ▸ bounded_sequenceCombination (pairSequences x y) z hb,
    ?_⟩
  intro N r hN hr
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hx.1 hy.1 hN
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hs := pairSpectrum_combination c M hc hM z
  change CorrLimits (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1))
    (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1)) (N ∘ φ) _ at hs
  rw [pairSequences_combo_add] at hs
  refine ⟨M z, fun n => tendsto_nhds_unique (hs n) ((hr n).comp hφ.tendsto_atTop), ?_⟩
  exact combinationMeasure_add_absolutelyContinuous M (integerCorrelation c) hM
    (baseVector 0) (baseVector 1) circleHaar
    (pairSpectrum_ac hp.strictMono c M hc hM 0 hx)
    (pairSpectrum_ac hp.strictMono c M hc hM 1 hy)

/-- Closure of spectrally singular sequences under addition. -/
theorem SpectrallySingular.add {x y : ℕ → ℂ} (hx : SpectrallySingular x)
    (hy : SpectrallySingular y) : SpectrallySingular (fun n => x n + y n) := by
  let v := baseVector 0
  let w := baseVector 1
  have hb (i : Fin 2) : BoundedSeq (pairSequences x y i) := by
    fin_cases i
    · exact hx.1
    · exact hy.1
  refine ⟨pairSequences_combo_add x y ▸ bounded_sequenceCombination (pairSequences x y) (v+w) hb,
    ?_⟩
  intro N r hN hr
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hx.1 hy.1 hN
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hs := pairSpectrum_combination c M hc hM (v+w)
  change CorrLimits (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1))
    (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1)) (N ∘ φ) _ at hs
  rw [pairSequences_combo_add] at hs
  refine ⟨M (v+w), fun n => tendsto_nhds_unique (hs n) ((hr n).comp hφ.tendsto_atTop), ?_⟩
  let ν := (M v : Measure UnitAddCircle) + (M w : Measure UnitAddCircle)
  have hvs : (M v : Measure UnitAddCircle).MutuallySingular circleHaar :=
    pairSpectrum_singular hp.strictMono c M hc hM 0 hx
  have hws : (M w : Measure UnitAddCircle).MutuallySingular circleHaar :=
    pairSpectrum_singular hp.strictMono c M hc hM 1 hy
  have hvd : (M v : Measure UnitAddCircle) ≪ ν := by
    intro A hA
    change ((M v : Measure UnitAddCircle) + (M w : Measure UnitAddCircle)) A = 0 at hA
    rw [add_apply] at hA
    exact (add_eq_zero.mp hA).1
  have hwd : (M w : Measure UnitAddCircle) ≪ ν := by
    intro A hA
    change ((M v : Measure UnitAddCircle) + (M w : Measure UnitAddCircle)) A = 0 at hA
    rw [add_apply] at hA
    exact (add_eq_zero.mp hA).2
  exact (hvs.add_left hws).mono_ac (combinationMeasure_add_absolutelyContinuous M
    (integerCorrelation c) hM v w ν hvd hwd) Measure.AbsolutelyContinuous.rfl

/-- Any measurable mass of the original spectrum lying outside the
approximant's spectrum is bounded by the upper Cesàro mean-square error. -/
private theorem coupled_spectrum_error {x y : ℕ → ℂ} {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hx : BoundedSeq x) (hy : BoundedSeq y) (hN : StrictMono N) (hr : CorrLimits x x N r)
    (μ : FiniteMeasure UnitAddCircle) (hμ : HasSpectrum r μ) {ε : ℝ}
    (hdist : ∀ᶠ N in atTop, realCesaro (fun n => ‖x n - y n‖ ^ 2) N ≤ ε) :
    ∃ (φ : ℕ → ℕ) (ry : ℕ → ℂ) (ν : FiniteMeasure UnitAddCircle),
      StrictMono φ ∧ CorrLimits y y (N ∘ φ) ry ∧ HasSpectrum ry ν ∧
        ∀ A : Set UnitAddCircle, (ν : Measure UnitAddCircle) A = 0 →
          (μ : Measure UnitAddCircle).real A ≤ ε := by
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hx hy hN
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  let v := baseVector 0
  let w := baseVector 1
  have heq : (μ : Measure UnitAddCircle) = M v := by
    apply measure_eq_of_fourier_nat
    intro n
    rw [hμ, pairSpectrum_basis c M hM 0 n]
    exact tendsto_nhds_unique ((hr n).comp hφ.tendsto_atTop) (hc 0 0 n)
  refine ⟨φ, c 1 1, M w, hφ, hc 1 1, pairSpectrum_basis c M hM 1, ?_⟩
  intro A hA
  have heqA := combinationMeasure_apply_of_null M (integerCorrelation c) hM (v-w) w A hA
  rw [sub_add_cancel] at heqA
  have hcorr := pairSpectrum_combination c M hc hM (v-w)
  change CorrLimits (sequenceCombination (pairSequences x y) (baseVector 0 - baseVector 1))
    (sequenceCombination (pairSequences x y) (baseVector 0 - baseVector 1)) (N ∘ φ) _ at hcorr
  rw [pairSequences_combo_sub] at hcorr
  have hRe := (Complex.continuous_re.tendsto _).comp (hcorr 0)
  simp only [Function.comp_def, re_corr_zero, Int.natCast_zero, measureFourier_zero,
    Complex.ofReal_re] at hRe
  rw [heq, Measure.real, heqA]
  have hbound : (M (v-w) : Measure UnitAddCircle).real Set.univ ≤ ε :=
    le_of_tendsto hRe (hp.strictMono.tendsto_atTop.eventually hdist)
  exact (measureReal_mono (Set.subset_univ A)).trans hbound

/-- Closure under limits in upper Cesàro mean square. The stated eventual
bound follows by taking any smaller approximation error in a limsup version. -/
theorem spectrallyLebesgue_of_meanSquare_approximation {x : ℕ → ℂ} (hx : BoundedSeq x)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ y : ℕ → ℂ, SpectrallyLebesgue y ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖x n - y n‖ ^ 2) N ≤ ε) :
    SpectrallyLebesgue x := by
  refine ⟨hx, ?_⟩
  intro N r hN hr
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hx hN hr
  refine ⟨μ, hμ, ?_⟩
  intro A hA
  have hsmall (ε : ℝ) (hε : 0 < ε) : (μ : Measure UnitAddCircle).real A ≤ ε := by
    obtain ⟨y, hy, hdist⟩ := happrox ε hε
    obtain ⟨φ, ry, ν, hφ, hry, hν, hcomp⟩ :=
      coupled_spectrum_error hx hy.1 hN hr μ hμ hdist
    obtain ⟨ν', hν', hac⟩ := hy.2 (N ∘ φ) ry (hN.comp hφ) hry
    have hEq : (ν : Measure UnitAddCircle) = ν' :=
      measure_eq_of_fourier_nat fun n => (hν n).trans (hν' n).symm
    apply hcomp A
    rw [hEq]
    exact hac hA
  have hz : (μ : Measure UnitAddCircle).real A = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra! hh
    have hp : 0 < (μ : Measure UnitAddCircle).real A := hh
    have hbound := hsmall ((μ : Measure UnitAddCircle).real A / 2) (div_pos hp (by norm_num))
    linarith only [hp, hbound]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz

/-- Closure of spectrally singular sequences under upper Cesàro
mean-square approximation, using the union of the approximants'
null-Haar supporting sets. -/
theorem spectrallySingular_of_meanSquare_approximation {x : ℕ → ℂ} (hx : BoundedSeq x)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ y : ℕ → ℂ, SpectrallySingular y ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖x n - y n‖ ^ 2) N ≤ ε) :
    SpectrallySingular x := by
  refine ⟨hx, ?_⟩
  intro N r hN hr
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hx hN hr
  refine ⟨μ, hμ, ?_⟩
  let δ (k : ℕ) : ℝ := (((k + 1 : ℕ) : ℝ))⁻¹
  have hs (k : ℕ) : ∃ A : Set UnitAddCircle, MeasurableSet A ∧ circleHaar A = 0 ∧
      (μ : Measure UnitAddCircle).real Aᶜ ≤ δ k := by
    obtain ⟨y, hy, hdist⟩ := happrox (δ k) (by dsimp [δ]; positivity)
    obtain ⟨φ, ry, ν, hφ, hry, hν, hcomp⟩ :=
      coupled_spectrum_error hx hy.1 hN hr μ hμ hdist
    obtain ⟨ν', hν', hsing⟩ := hy.2 (N ∘ φ) ry (hN.comp hφ) hry
    have hEq : (ν : Measure UnitAddCircle) = ν' :=
      measure_eq_of_fourier_nat fun n => (hν n).trans (hν' n).symm
    obtain ⟨A, hA, hνA, hHA⟩ := hsing
    refine ⟨Aᶜ, hA.compl, hHA, ?_⟩
    rw [compl_compl]
    exact hcomp A (hEq.symm ▸ hνA)
  choose A hA hH hmass using hs
  let U := ⋃ k, A k
  have hbound (k : ℕ) : (μ : Measure UnitAddCircle).real Uᶜ ≤ δ k :=
    (measureReal_mono (Set.compl_subset_compl.mpr (Set.subset_iUnion A k))).trans (hmass k)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hcast := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [δ, Function.comp_def] using tendsto_inv_atTop_zero.comp hcast
  have hzero : (μ : Measure UnitAddCircle).real Uᶜ = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto tendsto_const_nhds hδ (Eventually.of_forall hbound))
      ENNReal.toReal_nonneg
  refine ⟨Uᶜ, (MeasurableSet.iUnion hA).compl,
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hzero, ?_⟩
  simpa only [compl_compl] using measure_iUnion_null hH

end

end VdC

end

end VdC_SpectralResults_Module

/- Source: VdC/Applications.lean -/
section VdC_Applications_Module

/-! # Applications -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

section

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

def SpectrallyLebesgueDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → SpectrallyLebesgue (fun n => f (x n))

def WeaklyMixingDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → NearlyWeakMixing (fun n => f (x n))

def SpectrallySingularDistribution (y : ℕ → Y) : Prop :=
  ∀ g : C(Y, ℂ), SpectrallySingular (fun n => g (y n))

def CompactDistribution (y : ℕ → Y) : Prop :=
  ∀ g : C(Y, ℂ), CompactSeq (fun n => g (y n))

theorem WeaklyMixingDistribution.equidistributed (μ : Measure X) [IsProbabilityMeasure μ]
    {x : ℕ → X} (hx : WeaklyMixingDistribution μ x) : Equidistributed μ x :=
  equidistributed_of_centered_tests μ x fun f hf => (hx f hf).cesaro_zero

omit [BorelSpace X] [CompactSpace X] in
theorem SpectrallyLebesgueDistribution.weaklyMixing (μ : Measure X) {x : ℕ → X}
    (hx : SpectrallyLebesgueDistribution μ x) : WeaklyMixingDistribution μ x :=
  fun f hf => (hx f hf).nearlyWeakMixing

omit [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
theorem CompactDistribution.spectrallySingular {y : ℕ → Y} (hy : CompactDistribution y) :
    SpectrallySingularDistribution y := fun g => spectrallySingular_of_compactSeq (hy g)

/-- PropertiesOfsLSequences(i), singular-indicator version. -/
theorem equidistributed_selected_of_sl_singular (μ : Measure X) [IsProbabilityMeasure μ]
    {x : ℕ → X} (hx : SpectrallyLebesgueDistribution μ x) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hd : HasPositiveLowerDensity (Set.range σ)) (hc : SpectrallySingular (selectionWeight (Set.range σ))) :
    Equidistributed μ (x ∘ σ) := by
  apply equidistributed_of_centered_tests
  intro f hf
  change Tendsto (cesaro fun k => f (x (σ k))) atTop (𝓝 0)
  exact tendsto_cesaro_selected_zero (fun n => f (x n)) hσ hd
    (cesaro_product_tendsto_zero_of_ac_singular (hx f hf) hc)

/-- PropertiesOfsLSequences(i), compact-indicator version. -/
theorem equidistributed_selected_of_wm_compact (μ : Measure X) [IsProbabilityMeasure μ]
    {x : ℕ → X} (hx : WeaklyMixingDistribution μ x) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (hd : HasPositiveLowerDensity (Set.range σ)) (hc : CompactSeq (selectionWeight (Set.range σ))) :
    Equidistributed μ (x ∘ σ) := by
  apply equidistributed_of_centered_tests
  intro f hf
  change Tendsto (cesaro fun k => f (x (σ k))) atTop (𝓝 0)
  exact tendsto_cesaro_selected_zero (fun n => f (x n)) hσ hd
    (nearlyWeakMixing_mul_compact (hx f hf) hc)

/-- PropertiesOfsLSequences(ii), compact second factor. -/
theorem equidistributed_pair_of_wm_compact [T2Space X] [T2Space Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {x : ℕ → X} {y : ℕ → Y} (hx : WeaklyMixingDistribution μ x)
    (hy : Equidistributed ν y) (hc : CompactDistribution y) :
    Equidistributed (μ.prod ν) (fun n => (x n, y n)) := by
  apply (equidistributed_prod_iff μ ν x y).2
  apply product_means_of_centered_tests μ ν x y (hx.equidistributed μ) hy
  intro f g hf _
  exact nearlyWeakMixing_mul_compact (hx f hf) (hc g)

/-- PropertiesOfsLSequences(ii), spectrally singular second factor. -/
theorem equidistributed_pair_of_sl_singular [T2Space X] [T2Space Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {x : ℕ → X} {y : ℕ → Y} (hx : SpectrallyLebesgueDistribution μ x)
    (hy : Equidistributed ν y) (hc : SpectrallySingularDistribution y) :
    Equidistributed (μ.prod ν) (fun n => (x n, y n)) := by
  apply (equidistributed_prod_iff μ ν x y).2
  apply product_means_of_centered_tests μ ν x y ((hx.weaklyMixing μ).equidistributed μ) hy
  intro f g hf _
  exact cesaro_product_tendsto_zero_of_ac_singular (hx f hf) (hc g)

end

noncomputable section

/-- The classical difference theorem, using Haar uniform distribution. -/
theorem equidistributed_of_torus_differences {d : ℕ} (x : ℕ → Torus d)
    (h : ∀ h : ℕ, 0 < h → Equidistributed (torusHaar d) (fun n => x (n + h) - x n)) :
    Equidistributed (torusHaar d) x := by
  apply (equidistributed_torus_iff x).2
  intro m hm
  apply NearlyOrthogonal.tendsto_cesaro_zero
  apply (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test (torusCharacter m) x)).2
  intro k hk
  change Tendsto (cesaro fun n => torusCharacter m (x (n + k)) * star (torusCharacter m (x n))) atTop (𝓝 0)
  simpa only [torusCharacter_point_sub] using
    (equidistributed_torus_iff _).1 (h k hk) m hm

/-- The modulo-one sum corollary for a weakly mixing and a compact distribution. -/
theorem equidistributed_torus_add_of_wm_compact {d : ℕ} {x y : ℕ → Torus d}
    (hx : WeaklyMixingDistribution (torusHaar d) x) (hy : CompactDistribution y) :
    Equidistributed (torusHaar d) (fun n => x n + y n) := by
  apply (equidistributed_torus_iff _).2
  intro m hm
  have h0 : testMean (torusHaar d) (torusCharacter m) = 0 := by simp [testMean_torusCharacter, hm]
  simpa only [torusCharacter_point_add, id_eq] using nearlyWeakMixing_mul_compact (hx _ h0) (hy (torusCharacter m))

/-- The modulo-one sum corollary for absolutely continuous and singular spectra. -/
theorem equidistributed_torus_add_of_sl_singular {d : ℕ} {x y : ℕ → Torus d}
    (hx : SpectrallyLebesgueDistribution (torusHaar d) x) (hy : SpectrallySingularDistribution y) :
    Equidistributed (torusHaar d) (fun n => x n + y n) := by
  apply (equidistributed_torus_iff _).2
  intro m hm
  have h0 : testMean (torusHaar d) (torusCharacter m) = 0 := by simp [testMean_torusCharacter, hm]
  simpa only [torusCharacter_point_add] using
    cesaro_product_tendsto_zero_of_ac_singular (hx _ h0) (hy (torusCharacter m))

end
end VdC

end

end VdC_Applications_Module

/- Source: VdC/BoundedPET.lean -/
section VdC_BoundedPET_Module

/-! # Bounded PET -/

@[expose] public section

open Filter Finset Function MeasureTheory Set
open scoped Topology BigOperators

namespace VdC

section

variable {X : Type*} [MeasurableSpace X]

private def orbitMax (T : X → X) (g : X → ℝ) : ℕ → X → ℝ
  | 0, _ => 0
  | n+1, x => max 0 (g x + orbitMax T g n (T x))

omit [MeasurableSpace X] in
private theorem orbitMax_nonneg (T : X → X) (g : X → ℝ) (n : ℕ) (x : X) :
    0 ≤ orbitMax T g n x := by cases n <;> simp [orbitMax]

omit [MeasurableSpace X] in
private theorem orbitMax_monotone (T : X → X) (g : X → ℝ) (x : X) :
    Monotone (fun n => orbitMax T g n x) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing x with
  | zero => exact orbitMax_nonneg T g _ _
  | succ n ih =>
    simp only [orbitMax]
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

private theorem orbitMax_measurable {T : X → X} {g : X → ℝ} (hT : Measurable T)
    (hg : Measurable g) (n : ℕ) : Measurable (orbitMax T g n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hg.add (ih.comp hT))

omit [MeasurableSpace X] in
private theorem orbitMax_le {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, |g x| ≤ C) (n : ℕ) (x : X) : orbitMax T g n x ≤ (n : ℝ)*C := by
  induction n generalizing x with
  | zero => simp [orbitMax]
  | succ n ih =>
    rw [orbitMax, Nat.cast_succ]
    refine max_le (by positivity) ?_
    have hb := (abs_le.mp (hg x)).2
    have hi := ih (T x)
    linarith only [hb, hi]

omit [MeasurableSpace X] in
private theorem orbit_sum_le_max (T : X → X) (g : X → ℝ) (n : ℕ) (x : X) :
    ∑ i ∈ range n, g (T^[i] x) ≤ orbitMax T g n x := by
  induction n generalizing x with
  | zero => simp [orbitMax]
  | succ n ih =>
    rw [Finset.sum_range_succ', orbitMax]
    simp only [iterate_zero_apply, iterate_succ_apply]
    refine le_trans ?_ (le_max_right _ _)
    linarith only [ih (T x)]

private theorem integrable_real_bounded {μ : Measure X} [IsFiniteMeasure μ] {g : X → ℝ}
    (hg : Measurable g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) : Integrable g μ := by
  refine Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun x => ?_)
  simpa only [Real.norm_eq_abs] using hb x

/-- The maximal ergodic inequality for a bounded real observable. The set in
the integral consists of the points where a running maximum of partial sums is positive. -/
private theorem maximal_orbit_integral_nonneg {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) {g : X → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) :
    0 ≤ ∫ x, (⋃ n : ℕ, {x | 0 < orbitMax T g n x}).indicator g x ∂μ := by
  classical
  let E (n : ℕ) : Set X := {x | 0 < orbitMax T g n x}
  have hEm (n : ℕ) : MeasurableSet (E n) := measurableSet_lt measurable_const (orbitMax_measurable hT.measurable hg n)
  have hEmono : Monotone E := fun a b hab x hx => hx.trans_le (orbitMax_monotone T g x hab)
  have hpoint (n : ℕ) (x : X) : orbitMax T g n x - orbitMax T g n (T x) ≤ (E n).indicator g x := by
    by_cases hx : x ∈ E n
    · rw [Set.indicator_of_mem hx]
      cases n with
      | zero => simp [E, orbitMax] at hx
      | succ n =>
        have hp : 0 < max 0 (g x + orbitMax T g n (T x)) := hx
        have hp' : 0 ≤ g x + orbitMax T g n (T x) := by
          by_contra! hn
          simp only [max_eq_left hn.le, lt_self_iff_false] at hp
        rw [orbitMax, max_eq_right hp']
        have hh := orbitMax_monotone T g (T x) (Nat.le_succ n)
        linarith only [hh]
    · rw [Set.indicator_of_notMem hx]
      have hn : orbitMax T g n x = 0 := le_antisymm (le_of_not_gt hx) (orbitMax_nonneg T g n x)
      rw [hn, zero_sub]
      exact neg_nonpos.mpr (orbitMax_nonneg T g n (T x))
  have hfinite (n : ℕ) : 0 ≤ ∫ x, (E n).indicator g x ∂μ := by
    have hMax : Integrable (orbitMax T g n) μ := by
      apply integrable_real_bounded (orbitMax_measurable hT.measurable hg n)
      intro x
      rw [abs_of_nonneg (orbitMax_nonneg T g n x)]
      exact orbitMax_le hC hb n x
    have hMaxT : Integrable (fun x => orbitMax T g n (T x)) μ := by
      apply integrable_real_bounded ((orbitMax_measurable hT.measurable hg n).comp hT.measurable)
      intro x
      change |orbitMax T g n (T x)| ≤ _
      rw [abs_of_nonneg (orbitMax_nonneg T g n (T x))]
      exact orbitMax_le hC hb n (T x)
    have hsame : (∫ x, orbitMax T g n (T x) ∂μ) = ∫ x, orbitMax T g n x ∂μ := by
      rw [← integral_map_of_stronglyMeasurable hT.measurable (orbitMax_measurable hT.measurable hg n).stronglyMeasurable,
        hT.map_eq]
    have h := integral_mono (hMax.sub hMaxT) ((integrable_real_bounded hg hb).indicator (hEm n)) (hpoint n)
    change (∫ x, orbitMax T g n x - orbitMax T g n (T x) ∂μ) ≤ ∫ x, (E n).indicator g x ∂μ at h
    rwa [integral_sub hMax hMaxT, hsame, sub_self] at h
  let U := ⋃ n, E n
  have hU : MeasurableSet U := MeasurableSet.iUnion hEm
  have ht : Tendsto (fun n => ∫ x, (E n).indicator g x ∂μ) atTop (𝓝 (∫ x, U.indicator g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hg.indicator (hEm n)).aestronglyMeasurable)
      (integrable_const _) ?_ ?_
    · intro n
      exact ae_of_all _ fun x => by
        by_cases hx : x ∈ E n
        · simpa only [Set.indicator_of_mem hx, Real.norm_eq_abs] using hb x
        · simpa only [Set.indicator_of_notMem hx, norm_zero] using hC
    · apply ae_of_all
      intro x
      have H : (fun n => (E n).indicator g x) =ᶠ[atTop] (fun _ => U.indicator g x) := by
        by_cases hx : x ∈ U
        · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
          filter_upwards [eventually_ge_atTop n] with k hk
          rw [Set.indicator_of_mem (hEmono hk hn), Set.indicator_of_mem hx]
        · exact Eventually.of_forall fun n => by
            have hn : x ∉ E n := fun h => hx (Set.mem_iUnion.mpr ⟨n,h⟩)
            simp only [Set.indicator_of_notMem hn, Set.indicator_of_notMem hx]
      exact tendsto_const_nhds.congr' H.symm
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hfinite)

private noncomputable def orbitRealAvg (T : X → X) (g : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  realCesaro (fun n => g (T^[n] x)) N

omit [MeasurableSpace X] in
private theorem orbitRealAvg_abs_le {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |g x| ≤ C) (x : X) (N : ℕ) : |orbitRealAvg T g N x| ≤ C := by
  by_cases hN : N = 0
  · simpa [orbitRealAvg, realCesaro, hN] using hC
  apply abs_le.mpr
  have hN' : 0 < N := Nat.pos_of_ne_zero hN
  exact ⟨(realCesaro_const_pos (-C) hN').symm.le.trans
      (realCesaro_mono (fun n => (abs_le.mp (hb (T^[n] x))).1) N),
    (realCesaro_mono (fun n => (abs_le.mp (hb (T^[n] x))).2) N).trans_eq (realCesaro_const_pos C hN')⟩

omit [MeasurableSpace X] in
private theorem orbitRealAvg_bddAbove {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |g x| ≤ C) (x : X) : atTop.IsBoundedUnder (· ≤ ·) (fun N => orbitRealAvg T g N x) :=
  isBoundedUnder_of_eventually_le (a := C) (Eventually.of_forall fun N => (abs_le.mp (orbitRealAvg_abs_le hC hb x N)).2)

omit [MeasurableSpace X] in
private theorem orbitRealAvg_cobdd {T : X → X} {g : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, |g x| ≤ C) (x : X) : atTop.IsCoboundedUnder (· ≤ ·) (fun N => orbitRealAvg T g N x) :=
  isCoboundedUnder_le_of_le _ (fun N => (abs_le.mp (orbitRealAvg_abs_le hC hb x N)).1)

private theorem limsup_le_of_tendsto_sub_zero {u v : ℕ → ℝ}
    (hu : atTop.IsCoboundedUnder (· ≤ ·) u) (hv : atTop.IsBoundedUnder (· ≤ ·) v)
    (h : Tendsto (fun n => u n - v n) atTop (𝓝 0)) : limsup u atTop ≤ limsup v atTop := by
  by_contra! hbad
  let δ := (limsup u atTop - limsup v atTop) / 3
  have hd : 0 < δ := by dsimp [δ]; linarith only [hbad]
  have he1 := h.eventually (gt_mem_nhds hd)
  have he2 := eventually_lt_add_pos_of_limsup_le hv (le_refl (limsup v atTop)) hd
  have hle : limsup u atTop ≤ limsup v atTop + 2*δ := by
    apply limsup_le_of_le hu
    filter_upwards [he1, he2] with n hn hn'
    linarith only [hn, hn']
  dsimp [δ] at hle
  linarith only [hbad, hle]

omit [MeasurableSpace X] in
private theorem limsup_orbitRealAvg_invariant {T : X → X} {g : X → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) (x : X) :
    limsup (fun N => orbitRealAvg T g N (T x)) atTop = limsup (fun N => orbitRealAvg T g N x) atTop := by
  have h := tendsto_realCesaro_shift_sub_zero hC (fun n => hb (T^[n] x)) 1
  have hshift : Tendsto (fun N => orbitRealAvg T g N (T x) - orbitRealAvg T g N x) atTop (𝓝 0) := by
    simpa only [orbitRealAvg, Nat.succ_eq_add_one, iterate_succ_apply] using h
  have hshift' : Tendsto (fun N => orbitRealAvg T g N x - orbitRealAvg T g N (T x)) atTop (𝓝 0) := by
    simpa only [neg_sub, neg_zero] using hshift.neg
  exact le_antisymm (limsup_le_of_tendsto_sub_zero (orbitRealAvg_cobdd hC hb (T x))
    (orbitRealAvg_bddAbove hC hb x) hshift) (limsup_le_of_tendsto_sub_zero
      (orbitRealAvg_cobdd hC hb x) (orbitRealAvg_bddAbove hC hb (T x)) hshift')

private theorem ae_limsup_orbitRealAvg_le {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, limsup (fun N => orbitRealAvg T g N x) atTop ≤ ∫ y, g y ∂μ := by
  classical
  let m := ∫ y, g y ∂μ
  let U (x : X) := limsup (fun N => orbitRealAvg T g N x) atTop
  have hm (N : ℕ) : Measurable (orbitRealAvg T g N) := by
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun n _ => hg.comp (hT.measurable.iterate n))
  have hU : Measurable U := Measurable.limsup hm
  have hUpper (q : ℚ) : ∀ᵐ x ∂μ, m < (q : ℝ) → U x ≤ q := by
    by_cases hq : m < (q : ℝ)
    · let B : Set X := {x | (q : ℝ) < U x}
      have hBm : MeasurableSet B := measurableSet_lt measurable_const hU
      have hBInv : T ⁻¹' B = B := by
        ext x
        change (q : ℝ) < U (T x) ↔ (q : ℝ) < U x
        rw [show U (T x) = U x from limsup_orbitRealAvg_invariant hC hb x]
      rcases hT.toPreErgodic.ae_mem_or_ae_notMem hBm.nullMeasurableSet
        (Eventually.of_forall fun x => by simp only [hBInv]) with hFull | hFail
      · exfalso
        let g' (x : X) := g x - (q : ℝ)
        have hg' : Measurable g' := hg.sub_const _
        have hb' (x : X) : |g' x| ≤ C + |(q : ℝ)| := (abs_sub _ _).trans (add_le_add (hb x) le_rfl)
        let E : Set X := ⋃ n : ℕ, {x | 0 < orbitMax T g' n x}
        have hSub : ∀ᵐ x ∂μ, x ∈ E := by
          filter_upwards [hFull] with x hx
          have hx' : (q : ℝ) < limsup (fun N => orbitRealAvg T g N x) atTop := hx
          have hv : ∃ᶠ N : ℕ in atTop, (q : ℝ) < orbitRealAvg T g N x := by
            by_contra h
            have he : ∀ᶠ N : ℕ in atTop, orbitRealAvg T g N x ≤ q := by
              simpa only [Filter.not_frequently, not_lt] using h
            exact hx'.not_ge (limsup_le_of_le (orbitRealAvg_cobdd hC hb x) he)
          obtain ⟨N, hn, hn'⟩ := ((eventually_gt_atTop (0 : ℕ)).and_frequently hv).exists
          have hN : 0 < (N : ℝ) := by exact_mod_cast hn
          have hsum : (q : ℝ) * N < ∑ n ∈ range N, g (T^[n] x) := (lt_div_iff₀ hN).mp hn'
          have hsum' : 0 < ∑ n ∈ range N, g' (T^[n] x) := by
            simp only [g', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            linarith only [hsum]
          exact Set.mem_iUnion.mpr ⟨N, hsum'.trans_le (orbit_sum_le_max T g' N x)⟩
        have ha : 0 ≤ ∫ x, E.indicator g' x ∂μ := maximal_orbit_integral_nonneg hT.toMeasurePreserving hg' (by positivity) hb'
        have hEq : (∫ x, E.indicator g' x ∂μ) = m - q := by
          rw [integral_congr_ae (hSub.mono fun x hx => Set.indicator_of_mem hx g')]
          exact integral_sub (integrable_real_bounded hg hb) (integrable_const _) |>.trans (by simp [m])
        rw [hEq] at ha
        linarith only [ha, hq]
      · exact hFail.mono fun x h => fun _ => le_of_not_gt h
    · exact Eventually.of_forall fun _ hm => False.elim (hq hm)
  filter_upwards [ae_all_iff.mpr hUpper] with x hx
  change U x ≤ m
  by_contra! H
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn H
  exact hq'.not_ge (hx q hq)

/-- Bounded-observable pointwise ergodic theorem, real form. -/
theorem ae_tendsto_orbitCesaro_real {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun N => realCesaro (fun n => g (T^[n] x)) N) atTop (𝓝 (∫ y, g y ∂μ)) := by
  have hb' : ∀ x, |(-g) x| ≤ C := fun x => by simpa only [Pi.neg_apply, abs_neg] using hb x
  filter_upwards [ae_limsup_orbitRealAvg_le hT hg hC hb, ae_limsup_orbitRealAvg_le hT hg.neg hC hb'] with x h1 h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_lt_add_pos_of_limsup_le (orbitRealAvg_bddAbove hC hb x) h1 hε,
    eventually_lt_add_pos_of_limsup_le (orbitRealAvg_bddAbove hC hb' x) h2 hε] with N hn hn'
  have he : orbitRealAvg T (-g) N x = -(orbitRealAvg T g N x) := by
    simp only [orbitRealAvg, realCesaro, Pi.neg_apply, sum_neg_distrib, neg_div]
  rw [he] at hn'
  simp only [Pi.neg_apply, integral_neg] at hn'
  rw [Real.dist_eq, abs_lt]
  change -ε < orbitRealAvg T g N x - (∫ y, g y ∂μ) ∧ orbitRealAvg T g N x - (∫ y, g y ∂μ) < ε
  constructor <;> linarith only [hn, hn']

/-- Bounded-observable pointwise ergodic theorem, complex form. -/
theorem ae_tendsto_orbitCesaro {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {g : X → ℂ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖g x‖ ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (cesaro (fun n => g (T^[n] x))) atTop (𝓝 (∫ y, g y ∂μ)) := by
  have hi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall hb)
  have hRe := ae_tendsto_orbitCesaro_real hT (Complex.continuous_re.measurable.comp hg) hC
    (fun x => (Complex.abs_re_le_norm (g x)).trans (hb x))
  have hIm := ae_tendsto_orbitCesaro_real hT (Complex.continuous_im.measurable.comp hg) hC
    (fun x => (Complex.abs_im_le_norm (g x)).trans (hb x))
  filter_upwards [hRe, hIm] with x hre him
  change Tendsto (fun N => realCesaro (fun n => (g (T^[n] x)).re) N) atTop
    (𝓝 (∫ y, (g y).re ∂μ)) at hre
  change Tendsto (fun N => realCesaro (fun n => (g (T^[n] x)).im) N) atTop
    (𝓝 (∫ y, (g y).im ∂μ)) at him
  have hIR : (∫ y, (g y).re ∂μ) = (∫ y, g y ∂μ).re := integral_re hi
  have hII : (∫ y, (g y).im ∂μ) = (∫ y, g y ∂μ).im := integral_im hi
  simp only [realCesaro_re, hIR] at hre
  have hm (u : ℕ → ℂ) (N : ℕ) : realCesaro (fun n => (u n).im) N = (cesaro u N).im := by
    unfold cesaro realCesaro
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.im_sum]
  simp only [hm, hII] at him
  have hr' := Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have hi' := (Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul_const Complex.I
  simpa only [Function.comp_def, Complex.re_add_im] using hr'.add hi'

end
end VdC

end

end VdC_BoundedPET_Module

/- Source: VdC/CompactClosure.lean -/
section VdC_CompactClosure_Module

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

end

end VdC_CompactClosure_Module

/- Source: VdC/Cube.lean -/
section VdC_Cube_Module

/-! # Cube -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace VdC

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev UnitInterval := Set.Icc (0 : ℝ) 1
abbrev Cube (d : ℕ) := Fin d → UnitInterval

/-- Lebesgue measure pulled back to the closed unit interval. -/
noncomputable def unitIntervalLebesgue : Measure UnitInterval :=
  Measure.comap ((↑) : UnitInterval → ℝ) volume

instance unitIntervalLebesgue_probability : IsProbabilityMeasure unitIntervalLebesgue := by
  constructor
  rw [unitIntervalLebesgue, comap_subtype_coe_apply measurableSet_Icc, Set.image_univ,
    Subtype.range_coe, Real.volume_Icc]
  simp

noncomputable def cubeLebesgue (d : ℕ) : Measure (Cube d) :=
  Measure.pi fun _ => unitIntervalLebesgue

instance cubeLebesgue_probability (d : ℕ) : IsProbabilityMeasure (cubeLebesgue d) := by
  unfold cubeLebesgue
  infer_instance

/-- The `o`-sequence characterization on the paper's actual closed cube.
The lag-pair measure is the product of two copies of cube Lebesgue measure. -/
theorem cube_orthogonal_iff_lag_pairs {d : ℕ} (x : ℕ → Cube d) :
    OrthogonalDistribution (cubeLebesgue d) x ↔ ∀ h : ℕ, 0 < h →
      Equidistributed ((cubeLebesgue d).prod (cubeLebesgue d)) (fun n => (x n, x (n+h))) :=
  orthogonalDistribution_iff_lag_pairs (cubeLebesgue d) x

def cubeToTorus {d : ℕ} (x : Cube d) : Torus d := fun i => ((x i : ℝ) : UnitAddCircle)

theorem continuous_cubeToTorus (d : ℕ) : Continuous (cubeToTorus (d := d)) := by
  exact continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_subtype_val.comp (continuous_apply i))

private theorem map_unitIntervalLebesgue :
    unitIntervalLebesgue.map (fun x : UnitInterval => ((x : ℝ) : UnitAddCircle)) = circleHaar := by
  have hq := UnitAddCircle.measurePreserving_mk 0
  rw [show (fun x : UnitInterval => ((x : ℝ) : UnitAddCircle)) =
      (((↑) : ℝ → UnitAddCircle) ∘ ((↑) : UnitInterval → ℝ)) from rfl,
    ← Measure.map_map hq.measurable measurable_subtype_coe, unitIntervalLebesgue,
    map_comap_subtype_coe measurableSet_Icc, ← restrict_Ioc_eq_restrict_Icc]
  have h : (volume : Measure UnitAddCircle) = circleHaar := by
    simpa [circleHaar] using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  simpa only [zero_add, h] using hq.map_eq

theorem cubeToTorus_measurePreserving (d : ℕ) :
    MeasurePreserving (cubeToTorus (d := d)) (cubeLebesgue d) (torusHaar d) := by
  refine ⟨(continuous_cubeToTorus d).measurable, ?_⟩
  let f (_ : Fin d) (x : UnitInterval) := ((x : ℝ) : UnitAddCircle)
  have hσ : ∀ i : Fin d, SigmaFinite (unitIntervalLebesgue.map (f i)) := by
    intro i
    rw [show f i = (fun x : UnitInterval => ((x : ℝ) : UnitAddCircle)) from rfl, map_unitIntervalLebesgue]
    infer_instance
  change (Measure.pi fun _ : Fin d => unitIntervalLebesgue).map (fun x i => f i (x i)) = _
  rw [Measure.pi_map_pi (μ := fun _ : Fin d => unitIntervalLebesgue) (hμ := hσ)]
  · simp only [f, map_unitIntervalLebesgue, torusHaar]
  · intro i
    exact ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val).measurable.aemeasurable

/-- Continuous-test uniform distribution on the cube descends to the torus. -/
theorem equidistributed_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (cubeLebesgue d) x) :
    Equidistributed (torusHaar d) (fun n => cubeToTorus (x n)) := by
  intro f
  let g : C(Cube d, ℂ) := f.comp ⟨cubeToTorus, continuous_cubeToTorus d⟩
  have hg : testMean (cubeLebesgue d) g = testMean (torusHaar d) f := by
    unfold testMean
    rw [← (cubeToTorus_measurePreserving d).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable f.continuous.stronglyMeasurable]
    rfl
  exact hg ▸ hx g

def CubeInterior {d : ℕ} (x : Cube d) : Prop :=
  ∀ i : Fin d, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1

theorem cubeToTorus_surjective (d : ℕ) : Function.Surjective (cubeToTorus (d := d)) := by
  intro y
  let f (i : Fin d) := AddCircle.equivIco (1 : ℝ) 0 (y i)
  exact ⟨fun i => ⟨f i, (f i).2.1, by simpa using (f i).2.2.le⟩,
    funext fun i => AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := y i)⟩

private theorem cubeToTorus_eq_of_interior {d : ℕ} {x y : Cube d} (hx : CubeInterior x)
    (h : cubeToTorus x = cubeToTorus y) : x = y := by
  funext i
  apply Subtype.ext
  have he : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
  by_cases hy : 0 < (y i : ℝ)
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := (1 : ℝ)) (a := 0)
      ⟨(hx i).1, by simpa using (x i).2.2⟩ ⟨hy, by simpa using (y i).2.2⟩).mp he
  have hy' : (y i : ℝ) = 0 := le_antisymm (le_of_not_gt hy) (y i).2.1
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨(x i).2.1, by simpa using (hx i).2⟩ ⟨(y i).2.1, by simp [hy']⟩).mp he

/-- Continuous boundary cutoff, increasing to one at every interior point. -/
noncomputable def cubeCutoff {d : ℕ} (K : ℕ) (x : Cube d) : ℝ :=
  ∏ i : Fin d, min 1 ((K : ℝ) * min (x i : ℝ) (1 - (x i : ℝ)))

theorem cubeCutoff_nonneg {d : ℕ} (K : ℕ) (x : Cube d) : 0 ≤ cubeCutoff K x := by
  unfold cubeCutoff
  apply Finset.prod_nonneg
  intro i _
  exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg K) (le_min (x i).2.1 (sub_nonneg.mpr (x i).2.2)))

theorem cubeCutoff_le_one {d : ℕ} (K : ℕ) (x : Cube d) : cubeCutoff K x ≤ 1 := by
  have hp : (∏ i : Fin d, min 1 ((K : ℝ) * min (x i : ℝ) (1 - (x i : ℝ)))) ≤ ∏ _i : Fin d, (1 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg K) (le_min (x i).2.1 (sub_nonneg.mpr (x i).2.2)))
    · intro i _
      exact min_le_left _ _
  simpa only [cubeCutoff, Finset.prod_const_one] using hp

theorem continuous_cubeCutoff {d : ℕ} (K : ℕ) : Continuous (cubeCutoff (d := d) K) := by
  apply continuous_finsetProd
  intro i _
  have hi : Continuous (fun x : Cube d => (x i : ℝ)) := continuous_subtype_val.comp (continuous_apply i)
  exact continuous_const.min ((hi.min (continuous_const.sub hi)).const_mul _)

theorem cubeCutoff_eq_zero_of_boundary {d : ℕ} (K : ℕ) {x : Cube d} (hx : ¬ CubeInterior x) :
    cubeCutoff K x = 0 := by
  unfold CubeInterior at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  have he : (x i : ℝ) = 0 ∨ (x i : ℝ) = 1 := by
    by_cases h0 : 0 < (x i : ℝ)
    · right
      exact le_antisymm (x i).2.2 (hi h0)
    · left
      exact le_antisymm (le_of_not_gt h0) (x i).2.1
  unfold cubeCutoff
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases he with h | h <;> simp [h]

theorem cubeCutoff_eventually_one {d : ℕ} {x : Cube d} (hx : CubeInterior x) :
    ∀ᶠ K : ℕ in atTop, cubeCutoff K x = 1 := by
  have hk : ∀ i : Fin d, ∀ᶠ K : ℕ in atTop, 1 ≤ (K : ℝ) * min (x i : ℝ) (1 - (x i : ℝ)) := by
    intro i
    have hd : 0 < min (x i : ℝ) (1 - (x i : ℝ)) := lt_min (hx i).1 (sub_pos.mpr (hx i).2)
    obtain ⟨K, hK⟩ := exists_nat_ge (1 / min (x i : ℝ) (1 - (x i : ℝ)))
    filter_upwards [eventually_ge_atTop K] with n hn
    exact (div_le_iff₀ hd).mp (hK.trans (by exact_mod_cast hn))
  filter_upwards [eventually_all.mpr hk] with K hK
  apply Finset.prod_eq_one
  intro i _
  exact min_eq_left (hK i)

theorem ae_cubeInterior (d : ℕ) : ∀ᵐ x ∂cubeLebesgue d, CubeInterior x := by
  have h1 : ∀ᵐ (x : UnitInterval) ∂unitIntervalLebesgue, 0 < (x : ℝ) ∧ (x : ℝ) < 1 := by
    apply (ae_restrict_iff_subtype (μ := (volume : Measure ℝ))
      (p := fun x : ℝ => 0 < x ∧ x < 1) (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))).mp
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (μ := fun _ : Fin d => unitIntervalLebesgue) i).quasiMeasurePreserving.ae h1

noncomputable def cubeCutoffTest {d : ℕ} (K : ℕ) (f : C(Cube d, ℂ)) : C(Cube d, ℂ) :=
  ⟨fun x => f x * (cubeCutoff K x : ℂ), f.continuous.mul (Complex.continuous_ofReal.comp (continuous_cubeCutoff K))⟩

theorem exists_cubeCutoff_descend {d : ℕ} (K : ℕ) (f : C(Cube d, ℂ)) :
    ∃ g : C(Torus d, ℂ), ∀ x : Cube d, g (cubeToTorus x) = cubeCutoffTest K f x := by
  classical
  let u := cubeCutoffTest K f
  have hcompat {x y : Cube d} (h : cubeToTorus x = cubeToTorus y) : u x = u y := by
    by_cases hx : CubeInterior x
    · rw [cubeToTorus_eq_of_interior hx h]
    have hy : ¬ CubeInterior y := fun hy => hx ((cubeToTorus_eq_of_interior hy h.symm).symm ▸ hy)
    simp only [u, cubeCutoffTest, ContinuousMap.coe_mk, cubeCutoff_eq_zero_of_boundary K hx,
      cubeCutoff_eq_zero_of_boundary K hy, Complex.ofReal_zero, mul_zero]
  let g : Torus d → ℂ := u ∘ Function.surjInv (cubeToTorus_surjective d)
  have hcomp (x : Cube d) : g (cubeToTorus x) = u x :=
    hcompat (Function.surjInv_eq (cubeToTorus_surjective d) (cubeToTorus x))
  have hq := Topology.IsQuotientMap.of_surjective_continuous (cubeToTorus_surjective d) (continuous_cubeToTorus d)
  have hcont : Continuous g := hq.continuous_iff.mpr (by simpa only [Function.comp_def, hcomp] using u.continuous)
  exact ⟨⟨g, hcont⟩, hcomp⟩

theorem tendsto_cutoffDeficit_integral (d : ℕ) :
    Tendsto (fun K : ℕ => ∫ x : Cube d, 1 - cubeCutoff K x ∂cubeLebesgue d) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := cubeLebesgue d) (F := fun K x => 1 - cubeCutoff K x) (f := fun _ => (0 : ℝ))
    (fun _ => 1) (fun K => (continuous_const.sub (continuous_cubeCutoff K)).aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro K
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (cubeCutoff_le_one K x))]
      exact sub_le_self _ (cubeCutoff_nonneg K x)
  · filter_upwards [ae_cubeInterior d] with x hx
    exact tendsto_const_nhds.congr' ((cubeCutoff_eventually_one hx).mono fun K hk => by simp [hk])

theorem norm_sub_cubeCutoffTest {d : ℕ} (K : ℕ) (f : C(Cube d, ℂ)) (x : Cube d) :
    ‖f x - cubeCutoffTest K f x‖ = ‖f x‖ * (1 - cubeCutoff K x) := by
  change ‖f x - f x * (cubeCutoff K x : ℂ)‖ = _
  rw [show f x - f x * (cubeCutoff K x : ℂ) = f x * ((1 - cubeCutoff K x : ℝ) : ℂ) by
    push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (cubeCutoff_le_one K x))]

theorem tendsto_testMean_cubeCutoffTest {d : ℕ} (f : C(Cube d, ℂ)) :
    Tendsto (fun K : ℕ => testMean (cubeLebesgue d) (cubeCutoffTest K f)) atTop
      (𝓝 (testMean (cubeLebesgue d) f)) := by
  apply tendsto_integral_of_dominated_convergence (bound := fun _ => ‖f‖)
  · exact fun K => (cubeCutoffTest K f).continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro K
    exact ae_of_all _ fun x => by
      change ‖f x * (cubeCutoff K x : ℂ)‖ ≤ ‖f‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cubeCutoff_nonneg K x)]
      exact (mul_le_of_le_one_right (norm_nonneg _) (cubeCutoff_le_one K x)).trans
        (ContinuousMap.norm_coe_le_norm f x)
  · filter_upwards [ae_cubeInterior d] with x hx
    exact tendsto_const_nhds.congr' ((cubeCutoff_eventually_one hx).mono fun K hk => by
      simp [cubeCutoffTest, hk])

theorem tendsto_cubeCutoffTest_l2 {d : ℕ} (f : C(Cube d, ℂ)) :
    Tendsto (fun K : ℕ => ∫ x : Cube d, ‖f x - cubeCutoffTest K f x‖ ^ 2 ∂cubeLebesgue d)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := cubeLebesgue d)
    (F := fun K x => ‖f x - cubeCutoffTest K f x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun _ => ‖f‖^2) (fun K => ((f.continuous.sub (cubeCutoffTest K f).continuous).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro K
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_sub_cubeCutoffTest]
      apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (cubeCutoff_le_one K x))) _ 2
      exact (mul_le_of_le_one_right (norm_nonneg _) (sub_le_self _ (cubeCutoff_nonneg K x))).trans
        (ContinuousMap.norm_coe_le_norm f x)
  · filter_upwards [ae_cubeInterior d] with x hx
    exact tendsto_const_nhds.congr' ((cubeCutoff_eventually_one hx).mono fun K hk => by
      simp [cubeCutoffTest, hk])

theorem tends_to_cube_test_of_pullback {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n)))
    {f : C(Cube d, ℂ)} {g : C(Torus d, ℂ)} (hg : ∀ x : Cube d, g (cubeToTorus x) = f x) :
    Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean (cubeLebesgue d) f)) := by
  have hmean : testMean (torusHaar d) g = testMean (cubeLebesgue d) f := by
    unfold testMean
    rw [← (cubeToTorus_measurePreserving d).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable g.continuous.stronglyMeasurable]
    simp only [hg]
  simpa only [hg, hmean] using hx g

private theorem tendsto_cubeCutoffDeficit {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n))) (K : ℕ) :
    Tendsto (realCesaro fun n => 1 - cubeCutoff K (x n)) atTop
      (𝓝 (∫ y : Cube d, 1 - cubeCutoff K y ∂cubeLebesgue d)) := by
  obtain ⟨g, hg⟩ := exists_cubeCutoff_descend K (1 : C(Cube d, ℂ))
  let deficit (y : Cube d) := 1 - cubeCutoff K y
  let F : C(Cube d, ℂ) := ⟨fun y => (deficit y : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.sub (continuous_cubeCutoff K))⟩
  have hcomp (y : Cube d) : (1 - g) (cubeToTorus y) = F y := by
    rw [ContinuousMap.sub_apply, ContinuousMap.one_apply, hg]
    change 1 - ((1:ℂ) * (cubeCutoff K y : ℂ)) = ((1 - cubeCutoff K y : ℝ) : ℂ)
    push_cast
    ring
  have ht := tends_to_cube_test_of_pullback hx hcomp
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp ht
  have hmean : testMean (cubeLebesgue d) F = (∫ y : Cube d, deficit y ∂cubeLebesgue d : ℝ) :=
    integral_complex_ofReal
  rw [hmean, Complex.ofReal_re] at hRe
  simpa only [Function.comp_def, ← realCesaro_re, F, ContinuousMap.coe_mk, Complex.ofReal_re] using hRe

private theorem norm_cesaro_le_realCesaro {u : ℕ → ℂ} {v : ℕ → ℝ} (h : ∀ n, ‖u n‖ ≤ v n) (N : ℕ) :
    ‖cesaro u N‖ ≤ realCesaro v N := by
  rw [cesaro, realCesaro, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => h n)) (by positivity)

/-- Distribution on the torus lifts to the closed cube. The periodic cutoff
handles both representatives of each seam, including sequences that meet the seams. -/
theorem equidistributed_of_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n))) :
    Equidistributed (cubeLebesgue d) x := by
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hDef := (tendsto_cutoffDeficit_integral d).const_mul ‖f‖
  have hsmall : ∀ᶠ K : ℕ in atTop,
      ‖f‖ * (∫ y : Cube d, 1 - cubeCutoff K y ∂cubeLebesgue d) < ε/3 := by
    have h := hDef.eventually (gt_mem_nhds (show ‖f‖ * (0:ℝ) < ε/3 by
      simpa only [mul_zero] using (show 0 < ε/3 by positivity)))
    exact h
  have hv := Metric.tendsto_nhds.mp (tendsto_testMean_cubeCutoffTest f) (ε/3) (by positivity)
  obtain ⟨K, hK, hMean⟩ := (hsmall.and hv).exists
  let u := cubeCutoffTest K f
  obtain ⟨g, hg⟩ := exists_cubeCutoff_descend K f
  have hU := tends_to_cube_test_of_pullback hx hg
  have hAvg := (tendsto_cubeCutoffDeficit hx K).const_mul ‖f‖
  have hErr : ∀ᶠ N : ℕ in atTop, ‖f‖ * realCesaro (fun n => 1 - cubeCutoff K (x n)) N < ε/3 :=
    hAvg.eventually (gt_mem_nhds hK)
  filter_upwards [Metric.tendsto_nhds.mp hU (ε/3) (by positivity), hErr] with N hUavg hN
  rw [dist_eq_norm] at hUavg hMean ⊢
  have hDiff : ‖cesaro (fun n => f (x n)) N - cesaro (fun n => u (x n)) N‖ ≤
      ‖f‖ * realCesaro (fun n => 1 - cubeCutoff K (x n)) N := by
    rw [← cesaro_sub, ← realCesaro_const_mul]
    apply norm_cesaro_le_realCesaro
    intro n
    rw [norm_sub_cubeCutoffTest K f (x n)]
    exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f (x n))
      (sub_nonneg.mpr (cubeCutoff_le_one K (x n)))
  let a := cesaro (fun n => f (x n)) N
  let b := cesaro (fun n => u (x n)) N
  let c := testMean (cubeLebesgue d) u
  let e := testMean (cubeLebesgue d) f
  have hTri : ‖a-e‖ ≤ ‖a-b‖ + ‖b-c‖ + ‖c-e‖ := by
    rw [show a-e = (a-b+(b-c))+(c-e) by ring]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le (a-b) (b-c)) le_rfl)
  change ‖a - e‖ < ε
  change ‖b - c‖ < ε / 3 at hUavg
  change ‖c - e‖ < ε / 3 at hMean
  change ‖a - b‖ ≤ _ at hDiff
  linarith only [hUavg, hMean, hN, hDiff, hTri]

/-- A zero-mean cube test is an L² limit of zero-mean periodic tests. -/
theorem exists_centered_periodic_test_approx_l2 {d : ℕ} (f : C(Cube d, ℂ))
    (hf : testMean (cubeLebesgue d) f = 0) :
    ∃ g : ℕ → C(Torus d, ℂ), (∀ K, testMean (torusHaar d) (g K) = 0) ∧
      Tendsto (fun K : ℕ => ∫ x : Cube d, ‖g K (cubeToTorus x) - f x‖ ^ 2 ∂cubeLebesgue d)
        atTop (𝓝 0) := by
  choose raw hraw using fun K : ℕ => exists_cubeCutoff_descend K f
  let m (K : ℕ) := testMean (torusHaar d) (raw K)
  let g (K : ℕ) := raw K - ContinuousMap.const (Torus d) (m K)
  have hmean (K : ℕ) : m K = testMean (cubeLebesgue d) (cubeCutoffTest K f) := by
    unfold m testMean
    rw [← (cubeToTorus_measurePreserving d).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable (raw K).continuous.stronglyMeasurable]
    simp only [hraw K]
  have hm : Tendsto m atTop (𝓝 0) := by
    have ht := tendsto_testMean_cubeCutoffTest f
    rw [hf] at ht
    exact ht.congr' (Eventually.of_forall fun K => (hmean K).symm)
  have hg (K : ℕ) : testMean (torusHaar d) (g K) = 0 := by
    unfold g
    rw [testMean_sub, testMean_const]
    exact sub_self _
  refine ⟨g, hg, ?_⟩
  have hbound (K : ℕ) : ‖m K‖ ≤ ‖f‖ := by
    rw [hmean, testMean]
    have h : ∀ᵐ x ∂cubeLebesgue d, ‖cubeCutoffTest K f x‖ ≤ ‖f‖ := ae_of_all _ fun x => by
      change ‖f x * (cubeCutoff K x : ℂ)‖ ≤ ‖f‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cubeCutoff_nonneg K x)]
      exact (mul_le_of_le_one_right (norm_nonneg _) (cubeCutoff_le_one K x)).trans
        (ContinuousMap.norm_coe_le_norm f x)
    simpa using norm_integral_le_of_norm_le_const h
  have herror (K : ℕ) (x : Cube d) : ‖g K (cubeToTorus x) - f x‖ ≤ 2 * ‖f‖ := by
    have ht : g K (cubeToTorus x) - f x = (cubeCutoffTest K f x - f x) - m K := by
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.const_apply, hraw]
      ring
    rw [ht]
    have ha : ‖cubeCutoffTest K f x - f x‖ ≤ ‖f‖ := by
      rw [norm_sub_rev (cubeCutoffTest K f x), norm_sub_cubeCutoffTest]
      exact (mul_le_of_le_one_right (norm_nonneg _) (sub_le_self _ (cubeCutoff_nonneg K x))).trans
        (ContinuousMap.norm_coe_le_norm f x)
    have hh := (norm_sub_le _ _).trans (add_le_add ha (hbound K))
    linarith only [hh]
  have ht := tendsto_integral_of_dominated_convergence (μ := cubeLebesgue d)
    (F := fun K x => ‖g K (cubeToTorus x) - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * ‖f‖)^2) (fun K => ((((g K).continuous.comp (continuous_cubeToTorus d)).sub
      f.continuous).norm.pow 2).aestronglyMeasurable) (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro K
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (herror K x) 2
  · filter_upwards [ae_cubeInterior d] with x hx
    have heq : ∀ᶠ K : ℕ in atTop, g K (cubeToTorus x) - f x = -(m K) := by
      filter_upwards [cubeCutoff_eventually_one hx] with K hK
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.const_apply, hraw, cubeCutoffTest,
        ContinuousMap.coe_mk, hK, Complex.ofReal_one, mul_one]
      ring
    simpa only [neg_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((hm.neg.congr' (heq.mono fun _ h => h.symm)).norm.pow 2)

theorem tendsto_realCesaro_cube_test {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (cubeLebesgue d) x) {u : Cube d → ℝ} (hu : Continuous u) :
    Tendsto (realCesaro fun n => u (x n)) atTop (𝓝 (∫ y, u y ∂cubeLebesgue d)) := by
  let F : C(Cube d, ℂ) := ⟨fun y => (u y : ℂ), Complex.continuous_ofReal.comp hu⟩
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (hx F)
  have hm : testMean (cubeLebesgue d) F = Complex.ofReal (∫ y, u y ∂cubeLebesgue d) :=
    integral_complex_ofReal
  rw [hm, Complex.ofReal_re] at ht
  simpa only [Function.comp_def, ← realCesaro_re, F, ContinuousMap.coe_mk, Complex.ofReal_re] using ht

/-- Periodic mean-zero approximants tested along an equidistributed cube sequence. -/
theorem exists_centered_periodic_sequence_approx_l2 {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (cubeLebesgue d) x) (f : C(Cube d, ℂ))
    (hf : testMean (cubeLebesgue d) f = 0) :
    ∃ g : ℕ → C(Torus d, ℂ), (∀ K, testMean (torusHaar d) (g K) = 0) ∧
      Tendsto (fun K : ℕ => limsup (fun N : ℕ =>
        realCesaro (fun n => ‖g K (cubeToTorus (x n)) - f (x n)‖ ^ 2) N) atTop) atTop (𝓝 0) := by
  obtain ⟨g, hg, hlim⟩ := exists_centered_periodic_test_approx_l2 f hf
  refine ⟨g, hg, ?_⟩
  refine hlim.congr' (Eventually.of_forall fun K => ?_)
  symm
  apply Tendsto.limsup_eq
  let U (y : Cube d) : ℝ := ‖g K (cubeToTorus y) - f y‖ ^ 2
  have hU : Continuous U := ((((g K).continuous.comp (continuous_cubeToTorus d)).sub
    f.continuous).norm.pow 2)
  exact tendsto_realCesaro_cube_test hx hU

/-- An eventual mean-square periodic approximation, directly on the original cube sequence. -/
theorem exists_centered_torus_approx {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n))) (f : C(Cube d, ℂ))
    (hf : testMean (cubeLebesgue d) f = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(Torus d, ℂ), testMean (torusHaar d) g = 0 ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖f (x n) - g (cubeToTorus (x n))‖ ^ 2) N ≤ ε := by
  obtain ⟨g, hg, hlim⟩ := exists_centered_periodic_test_approx_l2 f hf
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨g K, hg K, ?_⟩
  let U (y : Cube d) : ℝ := ‖g K (cubeToTorus y) - f y‖ ^ 2
  have hU : Continuous U := ((((g K).continuous.comp (continuous_cubeToTorus d)).sub f.continuous).norm.pow 2)
  have h := tendsto_realCesaro_cube_test (equidistributed_of_cubeToTorus hx) hU
  filter_upwards [h.eventually (gt_mem_nhds hK)] with N hN
  simpa only [U, norm_sub_rev] using hN.le

end VdC

end

end VdC_Cube_Module

/- Source: VdC/Difference.lean -/
section VdC_Difference_Module

/-! # Difference -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

private theorem limsup_nonneg_of_bounded {u : ℕ → ℝ} (h₀ : ∀ n, 0 ≤ u n)
    (h₁ : ∃ B, ∀ n, u n ≤ B) : 0 ≤ limsup u atTop :=
  le_limsup_of_frequently_le (Frequently.of_forall h₀) (isBoundedUnder_of h₁)

theorem spectrallyLebesgue_of_corr_majorant {u : ℕ → ℂ} (hu : BoundedSeq u) (D : ℕ → ℝ)
    (K : ℝ) (hs : Summable fun h => (D h) ^ 2)
    (hbound : ∀ h, limsup (fun N => ‖corr u u (h + 1) N‖ ^ 2) atTop ≤ K ^ 2 * (D h) ^ 2) :
    SpectrallyLebesgue u := by
  apply spectrallyLebesgue_of_limsup_square_summable hu
  obtain ⟨B, hB, hb⟩ := hu
  refine Summable.of_nonneg_of_le (fun h => ?_) hbound (hs.mul_left (K ^ 2))
  apply limsup_nonneg_of_bounded (fun _ => sq_nonneg _)
  refine ⟨(B * B) ^ 2, fun N => ?_⟩
  gcongr
  exact norm_corr_le hB hB hb hb _ _

theorem nearlyWeakMixing_of_corr_majorant {u : ℕ → ℂ} (hu : BoundedSeq u) (D : ℕ → ℝ)
    (K : ℝ)
    (hd : Tendsto (realCesaro D) atTop (𝓝 0))
    (hbound : ∀ h, limsup (fun N => ‖corr u u (h + 1) N‖) atTop ≤ K * D h) :
    NearlyWeakMixing u := by
  apply nearlyWeakMixing_of_upper_corr hu
  obtain ⟨B, hB, hb⟩ := hu
  have hz (j : ℕ) : 0 ≤ limsup (fun N => ‖corr u u (j + 1) N‖) atTop :=
    limsup_nonneg_of_bounded (fun _ => norm_nonneg _) ⟨B * B, norm_corr_le hB hB hb hb _⟩
  apply squeeze_zero (realCesaro_nonneg hz) (realCesaro_mono hbound)
  change Tendsto (fun N => realCesaro (fun n => K * D n) N) atTop (𝓝 0)
  simpa only [realCesaro_const_mul, mul_zero] using hd.const_mul K

/-- Turn finite discrepancy bounds for the differences into upper correlation
bounds. `E h N` is the finite discrepancy at positive lag `h+1`. -/
theorem upper_corr_of_finite_bounds {u : ℕ → ℂ} (E : ℕ → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hE : ∀ h N, E h N ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ h N, ‖corr u u (h + 1) N‖ ≤ K * E h N) (h : ℕ) :
    limsup (fun N => ‖corr u u (h + 1) N‖) atTop ≤ K * limsup (E h) atTop := by
  have hEa := isBoundedUnder_of_eventually_le (f := atTop) (Eventually.of_forall fun N => (hE h N).2)
  have hEb := isCoboundedUnder_le_of_le (f := E h) atTop (fun N => (hE h N).1)
  have hmono : Monotone (fun a : ℝ => K * a) := fun _ _ hab => mul_le_mul_of_nonneg_left hab hK
  have heq := hmono.map_limsup_of_continuousAt (F := atTop) (E h)
    ((continuous_const.mul continuous_id).continuousAt) hEa hEb
  rw [heq]
  refine limsup_le_limsup (Eventually.of_forall (hb h)) ?_ ?_
  · exact isCoboundedUnder_le_of_le atTop (fun _ => norm_nonneg _)
  · apply isBoundedUnder_of_eventually_le (a := K)
    exact Eventually.of_forall fun N => mul_le_of_le_one_right hK (hE h N).2

theorem upper_corr_square_of_finite_bounds {u : ℕ → ℂ} (E : ℕ → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hE : ∀ h N, E h N ∈ Set.Icc (0 : ℝ) 1)
    (hb : ∀ h N, ‖corr u u (h + 1) N‖ ≤ K * E h N) (h : ℕ) :
    limsup (fun N => ‖corr u u (h + 1) N‖ ^ 2) atTop ≤ K ^ 2 * (limsup (E h) atTop) ^ 2 := by
  have hnorm (N : ℕ) : ‖corr u u (h + 1) N‖ ≤ K :=
    (hb h N).trans (mul_le_of_le_one_right hK (hE h N).2)
  have hC : 0 ≤ limsup (fun N => ‖corr u u (h + 1) N‖) atTop :=
    limsup_nonneg_of_bounded (fun _ => norm_nonneg _) ⟨K, hnorm⟩
  let sqpos (a : ℝ) := (max a 0) ^ 2
  have hmono : Monotone sqpos := fun a b hab => by
    dsimp [sqpos]
    gcongr
  have hcont : Continuous sqpos := (continuous_id.max continuous_const).pow 2
  have heq := hmono.map_limsup_of_continuousAt (F := atTop) (fun N => ‖corr u u (h + 1) N‖)
    hcont.continuousAt (isBoundedUnder_of_eventually_le (Eventually.of_forall hnorm))
    (isCoboundedUnder_le_of_le _ (fun _ => norm_nonneg _))
  simp only [sqpos, max_eq_left hC, Function.comp_def, max_eq_left (norm_nonneg _)] at heq
  rw [← heq, ← mul_pow]
  gcongr
  exact upper_corr_of_finite_bounds E K hK hE hb h

/-- The Fourier-character implication in GeneralizationOfClassicalvdC.
The finite character-versus-rectangle estimate enters as `hKH`. -/
theorem spectral_difference_character {d : ℕ} (x : ℕ → Torus d) (m : Fin d → ℤ)
    (E : ℕ → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hE : ∀ h N, E h N ∈ Set.Icc (0 : ℝ) 1)
    (hKH : ∀ h N, ‖cesaro (fun n => torusCharacter m (x (n + (h + 1)) - x n)) N‖ ≤ K * E h N)
    (hd : Summable fun h => (limsup (E h) atTop) ^ 2) :
    SpectrallyLebesgue (fun n => torusCharacter m (x n)) := by
  apply spectrallyLebesgue_of_corr_majorant (bounded_test (torusCharacter m) x) (fun h => limsup (E h) atTop) K hd
  apply upper_corr_square_of_finite_bounds E K hK hE
  simpa only [torusCharacter_point_sub, corr] using hKH

/-- The Fourier-character implication in WeakMixingUDvdC. -/
theorem weakMixing_difference_character {d : ℕ} (x : ℕ → Torus d) (m : Fin d → ℤ)
    (E : ℕ → ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hE : ∀ h N, E h N ∈ Set.Icc (0 : ℝ) 1)
    (hKH : ∀ h N, ‖cesaro (fun n => torusCharacter m (x (n + (h + 1)) - x n)) N‖ ≤ K * E h N)
    (hd : Tendsto (realCesaro (fun h => limsup (E h) atTop)) atTop (𝓝 0)) :
    NearlyWeakMixing (fun n => torusCharacter m (x n)) := by
  apply nearlyWeakMixing_of_corr_majorant (bounded_test (torusCharacter m) x) (fun h => limsup (E h) atTop) K hd
  apply upper_corr_of_finite_bounds E K hK hE
  simpa only [torusCharacter_point_sub, corr] using hKH

end VdC

end

end VdC_Difference_Module

/- Source: VdC/Rectangles.lean -/
section VdC_Rectangles_Module

/-! # Rectangles -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

noncomputable section

def rectangleFrequency {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ)
    (a b : Fin d → UnitInterval) : ℝ := by
  classical
  exact (((range N).filter fun n => ∀ i, (a i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ b i).card : ℝ) / N

def rectangleVolume {d : ℕ} (a b : Fin d → UnitInterval) : ℝ :=
  ∏ i, max 0 ((b i : ℝ) - (a i : ℝ))

def rectangleDiscrepancy {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ) : ℝ :=
  sSup (Set.range fun ab : (Fin d → UnitInterval) × (Fin d → UnitInterval) =>
    |rectangleFrequency u N ab.1 ab.2 - rectangleVolume ab.1 ab.2|)

private theorem rectangle_deviation_le_one {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ)
    (a b : Fin d → UnitInterval) : |rectangleFrequency u N a b - rectangleVolume a b| ≤ 1 := by
  classical
  have hvol0 : 0 ≤ rectangleVolume a b := Finset.prod_nonneg fun _ _ => le_max_left ..
  have hvol1 : rectangleVolume a b ≤ 1 := by
    apply Finset.prod_le_one₀ (fun _ _ => le_max_left _ _)
    intro i _
    exact max_le zero_le_one (by linarith [(b i).property.2, (a i).property.1])
  have hf0 : 0 ≤ rectangleFrequency u N a b := by unfold rectangleFrequency; positivity
  have hf1 : rectangleFrequency u N a b ≤ 1 := by
    by_cases hN : N = 0
    · simp [rectangleFrequency, hN]
    have hNr : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [rectangleFrequency, div_le_iff₀ hNr, one_mul]
    exact_mod_cast (card_filter_le _ _).trans_eq (card_range N)
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem rectangle_deviation_le_discrepancy {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ)
    (a b : Fin d → UnitInterval) : |rectangleFrequency u N a b - rectangleVolume a b| ≤ rectangleDiscrepancy u N :=
  le_csSup ⟨1, by rintro _ ⟨⟨a, b⟩, rfl⟩; exact rectangle_deviation_le_one u N a b⟩ ⟨(a, b), rfl⟩

theorem rectangleDiscrepancy_mem_Icc {d : ℕ} (u : ℕ → Fin d → UnitInterval) (N : ℕ) :
    rectangleDiscrepancy u N ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  let z : UnitInterval := ⟨0, by simp⟩
  change 0 ≤ rectangleDiscrepancy u N ∧ rectangleDiscrepancy u N ≤ 1
  refine ⟨(abs_nonneg _).trans (rectangle_deviation_le_discrepancy u N (fun _ => z) (fun _ => z)), ?_⟩
  unfold rectangleDiscrepancy
  apply csSup_le ⟨_, Set.mem_range_self (fun _ => z, fun _ => z)⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact rectangle_deviation_le_one u N a b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def unitRepresentative (t : UnitAddCircle) : UnitInterval :=
  let y := AddCircle.equivIco (1 : ℝ) (0 : ℝ) t
  ⟨y, ⟨y.property.1, by simpa only [zero_add] using y.property.2.le⟩⟩

theorem unitRepresentative_coe (t : UnitAddCircle) : ((unitRepresentative t : ℝ) : UnitAddCircle) = t :=
  AddCircle.coe_equivIco ..

def differenceDiscrepancy {d : ℕ} (x : ℕ → Torus d) (h N : ℕ) : ℝ :=
  rectangleDiscrepancy (fun n i => unitRepresentative (x (n + (h + 1)) i - x n i)) N

def upperDifferenceDiscrepancy {d : ℕ} (x : ℕ → Torus d) (h : ℕ) : ℝ :=
  limsup (differenceDiscrepancy x h) atTop

/-- The explicit finite Fourier estimate used in the manuscript's two difference
theorems. Each frequency has its own constant, uniform over lag and length. -/
def CharacterRectangleEstimate {d : ℕ} (x : ℕ → Torus d) : Prop :=
  ∀ m : Fin d → ℤ, m ≠ 0 → ∃ K : ℝ, 0 ≤ K ∧ ∀ h N,
    ‖cesaro (fun n => torusCharacter m (x (n + (h + 1)) - x n)) N‖ ≤
      K * differenceDiscrepancy x h N

theorem spectral_character_of_rectangle_discrepancy {d : ℕ} (x : ℕ → Torus d)
    (hKH : CharacterRectangleEstimate x) (hD : Summable (fun h => upperDifferenceDiscrepancy x h ^ 2))
    (m : Fin d → ℤ) (hm : m ≠ 0) : SpectrallyLebesgue (fun n => torusCharacter m (x n)) := by
  obtain ⟨K, hK, hb⟩ := hKH m hm
  exact spectral_difference_character x m (differenceDiscrepancy x) K hK
    (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) hb hD

theorem weakMixing_character_of_rectangle_discrepancy {d : ℕ} (x : ℕ → Torus d)
    (hKH : CharacterRectangleEstimate x) (hD : Tendsto (realCesaro (upperDifferenceDiscrepancy x)) atTop (𝓝 0))
    (m : Fin d → ℤ) (hm : m ≠ 0) : NearlyWeakMixing (fun n => torusCharacter m (x n)) := by
  obtain ⟨K, hK, hb⟩ := hKH m hm
  exact weakMixing_difference_character x m (differenceDiscrepancy x) K hK
    (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) hb hD

end
end VdC

end

end VdC_Rectangles_Module

/- Source: VdC/FourierTests.lean -/
section VdC_FourierTests_Module

/-! # Fourier Tests -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

private theorem center_add (f g : C(X, ℂ)) : center μ (f + g) = center μ f + center μ g := by
  ext x
  simp [center, testMean_add]
  ring

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
private theorem center_smul (c : ℂ) (f : C(X, ℂ)) : center μ (c • f) = c • center μ f := by
  ext x
  simp [center, testMean_smul, mul_sub]

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
private theorem center_zero : center μ (0 : C(X, ℂ)) = 0 := by
  ext x
  simp [center, testMean]

omit [BorelSpace X] in
private theorem norm_testMean_le (f : C(X, ℂ)) : ‖testMean μ f‖ ≤ ‖f‖ := by
  simpa [testMean] using norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall fun a => ContinuousMap.norm_coe_le_norm f a)

private theorem centered_test_approximation (x : ℕ → X) (f : C(X, ℂ)) (hf : testMean μ f = 0)
    (s : Set C(X, ℂ)) (hd : (Submodule.span ℂ s).topologicalClosure = ⊤)
    (P : (ℕ → ℂ) → Prop) (hzero : P (fun _ => 0))
    (hadd : ∀ u v, P u → P v → P (fun n => u n + v n))
    (hsmul : ∀ u, ∀ c : ℂ, P u → P (fun n => c * u n))
    (hs : ∀ g ∈ s, P (fun n => center μ g (x n)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℕ → ℂ, P u ∧ ∀ᶠ N in atTop, realCesaro (fun n => ‖f (x n) - u n‖ ^ 2) N ≤ ε := by
  have hspan : ∀ g ∈ Submodule.span ℂ s, P (fun n => center μ g (x n)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg => exact hs g hg
    | zero => simpa only [center_zero, ContinuousMap.zero_apply] using hzero
    | add g k _ _ hg hk => simpa only [center_add, ContinuousMap.add_apply] using hadd _ _ hg hk
    | smul c g _ hg => simpa only [center_smul, ContinuousMap.smul_apply, smul_eq_mul] using hsmul _ c hg
  have hclose : f ∈ closure (↑(Submodule.span ℂ s) : Set C(X, ℂ)) := by
    change f ∈ (Submodule.span ℂ s).topologicalClosure
    rw [hd]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hclose (Real.sqrt ε / 2) (by positivity)
  rw [dist_eq_norm] at hdist
  refine ⟨fun n => center μ g (x n), hspan g hg, Eventually.of_forall fun N => ?_⟩
  have hnorm (n : ℕ) : ‖f (x n) - center μ g (x n)‖ ≤ Real.sqrt ε := by
    have hmean : ‖testMean μ g‖ ≤ ‖f - g‖ := by
      simpa [testMean_sub, hf] using norm_testMean_le μ (f - g)
    have ht := (norm_add_le (f (x n) - g (x n)) (testMean μ g)).trans
      (add_le_add (ContinuousMap.norm_coe_le_norm (f - g) (x n)) hmean)
    have he : f (x n) - center μ g (x n) = (f (x n) - g (x n)) + testMean μ g := by
      simp [center]
      ring
    rw [he]
    linarith only [ht, hdist]
  have hsqr (n : ℕ) : ‖f (x n) - center μ g (x n)‖ ^ 2 ≤ ε := by
    rw [← Real.sq_sqrt hε.le]
    gcongr
    exact hnorm n
  by_cases hN : 0 < N
  · exact (realCesaro_mono hsqr N).trans_eq (realCesaro_const_pos ε hN)
  · simp [realCesaro, Nat.eq_zero_of_not_pos hN, hε.le]

end

noncomputable section

private theorem center_torusCharacter_nonzero {d : ℕ} {m : Fin d → ℤ} (hm : m ≠ 0) :
    center (torusHaar d) (torusCharacter m) = torusCharacter m := by
  ext x
  simp [center, testMean_torusCharacter, hm]

private theorem center_torusCharacter_zero {d : ℕ} :
    center (torusHaar d) (torusCharacter (0 : Fin d → ℤ)) = 0 := by
  unfold center
  rw [testMean_torusCharacter, ite_eq_left rfl, torusCharacter_zero]
  ext x
  simp

/-- Integer characters suffice for the spectral Lebesgue definition on the torus. -/
theorem spectralLebesgueDistribution_iff_torus_characters {d : ℕ} (x : ℕ → Torus d) :
    SpectrallyLebesgueDistribution (torusHaar d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      SpectrallyLebesgue (fun n => torusCharacter m (x n)) := by
  constructor
  · intro h m hm
    exact h _ (by simp [testMean_torusCharacter, hm])
  · intro h f hf
    apply spectrallyLebesgue_of_meanSquare_approximation (bounded_test f x)
    apply centered_test_approximation _ x f hf _ (torusCharacters_dense d) SpectrallyLebesgue
      spectrallyLebesgue_zero (fun _ _ hu hv => hu.add hv) (fun _ c hu => hu.const_mul c)
    rintro _ ⟨m, rfl⟩
    by_cases hm : m = 0
    · subst m
      simpa only [center_torusCharacter_zero, ContinuousMap.zero_apply] using spectrallyLebesgue_zero
    · simpa only [center_torusCharacter_nonzero hm] using h m hm

/-- Integer characters suffice for the weak mixing definition on the torus. -/
theorem weaklyMixingDistribution_iff_torus_characters {d : ℕ} (x : ℕ → Torus d) :
    WeaklyMixingDistribution (torusHaar d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      NearlyWeakMixing (fun n => torusCharacter m (x n)) := by
  constructor
  · intro h m hm
    exact h _ (by simp [testMean_torusCharacter, hm])
  · intro h f hf
    have hzero : NearlyWeakMixing (fun _ => 0) := by
      apply (NearlyOrthogonal.nearlyWeakMixing (x := fun _ => 0))
      apply (nearlyOrthogonal_iff_corr_tendsto_zero ⟨0, le_rfl, by simp⟩).2
      intro k hk
      have he : corr (fun _ => 0) (fun _ => 0) k = fun _ => 0 := by ext N; simp [corr, cesaro]
      rw [he]
      exact tendsto_const_nhds
    apply nearlyWeakMixing_of_cesaro_l2_approx (bounded_test f x)
    apply centered_test_approximation _ x f hf _ (torusCharacters_dense d) NearlyWeakMixing hzero
    · intro u v hu hv
      simpa only [one_mul] using hu.add_const_mul hv 1
    · intro u c hu
      simpa only [zero_add] using hzero.add_const_mul hu c
    · rintro _ ⟨m, rfl⟩
      by_cases hm : m = 0
      · subst m
        simpa only [center_torusCharacter_zero, ContinuousMap.zero_apply] using hzero
      · simpa only [center_torusCharacter_nonzero hm] using h m hm

/-- PreliminaryVersionOfUniformDistributionLebesgueSpectrumvdC on the torus. -/
theorem spectral_difference_from_fourier {d : ℕ} (x : ℕ → Torus d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Summable (fun j => limsup
      (fun N => ‖cesaro (fun n => torusCharacter m (x (n + (j + 1)) - x n)) N‖ ^ 2) atTop)) :
    SpectrallyLebesgueDistribution (torusHaar d) x := by
  apply (spectralLebesgueDistribution_iff_torus_characters x).2
  intro m hm
  apply spectrallyLebesgue_of_limsup_square_summable (bounded_test (torusCharacter m) x)
  simpa only [torusCharacter_point_sub, corr] using h m hm

/-- PreliminaryVersionOfUniformDistributionWeakMixingvdC on the torus. -/
theorem weakMixing_difference_from_fourier {d : ℕ} (x : ℕ → Torus d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Tendsto (realCesaro (fun j => limsup
      (fun N => ‖cesaro (fun n => torusCharacter m (x (n + (j + 1)) - x n)) N‖) atTop)) atTop (𝓝 0)) :
    WeaklyMixingDistribution (torusHaar d) x := by
  apply (weaklyMixingDistribution_iff_torus_characters x).2
  intro m hm
  apply nearlyWeakMixing_of_upper_corr (bounded_test (torusCharacter m) x)
  simpa only [torusCharacter_point_sub, corr] using h m hm

/-- Torus version of GeneralizationOfClassicalvdC with the finite rectangle
estimate supplied as a hypothesis. -/
theorem spectral_difference_theorem {d : ℕ} (x : ℕ → Torus d) (hKH : CharacterRectangleEstimate x)
    (hD : Summable (fun h => upperDifferenceDiscrepancy x h ^ 2)) :
    SpectrallyLebesgueDistribution (torusHaar d) x :=
  (spectralLebesgueDistribution_iff_torus_characters x).2
    (spectral_character_of_rectangle_discrepancy x hKH hD)

/-- Torus version of WeakMixingUDvdC with the finite rectangle estimate
supplied as a hypothesis. -/
theorem weakMixing_difference_theorem {d : ℕ} (x : ℕ → Torus d) (hKH : CharacterRectangleEstimate x)
    (hD : Tendsto (realCesaro (upperDifferenceDiscrepancy x)) atTop (𝓝 0)) :
    WeaklyMixingDistribution (torusHaar d) x :=
  (weaklyMixingDistribution_iff_torus_characters x).2
    (weakMixing_character_of_rectangle_discrepancy x hKH hD)

end
end VdC

end

end VdC_FourierTests_Module

/- Source: VdC/RectangleFourier.lean -/
section VdC_RectangleFourier_Module

/-! A finite Fourier bound from closed upper rectangles. The proof writes each
coordinate character as an integral over one threshold, expands the product,
and applies the rectangle bound inside the resulting integrals. -/

@[expose] public section

open Finset Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace VdC

noncomputable section
open Classical

private abbrev Interval := Icc (0 : ℝ) 1

private def intervalUniform : Measure Interval := Measure.comap Subtype.val volume

private theorem intervalUniform_map : intervalUniform.map (Subtype.val : Interval → ℝ) =
    volume.restrict (Icc (0 : ℝ) 1) :=
  map_comap_subtype_coe measurableSet_Icc volume

private instance : IsProbabilityMeasure intervalUniform := by
  constructor
  rw [intervalUniform, comap_subtype_coe_apply measurableSet_Icc, Set.image_univ,
    Subtype.range_coe, Real.volume_Icc]
  norm_num

private def cubeUniform (ι : Type) [Fintype ι] : Measure (ι → Interval) :=
  Measure.pi fun _ ↦ intervalUniform

private instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (cubeUniform ι) := by
  unfold cubeUniform
  infer_instance

private def upperRectangle {ι : Type} (s : Finset ι) (t : ι → Interval) : Set (ι → Interval) :=
  {x | ∀ i ∈ s, (x i : ℝ) ≤ t i}

private theorem upperRectangle_measurable {ι : Type} [Fintype ι] (s : Finset ι) (t : ι → Interval) :
    MeasurableSet (upperRectangle s t) := by
  classical
  have he : upperRectangle s t = ⋂ i ∈ s, {x : ι → Interval | (x i : ℝ) ≤ t i} := by
    ext x; simp [upperRectangle]
  rw [he]
  apply MeasurableSet.biInter s.countable_toSet
  intro i _
  exact measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply _)) measurable_const

private def upperKernel {ι : Type} [Fintype ι] (w : ι → Interval → ℂ)
    (x t : ι → Interval) : ℂ :=
  ∏ i, ((if (x i : ℝ) ≤ t i then w i (t i) else 0) + 1)

private theorem upperKernel_measurable {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (hw : ∀ i, Measurable (w i)) :
    Measurable (uncurry (upperKernel w)) := by
  unfold upperKernel uncurry
  apply Finset.measurable_prod
  intro i _
  apply Measurable.add ?_ measurable_const
  apply Measurable.ite ?_ ((hw i).comp ((measurable_pi_apply i).comp measurable_snd)) measurable_const
  exact measurableSet_le (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_fst))
    (measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd))

private theorem upperKernel_norm_le {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i) (x t : ι → Interval) :
    ‖upperKernel w x t‖ ≤ ∏ i, (B i + 1) := by
  unfold upperKernel
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
  intro i _
  split
  · exact (norm_add_le _ _).trans (by simpa using add_le_add_right (hB i (t i)) 1)
  · simp only [zero_add, norm_one]
    linarith [(norm_nonneg _).trans (hB i (t i))]

private theorem upperKernel_expand {ι : Type} [Fintype ι] (w : ι → Interval → ℂ) (x t : ι → Interval) :
    upperKernel w x t = ∑ s : Finset ι,
      (if x ∈ upperRectangle s t then (1 : ℂ) else 0) * ∏ i ∈ s, w i (t i) := by
  classical
  unfold upperKernel
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_const_one, mul_one]
  by_cases h : x ∈ upperRectangle s t
  · rw [ite_eq_left h, one_mul]
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_left (h i hi)
  · rw [ite_eq_right h, zero_mul]
    have h' : ∃ i ∈ s, ¬ (x i : ℝ) ≤ t i := by
      change ¬ (∀ i ∈ s, _) at h
      push Not at h
      simpa only [not_le] using h
    obtain ⟨i, hi, hki⟩ := h'
    exact Finset.prod_eq_zero hi (ite_eq_right hki)

private theorem upperKernel_integral_expand {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (μ : Measure (ι → Interval)) [IsFiniteMeasure μ] (t : ι → Interval) :
    (∫ x, upperKernel w x t ∂μ) = ∑ s : Finset ι,
      Complex.ofReal (μ.real (upperRectangle s t)) * ∏ i ∈ s, w i (t i) := by
  classical
  let c (s : Finset ι) : ℂ := ∏ i ∈ s, w i (t i)
  have hintegral (s : Finset ι) : Integrable (fun x : ι → Interval ↦
      (if x ∈ upperRectangle s t then (1 : ℂ) else 0) * c s) μ := by
    have h : Integrable ((upperRectangle s t).indicator fun _ ↦ (1 : ℂ)) μ :=
      (integrable_const _).indicator (upperRectangle_measurable s t)
    simpa only [Set.indicator] using h.mul_const (c s)
  simp_rw [upperKernel_expand]
  rw [integral_finsetSum _ (fun s _ ↦ hintegral s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_mul_const]
  change (∫ x, (upperRectangle s t).indicator (fun _ ↦ (1 : ℂ)) x ∂μ) * c s = _
  rw [integral_indicator (upperRectangle_measurable s t), setIntegral_const, Complex.real_smul, mul_one]

private theorem upperKernel_integral_sub_bound {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i)
    (μ ν : Measure (ι → Interval)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (D : ℝ) (hD : 0 ≤ D) (t : ι → Interval)
    (hd : ∀ s, |μ.real (upperRectangle s t) - ν.real (upperRectangle s t)| ≤ D) :
    ‖(∫ x, upperKernel w x t ∂μ) - (∫ x, upperKernel w x t ∂ν)‖ ≤ D * ∏ i, (B i + 1) := by
  classical
  rw [upperKernel_integral_expand, upperKernel_integral_expand, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [Fintype.prod_add, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  simp only [Finset.prod_const_one, mul_one, ← sub_mul, ← Complex.ofReal_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, norm_prod]
  exact mul_le_mul (hd s) (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hB i _))
    (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hD

private theorem upperKernel_integrable_prod {ι : Type} [Fintype ι]
    (w : ι → Interval → ℂ) (hw : ∀ i, Measurable (w i))
    (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i) (μ ν : Measure (ι → Interval))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : Integrable (uncurry (upperKernel w)) (μ.prod ν) := by
  refine (integrable_const (∏ i, (B i + 1))).mono' (upperKernel_measurable w hw).aestronglyMeasurable ?_
  exact ae_of_all _ fun p ↦ upperKernel_norm_le w B hB p.1 p.2

private theorem product_test_bound_of_upper_rectangles {ι : Type} [Fintype ι]
    (w f : ι → Interval → ℂ) (hw : ∀ i, Measurable (w i))
    (B : ι → ℝ) (hB : ∀ i u, ‖w i u‖ ≤ B i)
    (hprimitive : ∀ i (x : Interval), (∫ t : Interval, ((if (x : ℝ) ≤ t then w i t else 0) + 1) ∂intervalUniform) = f i x)
    (μ ν : Measure (ι → Interval)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ s t, |μ.real (upperRectangle s t) - ν.real (upperRectangle s t)| ≤ D) :
    ‖(∫ x : ι → Interval, ∏ i, f i (x i) ∂μ) - (∫ x : ι → Interval, ∏ i, f i (x i) ∂ν)‖ ≤
      D * ∏ i, (B i + 1) := by
  let τ := cubeUniform ι
  have hI1 := upperKernel_integrable_prod w hw B hB μ τ
  have hI2 := upperKernel_integrable_prod w hw B hB ν τ
  have hpoint (x : ι → Interval) : (∫ t, upperKernel w x t ∂τ) = ∏ i, f i (x i) := by
    unfold upperKernel τ cubeUniform
    rw [integral_fintype_prod_eq_prod (fun i (t : Interval) ↦
      (if (x i : ℝ) ≤ t then w i t else 0) + 1)]
    simp_rw [hprimitive]
  simp_rw [← hpoint]
  have hI1' : Integrable (fun t ↦ ∫ x, upperKernel w x t ∂μ) τ := hI1.integral_prod_right
  have hI2' : Integrable (fun t ↦ ∫ x, upperKernel w x t ∂ν) τ := hI2.integral_prod_right
  rw [integral_integral_swap hI1, integral_integral_swap hI2, ← integral_sub hI1' hI2']
  simpa using norm_integral_le_of_norm_le_const (μ := τ) (ae_of_all τ fun t ↦
    upperKernel_integral_sub_bound w B hB μ ν D hD t (fun s ↦ hd s t))

private def rate (m : ℤ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)

private def realCharacter (m : ℤ) (t : ℝ) : ℂ := Complex.exp (rate m * (t : ℂ))

private theorem realCharacter_eq_fourier (m : ℤ) (t : ℝ) :
    realCharacter m t = _root_.fourier m (t : UnitAddCircle) := by
  rw [fourier_coe_apply]
  simp [realCharacter, rate]

private theorem realCharacter_zero (m : ℤ) : realCharacter m 0 = 1 := by simp [realCharacter]

private theorem realCharacter_one (m : ℤ) : realCharacter m 1 = 1 := by
  rw [realCharacter_eq_fourier, AddCircle.coe_period, fourier_eval_zero]

private def weight (m : ℤ) (t : ℝ) : ℂ := -(rate m) * realCharacter m t

private theorem continuous_weight (m : ℤ) : Continuous (weight m) := by
  unfold weight realCharacter
  fun_prop

private theorem norm_weight (m : ℤ) (t : ℝ) : ‖weight m t‖ = ‖rate m‖ := by
  have hn : ‖realCharacter m t‖ = 1 := by
    rw [realCharacter_eq_fourier, fourier_apply, Circle.norm_coe]
  rw [weight, norm_mul, norm_neg, hn, mul_one]

private theorem norm_rate (m : ℤ) : ‖rate m‖ = 2 * Real.pi * (m.natAbs : ℝ) := by
  simp [rate, abs_of_nonneg Real.pi_pos.le, Complex.norm_intCast, Int.cast_abs]

private theorem integral_intervalUniform (g : ℝ → ℂ) (hg : Measurable g) :
    (∫ t : Interval, g t ∂intervalUniform) = ∫ t in (0 : ℝ)..1, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ← intervalUniform_map, integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]

private theorem weight_threshold_integral (m : ℤ) (x : Interval) :
    (∫ t : Interval, ((if (x : ℝ) ≤ t then weight m t else 0) + 1) ∂intervalUniform) = realCharacter m x := by
  let g := (Ici (x : ℝ)).indicator (weight m)
  have hg : Measurable g := (continuous_weight m).measurable.indicator measurableSet_Ici
  have hg_int : Integrable (fun t : Interval ↦ g t) intervalUniform := by
    refine (integrable_const ‖rate m‖).mono' (hg.comp measurable_subtype_coe).aestronglyMeasurable
      (ae_of_all _ fun t ↦ ?_)
    by_cases h : (x : ℝ) ≤ t <;> simp [g, h, norm_weight]
  change (∫ t : Interval, g t + 1 ∂intervalUniform) = _
  rw [integral_add hg_int (integrable_const _), integral_const, probReal_univ, one_smul,
    integral_intervalUniform g hg, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have he : Ici (x : ℝ) ∩ Icc (0 : ℝ) 1 = Icc (x : ℝ) 1 := by
    ext t; simp only [mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, x.property.1.trans h.1, h.2⟩⟩
  rw [he, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le x.property.2]
  by_cases h : rate m = 0
  · simp [weight, realCharacter, h]
  have hw : (∫ t in (x : ℝ)..1, weight m t) = -(rate m) *
      ((realCharacter m 1 - realCharacter m x) / rate m) := by
    unfold weight realCharacter
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex h]
  rw [hw, realCharacter_one]
  field_simp
  ring

private theorem integral_realCharacter_zero {m : ℤ} (hm : m ≠ 0) :
    (∫ t : Interval, realCharacter m t ∂intervalUniform) = 0 := by
  rw [integral_intervalUniform _ (by unfold realCharacter; fun_prop)]
  have hr : rate m ≠ 0 := by simp [rate, Real.pi_ne_zero, Complex.I_ne_zero, hm]
  change (∫ t in (0 : ℝ)..1, Complex.exp (rate m * t)) = 0
  rw [integral_exp_mul_complex hr]
  change (realCharacter m 1 - realCharacter m 0) / rate m = 0
  simp [realCharacter_one, realCharacter_zero]

private theorem integral_productCharacter_zero {ι : Type} [Fintype ι]
    {m : ι → ℤ} (hm : m ≠ 0) : (∫ x : ι → Interval, ∏ i, realCharacter (m i) (x i) ∂cubeUniform ι) = 0 := by
  have h : ∃ i, m i ≠ 0 := by
    by_contra! hall
    exact hm (funext hall)
  obtain ⟨i, hi⟩ := h
  unfold cubeUniform
  rw [integral_fintype_prod_eq_prod (fun i (x : Interval) ↦ realCharacter (m i) x)]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (integral_realCharacter_zero hi)

private theorem upperRectangle_uniform_measure {ι : Type} [Fintype ι] (s : Finset ι) (t : ι → Interval) :
    (cubeUniform ι).real (upperRectangle s t) = ∏ i ∈ s, ((t i : Interval) : ℝ) := by
  classical
  have huniform (a : Interval) : intervalUniform {x : Interval | (x : ℝ) ≤ a} = ENNReal.ofReal a := by
    rw [intervalUniform, comap_subtype_coe_apply measurableSet_Icc]
    have he : (Subtype.val '' {x : Interval | (x : ℝ) ≤ a}) = Icc (0 : ℝ) (a : ℝ) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property.1, hy⟩
      · intro hz
        exact ⟨⟨z, ⟨hz.1, hz.2.trans a.property.2⟩⟩, hz.2, rfl⟩
    rw [he, Real.volume_Icc, sub_zero]
  have hrectangle : upperRectangle s t = univ.pi (fun i ↦ if i ∈ s then
      {x : Interval | (x : ℝ) ≤ t i} else univ) := by
    ext x
    simp [upperRectangle]
  rw [hrectangle, measureReal_def, cubeUniform, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ i, (intervalUniform (if i ∈ s then {x : Interval | (x : ℝ) ≤ t i} else univ)).toReal) = _
  have ht (i : ι) : 0 ≤ ((t i : Interval) : ℝ) := (t i).property.1
  simp only [apply_ite intervalUniform, huniform, measure_univ, apply_ite ENNReal.toReal,
    ENNReal.toReal_ofReal (ht _), ENNReal.toReal_one, Finset.prod_ite_mem, Finset.univ_inter]

private def empiricalMeasure {ι : Type} (u : ℕ → ι → Interval) (N : ℕ) : Measure (ι → Interval) :=
  ENNReal.ofReal ((N : ℝ)⁻¹) • ∑ j ∈ Finset.range N, Measure.dirac (u j)

private instance {ι : Type} (u : ℕ → ι → Interval) (N : ℕ) : IsFiniteMeasure (empiricalMeasure u N) := by
  constructor
  rw [empiricalMeasure, smul_apply, sum_apply, smul_eq_mul]
  simp [ENNReal.mul_lt_top]

private theorem integral_empiricalMeasure {ι : Type} [Fintype ι] (u : ℕ → ι → Interval) (N : ℕ)
    (f : (ι → Interval) → ℂ) :
    (∫ x, f x ∂empiricalMeasure u N) = cesaro (fun n ↦ f (u n)) N := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ ↦ integrable_dirac (eNorm_lt_top)), cesaro]
  simp only [integral_dirac, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _)),
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

private theorem empiricalMeasure_real_apply {ι : Type} [Fintype ι] (u : ℕ → ι → Interval) (N : ℕ)
    {s : Set (ι → Interval)} (hs : MeasurableSet s) :
    (empiricalMeasure u N).real s = (((Finset.range N).filter fun j ↦ u j ∈ s).card : ℝ) / N := by
  classical
  have h := integral_empiricalMeasure u N (s.indicator fun _ ↦ (1 : ℂ))
  rw [integral_indicator hs, setIntegral_const, Complex.real_smul, mul_one] at h
  apply_fun Complex.re at h
  simpa [cesaro, Set.indicator, ← Finset.sum_filter, Complex.ofReal_div,
    Complex.ofReal_natCast] using h

/-- The maximum absolute coordinate of an integer frequency. -/
def maxFourierFrequency {d : ℕ} (m : Fin d → ℤ) : ℕ :=
  (univ : Finset (Fin d)).sup fun i ↦ (m i).natAbs

def fourierDiscrepancyConstant {d : ℕ} (m : Fin d → ℤ) : ℝ :=
  (4 * Real.pi * (maxFourierFrequency m : ℝ)) ^ d

theorem fourierDiscrepancyConstant_nonneg {d : ℕ} (m : Fin d → ℤ) :
    0 ≤ fourierDiscrepancyConstant m := by unfold fourierDiscrepancyConstant; positivity

/-- The anchored-box discrepancy controls the finite Fourier coefficient at every
nonzero frequency, with the manuscript's constant `(4πM)^d`. -/
theorem finite_fourier_bound_of_upper_rectangles {d : ℕ} (m : Fin d → ℤ) (hm : m ≠ 0)
    (u : ℕ → Fin d → Icc (0 : ℝ) 1) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ (s : Finset (Fin d)) (t : Fin d → Icc (0 : ℝ) 1),
      |(((range N).filter fun j ↦ ∀ i ∈ s, (u j i : ℝ) ≤ t i).card : ℝ) / N -
        ∏ i ∈ s, (t i : ℝ)| ≤ D) :
    ‖cesaro (fun j ↦ ∏ i, _root_.fourier (m i) ((u j i : ℝ) : UnitAddCircle)) N‖ ≤
      fourierDiscrepancyConstant m * D := by
  let M : ℕ := maxFourierFrequency m
  have hMle (i : Fin d) : (m i).natAbs ≤ M :=
    Finset.le_sup (s := univ) (f := fun j : Fin d ↦ (m j).natAbs) (Finset.mem_univ i)
  have hM₀ : (1 : ℝ) ≤ M := by
    have hnz : ∃ i, m i ≠ 0 := by
      by_contra! he
      exact hm (funext he)
    obtain ⟨i, hi⟩ := hnz
    have hpos : 0 < (m i).natAbs := by simpa using hi
    exact_mod_cast (hpos.trans_le (hMle i))
  have hcomp : (∏ i, (‖rate (m i)‖ + 1)) ≤ (4 * Real.pi * (M : ℝ)) ^ d := by
    calc
      _ ≤ ∏ _ : Fin d, (4 * Real.pi * (M : ℝ)) := by
        apply Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
        intro i _
        have hcast : ((m i).natAbs : ℝ) ≤ M := by exact_mod_cast hMle i
        rw [norm_rate]
        calc
          _ ≤ 2 * Real.pi * (M : ℝ) + 1 := by gcongr
          _ ≤ _ := by
            have hn : 2 * Real.pi ≤ 2 * Real.pi * (M : ℝ) :=
              (mul_one _).symm.le.trans (mul_le_mul_of_nonneg_left hM₀ (by positivity))
            linarith [Real.two_le_pi]
      _ = _ := by simp
  have hb := product_test_bound_of_upper_rectangles
    (fun i t ↦ weight (m i) t) (fun i t ↦ realCharacter (m i) t)
    (fun i ↦ (continuous_weight (m i)).measurable.comp measurable_subtype_coe)
    (fun i ↦ ‖rate (m i)‖) (fun i t ↦ (norm_weight (m i) t).le) (fun i ↦ weight_threshold_integral (m i))
    (empiricalMeasure u N) (cubeUniform (Fin d)) D hD (fun s t ↦ by
      rw [empiricalMeasure_real_apply u N (upperRectangle_measurable s t), upperRectangle_uniform_measure]
      have heq : ((range N).filter fun j ↦ u j ∈ upperRectangle s t) =
          (range N).filter (fun j ↦ ∀ i ∈ s, (u j i : ℝ) ≤ t i) := by
        apply Finset.filter_congr
        intro j _
        rfl
      rw [heq]
      exact hd s t)
  rw [integral_empiricalMeasure, integral_productCharacter_zero hm, sub_zero] at hb
  calc
    _ ≤ (∏ i, (‖rate (m i)‖ + 1)) * D := by simpa only [realCharacter_eq_fourier, mul_comm D] using hb
    _ ≤ _ := mul_le_mul_of_nonneg_right hcomp hD

end
end VdC

end

end VdC_RectangleFourier_Module

/- Source: VdC/RectangleTransfer.lean -/
section VdC_RectangleTransfer_Module

/-! # Rectangle Transfer -/

@[expose] public section

open Finset MeasureTheory Set
open scoped BigOperators

namespace VdC

noncomputable section

/-- The manuscript's finite Fourier estimate in terms of its closed-rectangle discrepancy. -/
theorem finite_fourier_rectangle_bound {d : ℕ} (m : Fin d → ℤ) (hm : m ≠ 0)
    (u : ℕ → Fin d → UnitInterval) (N : ℕ) :
    ‖cesaro (fun n ↦ torusCharacter m (fun i ↦ ((u n i : ℝ) : UnitAddCircle))) N‖ ≤
      fourierDiscrepancyConstant m * rectangleDiscrepancy u N := by
  classical
  have h := finite_fourier_bound_of_upper_rectangles m hm u N
    (rectangleDiscrepancy u N) (rectangleDiscrepancy_mem_Icc u N).1
  apply h
  intro s t
  let a : Fin d → UnitInterval := fun _ ↦ ⟨0, by simp⟩
  let b : Fin d → UnitInterval := fun i ↦ if i ∈ s then t i else ⟨1, by simp⟩
  have hf (n : ℕ) : (∀ i, (a i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ b i) ↔
      ∀ i ∈ s, (u n i : ℝ) ≤ t i := by
    refine ⟨fun H i hi ↦ ?_, fun H i ↦ ⟨(u n i).property.1, ?_⟩⟩
    · simpa [b, hi] using (H i).2
    by_cases hi : i ∈ s
    · simpa [b, hi] using H i hi
    · simpa [b, hi] using (u n i).property.2
  have hfreq : rectangleFrequency u N a b =
      (((range N).filter fun n ↦ ∀ i ∈ s, (u n i : ℝ) ≤ t i).card : ℝ) / N := by
    unfold rectangleFrequency
    exact congrArg (fun T : Finset ℕ ↦ (T.card : ℝ) / N) (Finset.filter_congr (fun n _ ↦ hf n))
  have hvol : rectangleVolume a b = ∏ i ∈ s, (t i : ℝ) := by
    unfold rectangleVolume
    simp only [a, sub_zero, max_eq_right (b _).property.1]
    simp only [b, apply_ite Subtype.val, Finset.prod_ite_mem, Finset.univ_inter]
  rw [← hfreq, ← hvol]
  exact rectangle_deviation_le_discrepancy u N a b

/-- The finite rectangle estimate for the differences of an arbitrary torus sequence. -/
theorem characterRectangleEstimate_all {d : ℕ} (x : ℕ → Torus d) : CharacterRectangleEstimate x := by
  intro m hm
  refine ⟨fourierDiscrepancyConstant m, fourierDiscrepancyConstant_nonneg m, fun h N ↦ ?_⟩
  let u (n : ℕ) (i : Fin d) := unitRepresentative (x (n + (h + 1)) i - x n i)
  have he (n : ℕ) : (fun i ↦ x (n + (h + 1)) i - x n i) = x (n + (h + 1)) - x n := rfl
  simpa only [u, unitRepresentative_coe, differenceDiscrepancy, he] using
    finite_fourier_rectangle_bound m hm u N

end
end VdC

end

end VdC_RectangleTransfer_Module

/- Source: VdC/CubeDifference.lean -/
section VdC_CubeDifference_Module

/-! # Cube Difference -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

noncomputable section

theorem spectrallyLebesgueDistribution_of_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : SpectrallyLebesgueDistribution (torusHaar d) (fun n => cubeToTorus (x n))) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x := by
  intro f hf
  apply spectrallyLebesgue_of_meanSquare_approximation (bounded_test f x)
  intro ε hε
  obtain ⟨g, hg, herr⟩ := exists_centered_torus_approx ((hx.weaklyMixing _).equidistributed _) f hf ε hε
  exact ⟨fun n => g (cubeToTorus (x n)), hx g hg, herr⟩

theorem weaklyMixingDistribution_of_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : WeaklyMixingDistribution (torusHaar d) (fun n => cubeToTorus (x n))) :
    WeaklyMixingDistribution (cubeLebesgue d) x := by
  intro f hf
  apply nearlyWeakMixing_of_cesaro_l2_approx (bounded_test f x)
  intro ε hε
  obtain ⟨g, hg, herr⟩ := exists_centered_torus_approx (hx.equidistributed _) f hf ε hε
  exact ⟨fun n => g (cubeToTorus (x n)), hx g hg, herr⟩

private def pullbackTest {d : ℕ} (g : C(Torus d, ℂ)) : C(Cube d, ℂ) :=
  g.comp ⟨cubeToTorus, continuous_cubeToTorus d⟩

private theorem testMean_pullbackTest {d : ℕ} (g : C(Torus d, ℂ)) :
    testMean (cubeLebesgue d) (pullbackTest g) = testMean (torusHaar d) g := by
  unfold testMean
  rw [← (cubeToTorus_measurePreserving d).map_eq,
    integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable g.continuous.stronglyMeasurable]
  rfl

theorem cube_sLebesgue_iff_characters {d : ℕ} (x : ℕ → Cube d) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      SpectrallyLebesgue (fun n => torusCharacter m (cubeToTorus (x n))) := by
  constructor
  · intro hx m hm
    exact hx (pullbackTest (torusCharacter m)) (by simp [testMean_pullbackTest, testMean_torusCharacter, hm])
  · intro h
    exact spectrallyLebesgueDistribution_of_cubeToTorus ((spectralLebesgueDistribution_iff_torus_characters _).2 h)

theorem cube_weakMixing_iff_characters {d : ℕ} (x : ℕ → Cube d) :
    WeaklyMixingDistribution (cubeLebesgue d) x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      NearlyWeakMixing (fun n => torusCharacter m (cubeToTorus (x n))) := by
  constructor
  · intro hx m hm
    exact hx (pullbackTest (torusCharacter m)) (by simp [testMean_pullbackTest, testMean_torusCharacter, hm])
  · intro h
    exact weaklyMixingDistribution_of_cubeToTorus ((weaklyMixingDistribution_iff_torus_characters _).2 h)

/-- GeneralizationOfClassicalvdC. The lag-difference discrepancies are those
of the coordinatewise modulo-one representatives. -/
theorem cube_spectral_difference_theorem {d : ℕ} (x : ℕ → Cube d)
    (h : Summable (fun j => upperDifferenceDiscrepancy (fun n => cubeToTorus (x n)) j ^ 2)) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x :=
  spectrallyLebesgueDistribution_of_cubeToTorus <|
    spectral_difference_theorem _ (characterRectangleEstimate_all _) h

/-- WeakMixingUDvdC. The limsup at each lag is taken before the lag average. -/
theorem cube_weakMixing_difference_theorem {d : ℕ} (x : ℕ → Cube d)
    (h : Tendsto (realCesaro (upperDifferenceDiscrepancy (fun n => cubeToTorus (x n)))) atTop (𝓝 0)) :
    WeaklyMixingDistribution (cubeLebesgue d) x :=
  weaklyMixingDistribution_of_cubeToTorus <|
    weakMixing_difference_theorem _ (characterRectangleEstimate_all _) h

/-- The Fourier-coefficient hypothesis from the preliminary spectral criterion. -/
theorem cube_spectral_difference_from_fourier {d : ℕ} (x : ℕ → Cube d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Summable (fun j => limsup (fun N =>
      ‖cesaro (fun n => torusCharacter m (cubeToTorus (x (n + (j + 1))) - cubeToTorus (x n))) N‖ ^ 2) atTop)) :
    SpectrallyLebesgueDistribution (cubeLebesgue d) x :=
  spectrallyLebesgueDistribution_of_cubeToTorus (spectral_difference_from_fourier _ h)

/-- The Fourier-coefficient hypothesis from the preliminary weak mixing criterion. -/
theorem cube_weakMixing_difference_from_fourier {d : ℕ} (x : ℕ → Cube d)
    (h : ∀ m : Fin d → ℤ, m ≠ 0 → Tendsto (realCesaro (fun j => limsup (fun N =>
      ‖cesaro (fun n => torusCharacter m (cubeToTorus (x (n + (j + 1))) - cubeToTorus (x n))) N‖) atTop))
      atTop (𝓝 0)) : WeaklyMixingDistribution (cubeLebesgue d) x :=
  weaklyMixingDistribution_of_cubeToTorus (weakMixing_difference_from_fourier _ h)

/-- UniformDistributionvanderCorputsDifferenceTheorem on the closed cube. -/
theorem equidistributed_of_cube_differences {d : ℕ} (x : ℕ → Cube d)
    (h : ∀ h : ℕ, 0 < h → Equidistributed (torusHaar d)
      (fun n => cubeToTorus (x (n + h)) - cubeToTorus (x n))) :
    Equidistributed (cubeLebesgue d) x :=
  equidistributed_of_cubeToTorus (equidistributed_of_torus_differences _ h)

end
end VdC

end

end VdC_CubeDifference_Module

/- Source: VdC/DigitExamples.lean -/
section VdC_DigitExamples_Module

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

end

end VdC_DigitExamples_Module

/- Source: VdC/ResidueAverages.lean -/
section VdC_ResidueAverages_Module

/-! Cesàro averages split over residue classes, including incomplete last blocks. -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

theorem sum_range_mul_residue {A : Type*} [AddCommMonoid A] (u : ℕ → A) (r N : ℕ) :
    ∑ n ∈ range (r * N), u n = ∑ t ∈ range r, ∑ n ∈ range N, u (r * n + t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]

/-- The average over a complete collection of `N` blocks of size `r`. -/
theorem cesaro_mul_residue (u : ℕ → ℂ) (r N : ℕ) :
    cesaro u (r * N) =
      (∑ t ∈ range r, cesaro (fun n ↦ u (r * n + t)) N) / (r : ℂ) := by
  simp only [cesaro]
  rw [sum_range_mul_residue, Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm (N : ℂ)]

private theorem natCast_mul_cesaro (u : ℕ → ℂ) (N : ℕ) :
    (N : ℂ) * cesaro u N = ∑ n ∈ range N, u n := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [cesaro]
  · rw [cesaro, ← mul_div_assoc, mul_div_cancel_left₀ _ (by exact_mod_cast hN)]

/-- Omitting the last `N-M` entries changes a normalized bounded average by at most
`2 C (N-M)/N`. Lean's zero-length average is zero. -/
theorem norm_cesaro_sub_prefix_le (u : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) {M N : ℕ} (hMN : M ≤ N) :
    ‖cesaro u N - cesaro u M‖ ≤ 2 * C * (↑(N - M) : ℝ) / (N : ℝ) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have : M = 0 := by omega
    simp [this]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have he : cesaro u N - cesaro u M =
      ((∑ n ∈ Ico M N, u n) - ((N - M : ℕ) : ℂ) * cesaro u M) / (N : ℂ) := by
    calc
      _ = ((M : ℂ) * cesaro u M + (∑ n ∈ Ico M N, u n)) / (N : ℂ) - cesaro u M := by
        rw [natCast_mul_cesaro, Finset.sum_range_add_sum_Ico _ hMN]
        rfl
      _ = _ := by rw [Nat.cast_sub hMN]; field_simp; ring
  rw [he, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have htail : ‖∑ n ∈ Ico M N, u n‖ ≤ (↑(N - M) : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ Ico M N, ‖u n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Ico M N, C := Finset.sum_le_sum fun n _ ↦ hu n
      _ = _ := by simp [Nat.card_Ico]
  have hscale : ‖((N - M : ℕ) : ℂ) * cesaro u M‖ ≤ (↑(N - M) : ℝ) * C := by
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_cesaro_le u hC hu M) (Nat.cast_nonneg _)
  exact (norm_sub_le _ _).trans (by nlinarith only [htail, hscale])

/-- A bounded sequence has the same limiting average along all lengths as along
lengths divisible by a fixed positive integer. -/
theorem tendsto_cesaro_of_chunked {u : ℕ → ℂ} {r : ℕ} {z : ℂ} (hr : 0 < r)
    (hu : BoundedSeq u) (h : Tendsto (fun N ↦ cesaro u (r * N)) atTop (𝓝 z)) :
    Tendsto (cesaro u) atTop (𝓝 z) := by
  obtain ⟨C, hC, hbound⟩ := hu
  have hdiv : Tendsto (fun N : ℕ ↦ N / r) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ eventually_atTop.2 ⟨b * r, fun N hN ↦ ?_⟩
    exact (Nat.le_div_iff_mul_le hr).2 hN
  have hchunk := h.comp hdiv
  have herr (N : ℕ) : ‖cesaro u N - cesaro u (r * (N / r))‖ ≤ (2 * C * r) / (N : ℝ) := by
    have he := Nat.mod_add_div N r
    have hle : r * (N / r) ≤ N := by omega
    have hrem : N - r * (N / r) ≤ r := by
      have hm := Nat.mod_lt N hr
      omega
    apply (norm_cesaro_sub_prefix_le u hC hbound hle).trans
    gcongr
  have hlim : Tendsto (fun N : ℕ ↦ (2 * C * (r : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
        (2 * C * (r : ℝ))
  have hnorm := squeeze_zero (fun _ ↦ norm_nonneg _) herr hlim
  have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [Function.comp_def, zero_add, sub_add_cancel] using hzero.add hchunk

/-- Combine the limiting averages of all residues of a bounded sequence. -/
theorem tendsto_cesaro_of_residue_limits {u : ℕ → ℂ} {r : ℕ} (hr : 0 < r)
    (hu : BoundedSeq u) (z : ℕ → ℂ)
    (h : ∀ t < r, Tendsto (cesaro (fun n ↦ u (r * n + t))) atTop (𝓝 (z t))) :
    Tendsto (cesaro u) atTop (𝓝 ((∑ t ∈ range r, z t) / (r : ℂ))) := by
  apply tendsto_cesaro_of_chunked hr hu
  simp_rw [cesaro_mul_residue]
  exact (tendsto_finsetSum _ (fun t ht ↦ h t (mem_range.1 ht))).div_const _

end VdC

end

end VdC_ResidueAverages_Module

/- Source: VdC/DigitCorrelation.lean -/
section VdC_DigitCorrelation_Module

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

end

end VdC_DigitCorrelation_Module

/- Source: VdC/DigitLacunary.lean -/
section VdC_DigitLacunary_Module

/-! # Digit Lacunary -/

@[expose] public section

open Filter
open scoped Topology ComplexConjugate

namespace VdC

noncomputable section

def digitAutocorrelation (r m : ℕ) (hr : 1 < r) (h : ℕ) : ℂ :=
  (digitCorrelation_limit_exists (m := m) hr h).choose

theorem tendsto_digitAutocorrelation {r m : ℕ} (hr : 1 < r) (h : ℕ) :
    Tendsto (corr (digitCharacter r m) (digitCharacter r m) h) atTop (𝓝 (digitAutocorrelation r m hr h)) :=
  (digitCorrelation_limit_exists (m := m) hr h).choose_spec

theorem digitAutocorrelation_zero {r m : ℕ} (hr : 1 < r) : digitAutocorrelation r m hr 0 = 1 :=
  tendsto_nhds_unique (tendsto_digitAutocorrelation hr 0)
    (tendsto_const_nhds.congr' ((eventually_gt_atTop (0 : ℕ)).mono fun _ hN => (digitCorrelation_zero hN).symm))

theorem digitAutocorrelation_one {r m : ℕ} (hr : 1 < r) :
    digitAutocorrelation r m hr 1 = digitFirstCorrelation r m :=
  tendsto_nhds_unique (tendsto_digitAutocorrelation hr 1) (tendsto_digitCorrelation_one hr)

theorem digitAutocorrelation_recursion {r m t : ℕ} (hr : 1 < r) (ht : t < r) (q : ℕ) :
    let a := digitAutocorrelation r m hr
    a (r*q+t) = (digitRoot r ^ m) ^ t *
      (((r-t : ℕ) : ℂ) * a q + (t : ℂ) * a (q+1)) / (r : ℂ) := by
  dsimp only
  have hN : Tendsto (fun N => r * N) atTop atTop :=
    (show StrictMono (fun N => r * N) from fun _ _ h => Nat.mul_lt_mul_of_pos_left h
      (lt_trans Nat.zero_lt_one hr)).tendsto_atTop
  have h := (tendsto_digitAutocorrelation (m := m) hr (r*q+t)).comp hN
  have hu := (tendsto_digitAutocorrelation (m := m) hr q).const_mul ((r-t : ℕ) : ℂ)
  have hv := (tendsto_digitAutocorrelation (m := m) hr (q+1)).const_mul (t : ℂ)
  apply tendsto_nhds_unique h
  refine (((hu.add hv).const_mul ((digitRoot r ^ m) ^ t)).div_const (r : ℂ)).congr fun N => ?_
  exact (digitCorrelation_chunks hr ht q N).symm

theorem digitAutocorrelation_left_mul {r m : ℕ} (hr : 1 < r) (q : ℕ) :
    digitAutocorrelation r m hr (r*q) = digitAutocorrelation r m hr q := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hr).ne'
  have h := digitAutocorrelation_recursion (m := m) hr (t := 0) (lt_trans Nat.zero_lt_one hr) q
  simpa [hc, mul_div_cancel_left₀] using h

theorem digitAutocorrelation_pow_mul {r m : ℕ} (hr : 1 < r) (k q : ℕ) :
    digitAutocorrelation r m hr (r^k*q) = digitAutocorrelation r m hr q := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, digitAutocorrelation_left_mul hr, ih]

theorem digitAutocorrelation_pow {r m : ℕ} (hr : 1 < r) (k : ℕ) :
    digitAutocorrelation r m hr (r^k) = digitFirstCorrelation r m := by
  simpa [digitAutocorrelation_one hr] using digitAutocorrelation_pow_mul (m := m) hr k 1

theorem tendsto_digitAutocorrelation_pow_sub_one {r m : ℕ} (hr : 1 < r) :
    let c := digitFirstCorrelation r m
    Tendsto (fun k => digitAutocorrelation r m hr (r^k-1)) atTop (𝓝 (c * star c)) := by
  dsimp only
  let c := digitFirstCorrelation r m
  let ζ := digitRoot r ^ m
  let α := star ζ / (r : ℂ)
  let s k := digitAutocorrelation r m hr (r^k-1)
  have hr0 : 0 < r := lt_trans Nat.zero_lt_one hr
  have hR : (1 : ℝ) < r := by exact_mod_cast hr
  have hRc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_pow]
  have hζ0 : ζ ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hζpow : ζ ^ r = 1 := by
    change (digitRoot r ^ m) ^ r = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, (digitRoot_primitive hr0).pow_eq_one, one_pow]
  have hunit : ζ * star ζ = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hζ, Complex.ofReal_one, one_pow]
  have hlast : ζ ^ (r-1) = star ζ := by
    apply (mul_right_inj' hζ0).1
    rw [mul_comm ζ (ζ ^ (r-1)), ← pow_succ, Nat.sub_add_cancel hr0, hζpow, hunit]
  have hden : (r : ℂ) - ζ ≠ 0 := by
    intro he
    have ht := congrArg norm (sub_eq_zero.mp he)
    rw [Complex.norm_natCast, hζ] at ht
    exact hR.ne ht.symm
  have hc : c * ((r : ℂ) - ζ) = ((r-1 : ℕ) : ℂ) * ζ := div_mul_cancel₀ _ hden
  have hc' : star c * ((r : ℂ) - star ζ) = ((r-1 : ℕ) : ℂ) * star ζ := by
    have hh := congrArg (starRingEnd ℂ) hc
    simpa only [map_mul, map_sub, map_natCast, starRingEnd_apply] using hh
  have he (k : ℕ) : s (k+1) - c * star c = α * (s k - c * star c) := by
    have hk : 0 < r^k := pow_pos hr0 _
    have hidx : r*(r^k-1)+(r-1) = r^(k+1)-1 := by
      rw [pow_succ', Nat.mul_sub_left_distrib, Nat.mul_one]
      have h := Nat.le_mul_of_pos_right r hk
      omega
    have ht : r-1 < r := by omega
    have hs := digitAutocorrelation_recursion (m := m) hr ht (r^k-1)
    dsimp only at hs
    rw [hidx, Nat.sub_add_cancel hk, show r-(r-1)=1 by omega, digitAutocorrelation_pow hr] at hs
    change digitAutocorrelation r m hr (r^(k+1)-1) - _ = _
    rw [hs, Nat.cast_one, one_mul]
    change ζ^(r-1) * (s k + ((r-1 : ℕ) : ℂ)*c) / (r:ℂ) - c*star c = _
    rw [hlast]
    dsimp [α]
    field_simp
    simp only [Complex.star_def] at hc' ⊢
    linear_combination -c * hc'
  have he' (k : ℕ) : s k - c*star c = α^k * (s 0-c*star c) := by
    induction k with
    | zero => simp
    | succ k ih => rw [he, ih, pow_succ', mul_assoc]
  have hα : ‖α‖ < 1 := by
    change ‖star ζ / (r : ℂ)‖ < 1
    rw [norm_div, norm_star, hζ, Complex.norm_natCast, one_div]
    exact inv_lt_one_of_one_lt₀ hR
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hα).mul_const (s 0-c*star c)
  have hh := ht.congr fun k => (he' k).symm
  have ht' := hh.add (tendsto_const_nhds (x := c*star c))
  simpa only [sub_add_cancel, zero_mul, zero_add, s, c] using ht'

end
end VdC

end

end VdC_DigitLacunary_Module

/- Source: VdC/SpectralSeparation.lean -/
section VdC_SpectralSeparation_Module

/-! # Spectral Separation -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Distinct squared-mean limits for the same continuous tests force mutual singularity. -/
theorem mutuallySingular_of_distinct_squared_mean_limits (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (F : ℕ → C(X, ℂ)) {a b : ℂ} (hab : a ≠ b)
    (ha : Tendsto (fun n => ∫ x, ‖F n x - a‖ ^ 2 ∂μ) atTop (𝓝 0))
    (hb : Tendsto (fun n => ∫ x, ‖F n x - b‖ ^ 2 ∂ν) atTop (𝓝 0)) : μ.MutuallySingular ν := by
  have hmeasure (ρ : Measure X) [IsFiniteMeasure ρ] (c : ℂ)
      (hc : Tendsto (fun n => ∫ x, ‖F n x - c‖ ^ 2 ∂ρ) atTop (𝓝 0)) :
      TendstoInMeasure ρ (fun n x => F n x) atTop (fun _ => c) := by
    apply tendstoInMeasure_iff_measureReal_dist.2
    intro ε hε
    have ht : Tendsto (fun n => (∫ x, ‖F n x - c‖ ^ 2 ∂ρ) / ε ^ 2) atTop (𝓝 0) := by
      simpa only [zero_div] using hc.div_const (ε ^ 2)
    refine squeeze_zero (fun _ => measureReal_nonneg) ?_ ht
    · intro n
      have hf : Integrable (fun x => ‖F n x - c‖ ^ 2) ρ :=
        ((F n).continuous.sub continuous_const).norm.pow 2 |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hM := mul_meas_ge_le_integral_of_nonneg (μ := ρ)
        (Eventually.of_forall fun x => sq_nonneg ‖F n x - c‖) hf (ε ^ 2)
      have hh : ρ.real { x | ε ≤ dist (F n x) c } ≤ ρ.real { x | ε ^ 2 ≤ ‖F n x - c‖ ^ 2 } :=
        measureReal_mono (fun x hx => by
          change ε ≤ dist (F n x) c at hx
          rw [dist_eq_norm] at hx
          exact pow_le_pow_left₀ hε.le hx 2)
      apply (le_div_iff₀ (sq_pos_of_pos hε)).2
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left hh (sq_nonneg ε)).trans hM
  obtain ⟨φ, hφ, hμ⟩ := (hmeasure μ a ha).exists_seq_tendsto_ae
  obtain ⟨ψ, hψ, hν⟩ := ((hmeasure ν b hb).comp hφ.tendsto_atTop).exists_seq_tendsto_ae
  let E := {x | Tendsto (fun n => F (φ (ψ n)) x) atTop (𝓝 a)}
  have hE : MeasurableSet E :=
    measurableSet_tendsto_fun (fun n => (F (φ (ψ n))).continuous.measurable) measurable_const
  refine ⟨Eᶜ, hE.compl, ?_, ?_⟩
  · exact ae_iff.1 (hμ.mono fun x hx => hx.comp hψ.tendsto_atTop)
  · rw [compl_compl]
    have hbad : ∀ᵐ x ∂ν, x ∉ E := hν.mono fun x hb' ha' => hab (tendsto_nhds_unique ha' hb')
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.1 hbad

/-- If the real Gram coefficients of bounded continuous tests are controlled
by a decaying Toeplitz envelope, the Cesàro means tend to zero in mean square. -/
theorem tendsto_squareIntegral_cesaro_of_gram (μ : Measure X) [IsFiniteMeasure μ]
    (u : ℕ → C(X, ℂ)) (D : ℕ → ℝ) (hD : ∀ h, 0 ≤ D h)
    (hlim : Tendsto D atTop (𝓝 0))
    (hGram : ∀ i j : ℕ, (testMean μ (u i * star (u j))).re ≤ D (i-j+(j-i))) :
    Tendsto (fun N => ∫ x, ‖cesaro (fun n => u n x) N‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hform (N : ℕ) : (∫ x, ‖cesaro (fun n => u n x) N‖ ^ 2 ∂μ) =
      (∑ i ∈ range N, ∑ j ∈ range N, (testMean μ (u i * star (u j))).re) / (N : ℝ)^2 := by
    have hpoint (x : X) : ‖cesaro (fun i => u i x) N‖ ^ 2 =
        (∑ i ∈ range N, ∑ j ∈ range N, (u i x * star (u j x)).re) / (N : ℝ)^2 := by
      let z := cesaro (fun i => u i x) N
      have hz : ‖z‖ ^ 2 = (z * star z).re := by
        rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [hz]
      change (cesaro (fun i => u i x) N * star (cesaro (fun i => u i x) N)).re = _
      rw [star_cesaro, cesaro, cesaro, div_mul_div_comm, Finset.sum_mul]
      simp only [Finset.mul_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, pow_two,
        Complex.div_ofReal_re, Complex.re_sum]
    rw [show (fun x => ‖cesaro (fun n => u n x) N‖ ^ 2) = _ from funext hpoint, integral_div]
    congr 1
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro j _
        exact integral_re (test_integrable μ (u i * star (u j)))
      · intro j _
        exact (test_integrable μ (u i * star (u j))).re
    · intro i _
      exact integrable_finsetSum _ (fun j _ => (test_integrable μ (u i * star (u j))).re)
  have hbound (N : ℕ) : (∫ x, ‖cesaro (fun n => u n x) N‖ ^ 2 ∂μ) ≤
      2 * (D 0 / (N : ℝ) + realCesaro (fun h => D (h+1)) N) := by
    rw [hform]
    by_cases hN : N = 0
    · simp [hN, realCesaro]
    have hNr : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    have ht := (sum_le_sum fun i _ => sum_le_sum fun j _ => hGram i j).trans
      (double_toeplitz_bound D hD N)
    apply (div_le_iff₀ (sq_pos_of_pos hNr)).2
    convert ht using 1
    rw [realCesaro]
    field_simp
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) hbound
  have hh := realCesaro_tendsto_zero_of_tendsto_zero (fun h => hD (h+1))
    (hlim.comp (tendsto_add_atTop_nat 1))
  simpa only [add_zero, mul_zero] using ((tendsto_const_div_atTop_nhds_zero_nat (D 0)).add hh).const_mul 2

end
end VdC

end

end VdC_SpectralSeparation_Module

/- Source: VdC/DigitSpectrum.lean -/
section VdC_DigitSpectrum_Module

/-! # Digit Spectrum -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

private def lacunaryCharacter (r k : ℕ) : C(UnitAddCircle, ℂ) := fourier (-(↑(r^k : ℕ) : ℤ))

private theorem testMean_lacunaryCharacter (μ : Measure UnitAddCircle) (r k : ℕ) :
    testMean μ (lacunaryCharacter r k) = measureFourier μ (↑(r^k : ℕ)) := rfl

private theorem testMean_lacunary_product (μ : Measure UnitAddCircle) (r i j : ℕ) :
    testMean μ (lacunaryCharacter r i * star (lacunaryCharacter r j)) =
      measureFourier μ ((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)) := by
  unfold testMean measureFourier
  congr 1
  ext x
  simp only [lacunaryCharacter, ContinuousMap.mul_apply, ContinuousMap.star_apply, Complex.star_def,
    ← fourier_neg, ← fourier_add]
  congr 2
  ring

private theorem testMean_centeredGram {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : C(X, ℂ)) {c : ℂ} (hf : testMean μ f = c) (hg : testMean μ g = c) :
    testMean μ ((f - ContinuousMap.const X c) * star (g - ContinuousMap.const X c)) =
      testMean μ (f * star g) - c * star c := by
  let a := ContinuousMap.const X c
  have he : (f-a) * star (g-a) = (f*star g - star c • f) - c • star g + ContinuousMap.const X (c*star c) := by
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.star_apply,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, a, ContinuousMap.const_apply, star_sub]
    ring
  change testMean μ ((f-a) * star (g-a)) = _
  rw [he, testMean_add, testMean_sub, testMean_sub, testMean_smul, testMean_smul, testMean_const,
    testMean_star, hf, hg]
  ring

private theorem lacunaryGram_real_symm {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (f g : C(X, ℂ)) :
    (testMean μ (f * star g)).re = (testMean μ (g * star f)).re := by
  rw [show f * star g = star (g * star f) by simp [mul_comm], testMean_star]
  rfl

private def lacunaryMean (r N : ℕ) : C(UnitAddCircle, ℂ) :=
  ⟨fun x => cesaro (fun k => lacunaryCharacter r k x) N, by unfold cesaro; fun_prop⟩

private theorem tendsto_lacunary_haar_measure_square {r : ℕ} (hr : 1 < r) :
    Tendsto (fun N => ∫ x, ‖lacunaryMean r N x - 0‖ ^ 2 ∂circleHaar) atTop (𝓝 0) := by
  let D (h : ℕ) : ℝ := if h = 0 then 1 else 0
  have hD : ∀ h, 0 ≤ D h := by intro h; unfold D; split <;> norm_num
  have hlim : Tendsto D atTop (𝓝 0) := tendsto_const_nhds.congr' <|
    (eventually_gt_atTop (0 : ℕ)).mono fun h hh => by simp [D, hh.ne']
  have hpow : StrictMono (fun k : ℕ => r^k) := pow_right_strictMono₀ hr
  have hGram (i j : ℕ) : (testMean circleHaar (lacunaryCharacter r i * star (lacunaryCharacter r j))).re ≤
      D (i-j+(j-i)) := by
    rw [testMean_lacunary_product]
    have he : measureFourier circleHaar ((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)) =
        if i = j then 1 else 0 := by
      unfold measureFourier
      change testMean circleHaar (fourier (-((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)))) = _
      rw [testMean_circle_character]
      have hz : -((↑(r^i : ℕ) : ℤ) - ↑(r^j : ℕ)) = 0 ↔ i = j := by
        rw [neg_eq_zero, sub_eq_zero]
        exact ⟨fun h => hpow.injective (by exact_mod_cast h), fun h => by rw [h]⟩
      simp only [hz]
    rw [he]
    by_cases h : i=j
    · subst j; simp [D]
    · rw [ite_eq_right h, Complex.zero_re]
      exact hD _
  simpa only [lacunaryMean, ContinuousMap.coe_mk, sub_zero] using
    tendsto_squareIntegral_cesaro_of_gram circleHaar (lacunaryCharacter r) D hD hlim hGram

private theorem tendsto_lacunary_digit_measure_square {r m : ℕ} (hr : 1 < r)
    (μ : FiniteMeasure UnitAddCircle) (hμ : HasSpectrum (digitAutocorrelation r m hr) μ) :
    Tendsto (fun N => ∫ x, ‖lacunaryMean r N x - digitFirstCorrelation r m‖ ^ 2 ∂(μ : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  have hmass : ((μ : Measure UnitAddCircle).real Set.univ : ℂ) = 1 := by
    simpa only [Nat.cast_zero, measureFourier_zero, digitAutocorrelation_zero hr] using hμ 0
  have : IsProbabilityMeasure (μ : Measure UnitAddCircle) := by
    constructor
    have h : (μ : Measure UnitAddCircle).real Set.univ = 1 := by exact_mod_cast hmass
    have hm := congrArg ENNReal.ofReal h
    rwa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_one] at hm
  let c := digitFirstCorrelation r m
  let u k : C(UnitAddCircle, ℂ) := lacunaryCharacter r k - ContinuousMap.const UnitAddCircle c
  let D k := ‖digitAutocorrelation r m hr (r^k-1)-c*star c‖
  have hD (k : ℕ) : 0 ≤ D k := norm_nonneg _
  have hlim : Tendsto D atTop (𝓝 0) := by
    simpa [D, c] using
      ((tendsto_digitAutocorrelation_pow_sub_one (m := m) hr).sub
        (tendsto_const_nhds (x := c*star c))).norm
  have hmean (k : ℕ) : testMean (μ : Measure UnitAddCircle) (lacunaryCharacter r k) = c := by
    rw [testMean_lacunaryCharacter, hμ, digitAutocorrelation_pow hr]
  have hGram (i j : ℕ) : (testMean (μ : Measure UnitAddCircle) (u i * star (u j))).re ≤
      D (i-j+(j-i)) := by
    suffices hle : ∀ (i j : ℕ), j ≤ i →
        (testMean (μ : Measure UnitAddCircle) (u i * star (u j))).re ≤ D (i-j) by
      rcases le_total j i with hij | hji
      · simpa [Nat.sub_eq_zero_of_le hij] using hle i j hij
      · rw [lacunaryGram_real_symm, Nat.sub_eq_zero_of_le hji, zero_add]
        exact hle j i hji
    intro i j hij
    have hpow : StrictMono (fun k : ℕ => r^k) := pow_right_strictMono₀ hr
    have hnat : r^i - r^j = r^j * (r^(i-j)-1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← pow_add, Nat.add_sub_of_le hij]
    change (testMean (μ : Measure UnitAddCircle)
      ((lacunaryCharacter r i - _) * star (lacunaryCharacter r j - _))).re ≤ _
    rw [testMean_centeredGram _ _ _ (hmean i) (hmean j), testMean_lacunary_product,
      ← Nat.cast_sub (hpow.monotone hij), hμ, hnat, digitAutocorrelation_pow_mul hr]
    exact Complex.re_le_norm _
  refine (tendsto_squareIntegral_cesaro_of_gram (μ : Measure UnitAddCircle) u D hD hlim hGram).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change ‖cesaro (fun n => lacunaryCharacter r n x-c) N‖ ^ 2 = ‖cesaro (fun n => lacunaryCharacter r n x) N-c‖ ^ 2
    rw [cesaro_sub, cesaro_const c hN]

/-- The base-r digit characters have singular spectral measures. This proof uses
their carry recursion and a lacunary Fourier average that separates those measures
from Haar measure. -/
theorem spectrallySingular_digitCharacter {r m : ℕ} (hr : 1 < r) :
    SpectrallySingular (digitCharacter r m) := by
  have hb : BoundedSeq (digitCharacter r m) := ⟨1, zero_le_one, fun _ => by simp⟩
  have hfull : CorrLimits (digitCharacter r m) (digitCharacter r m) id (digitAutocorrelation r m hr) :=
    fun h => tendsto_digitAutocorrelation hr h
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hb strictMono_id hfull
  have hs := mutuallySingular_of_distinct_squared_mean_limits (μ : Measure UnitAddCircle) circleHaar
    (lacunaryMean r) (digitFirstCorrelation_ne_zero (m := m) hr)
    (tendsto_lacunary_digit_measure_square hr μ hμ) (tendsto_lacunary_haar_measure_square hr)
  refine ⟨hb, fun N q hN hq => ⟨μ, fun h => ?_, hs⟩⟩
  rw [hμ]
  exact tendsto_nhds_unique ((tendsto_digitAutocorrelation hr h).comp hN.tendsto_atTop) (hq h)

/-- The manuscript's generalized Thue–Morse digit-sum residue example. -/
theorem spectrallySingular_digitResidue {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    HasPositiveLowerDensity (digitResidue r j) ∧ SpectrallySingular (selectionWeight (digitResidue r j)) :=
  ⟨digitResidue_positive_lowerDensity hr hj,
    spectrallySingular_digitResidue_of_characters hr hj (fun _ _ _ => spectrallySingular_digitCharacter hr)⟩

theorem spectrallySingular_digitResidue_enumeration {r j : ℕ} (hr : 1 < r) (hj : j < r) :
    StrictMono (digitResidueIndex r j) ∧ Set.range (digitResidueIndex r j) = digitResidue r j ∧
      HasPositiveLowerDensity (Set.range (digitResidueIndex r j)) ∧
      SpectrallySingular (selectionWeight (Set.range (digitResidueIndex r j))) := by
  refine ⟨strictMono_digitResidueIndex hr hj, range_digitResidueIndex hr hj, ?_⟩
  rw [range_digitResidueIndex hr hj]
  exact spectrallySingular_digitResidue hr hj

def thueMorsePositive : Set ℕ := {n | (-1 : ℂ)^digitSum 2 n = 1}

theorem thueMorsePositive_eq_digitResidue : thueMorsePositive = digitResidue 2 0 := by
  ext n
  change (-1 : ℂ)^digitSum 2 n = 1 ↔ digitSum 2 n % 2 = 0
  rw [neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1), Nat.even_iff]

/-- The positive entries of the binary Thue–Morse word give a spectrally singular
selection of positive density. -/
theorem thueMorse_positive_spectrallySingular :
    HasPositiveLowerDensity thueMorsePositive ∧ SpectrallySingular (selectionWeight thueMorsePositive) := by
  rw [thueMorsePositive_eq_digitResidue]
  exact spectrallySingular_digitResidue (by decide) (by decide)

end
end VdC

end

end VdC_DigitSpectrum_Module

/- Source: VdC/RectangleMeasure.lean -/
section VdC_RectangleMeasure_Module

/-! The closed rectangles used to compute the finite discrepancy on the cube. -/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace VdC

noncomputable section
open Classical

/-- The product of the closed intervals with endpoints `a i` and `b i`. -/
def closedRectangle {d : ℕ} (a b : Fin d → UnitInterval) : Set (Cube d) :=
  Set.univ.pi fun i ↦ Subtype.val ⁻¹' Set.Icc (a i : ℝ) (b i : ℝ)

theorem measurableSet_closedRectangle {d : ℕ} (a b : Fin d → UnitInterval) :
    MeasurableSet (closedRectangle a b) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc.preimage measurable_subtype_coe

/-- The product-of-lengths formula is the actual Lebesgue mass in the closed cube. -/
theorem rectangleVolume_eq_measure {d : ℕ} (a b : Fin d → UnitInterval) :
    rectangleVolume a b = (cubeLebesgue d).real (closedRectangle a b) := by
  unfold rectangleVolume closedRectangle cubeLebesgue
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [unitIntervalLebesgue, comap_subtype_coe_apply measurableSet_Icc]
  have hi : Subtype.val '' (Subtype.val ⁻¹' Set.Icc (a i : ℝ) (b i : ℝ) : Set UnitInterval) =
      Set.Icc (a i : ℝ) (b i : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, (a i).property.1.trans hx.1, hx.2.trans (b i).property.2⟩, hx, rfl⟩
  rw [hi, Real.volume_Icc, ENNReal.toReal_ofReal', max_comm]

/-- The finite count is the Cesàro average of the closed rectangle's indicator. -/
theorem rectangleFrequency_eq_indicator_average {d : ℕ} (u : ℕ → Cube d) (N : ℕ)
    (a b : Fin d → UnitInterval) :
    rectangleFrequency u N a b =
      realCesaro (fun j ↦ if u j ∈ closedRectangle a b then 1 else 0) N := by
  classical
  unfold rectangleFrequency realCesaro
  rw [← Finset.sum_filter]
  have he : ((range N).filter fun j ↦ ∀ i, (a i : ℝ) ≤ u j i ∧ (u j i : ℝ) ≤ b i) =
      (range N).filter (fun j ↦ u j ∈ closedRectangle a b) := by
    apply Finset.filter_congr
    intro j _
    simp only [closedRectangle, Set.mem_univ_pi, Set.mem_preimage, Set.mem_Icc]
  rw [he]
  simp

/-- Any bound for a family containing the closed rectangles bounds the formal discrepancy. -/
theorem rectangleDiscrepancy_le_of_family_bound {d : ℕ} (u : ℕ → Cube d) (N : ℕ)
    (𝓡 : Set (Set (Cube d))) (h𝓡 : ∀ a b, closedRectangle a b ∈ 𝓡)
    (C : ℝ) (hC : ∀ B ∈ 𝓡,
      |realCesaro (fun j ↦ if u j ∈ B then 1 else 0) N - (cubeLebesgue d).real B| ≤ C) :
    rectangleDiscrepancy u N ≤ C := by
  classical
  unfold rectangleDiscrepancy
  apply csSup_le
  · let z : Fin d → UnitInterval := fun _ ↦ ⟨0, by simp⟩
    exact ⟨_, ⟨(z, z), rfl⟩⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  simpa only [rectangleFrequency_eq_indicator_average, rectangleVolume_eq_measure] using
    hC (closedRectangle a b) (h𝓡 a b)

end

end VdC

end

end VdC_RectangleMeasure_Module

/- Source: VdC/DiscrepancySelection.lean -/
section VdC_DiscrepancySelection_Module

/-! # Discrepancy Selection -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology

namespace VdC

private theorem prefix_filter_range {σ : ℕ → ℕ} (hσ : StrictMono σ) (N : ℕ) :
    let A := Set.range σ
    letI := Classical.decPred (· ∈ A)
    let K := initialCount A N
    (range N).filter (· ∈ A) = (range K).map ⟨σ, hσ.injective⟩ := by
  classical
  dsimp only
  have hex : ∃ k, N ≤ σ k := ⟨N, hσ.id_le N⟩
  let M := Nat.find hex
  have HM : N ≤ σ M := Nat.find_spec hex
  have Hlt (k : ℕ) : σ k < N ↔ k < M := by
    constructor
    · intro hk
      by_contra! h
      exact (not_lt_of_ge (HM.trans (hσ.monotone h))) hk
    · intro hk
      exact lt_of_not_ge (Nat.find_min hex hk)
  have he : (range N).filter (· ∈ Set.range σ) = (range M).map ⟨σ, hσ.injective⟩ := by
    ext n
    simp only [mem_filter, mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hn, k, rfl⟩
      exact ⟨k, (Hlt k).mp hn, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Hlt k).mpr hk, ⟨k, rfl⟩⟩
  have hc : initialCount (Set.range σ) N = M := by unfold initialCount; rw [he, card_map, card_range]
  simpa only [hc] using he

/-- Erasing observations can account for at most the erased fraction of
rectangle discrepancy, plus the discrepancy in the retained observations. -/
theorem rectangleDiscrepancy_le_erased {d : ℕ} (u : ℕ → Cube d) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {N : ℕ} (hN : 0 < N) :
    let K := initialCount (Set.range σ) N
    rectangleDiscrepancy u N ≤ 1 - (K : ℝ) / (N : ℝ) + rectangleDiscrepancy (u ∘ σ) K := by
  classical
  let A := Set.range σ
  let K := initialCount A N
  let F := range N
  let e : ℕ ↪ ℕ := ⟨σ, hσ.injective⟩
  change rectangleDiscrepancy u N ≤ 1 - (K : ℝ) / (N : ℝ) + rectangleDiscrepancy (u ∘ σ) K
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmap : F.filter (· ∈ A) = (range K).map e := prefix_filter_range hσ N
  have hk : K = (F.filter (· ∈ A)).card := rfl
  have hK : K ≤ N := by rw [hk, ← card_range N]; exact card_filter_le ..
  have hKN : (K : ℝ) ≤ N := by exact_mod_cast hK
  have hbad : ((F.filter (· ∉ A)).card : ℝ) = N-K := by
    have he := card_filter_add_card_filter_not (s := F) (· ∈ A)
    rw [← hk, card_range] at he
    have heR : (K : ℝ) + ((F.filter (· ∉ A)).card : ℝ) = N := by exact_mod_cast he
    linarith
  unfold rectangleDiscrepancy
  apply csSup_le ⟨_, Set.mem_range_self ((fun _ => ⟨0, by simp⟩), (fun _ => ⟨0, by simp⟩))⟩
  rintro _ ⟨⟨a, b⟩, rfl⟩
  let P (n : ℕ) := ∀ i, (a i : ℝ) ≤ u n i ∧ (u n i : ℝ) ≤ b i
  let L := ((F.filter (· ∉ A)).filter P).card
  let v := rectangleVolume a b
  have hv : v ∈ Set.Icc (0 : ℝ) 1 := by
    change rectangleVolume a b ∈ _
    rw [rectangleVolume_eq_measure]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have hl : (L : ℝ) ≤ N-K := by
    rw [← hbad]
    exact_mod_cast card_filter_le (F.filter (· ∉ A)) P
  have hf : rectangleFrequency u N a b =
      (K * rectangleFrequency (u ∘ σ) K a b + L) / (N : ℝ) := by
    have hc : (F.filter P).card = ((F.filter (· ∈ A)).filter P).card + L := by
      have hh := card_filter_add_card_filter_not (s := F.filter P) (· ∈ A)
      simpa [L, filter_filter, and_comm] using hh.symm
    have hgood : ((F.filter (· ∈ A)).filter P).card = ((range K).filter (P ∘ σ)).card := by
      rw [hmap, filter_map, card_map]
      rfl
    have hv' : (K : ℝ) * rectangleFrequency (u ∘ σ) K a b = (((range K).filter (P ∘ σ)).card : ℝ) := by
      by_cases hk' : K = 0
      · simp [hk']
      · change (K : ℝ) * ((((range K).filter (P ∘ σ)).card : ℝ) / K) = _
        have hk'R : (K : ℝ) ≠ 0 := by exact_mod_cast hk'
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hk'R]
    change ((F.filter P).card : ℝ) / N = _
    rw [hc, Nat.cast_add, hgood, hv']
  have he : rectangleFrequency u N a b - v =
      (K : ℝ)/N*(rectangleFrequency (u ∘ σ) K a b-v) + ((L : ℝ) - (N-K)*v)/N := by
    rw [hf]
    field_simp
    ring
  have hterm : |((L : ℝ)-(N-K)*v)/N| ≤ 1 - (K : ℝ)/N := by
    rw [abs_div, abs_of_pos hN', show 1 - (K : ℝ)/N = (N-K)/N by field_simp]
    apply div_le_div_of_nonneg_right _ hN'.le
    have hL0 : (0:ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    have ha : 0 ≤ ((N:ℝ)-K)*v := mul_nonneg (sub_nonneg.mpr hKN) hv.1
    have hb : ((N:ℝ)-K)*v ≤ N-K := mul_le_of_le_one_right (sub_nonneg.mpr hKN) hv.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmain : |(K : ℝ)/N*(rectangleFrequency (u ∘ σ) K a b-v)| ≤ rectangleDiscrepancy (u ∘ σ) K := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (K : ℝ)/N)]
    have hh : (K : ℝ)/N ≤ 1 := (div_le_one hN').mpr hKN
    exact (mul_le_of_le_one_left (abs_nonneg _) hh).trans (rectangle_deviation_le_discrepancy _ _ _ _)
  change |rectangleFrequency u N a b - v| ≤ 1 - (K : ℝ) / N + rectangleDiscrepancy (u ∘ σ) K
  rw [he]
  exact (abs_add_le ..).trans (by linarith only [hterm, hmain])

theorem limsup_rectangleDiscrepancy_le_erased {d : ℕ} (u : ℕ → Cube d) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) {δ : ℝ}
    (hUD : Tendsto (rectangleDiscrepancy (u ∘ σ)) atTop (𝓝 0))
    (hbad : ∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
      1 - (initialCount (Set.range σ) N : ℝ) / (N : ℝ) ≤ δ + ε) :
    limsup (rectangleDiscrepancy u) atTop ≤ δ := by
  have hmono : Monotone (initialCount (Set.range σ)) := by
    intro M N hMN
    classical
    exact card_le_card (filter_subset_filter _ (range_mono hMN))
  have hKt : Tendsto (initialCount (Set.range σ)) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    refine eventually_atTop.2 ⟨σ K + 1, fun N hN => ?_⟩
    exact (Nat.le_succ K).trans ((initialCount_at_selection hσ K).ge.trans (hmono hN))
  refine (limsup_le_iff' (isCoboundedUnder_le_of_le atTop fun N => (rectangleDiscrepancy_mem_Icc u N).1)
    (isBoundedUnder_of ⟨1, fun N => (rectangleDiscrepancy_mem_Icc u N).2⟩)).2 ?_
  intro y hy
  let ε := (y-δ)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsmall := (hUD.comp hKt).eventually (gt_mem_nhds hε)
  filter_upwards [hsmall, hbad ε hε, eventually_gt_atTop (0 : ℕ)] with N hsmall hbad' hN
  have hsplit := rectangleDiscrepancy_le_erased u hσ hN
  dsimp only at hsmall hsplit
  dsimp [ε] at hsmall hbad'
  linarith only [hsplit, hsmall, hbad']

end VdC

end

end VdC_DiscrepancySelection_Module

/- Source: VdC/DuplicationBlocks.lean -/
section VdC_DuplicationBlocks_Module

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

end

end VdC_DuplicationBlocks_Module

/- Source: VdC/PolynomialPhases.lean -/
section VdC_PolynomialPhases_Module

/-! Linear and quadratic exponential averages needed for the polynomial example. -/

@[expose] public section

open Filter Function MeasureTheory
open scoped ComplexConjugate Topology

namespace VdC

noncomputable section

/-- The exponential character `exp(2πit)`. -/
def phase (t : ℝ) : ℂ := fourier (T := 1) 1 (t : UnitAddCircle)

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (a b : ℝ) : phase (a + b) = phase a * phase b := by
  simp only [phase, AddCircle.coe_add, fourier_apply, one_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul]

@[simp] theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  rw [phase, fourier_apply, Circle.norm_coe]

theorem phase_frequency (m : ℤ) (t : ℝ) :
    fourier m (t : UnitAddCircle) = phase ((m : ℝ) * t) := by
  rw [phase, fourier_apply, fourier_apply, one_zsmul, ← zsmul_eq_mul, AddCircle.coe_zsmul]

theorem star_phase (a : ℝ) : star (phase a) = phase (-a) := by
  change conj (fourier 1 (a : UnitAddCircle)) = phase (-a)
  rw [← fourier_neg, phase_frequency, Int.cast_neg, Int.cast_one, neg_one_mul]

theorem phase_sub (a b : ℝ) : phase (a - b) = phase a * star (phase b) := by
  rw [sub_eq_add_neg, phase_add, star_phase]

theorem phase_ne_one_of_irrational {b : ℝ} (hb : Irrational b) : phase b ≠ 1 := by
  intro h
  have hto : AddCircle.toCircle (b : UnitAddCircle) = AddCircle.toCircle (0 : UnitAddCircle) := by
    apply Subtype.ext
    simpa only [phase, fourier_apply, one_zsmul, AddCircle.toCircle_zero, Circle.coe_one] using h
  have h0 := (AddCircle.injective_toCircle (one_ne_zero : (1 : ℝ) ≠ 0)) hto
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
  exact hb.ne_int m (by simpa [zsmul_eq_mul] using hm.symm)

/-- The geometric-sum estimate is uniform in the intercept and prefix length. -/
theorem norm_sum_linear_phase_le {b : ℝ} (hb : phase b ≠ 1) (c : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (b * (n : ℝ) + c)‖ ≤ 2 / ‖phase b - 1‖ := by
  have hstep (n : ℕ) : phase (b * ((n+1 : ℕ) : ℝ) + c) =
      phase b * phase (b * (n : ℝ) + c) := by
    rw [← phase_add]
    congr 1
    push_cast
    ring
  have hsum (L : ℕ) : (phase b - 1) *
      (∑ n ∈ Finset.range L, phase (b * (n : ℝ) + c)) = phase (b * (L : ℝ) + c) - phase c := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, mul_add, ih, hstep]
      ring
  have hd : 0 < ‖phase b - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  rw [le_div_iff₀ hd, mul_comm, ← norm_mul, hsum]
  simpa [one_add_one_eq_two] using norm_sub_le (phase (b * (N : ℝ) + c)) (phase c)

/-- The linear exponential sum tends to zero when its slope is irrational. -/
theorem tendsto_cesaro_linear_phase {b : ℝ} (hb : Irrational b) (c : ℝ) :
    Tendsto (cesaro (fun n : ℕ ↦ phase (b * (n : ℝ) + c))) atTop (𝓝 0) := by
  let u (n : ℕ) := phase (b * (n : ℝ) + c)
  have hU : BoundedSeq u := ⟨1, zero_le_one, fun n ↦ (norm_phase _).le⟩
  have hstep : (fun n ↦ u (n + 1)) = fun n ↦ phase b * u n := by
    funext n
    dsimp only [u]
    rw [← phase_add]
    congr 1
    push_cast
    ring
  have h := tendsto_cesaro_shift_sub_zero hU 1
  rw [hstep] at h
  have he (N : ℕ) : cesaro (fun n ↦ phase b * u n) N - cesaro u N =
      (phase b - 1) * cesaro u N := by rw [cesaro_const_mul, sub_mul, one_mul]
  simp_rw [he] at h
  have hne : phase b - 1 ≠ 0 := sub_ne_zero.mpr (phase_ne_one_of_irrational hb)
  have hdiv := h.const_mul (phase b - 1)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_zero] using hdiv

/-- The quadratic exponential sum tends to zero when its leading coefficient is
irrational. All positive-lag autocorrelations reduce to the linear result. -/
theorem tendsto_cesaro_quadratic_phase {a : ℝ} (ha : Irrational a) (b c : ℝ) :
    Tendsto (cesaro (fun n : ℕ ↦ phase (a * (n : ℝ)^2 + b * (n : ℝ) + c))) atTop (𝓝 0) := by
  let u (n : ℕ) := phase (a * (n : ℝ)^2 + b * (n : ℝ) + c)
  have hU : BoundedSeq u := ⟨1, zero_le_one, fun n ↦ (norm_phase _).le⟩
  apply NearlyOrthogonal.tendsto_cesaro_zero
  apply (nearlyOrthogonal_iff_corr_tendsto_zero hU).2
  intro h hh
  have he : (fun n ↦ u (n + h) * star (u n)) =
      fun n : ℕ ↦ phase ((2 * a * (h : ℝ)) * (n : ℝ) + (a * (h : ℝ)^2 + b * (h : ℝ))) := by
    funext n
    simp only [u, ← phase_sub, Nat.cast_add]
    congr 1
    ring
  have hirr : Irrational (2 * a * (h : ℝ)) := by
    have ha2 : Irrational (2 * a) := by
      simpa only [Int.cast_ofNat] using ha.intCast_mul (m := 2) (by norm_num)
    exact ha2.mul_natCast hh.ne'
  unfold corr
  rw [he]
  exact tendsto_cesaro_linear_phase hirr _

/-- The normalized phase of a nonconstant integer polynomial of degree at most two
vanishes on average when the common factor `α` is irrational. -/
theorem tendsto_cesaro_integer_quadratic_phase {α : ℝ} (hα : Irrational α)
    (a b c : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    Tendsto (cesaro (fun n : ℕ ↦ phase (α * ((a : ℝ) * (n : ℝ)^2 + (b : ℝ) * (n : ℝ) + (c : ℝ)))))
      atTop (𝓝 0) := by
  have he : (fun n : ℕ ↦ phase (α * ((a : ℝ) * (n : ℝ)^2 + (b : ℝ) * (n : ℝ) + (c : ℝ)))) =
      fun n : ℕ ↦ phase ((α * a) * (n : ℝ)^2 + (α * b) * (n : ℝ) + α * c) := by
    funext n
    congr 1
    ring
  rw [he]
  by_cases ha : a = 0
  · subst a
    simpa using tendsto_cesaro_linear_phase (hα.mul_intCast (h.resolve_left (by simp))) (α * c)
  · exact tendsto_cesaro_quadratic_phase (hα.mul_intCast ha) _ _

end

end VdC

end

end VdC_PolynomialPhases_Module

/- Source: VdC/DuplicationEstimates.lean -/
section VdC_DuplicationEstimates_Module

/-! Uniform exponential-sum estimates for the duplicated blocks. -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

noncomputable section

/-- The amount subtracted from an index in the second half of its group. -/
def duplicationOffset (p r : ℕ) : ℤ := if r < p then 0 else (p : ℤ)

/-- The change in the original index under a lag inside one stage. -/
def duplicationGap (p h r : ℕ) : ℤ :=
  (h : ℤ) + duplicationOffset p r - duplicationOffset p ((r+h) % (2*p))

theorem duplicationGap_eq_zero_iff {p h r : ℕ} (hp : 0 < p) (hh : 0 < h) :
    duplicationGap p h r = 0 ↔ p = h ∧ r < p := by
  constructor
  · intro he
    by_cases h₁ : r < p <;> by_cases h₂ : (r+h) % (2*p) < p
    all_goals simp [duplicationGap, duplicationOffset, h₁, h₂] at he ⊢
    all_goals omega
  · rintro ⟨rfl, hr'⟩
    rw [duplicationGap, duplicationOffset, ite_eq_left hr',
      Nat.mod_eq_of_lt (by omega : r+p < 2*p), duplicationOffset, ite_eq_right (by omega)]
    ring

/-- The coincidences prescribed by the block construction. -/
def duplicationMask (p h t : ℕ) : Prop := p = h ∧ t % (2*p) < p

instance (p h t : ℕ) : Decidable (duplicationMask p h t) := by
  unfold duplicationMask
  infer_instance

def localIndex (A p t : ℕ) : ℤ :=
  (A : ℤ) + t - duplicationOffset p (t % (2*p))

/-- The masked exponential on a stage extended periodically beyond its right boundary. -/
def localMaskedPhase (α : ℝ) (m : ℤ) (A p h t : ℕ) : ℂ :=
  if duplicationMask p h t then 0
  else phase ((m : ℝ) * α *
    ((localIndex A p (t+h) : ℝ)^2 - (localIndex A p t : ℝ)^2))

private theorem norm_localMaskedPhase_le (α : ℝ) (m : ℤ) (A p h t : ℕ) :
    ‖localMaskedPhase α m A p h t‖ ≤ 1 := by
  unfold localMaskedPhase
  split <;> simp

def stageSlopeInt (m : ℤ) (p h r : ℕ) : ℤ :=
  4 * (p : ℤ) * m * duplicationGap p h r

private def stageIntercept (α : ℝ) (m : ℤ) (A p h r : ℕ) : ℝ :=
  (m : ℝ) * α * ((localIndex A p (r+h) : ℝ)^2 - (localIndex A p r : ℝ)^2)

private theorem localIndex_block (A p j r : ℕ) :
    localIndex A p ((2*p)*j+r) = (2*p : ℕ) * (j : ℤ) + localIndex A p r := by
  simp only [localIndex, Nat.mul_add_mod, Nat.cast_add, Nat.cast_mul]
  ring

private theorem localIndex_gap {A p h r : ℕ} (hr : r < 2*p) :
    localIndex A p (r+h) - localIndex A p r = duplicationGap p h r := by
  simp only [localIndex, duplicationGap, Nat.cast_add, Nat.mod_eq_of_lt hr]
  ring

private theorem localMaskedPhase_block {α : ℝ} {m : ℤ} {A p h r : ℕ}
    (hr : r < 2*p) (hn : ¬ (p = h ∧ r < p)) (j : ℕ) :
    localMaskedPhase α m A p h ((2*p)*j+r) =
      phase ((α * stageSlopeInt m p h r) * (j : ℝ) + stageIntercept α m A p h r) := by
  have hmask : ¬ duplicationMask p h ((2*p)*j+r) := by
    simpa [duplicationMask, Nat.mul_add_mod, Nat.mod_eq_of_lt hr] using hn
  rw [localMaskedPhase, ite_eq_right hmask]
  rw [add_assoc, localIndex_block, localIndex_block]
  have he := congrArg (fun x : ℤ ↦ (x : ℝ)) (localIndex_gap (A := A) (h := h) hr)
  push_cast at he
  congr 1
  simp only [stageSlopeInt, stageIntercept]
  push_cast
  rw [← he]
  ring

def residuePhaseBound (α : ℝ) (m : ℤ) (p h r : ℕ) : ℝ :=
  if p = h ∧ r < p then 0 else 2 / ‖phase (α * stageSlopeInt m p h r) - 1‖

private theorem residuePhaseBound_nonneg (α : ℝ) (m : ℤ) (p h r : ℕ) :
    0 ≤ residuePhaseBound α m p h r := by
  unfold residuePhaseBound
  split <;> positivity

private theorem norm_sum_residueMaskedPhase_le {α : ℝ} (hα : Irrational α) {m : ℤ}
    (hm : m ≠ 0) {p h r : ℕ} (hp : 0 < p) (hh : 0 < h) (hr : r < 2*p) (A L : ℕ) :
    ‖∑ j ∈ range L, localMaskedPhase α m A p h ((2*p)*j+r)‖ ≤ residuePhaseBound α m p h r := by
  by_cases hz : p = h ∧ r < p
  · have he (j : ℕ) : duplicationMask p h ((2*p)*j+r) := by
      simpa [duplicationMask, Nat.mul_add_mod, Nat.mod_eq_of_lt hr] using hz
    simp only [localMaskedPhase, he, ite_true, Finset.sum_const_zero, norm_zero]
    rw [residuePhaseBound, ite_eq_left hz]
  · simp_rw [localMaskedPhase_block hr hz]
    rw [residuePhaseBound, ite_eq_right hz]
    apply norm_sum_linear_phase_le
    apply phase_ne_one_of_irrational
    apply hα.mul_intCast
    have hg := mt (duplicationGap_eq_zero_iff (r := r) hp hh).mp hz
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hp.ne')) hm) hg

/-- Intercept-independent bound for every prefix of a masked stage, including the
incomplete group and the right-boundary terms of the actual construction. -/
def stagePhaseBound (α : ℝ) (m : ℤ) (p h : ℕ) : ℝ :=
  (∑ r ∈ range (2*p), residuePhaseBound α m p h r) + (2*p : ℕ) + 2*(h : ℝ)

theorem stagePhaseBound_nonneg (α : ℝ) (m : ℤ) (p h : ℕ) :
    0 ≤ stagePhaseBound α m p h := by
  have h := Finset.sum_nonneg (s := range (2*p)) (fun r _ ↦ residuePhaseBound_nonneg α m p h r)
  unfold stagePhaseBound
  positivity

private theorem norm_sum_localMaskedPhase_le {α : ℝ} (hα : Irrational α) {m : ℤ}
    (hm : m ≠ 0) {p h : ℕ} (hp : 0 < p) (hh : 0 < h) (A L : ℕ) :
    ‖∑ t ∈ range L, localMaskedPhase α m A p h t‖ ≤
      (∑ r ∈ range (2*p), residuePhaseBound α m p h r) + (2*p : ℕ) := by
  let u := localMaskedPhase α m A p h
  let k := L / (2*p)
  let s := L % (2*p)
  have he : (2*p)*k+s = L := by
    simpa [k, s, add_comm] using Nat.mod_add_div L (2*p)
  have hs : s ≤ 2*p := (Nat.mod_lt _ (by omega)).le
  rw [← he, Finset.sum_range_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [sum_range_mul_residue]
    exact (norm_sum_le _ _).trans (sum_le_sum fun r hr ↦
      norm_sum_residueMaskedPhase_le hα hm hp hh (mem_range.mp hr) A k)
  · apply (norm_sum_le _ _).trans
    exact (sum_le_sum (g := fun _ ↦ (1 : ℝ)) fun t _ ↦ norm_localMaskedPhase_le ..).trans
      (by simp; exact_mod_cast hs)

theorem duplicationBlock_bounds (request : ℕ → ℕ) (n : ℕ) :
    duplicationStart request (duplicationBlock request n) ≤ n ∧
      n < duplicationStart request (duplicationBlock request n+1) := by
  have he : ∃ q, n < duplicationStart request (q+1) :=
    ⟨n, (Nat.lt_succ_self n).trans_le (le_duplicationStart request (n+1))⟩
  obtain ⟨hh, hmin⟩ := (Nat.find_eq_iff he).mp (rfl : Nat.find he = Nat.find he)
  change duplicationStart request (Nat.find he) ≤ n ∧ _
  refine ⟨?_, hh⟩
  rcases e : Nat.find he with _ | q
  · exact Nat.zero_le _
  · simpa only [not_lt] using hmin q (by rw [e]; omega)

/-- The intentional coincidences in the doubled-square construction at lag `h`. -/
def duplicationCoincidence (request : ℕ → ℕ) (h n : ℕ) : Prop :=
  let q := duplicationBlock request n
  duplicationMask (duplicationLag q) h (n - duplicationStart request q)

instance (request : ℕ → ℕ) (h n : ℕ) : Decidable (duplicationCoincidence request h n) := by
  unfold duplicationCoincidence
  infer_instance

/-- The actual masked Fourier exponential of a lagged difference. -/
def duplicationMaskedPhase (request : ℕ → ℕ) (α : ℝ) (m : ℤ) (h n : ℕ) : ℂ :=
  if duplicationCoincidence request h n then 0
  else phase ((m : ℝ) * α *
    ((duplicationIndex request (n+h) : ℝ)^2 - (duplicationIndex request n : ℝ)^2))

private theorem norm_duplicationMaskedPhase_le (request : ℕ → ℕ) (α : ℝ) (m : ℤ) (h n : ℕ) :
    ‖duplicationMaskedPhase request α m h n‖ ≤ 1 := by
  unfold duplicationMaskedPhase
  split <;> simp

private theorem duplicationIndex_eq_localIndex {request : ℕ → ℕ} {q t : ℕ}
    (ht : duplicationStart request q + t < duplicationStart request (q+1)) :
    (duplicationIndex request (duplicationStart request q+t) : ℤ) =
      localIndex (duplicationStart request q) (duplicationLag q) t := by
  let A := duplicationStart request q
  let p := duplicationLag q
  have hb := duplicationBlock_eq (Nat.le_add_right A t) ht
  unfold duplicationIndex
  rw [hb]
  change (↑(if (A+t-A) % (2*p) < p then A+t else A+t-p) : ℤ) = localIndex A p t
  rw [Nat.add_sub_cancel_left]
  by_cases hr : t % (2*p) < p
  · simp [localIndex, duplicationOffset, hr]
  · rw [ite_eq_right hr, Nat.cast_sub ((not_lt.mp hr).trans ((Nat.mod_le ..).trans (Nat.le_add_left ..)))]
    simp [localIndex, duplicationOffset, hr]

private theorem duplicationMaskedPhase_eq_local {request : ℕ → ℕ} {α : ℝ} {m : ℤ}
    {q h t : ℕ}
    (ht : duplicationStart request q + t + h < duplicationStart request (q+1)) :
    duplicationMaskedPhase request α m h (duplicationStart request q+t) =
      localMaskedPhase α m (duplicationStart request q) (duplicationLag q) h t := by
  let A := duplicationStart request q
  have ht' : A + t < duplicationStart request (q+1) := by omega
  have ht'' : A + (t+h) < duplicationStart request (q+1) := by omega
  have hb := duplicationBlock_eq (Nat.le_add_right A t) ht'
  have hindex := congrArg (fun x : ℤ ↦ (x : ℝ)) (duplicationIndex_eq_localIndex ht')
  have hindex' := congrArg (fun x : ℤ ↦ (x : ℝ)) (duplicationIndex_eq_localIndex ht'')
  push_cast at hindex hindex'
  have he : duplicationCoincidence request h (A+t) ↔ duplicationMask (duplicationLag q) h t := by
    unfold duplicationCoincidence
    dsimp only
    rw [hb, Nat.add_sub_cancel_left]
  change duplicationMaskedPhase request α m h (A+t) = localMaskedPhase α m A (duplicationLag q) h t
  unfold duplicationMaskedPhase localMaskedPhase
  by_cases hs : duplicationMask (duplicationLag q) h t
  · rw [ite_eq_left (he.mpr hs), ite_eq_left hs]
  · rw [ite_eq_right (mt he.mp hs), ite_eq_right hs, add_assoc, hindex, hindex']

/-- Every stage prefix, including any terms whose lag crosses the stage boundary,
has a uniformly bounded masked exponential sum. -/
theorem norm_sum_duplicationMaskedPhase_stage_le {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) (request : ℕ → ℕ) (q : ℕ) {h L : ℕ} (hh : 0 < h)
    (hL : duplicationStart request q + L ≤ duplicationStart request (q+1)) :
    ‖∑ t ∈ range L, duplicationMaskedPhase request α m h (duplicationStart request q+t)‖ ≤
      stagePhaseBound α m (duplicationLag q) h := by
  let A := duplicationStart request q
  let p := duplicationLag q
  let B := duplicationStart request (q+1)
  let S := min L (B-A-h)
  let u := fun t ↦ duplicationMaskedPhase request α m h (A+t)
  have hs : S ≤ L := min_le_left _ _
  have ht : L-S ≤ h := by
    have hh' : L ≤ B-A := by omega
    dsimp [S]
    omega
  have he : L = S+(L-S) := by omega
  change ‖∑ t ∈ range L, u t‖ ≤ _
  rw [he, Finset.sum_range_add]
  have hu : (∑ t ∈ range S, u t) =
      ∑ t ∈ range S, localMaskedPhase α m A p h t := by
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    apply duplicationMaskedPhase_eq_local (q := q)
    dsimp [S] at ht'
    omega
  rw [hu]
  have htail : ‖∑ t ∈ range (L-S), u (S+t)‖ ≤ (h : ℝ) := by
    apply (norm_sum_le _ _).trans
    exact (sum_le_sum (g := fun _ ↦ (1 : ℝ)) fun t _ ↦ norm_duplicationMaskedPhase_le ..).trans
      (by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; exact_mod_cast ht)
  have hmain := norm_sum_localMaskedPhase_le hα hm (duplicationLag_pos q) hh A S
  have hsum := (norm_add_le _ _).trans (add_le_add hmain htail)
  exact hsum.trans (by unfold stagePhaseBound; dsimp [p] at *; linarith)

private theorem norm_sum_duplicationMaskedPhase_stages_le {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) (request : ℕ → ℕ) {h : ℕ} (hh : 0 < h) (q : ℕ) :
    ‖∑ t ∈ range (duplicationStart request q), duplicationMaskedPhase request α m h t‖ ≤
      ∑ i ∈ range q, stagePhaseBound α m (duplicationLag i) h := by
  induction q with
  | zero => simp [duplicationStart]
  | succ q ih =>
    let A := duplicationStart request q
    let L := (2 * duplicationLag q) * duplicationGroups request q
    have hL : A+L = duplicationStart request (q+1) := (duplicationStart_succ request q).symm
    rw [← hL, Finset.sum_range_add, Finset.sum_range_succ]
    exact (norm_add_le ..).trans (add_le_add ih
      (norm_sum_duplicationMaskedPhase_stage_le hα hm request q hh hL.le))

/-- Growth sufficient to make all complete and partial stage errors negligible. -/
def duplicationGrowth (α : ℝ) (q : ℕ) : ℕ :=
  (q+1) * ⌈∑ h ∈ range (q+1), ∑ m ∈ Icc (-(q : ℤ)) (q : ℤ),
    ∑ i ∈ range (q+1), stagePhaseBound α m (duplicationLag i) h⌉₊

private theorem request_le_start (request : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    request q ≤ duplicationStart request q := by
  rcases q with _ | q
  · omega
  rw [duplicationStart_succ]
  have hp := duplicationLag_pos q
  have hm : 1 ≤ 2 * duplicationLag q := by omega
  have hh : duplicationGroups request q ≤ 2 * duplicationLag q * duplicationGroups request q := by
    simpa only [one_mul] using Nat.mul_le_mul_right (duplicationGroups request q) hm
  exact (Nat.le_add_left _ _).trans (hh.trans (Nat.le_add_left _ _))

private theorem prefix_error_le_start (α : ℝ) {m : ℤ} {h q : ℕ} (hq : 0 < q)
    (hhq : h ≤ q) (hmq : m ∈ Icc (-(q : ℤ)) (q : ℤ)) :
    ((q : ℝ)+1) * (∑ i ∈ range (q+1), stagePhaseBound α m (duplicationLag i) h) ≤
      (duplicationStart (duplicationGrowth α) q : ℝ) := by
  let E (j : ℕ) (k : ℤ) := ∑ i ∈ range (q+1), stagePhaseBound α k (duplicationLag i) j
  have hE j k : 0 ≤ E j k :=
    Finset.sum_nonneg fun i _ ↦ stagePhaseBound_nonneg α k (duplicationLag i) j
  have hsum : E h m ≤ ∑ j ∈ range (q+1), ∑ k ∈ Icc (-(q : ℤ)) (q : ℤ), E j k :=
    (single_le_sum (fun k _ ↦ hE h k) hmq).trans
      (single_le_sum (fun j _ ↦ Finset.sum_nonneg fun k _ ↦ hE j k) (mem_range.mpr (by omega)))
  have hc : ((duplicationGrowth α q : ℕ) : ℝ) ≤
      (duplicationStart (duplicationGrowth α) q : ℝ) := by
    exact_mod_cast request_le_start (duplicationGrowth α) hq
  refine (mul_le_mul_of_nonneg_left (hsum.trans (Nat.le_ceil _)) (by positivity)).trans ?_
  simpa only [duplicationGrowth, Nat.cast_mul, Nat.cast_add, Nat.cast_one, E] using hc

/-- Once the intentional coincidences are removed, every positive-lag nonzero Fourier
average tends to zero. The masked averages keep their original denominator. -/
theorem tendsto_cesaro_duplicationMaskedPhase_zero {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) {h : ℕ} (hh : 0 < h) :
    Tendsto (cesaro (duplicationMaskedPhase (duplicationGrowth α) α m h)) atTop (𝓝 0) := by
  let request := duplicationGrowth α
  let u := duplicationMaskedPhase request α m h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1/ε)
  let Q := max (max K 1) (max h m.natAbs)
  refine ⟨duplicationStart request Q, fun N hN ↦ ?_⟩
  let q := duplicationBlock request N
  let A := duplicationStart request q
  obtain ⟨hA, hB⟩ := duplicationBlock_bounds request N
  change A ≤ N at hA
  change N < duplicationStart request (q+1) at hB
  have hQ : Q ≤ q := by
    by_contra! hn
    exact (not_lt_of_ge hN) (hB.trans_le ((duplicationStart_strictMono request).monotone (by omega)))
  have hKq : K ≤ q := (le_max_left K 1).trans ((le_max_left _ _).trans hQ)
  have h1q : 0 < q := (le_max_right K 1).trans ((le_max_left _ _).trans hQ)
  have hhq : h ≤ q := (le_max_left h m.natAbs).trans ((le_max_right _ _).trans hQ)
  have hmq' : m.natAbs ≤ q := (le_max_right h m.natAbs).trans ((le_max_right _ _).trans hQ)
  have hmq : m ∈ Icc (-(q : ℤ)) (q : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  have hNr : 0 < (N : ℝ) := by
    exact_mod_cast (h1q.trans_le ((le_duplicationStart request q).trans hA))
  have hqr : 0 < (q : ℝ)+1 := by positivity
  have hN' : N = A+(N-A) := by omega
  have hL : A+(N-A) ≤ duplicationStart request (q+1) := by omega
  let E := ∑ i ∈ range (q+1), stagePhaseBound α m (duplicationLag i) h
  have he : ‖∑ t ∈ range N, u t‖ ≤ E := by
    rw [hN', Finset.sum_range_add]
    apply (norm_add_le ..).trans
    change ‖∑ t ∈ range A, u t‖ + ‖∑ t ∈ range (N-A), u (A+t)‖ ≤ E
    dsimp only [E]
    rw [Finset.sum_range_succ]
    exact add_le_add (norm_sum_duplicationMaskedPhase_stages_le hα hm request hh q)
      (norm_sum_duplicationMaskedPhase_stage_le hα hm request q hh hL)
  have hEN : ((q : ℝ)+1)*E ≤ (N : ℝ) :=
    (prefix_error_le_start α h1q hhq hmq).trans (by exact_mod_cast hA)
  have hEdiv : E / (N : ℝ) ≤ 1 / ((q : ℝ)+1) := by
    rw [div_le_div_iff₀ hNr hqr, one_mul, mul_comm]
    exact hEN
  have hKqr : (K : ℝ) ≤ q := by exact_mod_cast hKq
  have hεq : (1 : ℝ) / ((q : ℝ)+1) < ε := by
    rw [div_lt_iff₀ hqr]
    have hf := (div_lt_iff₀ hε).mp hK
    have hg := mul_le_mul_of_nonneg_right (show (K : ℝ) ≤ (q : ℝ)+1 by linarith) hε.le
    nlinarith only [hf, hg]
  rw [dist_zero_right, cesaro, norm_div, Complex.norm_natCast]
  exact ((div_le_div_of_nonneg_right he hNr.le).trans hEdiv).trans_lt hεq

theorem duplicationCoincidence_lag {request : ℕ → ℕ} {h n : ℕ}
    (hc : duplicationCoincidence request h n) :
    duplicationLag (duplicationBlock request n) = h := hc.1

/-- Each prescribed coincidence pairs a first-half index with its second-half copy. -/
theorem duplicationCoincidence_pair {request : ℕ → ℕ} {h n : ℕ}
    (hc : duplicationCoincidence request h n) :
    duplicationIndex request (n+h) = duplicationIndex request n ∧
      ¬ duplicationCoincidence request h (n+h) := by
  let q := duplicationBlock request n
  let A := duplicationStart request q
  let p := duplicationLag q
  let k := (n-A)/(2*p)
  let r := (n-A)%(2*p)
  have hp : p = h := hc.1
  have hr : r < p := hc.2
  obtain ⟨ha, hb⟩ := duplicationBlock_bounds request n
  change A ≤ n at ha
  change n < duplicationStart request (q+1) at hb
  have hd : (2*p)*k+r = n-A := by
    simpa [k, r, add_comm] using Nat.mod_add_div (n-A) (2*p)
  have hn : n = A+(2*p)*k+r := by omega
  have hb' : duplicationStart request (q+1) = A+2*p*duplicationGroups request q :=
    duplicationStart_succ request q
  have hk : k < duplicationGroups request q := by
    by_contra! hh
    have hm := Nat.mul_le_mul_left (2*p) hh
    omega
  have hx := duplicationIndex_first_half request q k r hk hr
  change duplicationIndex request (A+(2*p)*k+r) = A+(2*p)*k+r ∧
      duplicationIndex request (A+(2*p)*k+r+p) = A+(2*p)*k+r at hx
  rw [← hn, hp] at hx
  refine ⟨hx.2.trans hx.1.symm, ?_⟩
  have hm := Nat.mul_le_mul_left (2*p) (by omega : k+1 ≤ duplicationGroups request q)
  rw [Nat.mul_succ] at hm
  have ht : n+h < duplicationStart request (q+1) := by omega
  have hq' := duplicationBlock_eq (show A ≤ n+h by omega) ht
  have hs : n+h-A = (2*p)*k+(r+p) := by omega
  have hr' : (n+h-A) % (2*p) = r+p := by
    rw [hs, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  intro hc'
  have he := hc'.2
  change (n+h-duplicationStart request (duplicationBlock request (n+h))) %
      (2*duplicationLag (duplicationBlock request (n+h))) <
        duplicationLag (duplicationBlock request (n+h)) at he
  rw [hq'] at he
  change (n+h-A)%(2*p) < p at he
  rw [hr'] at he
  omega

end

end VdC

end

end VdC_DuplicationEstimates_Module

/- Source: VdC/DuplicationSpectrum.lean -/
section VdC_DuplicationSpectrum_Module

/-! The spectrally Lebesgue example with upper discrepancy one half at every lag. -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

noncomputable section

private def duplicateWeight (request : ℕ → ℕ) (h n : ℕ) : ℂ :=
  if duplicationCoincidence request h n then 1 else 0

private def duplicationFrequency (request : ℕ → ℕ) (α : ℝ) (m : ℤ) (n : ℕ) : ℂ :=
  phase ((m : ℝ) * α * (duplicationIndex request n : ℝ)^2)

private theorem torusCharacter_duplication (request : ℕ → ℕ) (α : ℝ) (m : Fin 1 → ℤ) (n : ℕ) :
    torusCharacter m (duplicationSequence request α n) = duplicationFrequency request α (m 0) n := by
  rw [torusCharacter_apply, Fin.prod_univ_one]
  exact (phase_frequency _ _).trans (by unfold duplicationFrequency; congr 1; ring)

theorem torusCharacter_duplication_difference (request : ℕ → ℕ) (α : ℝ)
    (m : Fin 1 → ℤ) (h n : ℕ) :
    torusCharacter m (duplicationSequence request α (n+h) - duplicationSequence request α n) =
      phase ((m 0 : ℝ) * α *
        ((duplicationIndex request (n+h) : ℝ)^2 - (duplicationIndex request n : ℝ)^2)) := by
  rw [torusCharacter_apply, Fin.prod_univ_one]
  change fourier (m 0)
    (((α * (duplicationIndex request (n+h) : ℝ)^2 : ℝ) : UnitAddCircle) -
      ((α * (duplicationIndex request n : ℝ)^2 : ℝ) : UnitAddCircle)) = _
  rw [← AddCircle.coe_sub, phase_frequency]
  congr 1
  ring

private theorem corr_duplicationFrequency (request : ℕ → ℕ) (α : ℝ) (m : ℤ) (h N : ℕ) :
    corr (duplicationFrequency request α m) (duplicationFrequency request α m) h N =
      cesaro (duplicationMaskedPhase request α m h) N + cesaro (duplicateWeight request h) N := by
  unfold corr
  rw [← cesaro_add]
  congr 1
  funext n
  rw [duplicationFrequency, duplicationFrequency, ← phase_sub]
  by_cases hc : duplicationCoincidence request h n
  · simp [duplicationMaskedPhase, duplicateWeight, hc, (duplicationCoincidence_pair hc).1]
  · simp only [duplicationMaskedPhase, duplicateWeight, hc, ite_false, add_zero]
    congr 1
    ring

private theorem sum_duplicateWeight_norm_le_one (request : ℕ → ℕ) (H N : ℕ) :
    ∑ h ∈ range H, ‖cesaro (duplicateWeight request (h+1)) N‖ ≤ 1 := by
  classical
  have hweight (n : ℕ) : ∑ h ∈ range H, ‖duplicateWeight request (h+1) n‖ ≤ 1 := by
    let p := duplicationLag (duplicationBlock request n)
    have hp : 0 < p := duplicationLag_pos _
    calc
      _ ≤ ∑ h ∈ range H, if h = p-1 then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro h _
        by_cases hc : duplicationCoincidence request (h+1) n
        · have hlag := duplicationCoincidence_lag hc
          have he : h = p-1 := by change p = h+1 at hlag; omega
          rw [duplicateWeight, ite_eq_left hc, ite_eq_left he, norm_one]
        · rw [duplicateWeight, ite_eq_right hc, norm_zero]
          split <;> norm_num
      _ ≤ 1 := by rw [sum_ite_eq']; split <;> norm_num
  simp only [cesaro, norm_div, Complex.norm_natCast, ← Finset.sum_div]
  apply (div_le_div_of_nonneg_right
    (sum_le_sum fun h _ ↦ norm_sum_le (range N) (duplicateWeight request (h+1)))
    (Nat.cast_nonneg N)).trans
  rw [Finset.sum_comm]
  have hN' := Finset.sum_le_sum (s := range N) (fun n _ ↦ hweight n)
  have hden : (∑ n ∈ range N, (1 : ℝ)) / (N : ℝ) ≤ 1 := by
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
    exact div_self_le_one (N : ℝ)
  exact (div_le_div_of_nonneg_right hN' (Nat.cast_nonneg N)).trans hden

private theorem duplicationFrequency_spectrallyLebesgue {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) : SpectrallyLebesgue (duplicationFrequency (duplicationGrowth α) α m) := by
  let request := duplicationGrowth α
  let u := duplicationFrequency request α m
  have hb (n : ℕ) : ‖u n‖ ≤ 1 := (norm_phase _).le
  have hu : BoundedSeq u := ⟨1, zero_le_one, hb⟩
  refine ⟨hu, fun N r hN hr ↦ ?_⟩
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hu hN hr
  refine ⟨μ, hμ, fourier_positive_l2_absolutelyContinuous μ ?_⟩
  have ht (h : ℕ) : Tendsto (fun q ↦ cesaro (duplicateWeight request (h+1)) (N q)) atTop
      (𝓝 (r (h+1))) := by
    have hg := (tendsto_cesaro_duplicationMaskedPhase_zero hα hm (Nat.succ_pos h)).comp hN.tendsto_atTop
    have hh := (hr (h+1)).sub hg
    simpa only [u, corr_duplicationFrequency, Function.comp_apply, add_sub_cancel_left, sub_zero] using hh
  have hsum : Summable (fun h : ℕ ↦ ‖r (h+1)‖) := by
    apply summable_of_sum_range_le (fun h ↦ norm_nonneg _) (c := 1)
    intro H
    exact le_of_tendsto (tendsto_finsetSum (range H) (fun h _ ↦ (ht h).norm))
      (Eventually.of_forall fun q ↦ sum_duplicateWeight_norm_le_one request H (N q))
  have hnorm (h : ℕ) : ‖r (h+1)‖ ≤ 1 := by
    apply le_of_tendsto (hr (h+1)).norm
    exact Eventually.of_forall fun q ↦ (norm_corr_le zero_le_one zero_le_one hb hb (h+1) (N q)).trans_eq
      (one_mul 1)
  simp_rw [hμ (Nat.succ _)]
  exact Summable.of_nonneg_of_le (fun h ↦ sq_nonneg _)
    (fun h ↦ by nlinarith [mul_nonneg (norm_nonneg (r (h+1))) (sub_nonneg.mpr (hnorm h))]) hsum

def duplicationCube (α : ℝ) (n : ℕ) : Cube 1 :=
  fun i ↦ unitRepresentative (duplicationSequence (duplicationGrowth α) α n i)

theorem cubeToTorus_duplicationCube (α : ℝ) :
    cubeToTorus ∘ duplicationCube α = duplicationSequence (duplicationGrowth α) α := by
  funext n i
  exact unitRepresentative_coe _

private theorem nonzero_one_frequency {m : Fin 1 → ℤ} (hm : m ≠ 0) : m 0 ≠ 0 := by
  intro hz
  apply hm
  funext i
  fin_cases i
  exact hz

theorem duplicationCube_spectrallyLebesgue {α : ℝ} (hα : Irrational α) :
    SpectrallyLebesgueDistribution (cubeLebesgue 1) (duplicationCube α) := by
  apply (cube_sLebesgue_iff_characters _).2
  intro m hm
  have he (n : ℕ) : cubeToTorus (duplicationCube α n) =
      duplicationSequence (duplicationGrowth α) α n :=
    congrFun (cubeToTorus_duplicationCube α) n
  simp_rw [he, torusCharacter_duplication]
  exact duplicationFrequency_spectrallyLebesgue hα (nonzero_one_frequency hm)

end

end VdC

end

end VdC_DuplicationSpectrum_Module

/- Source: VdC/ErgodicExamples.lean -/
section VdC_ErgodicExamples_Module

/-! # Ergodic Examples -/

@[expose] public section

open Filter Finset Function MeasureTheory Set TopologicalSpace
open scoped Topology BigOperators ComplexConjugate

namespace VdC

section Observable

variable {X : Type*} [MeasurableSpace X]

def orbitSequence (T : X → X) (x : X) (n : ℕ) : X := T^[n] x

def BoundedObservable (f : X → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C

noncomputable def koopmanCorrelation (μ : Measure X) (T : X → X) (f : X → ℂ) (h : ℕ) : ℂ :=
  ∫ y, f (T^[h] y) * star (f y) ∂μ

def KoopmanWeakMixing (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f → (∫ y, f y ∂μ) = 0 →
    Tendsto (realCesaro (fun h => ‖koopmanCorrelation μ T f (h+1)‖)) atTop (𝓝 0)

def KoopmanLebesgueSpectrum (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f → (∫ y, f y ∂μ) = 0 →
    ∃ ν : FiniteMeasure UnitAddCircle, HasSpectrum (koopmanCorrelation μ T f) ν ∧
      (ν : Measure UnitAddCircle) ≪ circleHaar

def KoopmanSingularSpectrum (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f →
    ∃ ν : FiniteMeasure UnitAddCircle, HasSpectrum (koopmanCorrelation μ T f) ν ∧
      (ν : Measure UnitAddCircle).MutuallySingular circleHaar

theorem BoundedObservable.orbit_bounded {f : X → ℂ} (hf : BoundedObservable f) (T : X → X) (x : X) :
    BoundedSeq (fun n => f (orbitSequence T x n)) := by
  obtain ⟨C, hC, hbound⟩ := hf.2
  exact ⟨C, hC, fun _ => hbound _⟩

/-- `EquationForExamples` for one bounded measurable observable, concurrently at all lags. -/
theorem ae_orbit_correlation {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {f : X → ℂ} (hf : BoundedObservable f) :
    ∀ᵐ x ∂μ, CorrLimits (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) id
      (koopmanCorrelation μ T f) := by
  apply ae_all_iff.mpr
  intro h
  let g (x : X) := f (T^[h] x) * star (f x)
  have hmeas : Measurable g := (hf.1.comp (hT.measurable.iterate h)).mul
    (Complex.continuous_conj.measurable.comp hf.1)
  obtain ⟨C, hC, hb⟩ := hf.2
  have hbound (x : X) : ‖g x‖ ≤ C*C := by
    change ‖f (T^[h] x) * star (f x)‖ ≤ C*C
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb _) (hb _) (norm_nonneg _) hC
  filter_upwards [ae_tendsto_orbitCesaro hT hmeas (mul_nonneg hC hC) hbound] with x hx
  have he (n : ℕ) : T^[n + h] x = T^[h] (T^[n] x) := by rw [Nat.add_comm n h, iterate_add_apply]
  simpa only [orbitSequence, corr, he, id_eq, koopmanCorrelation, g] using hx

private theorem sub_limit_eq {x : ℕ → ℂ} {r u : ℕ → ℂ} (h : CorrLimits x x id r)
    {M : ℕ → ℕ} (hM : StrictMono M) (hu : CorrLimits x x M u) : u = r := by
  funext k
  exact tendsto_nhds_unique (hu k) ((h k).comp hM.tendsto_atTop)

theorem nearlyWeakMixing_of_full_self_corr {x : ℕ → ℂ} (hx : BoundedSeq x) {r : ℕ → ℂ}
    (hr : CorrLimits x x id r) (ht : Tendsto (realCesaro (fun h => ‖r (h+1)‖)) atTop (𝓝 0)) :
    NearlyWeakMixing x := by
  apply nearlyWeakMixing_of_self_mean hx
  intro M u hM hu
  rwa [sub_limit_eq hr hM hu]

theorem spectrallyLebesgue_of_full_self_corr {x : ℕ → ℂ} (hx : BoundedSeq x) {r : ℕ → ℂ}
    (hr : CorrLimits x x id r) {ν : FiniteMeasure UnitAddCircle} (hν : HasSpectrum r ν)
    (ha : (ν : Measure UnitAddCircle) ≪ circleHaar) : SpectrallyLebesgue x := by
  exact ⟨hx, fun M u hM hu => ⟨ν, (sub_limit_eq hr hM hu).symm ▸ hν, ha⟩⟩

theorem spectrallySingular_of_full_self_corr {x : ℕ → ℂ} (hx : BoundedSeq x) {r : ℕ → ℂ}
    (hr : CorrLimits x x id r) {ν : FiniteMeasure UnitAddCircle} (hν : HasSpectrum r ν)
    (hs : (ν : Measure UnitAddCircle).MutuallySingular circleHaar) : SpectrallySingular x := by
  exact ⟨hx, fun M u hM hu => ⟨ν, (sub_limit_eq hr hM hu).symm ▸ hν, hs⟩⟩

end Observable

section ContinuousTests

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem boundedObservable_of_continuous (f : C(X, ℂ)) : BoundedObservable f :=
  ⟨f.continuous.measurable, ‖f‖, norm_nonneg _, ContinuousMap.norm_coe_le_norm f⟩

omit [MeasurableSpace X] [BorelSpace X] in
private theorem norm_corr_pair_sub_le (f g : C(X, ℂ)) (a b : X) :
    ‖f a * star (f b) - g a * star (g b)‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  rw [show f a * star (f b) - g a * star (g b) =
      (f a-g a) * star (f b) + g a * star (f b-g b) by rw [star_sub]; ring]
  calc
    _ ≤ ‖(f a-g a)*star (f b)‖ + ‖g a * star (f b-g b)‖ := norm_add_le _ _
    _ ≤ ‖f-g‖*‖f‖ + ‖g‖*‖f-g‖ := by
      simp only [norm_mul, norm_star]
      exact add_le_add
        (mul_le_mul (ContinuousMap.norm_coe_le_norm (f-g) a) (ContinuousMap.norm_coe_le_norm f b)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (ContinuousMap.norm_coe_le_norm g a) (ContinuousMap.norm_coe_le_norm (f-g) b)
          (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

private theorem norm_koopmanCorrelation_sub_le (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) (f g : C(X, ℂ)) (h : ℕ) :
    ‖koopmanCorrelation μ T f h - koopmanCorrelation μ T g h‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  have hint (w : C(X, ℂ)) : Integrable (fun y => w (T^[h] y) * star (w y)) μ := by
    apply Integrable.of_bound (((w.continuous.measurable.comp (hT.iterate h)).mul
      (Complex.continuous_conj.measurable.comp w.continuous.measurable)).aestronglyMeasurable) (‖w‖*‖w‖)
    exact Eventually.of_forall fun y => by
      change ‖w (T^[h] y) * star (w y)‖ ≤ _
      rw [norm_mul, norm_star]
      exact mul_le_mul (ContinuousMap.norm_coe_le_norm w _) (ContinuousMap.norm_coe_le_norm w _)
        (norm_nonneg _) (norm_nonneg _)
  rw [koopmanCorrelation, koopmanCorrelation, ← integral_sub (hint f) (hint g)]
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall fun y => norm_corr_pair_sub_le f g (T^[h] y) y)

omit [MeasurableSpace X] [BorelSpace X] in
private theorem norm_orbit_corr_sub_le (T : X → X) (x : X) (f g : C(X, ℂ)) (h N : ℕ) :
    ‖corr (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) h N -
      corr (fun n => g (orbitSequence T x n)) (fun n => g (orbitSequence T x n)) h N‖ ≤
      ‖f-g‖*(‖f‖+‖g‖) := by
  rw [corr, corr, ← cesaro_sub]
  exact norm_cesaro_le _ (by positivity) (fun n => norm_corr_pair_sub_le f g _ _) N

/-- A single full-measure set works for all continuous tests and all lags. -/
theorem ae_continuous_orbit_correlation [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) : ∀ᵐ x ∂μ, ∀ f : C(X, ℂ),
      CorrLimits (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) id
        (koopmanCorrelation μ T f) := by
  classical
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense C(X, ℂ)
  have : Countable S := hSc.to_subtype
  have hS : ∀ᵐ x ∂μ, ∀ g : S,
      CorrLimits (fun n => g.1 (orbitSequence T x n)) (fun n => g.1 (orbitSequence T x n)) id
        (koopmanCorrelation μ T g.1) :=
    ae_all_iff.mpr fun g => ae_orbit_correlation hT (boundedObservable_of_continuous g.1)
  filter_upwards [hS] with x hx
  intro f h
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := min 1 (ε / (12 * (‖f‖ + 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hSd f) δ hδ
  rw [dist_eq_norm] at hfg
  have hgB : ‖g‖ ≤ ‖f‖+1 := by
    have hh := hfg.le.trans (min_le_left _ _ : δ ≤ 1)
    have ht := norm_add_le (g-f) f
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith only [hh, ht]
  have hE : ‖f-g‖*(‖f‖+‖g‖) ≤ ε/4 := by
    have hh := hfg.le.trans (min_le_right _ _ : δ ≤ ε/(12*(‖f‖+1)))
    refine (mul_le_mul hh (show ‖f‖+‖g‖ ≤ 2*‖f‖+1 by linarith only [hgB])
      (by positivity) (by positivity)).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 12*(‖f‖+1))]
    nlinarith only [hε, mul_nonneg hε.le (norm_nonneg f)]
  filter_upwards [Metric.tendsto_nhds.mp (hx ⟨g, hg⟩ h) (ε/3) (by positivity)] with N hN
  let a := corr (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) h N
  let b := corr (fun n => g (orbitSequence T x n)) (fun n => g (orbitSequence T x n)) h N
  let u := koopmanCorrelation μ T g h
  let v := koopmanCorrelation μ T f h
  rw [dist_eq_norm] at hN ⊢
  have hab : ‖a-b‖ ≤ ε/4 := (norm_orbit_corr_sub_le T x f g h N).trans hE
  have huv : ‖u-v‖ ≤ ε/4 := by
    rw [norm_sub_rev]
    exact (norm_koopmanCorrelation_sub_le μ hT.measurable f g h).trans hE
  have hh : ‖a-v‖ ≤ ‖a-b‖ + ‖b-u‖ + ‖u-v‖ := by
    rw [show a-v = (a-b+(b-u))+(u-v) by ring]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  change ‖a-v‖ < ε
  change ‖b-u‖ < ε/3 at hN
  linarith only [hab, huv, hN, hh, hε]

/-- `LemmaConstructingSequences` (i), in the correlation formulation of weak mixing. -/
theorem ae_orbit_weaklyMixing [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hm : KoopmanWeakMixing μ T) :
    ∀ᵐ x ∂μ, WeaklyMixingDistribution μ (orbitSequence T x) := by
  filter_upwards [ae_continuous_orbit_correlation hT] with x hx
  intro f hf
  exact nearlyWeakMixing_of_full_self_corr (bounded_test f _) (hx f) (hm f (boundedObservable_of_continuous f) hf)

/-- `LemmaConstructingSequences` (ii). -/
theorem ae_orbit_spectrallyLebesgue [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hm : KoopmanLebesgueSpectrum μ T) :
    ∀ᵐ x ∂μ, SpectrallyLebesgueDistribution μ (orbitSequence T x) := by
  filter_upwards [ae_continuous_orbit_correlation hT] with x hx
  intro f hf
  obtain ⟨ν, hν, ha⟩ := hm f (boundedObservable_of_continuous f) hf
  exact spectrallyLebesgue_of_full_self_corr (bounded_test f _) (hx f) hν ha

/-- `LemmaConstructingSequences` (v). -/
theorem ae_orbit_spectrallySingular [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hm : KoopmanSingularSpectrum μ T) :
    ∀ᵐ x ∂μ, SpectrallySingularDistribution (orbitSequence T x) := by
  filter_upwards [ae_continuous_orbit_correlation hT] with x hx
  intro f
  obtain ⟨ν, hν, ha⟩ := hm f (boundedObservable_of_continuous f)
  exact spectrallySingular_of_full_self_corr (bounded_test f _) (hx f) hν ha

end ContinuousTests

section Visits

variable {X : Type*} [MeasurableSpace X]

def visitTimes (T : X → X) (A : Set X) (x : X) : Set ℕ := {n | orbitSequence T x n ∈ A}

noncomputable def visitObservable (A : Set X) (x : X) : ℂ := A.indicator (fun _ => 1) x

theorem boundedObservable_visit (A : Set X) (hA : MeasurableSet A) :
    BoundedObservable (visitObservable A) := by
  refine ⟨measurable_const.indicator hA, 1, zero_le_one, ?_⟩
  intro x
  unfold visitObservable
  by_cases hx : x ∈ A <;> simp [hx, zero_le_one]

omit [MeasurableSpace X] in
theorem visitObservable_orbit (T : X → X) (A : Set X) (x : X) (n : ℕ) :
    visitObservable A (orbitSequence T x n) = selectionWeight (visitTimes T A x) n := by
  by_cases h : orbitSequence T x n ∈ A <;> simp [visitObservable, selectionWeight, visitTimes, h]

theorem realCesaro_selectionWeight (A : Set ℕ) (N : ℕ) :
    realCesaro (fun n => (selectionWeight A n).re) N = (initialCount A N : ℝ) / N := by
  classical
  unfold realCesaro initialCount
  congr 1
  have hpt (n : ℕ) : (selectionWeight A n).re = if n ∈ A then 1 else 0 := by
    by_cases h : n ∈ A <;> simp [selectionWeight, h]
  simp only [hpt, ← Finset.sum_filter]
  simp

theorem ae_visit_density {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, Tendsto (fun N => (initialCount (visitTimes T A x) N : ℝ) / (N : ℝ)) atTop (𝓝 (μ.real A)) := by
  have hB := boundedObservable_visit A hA
  obtain ⟨C, hC, hb⟩ := hB.2
  filter_upwards [ae_tendsto_orbitCesaro hT hB.1 hC hb] with x hx
  have hCpx := Complex.continuous_re.continuousAt.tendsto.comp hx
  have hint : (∫ y, visitObservable A y ∂μ) = (μ.real A : ℂ) := by
    change (∫ y, A.indicator (fun _ => (1 : ℂ)) y ∂μ) = _
    rw [integral_indicator_const 1 hA, Complex.real_smul, mul_one]
  change Tendsto (fun N => (cesaro (fun n => visitObservable A (orbitSequence T x n)) N).re)
    atTop (𝓝 (∫ y, visitObservable A y ∂μ).re) at hCpx
  simpa only [← realCesaro_re, visitObservable_orbit,
    realCesaro_selectionWeight, hint, Complex.ofReal_re] using hCpx

theorem positiveLowerDensity_of_density_limit {A : Set ℕ} {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun N => (initialCount A N : ℝ) / (N : ℝ)) atTop (𝓝 a)) : HasPositiveLowerDensity A := by
  refine ⟨a/2, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ), h.eventually (lt_mem_nhds (show a/2 < a by linarith))] with N hn hu
  have hN : 0 < (N : ℝ) := by exact_mod_cast hn
  exact (le_div_iff₀ hN).mp hu.le

theorem exists_enumeration_of_positiveLowerDensity {A : Set ℕ} (h : HasPositiveLowerDensity A) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = A := by
  classical
  have hi : A.Infinite := by
    by_contra H
    have hf : A.Finite := Set.not_infinite.mp H
    obtain ⟨δ, hδ, hev⟩ := h
    obtain ⟨N, hN⟩ := exists_nat_gt ((hf.toFinset.card : ℝ)/δ)
    obtain ⟨n, hn, hn'⟩ := ((eventually_ge_atTop N).and hev).exists
    have hh : initialCount A n ≤ hf.toFinset.card := by
      unfold initialCount
      apply Finset.card_le_card
      intro i hi
      exact hf.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
    have hh' : (initialCount A n : ℝ) ≤ hf.toFinset.card := by exact_mod_cast hh
    have hlt : ((hf.toFinset.card : ℝ)/δ) < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
    have hc := (div_lt_iff₀ hδ).mp hlt
    nlinarith only [hn', hh', hc]
  have : Infinite A := hi.to_subtype
  let v := Nat.Subtype.orderIsoOfNat A
  refine ⟨fun n => (v n : ℕ), fun a b hab => v.strictMono hab, ?_⟩
  ext n
  constructor
  · rintro ⟨j, rfl⟩
    exact (v j).property
  · intro hn
    obtain ⟨j, hj⟩ := v.surjective ⟨n, hn⟩
    exact ⟨j, congrArg Subtype.val hj⟩

/-- `LemmaConstructingSequences` (vi), including the positive-density visit enumeration. -/
theorem ae_visits_spectrallySingular {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hs : KoopmanSingularSpectrum μ T) {A : Set X}
    (hA : MeasurableSet A) (hpos : 0 < μ A) :
    ∀ᵐ x ∂μ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
      HasPositiveLowerDensity (Set.range σ) ∧ SpectrallySingular (selectionWeight (Set.range σ)) := by
  have hp : 0 < μ.real A := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  have hB := boundedObservable_visit A hA
  obtain ⟨ν, hν, hS⟩ := hs (visitObservable A) hB
  filter_upwards [ae_visit_density hT hA, ae_orbit_correlation hT hB] with x hx hr
  have hd := positiveLowerDensity_of_density_limit hp hx
  obtain ⟨σ, hσ, hR⟩ := exists_enumeration_of_positiveLowerDensity hd
  refine ⟨σ, hσ, hR, ?_, ?_⟩
  · rwa [hR]
  · rw [hR]
    have hh := spectrallySingular_of_full_self_corr (hB.orbit_bounded T x) hr hν hS
    simpa only [visitObservable_orbit] using hh

end Visits

section Discrete

variable {X : Type*} [MeasurableSpace X]

/-- A bounded measurable Koopman eigenfunction with a unit-modulus eigenvalue. -/
structure BoundedKoopmanEigenfunction (μ : Measure X) (T : X → X) where
  value : X → ℂ
  bounded : BoundedObservable value
  eigenvalue : ℂ
  norm_eigenvalue : ‖eigenvalue‖ = 1
  eigen : ∀ᵐ x ∂μ, value (T x) = eigenvalue * value x

/-- The pure-point assumption in its L² approximation form. Coefficients can be
absorbed into the eigenfunctions, so it suffices to use finite sums. -/
def KoopmanDiscreteSpectrum (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f → ∀ ε : ℝ, 0 < ε →
    ∃ (k : ℕ) (e : Fin k → BoundedKoopmanEigenfunction μ T),
      (∫ x, ‖f x - ∑ i, (e i).value x‖ ^ 2 ∂μ) < ε

theorem ae_eigenfunction_orbit_pow {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    (e : BoundedKoopmanEigenfunction μ T) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, e.value (orbitSequence T x n) = e.value x * e.eigenvalue^n := by
  have hh : ∀ᵐ x ∂μ, ∀ n : ℕ,
      e.value (T (T^[n] x)) = e.eigenvalue * e.value (T^[n] x) :=
    ae_all_iff.mpr fun n => (hT.iterate n).quasiMeasurePreserving.ae e.eigen
  filter_upwards [hh] with x hx
  intro n
  induction n with
  | zero => simp [orbitSequence]
  | succ n ih =>
    simp only [orbitSequence, iterate_succ_apply', hx n] at ih ⊢
    rw [ih, pow_succ]
    ring

theorem compactAlong_exponential (a lam : ℂ) (hlam : ‖lam‖ = 1) {M : ℕ → ℕ} (hM : StrictMono M) :
    CompactAlong (fun n => a * lam^n) M := by
  classical
  refine ⟨⟨‖a‖, norm_nonneg _, fun n => by simp [norm_pow, hlam]⟩, hM, ?_⟩
  intro σ r hσ hr ε hε
  let u (m : ℕ) := a * lam^(m+1)
  have hclosed : closure (Set.range u) ⊆ Metric.closedBall (0 : ℂ) ‖a‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    rintro _ ⟨n, rfl⟩
    simp [u, Metric.mem_closedBall, norm_pow, hlam]
  have hcomp : IsCompact (closure (Set.range u)) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hclosed
  obtain ⟨s, hs, hfinite, hcover⟩ := exists_finite_cover_balls_of_isCompact_closure hcomp
    (Real.sqrt_pos.mpr hε)
  let j (z : ℂ) := if h : z ∈ Set.range u then Classical.choose h else 0
  have hj {z : ℂ} (hz : z ∈ s) : u (j z) = z := by
    unfold j
    rw [dite_eq_left (hs hz)]
    exact Classical.choose_spec (hs hz)
  obtain ⟨K, hK⟩ := (hfinite.image j).bddAbove
  refine ⟨K, fun m => ?_⟩
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self m))
  obtain ⟨hzs, hball⟩ := Set.mem_iUnion.mp hz
  let k := j z
  have hk : k ≤ K := hK ⟨z, hzs, rfl⟩
  have hnorm : ‖u m - u k‖ < Real.sqrt ε := by
    rw [hj hzs]
    simpa only [dist_eq_norm] using Metric.mem_ball.mp hball
  have hsq : ‖u m - u k‖^2 < ε := by
    rw [← Real.sq_sqrt hε.le]
    exact pow_lt_pow_left₀ hnorm (norm_nonneg _) (by decide)
  refine ⟨k, hk, ‖u m - u k‖^2, hsq, ?_⟩
  have hpoint (n : ℕ) : ‖a * lam^(n+(m+1)) - a * lam^(n+(k+1))‖^2 = ‖u m-u k‖^2 := by
    rw [pow_add lam n (m+1), pow_add lam n (k+1)]
    rw [show a * (lam^n * lam^(m+1)) - a * (lam^n * lam^(k+1)) = lam^n * (u m - u k) by dsimp [u]; ring]
    simp [norm_pow, hlam]
  simp only [hpoint]
  exact (realCesaro_const_tendsto (‖u m-u k‖^2)).comp (hM.comp hσ).tendsto_atTop

private theorem boundedObservable_finset_sum {ι : Type*} (s : Finset ι) (g : ι → X → ℂ)
    (hg : ∀ i, BoundedObservable (g i)) : BoundedObservable (fun x => ∑ i ∈ s, g i x) := by
  classical
  choose C hC hb using fun i => (hg i).2
  refine ⟨Finset.measurable_sum _ (fun i _ => (hg i).1), ∑ i ∈ s, C i,
    sum_nonneg (fun i _ => hC i), fun x => (norm_sum_le _ _).trans (sum_le_sum fun i _ => hb i x)⟩

theorem ae_orbit_test_compact_of_discrete {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hd : KoopmanDiscreteSpectrum μ T) {f : X → ℂ} (hf : BoundedObservable f) :
    ∀ᵐ x ∂μ, CompactSeq (fun n => f (orbitSequence T x n)) := by
  classical
  choose D e hE using fun k : ℕ => hd f hf (1/((k : ℝ)+1)) (by positivity)
  let g (k : ℕ) (x : X) := ∑ i : Fin (D k), (e k i).value x
  have hG (k : ℕ) : BoundedObservable (g k) :=
    boundedObservable_finset_sum univ (fun i => (e k i).value) (fun i => (e k i).bounded)
  have hComp (k : ℕ) : ∀ᵐ x ∂μ, CompactSeq (fun n => g k (orbitSequence T x n)) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin (D k) => ae_eigenfunction_orbit_pow hT.toMeasurePreserving (e k i))] with x hx
    unfold g
    apply compactAlong_finset_sum strictMono_id
    intro i _
    have hfun : (fun n => (e k i).value (orbitSequence T x n)) = fun n => (e k i).value x * (e k i).eigenvalue^n := funext (hx i)
    rw [hfun]
    exact compactAlong_exponential _ _ (e k i).norm_eigenvalue strictMono_id
  have hMean (k : ℕ) : ∀ᵐ x ∂μ,
      Tendsto (realCesaro (fun n => ‖f (orbitSequence T x n)-g k (orbitSequence T x n)‖^2)) atTop
        (𝓝 (∫ y, ‖f y-g k y‖^2 ∂μ)) := by
    obtain ⟨C, hC, hb⟩ := hf.2
    obtain ⟨B, hB, hc⟩ := (hG k).2
    let U (y : X) := ‖f y-g k y‖^2
    have hU : Measurable U := (hf.1.sub (hG k).1).norm.pow_const _
    have hBound (y : X) : |U y| ≤ (C+B)^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hb y) (hc y))) 2
    exact ae_tendsto_orbitCesaro_real hT hU (sq_nonneg _) hBound
  filter_upwards [ae_all_iff.mpr hComp, ae_all_iff.mpr hMean] with x hx hx'
  apply compactAlong_of_meanSquare_approximation (hf.orbit_bounded T x) strictMono_id
  intro ε hε
  have ht : Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨fun n => g k (orbitSequence T x n), hx k, ?_⟩
  have hu : (∫ y, ‖f y-g k y‖^2 ∂μ) < ε := (hE k).trans hk
  exact ((hx' k).eventually (gt_mem_nhds hu)).mono (fun _ h => h.le)

/-- `LemmaConstructingSequences` (iv), including the positive-density visit enumeration. -/
theorem ae_visits_compact {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hs : KoopmanDiscreteSpectrum μ T) {A : Set X}
    (hA : MeasurableSet A) (hpos : 0 < μ A) :
    ∀ᵐ x ∂μ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
      HasPositiveLowerDensity (Set.range σ) ∧ CompactSeq (selectionWeight (Set.range σ)) := by
  have hp : 0 < μ.real A := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  filter_upwards [ae_visit_density hT hA, ae_orbit_test_compact_of_discrete hT hs (boundedObservable_visit A hA)] with x hx hc
  have hd := positiveLowerDensity_of_density_limit hp hx
  obtain ⟨σ, hσ, hR⟩ := exists_enumeration_of_positiveLowerDensity hd
  refine ⟨σ, hσ, hR, ?_, ?_⟩
  · rwa [hR]
  · rw [hR]
    simpa only [visitObservable_orbit] using hc

end Discrete

/-- `LemmaConstructingSequences` (iii). Deduce one full-measure set for all
continuous tests from the countable dense family and compact L² closure. -/
theorem ae_orbit_compact {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hd : KoopmanDiscreteSpectrum μ T) :
    ∀ᵐ x ∂μ, CompactDistribution (orbitSequence T x) := by
  classical
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense C(X, ℂ)
  have : Countable S := hSc.to_subtype
  have hS : ∀ᵐ x ∂μ, ∀ g : S, CompactSeq (fun n => g.1 (orbitSequence T x n)) :=
    ae_all_iff.mpr fun g => ae_orbit_test_compact_of_discrete hT hd (boundedObservable_of_continuous g.1)
  filter_upwards [hS] with x hx
  intro f
  apply compactAlong_of_meanSquare_approximation (bounded_test f _) strictMono_id
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hSd f) (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  rw [dist_eq_norm] at hfg
  refine ⟨fun n => g (orbitSequence T x n), hx ⟨g, hg⟩, Eventually.of_forall fun N => ?_⟩
  have hh (n : ℕ) : ‖f (orbitSequence T x n)-g (orbitSequence T x n)‖^2 ≤ ε := by
    rw [← Real.sq_sqrt hε.le]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((ContinuousMap.norm_coe_le_norm (f-g) _).trans hfg.le) 2
  by_cases hN : 0 < N
  · exact (realCesaro_mono hh N).trans_eq (realCesaro_const_pos ε hN)
  · simp [realCesaro, Nat.eq_zero_of_not_pos hN, hε.le]

end VdC

end

end VdC_ErgodicExamples_Module

/- Source: VdC/ThesisWeakMixing.lean -/
section VdC_ThesisWeakMixing_Module

/-! The permissible-pair formulations in the thesis's weak-mixing characterization. -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace VdC

noncomputable section

/-- Each lag has a discrepancy limit along the same increasing averaging lengths. -/
def PermissiblePair (D : ℕ → ℕ → ℝ) (M : ℕ → ℕ) (δ : ℕ → ℝ) : Prop :=
  StrictMono M ∧ ∀ h, Tendsto (fun q => D h (M q)) atTop (𝓝 (δ h))

def MeanPermissibleDiscrepancyZero (D : ℕ → ℕ → ℝ) : Prop :=
  ∀ M δ, PermissiblePair D M δ → Tendsto (realCesaro δ) atTop (𝓝 0)

/-- Concatenate the two coordinate blocks at lag h+1. -/
def cubeLagPair {d e : ℕ} (x : ℕ → Cube d) (y : ℕ → Cube e) (h n : ℕ) : Cube (d + e) :=
  Fin.addCases (x n) (y (n + (h + 1)))

def jointDiscrepancy {d e : ℕ} (x : ℕ → Cube d) (y : ℕ → Cube e) (h N : ℕ) : ℝ :=
  rectangleDiscrepancy (cubeLagPair x y h) N

def ThesisCrossDiscrepancy {d : ℕ} (x : ℕ → Cube d) : Prop :=
  ∀ e : ℕ, 0 < e → ∀ y : ℕ → Cube e, Equidistributed (cubeLebesgue e) y →
    MeanPermissibleDiscrepancyZero (jointDiscrepancy x y)

def ThesisSelfDiscrepancy {d : ℕ} (x : ℕ → Cube d) : Prop :=
  MeanPermissibleDiscrepancyZero (jointDiscrepancy x x)

def ThesisDifferenceDiscrepancy {d : ℕ} (x : ℕ → Cube d) : Prop :=
  MeanPermissibleDiscrepancyZero (differenceDiscrepancy (fun n => cubeToTorus (x n)))

/-- The discrepancy limits can always be made to exist by one further extraction. -/
theorem exists_permissible_pair_refinement {D : ℕ → ℕ → ℝ} {M : ℕ → ℕ}
    (hM : StrictMono M) (hB : ∀ h N, D h N ∈ Set.Icc (0 : ℝ) 1) :
    ∃ φ δ, StrictMono φ ∧ PermissiblePair D (M ∘ φ) δ := by
  obtain ⟨φ, c, hφ, hc⟩ := exists_common_subsequence
    (fun (q h : ℕ) => (D h (M q) : ℂ)) (fun h =>
    ⟨1, zero_le_one, fun n => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB h (M n)).1]
        using (hB h (M n)).2⟩)
  refine ⟨φ, fun h => (c h).re, hφ, hM.comp hφ, fun h => ?_⟩
  have hh := Complex.continuous_re.continuousAt.tendsto.comp (hc h)
  simpa only [Function.comp_def, Complex.ofReal_re] using hh

private theorem nearlyWeakMixing_of_permissible_discrepancies {u : ℕ → ℂ}
    (hu : BoundedSeq u) (D : ℕ → ℕ → ℝ) (hB : ∀ h N, D h N ∈ Set.Icc (0 : ℝ) 1)
    (K : ℝ) (hbound : ∀ h N, ‖corr u u (h+1) N‖ ≤ K * D h N)
    (hD : MeanPermissibleDiscrepancyZero D) : NearlyWeakMixing u := by
  apply nearlyWeakMixing_of_self_mean hu
  intro M r hM hr
  obtain ⟨φ, δ, hφ, hp⟩ := exists_permissible_pair_refinement hM hB
  have hlim := (hD _ _ hp).const_mul K
  rw [mul_zero] at hlim
  have hg (h : ℕ) : ‖r (h+1)‖ ≤ K * δ h := by
    exact le_of_tendsto_of_tendsto ((hr (h+1)).comp hφ.tendsto_atTop).norm
      ((hp.2 h).const_mul K) (Eventually.of_forall fun q => hbound h ((M ∘ φ) q))
  apply squeeze_zero (realCesaro_nonneg (fun _ => norm_nonneg _)) _ hlim
  intro H
  rw [← realCesaro_const_mul]
  exact realCesaro_mono hg H

/-- The difference-discrepancy condition implies weak mixing, (iv) → (i).
The extraction here is from an arbitrary permissible autocorrelation subsequence. -/
theorem weakMixing_of_thesisDifferenceDiscrepancy {d : ℕ} {x : ℕ → Cube d}
    (hx : ThesisDifferenceDiscrepancy x) : WeaklyMixingDistribution (cubeLebesgue d) x := by
  apply (cube_weakMixing_iff_characters x).2
  intro m hm
  let z : ℕ → Torus d := fun n => cubeToTorus (x n)
  obtain ⟨K, _, hbound⟩ := characterRectangleEstimate_all z m hm
  apply nearlyWeakMixing_of_permissible_discrepancies (bounded_test (torusCharacter m) z)
    (differenceDiscrepancy z) (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) K _ hx
  intro h N
  simpa only [corr, torusCharacter_point_sub] using hbound h N

private theorem pair_character_eq {d e : ℕ} (a : Fin d → ℤ) (b : Fin e → ℤ)
    (x : Cube d) (y : Cube e) :
    torusCharacter (Fin.addCases a b) (cubeToTorus (Fin.addCases x y)) =
      torusCharacter a (cubeToTorus x) * torusCharacter b (cubeToTorus y) := by
  rw [torusCharacter_apply, Fin.prod_univ_add]
  simp only [cubeToTorus, Fin.addCases_left, Fin.addCases_right, torusCharacter_apply]

private theorem pair_frequency_ne_zero {d e : ℕ} {a : Fin d → ℤ} {b : Fin e → ℤ}
    (ha : a ≠ 0) : (Fin.addCases a b : Fin (d + e) → ℤ) ≠ 0 := by
  intro h
  exact ha (funext fun i => by simpa using congrFun h (Fin.castAdd e i))

/-- The joint self-discrepancy condition implies weak mixing, (iii) → (i). -/
theorem weakMixing_of_thesisSelfDiscrepancy {d : ℕ} {x : ℕ → Cube d}
    (hx : ThesisSelfDiscrepancy x) : WeaklyMixingDistribution (cubeLebesgue d) x := by
  apply (cube_weakMixing_iff_characters x).2
  intro m hm
  let k : Fin (d+d) → ℤ := Fin.addCases (-m) m
  have hk : k ≠ 0 := pair_frequency_ne_zero (neg_ne_zero.mpr hm)
  apply nearlyWeakMixing_of_permissible_discrepancies
    (bounded_test (torusCharacter m) (fun n => cubeToTorus (x n)))
    (jointDiscrepancy x x) (fun _ _ => rectangleDiscrepancy_mem_Icc _ _)
    (fourierDiscrepancyConstant k) _ hx
  intro h N
  have he (n : ℕ) :
      torusCharacter k (cubeToTorus (cubeLagPair x x h n)) =
        torusCharacter m (cubeToTorus (x (n+(h+1)))) * star (torusCharacter m (cubeToTorus (x n))) := by
    change torusCharacter (Fin.addCases (-m) m)
      (cubeToTorus (Fin.addCases (x n) (x (n + (h + 1))))) = _
    rw [pair_character_eq, torusCharacter_neg, ContinuousMap.star_apply, mul_comm]
  have hb := finite_fourier_rectangle_bound k hk (cubeLagPair x x h) N
  change ‖cesaro (fun n => torusCharacter k (cubeToTorus (cubeLagPair x x h n))) N‖ ≤ _ at hb
  simpa only [corr, ← he, jointDiscrepancy] using hb

/-- The cross condition tested at the self sequence, once that sequence is uniformly distributed. -/
theorem thesisSelfDiscrepancy_of_cross_of_equidistributed {d : ℕ} (hd : 0 < d)
    {x : ℕ → Cube d} (hx : ThesisCrossDiscrepancy x) (hU : Equidistributed (cubeLebesgue d) x) :
    ThesisSelfDiscrepancy x := hx d hd x hU

private theorem tendsto_zero_of_permissible_bound {u : ℕ → ℂ} (hu : BoundedSeq u)
    {D : ℕ → ℕ → ℝ} (hB : ∀ h N, D h N ∈ Set.Icc (0 : ℝ) 1)
    (hD : MeanPermissibleDiscrepancyZero D) (K : ℝ)
    (hbound : ∀ h N, ‖u N‖ ≤ K * D h N) : Tendsto u atTop (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, _, hψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨φ, c, hφ, hc⟩ := exists_common_subsequence
    (fun (q : ℕ) (_ : Unit) => u ((ns ∘ ψ) q)) (fun _ => by
      obtain ⟨C, hC, hC'⟩ := hu
      exact ⟨C, hC, fun _ => hC' _⟩)
  obtain ⟨τ, δ, hτ, hp⟩ := exists_permissible_pair_refinement (hψ.comp hφ) hB
  have huc := (hc ()).comp hτ.tendsto_atTop
  have h' (h : ℕ) : ‖c ()‖ ≤ K * δ h :=
    le_of_tendsto_of_tendsto huc.norm ((hp.2 h).const_mul K)
      (Eventually.of_forall fun _ => hbound h _)
  have hlimit : ‖c ()‖ ≤ 0 := by
    have hr := (hD _ _ hp).const_mul K
    rw [mul_zero] at hr
    apply le_of_tendsto_of_tendsto (realCesaro_const_tendsto ‖c ()‖) hr
    filter_upwards [] with H
    rw [← realCesaro_const_mul]
    exact realCesaro_mono h' H
  have hz : c () = 0 := norm_le_zero_iff.mp hlimit
  rw [hz] at huc
  exact ⟨ψ ∘ φ ∘ τ, huc⟩

/-- The cross condition already forces the unshifted marginal to be uniformly distributed
as soon as there is one uniformly distributed comparison sequence of positive dimension. -/
theorem equidistributed_of_thesisCross_with_comparison {d e : ℕ} (he : 0 < e)
    {x : ℕ → Cube d} (hx : ThesisCrossDiscrepancy x) (y : ℕ → Cube e)
    (hy : Equidistributed (cubeLebesgue e) y) : Equidistributed (cubeLebesgue d) x := by
  apply equidistributed_of_cubeToTorus
  apply (equidistributed_torus_iff _).2
  intro m hm
  let u (N : ℕ) : ℂ := cesaro (fun n => torusCharacter m (cubeToTorus (x n))) N
  let k : Fin (d + e) → ℤ := Fin.addCases m 0
  have hk : k ≠ 0 := pair_frequency_ne_zero hm
  refine tendsto_zero_of_permissible_bound (u := u) ⟨1, zero_le_one, fun N => ?_⟩
    (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) (hx e he y hy)
    (fourierDiscrepancyConstant k) ?_
  · exact norm_cesaro_le _ zero_le_one (fun n => (torusCharacter_norm m _).le) N
  · intro h N
    have hb := finite_fourier_rectangle_bound k hk (cubeLagPair x y h) N
    change ‖cesaro (fun n => torusCharacter k (cubeToTorus (cubeLagPair x y h n))) N‖ ≤ _ at hb
    have heq (n : ℕ) :
        torusCharacter k (cubeToTorus (cubeLagPair x y h n)) = torusCharacter m (cubeToTorus (x n)) := by
      change torusCharacter (Fin.addCases m 0) (cubeToTorus (Fin.addCases (x n) (y (n+(h+1))))) = _
      rw [pair_character_eq, torusCharacter_zero]
      simp
    simpa only [heq, u, jointDiscrepancy] using hb

/-- There exists a uniformly distributed sequence in the one-dimensional cube. -/
theorem exists_equidistributed_one_cube : ∃ y : ℕ → Cube 1, Equidistributed (cubeLebesgue 1) y := by
  let c : UnitAddCircle := ((Real.sqrt 2 : ℝ) : UnitAddCircle)
  let y (n : ℕ) (_ : Fin 1) : UnitInterval := unitRepresentative (n • c)
  refine ⟨y, equidistributed_of_cubeToTorus ((equidistributed_torus_iff _).2 ?_)⟩
  intro m hm
  have hnon : m 0 ≠ 0 := by
    intro h
    exact hm (funext fun i => by change m i = 0; rw [Fin.eq_zero i]; exact h)
  let ω : ℂ := fourier (m 0) c
  have hω1 : ‖ω‖ = 1 := by simp [ω, fourier_apply]
  have hω : ω ≠ 1 := by
    intro h
    have hc' : (m 0) • c = 0 := by
      apply AddCircle.injective_toCircle one_ne_zero
      apply Subtype.ext
      simpa [ω, fourier_apply] using h
    rw [show c = ((Real.sqrt 2 : ℝ) : UnitAddCircle) from rfl, ← AddCircle.coe_zsmul,
      AddCircle.coe_eq_zero_iff] at hc'
    obtain ⟨j, hj⟩ := hc'
    exact (irrational_iff_ne_rational _).1 irrational_sqrt_two j (m 0) hnon
      ((eq_div_iff (by exact_mod_cast hnon)).2 (by simpa [zsmul_eq_mul, mul_comm] using hj.symm))
  have hz (n : ℕ) : fourier (m 0) (n • c) = ω ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      simp only [ω, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
  have hf (n : ℕ) : torusCharacter m (cubeToTorus (y n)) = ω ^ n := by
    simpa only [torusCharacter_apply, Fin.prod_univ_one, cubeToTorus, y, unitRepresentative_coe] using hz n
  simp_rw [hf]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖ω - 1‖))
  rw [cesaro, geom_sum_eq hω, norm_div, norm_div, Complex.norm_natCast]
  have hωp : ‖ω ^ N - 1‖ ≤ 2 := by
    simpa only [norm_pow, hω1, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (ω ^ N) 1
  exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hωp (norm_nonneg _)) (by positivity)

/-- The cross condition implies the joint self condition, (ii) → (iii). -/
theorem thesisSelfDiscrepancy_of_cross {d : ℕ} (hd : 0 < d) {x : ℕ → Cube d}
    (hx : ThesisCrossDiscrepancy x) : ThesisSelfDiscrepancy x := by
  obtain ⟨y, hy⟩ := exists_equidistributed_one_cube
  exact thesisSelfDiscrepancy_of_cross_of_equidistributed hd hx
    (equidistributed_of_thesisCross_with_comparison (by decide) hx y hy)

/-- The cube probability assigned to the first N observations, for N positive. -/
def cubeEmpirical {d : ℕ} (u : ℕ → Cube d) (N : ℕ) (hN : 0 < N) :
    ProbabilityMeasure (Cube d) := by
  refine ⟨(N : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range N, Measure.dirac (u n), ⟨?_⟩⟩
  rw [smul_apply, sum_apply, smul_eq_mul]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

theorem integral_cubeEmpirical {d : ℕ} (u : ℕ → Cube d) (N : ℕ) (hN : 0 < N)
    (f : Cube d → ℂ) :
    (∫ x, f x ∂(cubeEmpirical u N hN : Measure (Cube d))) = cesaro (fun n => f (u n)) N := by
  change (∫ x, f x ∂((N : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range N, Measure.dirac (u n))) = _
  rw [integral_smul_measure, integral_finsetSum_measure (fun _ _ => integrable_dirac eNorm_lt_top), cesaro]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

theorem cubeEmpirical_real_closedRectangle {d : ℕ} (u : ℕ → Cube d) (N : ℕ) (hN : 0 < N)
    (a b : Cube d) :
    (cubeEmpirical u N hN : Measure (Cube d)).real (closedRectangle a b) =
      rectangleFrequency u N a b := by
  classical
  let s := closedRectangle a b
  have h := integral_cubeEmpirical u N hN (s.indicator fun _ => (1 : ℂ))
  rw [integral_indicator (measurableSet_closedRectangle a b), setIntegral_const,
    Complex.real_smul, mul_one] at h
  apply_fun Complex.re at h
  rw [rectangleFrequency_eq_indicator_average]
  simpa [s, cesaro, realCesaro, Set.indicator, ← Complex.ofReal_div, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast] using h

private theorem cube_ae_coordinate_ne {d : ℕ} (i : Fin d) (a : UnitInterval) :
    ∀ᵐ x ∂cubeLebesgue d, x i ≠ a := by
  have h : ∀ᵐ t ∂unitIntervalLebesgue, t ≠ a := by
    apply ae_iff.mpr
    change unitIntervalLebesgue {t : UnitInterval | ¬t ≠ a} = 0
    rw [show {t : UnitInterval | ¬t ≠ a} = {a} by ext t; simp,
      unitIntervalLebesgue, comap_subtype_coe_apply measurableSet_Icc]
    simp
  exact (measurePreserving_eval (μ := fun _ : Fin d => unitIntervalLebesgue) i).quasiMeasurePreserving.ae h

/-- All closed boxes are continuity sets of cube Lebesgue measure. -/
theorem cubeLebesgue_frontier_closedRectangle {d : ℕ} (a b : Cube d) :
    cubeLebesgue d (frontier (closedRectangle a b)) = 0 := by
  have hclosed : IsClosed (closedRectangle a b) := by
    rw [show closedRectangle a b = ⋂ i, (fun x : Cube d => (x i : ℝ)) ⁻¹'
      Set.Icc (a i : ℝ) (b i : ℝ) by
      ext x
      simp only [closedRectangle, Set.mem_univ_pi, Set.mem_iInter, Set.mem_preimage]]
    exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_subtype_val.comp (continuous_apply i))
  let U := ⋂ i, (fun x : Cube d => (x i : ℝ)) ⁻¹' Set.Ioo (a i : ℝ) (b i : ℝ)
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage (continuous_subtype_val.comp (continuous_apply i))
  have hUB : U ⊆ closedRectangle a b := by
    intro x hx
    rw [closedRectangle, Set.mem_univ_pi]
    intro i
    exact Set.Ioo_subset_Icc_self (Set.mem_iInter.mp hx i)
  have ha : ∀ᵐ x ∂cubeLebesgue d, ∀ i, x i ≠ a i :=
    ae_all_iff.mpr fun i => cube_ae_coordinate_ne i (a i)
  have hb : ∀ᵐ x ∂cubeLebesgue d, ∀ i, x i ≠ b i :=
    ae_all_iff.mpr fun i => cube_ae_coordinate_ne i (b i)
  have h : ∀ᵐ x ∂cubeLebesgue d, x ∉ frontier (closedRectangle a b) := by
    filter_upwards [ha, hb] with x hxa hxb
    intro hxf
    rw [frontier, hclosed.closure_eq] at hxf
    have hxU : x ∈ U := by
      apply Set.mem_iInter.mpr
      intro i
      have h := Set.mem_univ_pi.mp hxf.1 i
      change (a i : ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (b i : ℝ) at h
      exact ⟨lt_of_le_of_ne h.1 (fun eq => hxa i (Subtype.ext eq.symm)),
        lt_of_le_of_ne h.2 (fun eq => hxb i (Subtype.ext eq))⟩
    exact hxf.2 (interior_maximal hUB hU hxU)
  simpa using ae_iff.mp h

def uniformCube (d : ℕ) : ProbabilityMeasure (Cube d) := ⟨cubeLebesgue d, inferInstance⟩

theorem tendsto_rectangleFrequency_of_empirical_tendsto {d : ℕ} {ι : Type*} {l : Filter ι}
    {u : ι → ℕ → Cube d} {N : ι → ℕ} {hN : ∀ q, 0 < N q}
    (ht : Tendsto (fun q => cubeEmpirical (u q) (N q) (hN q)) l (𝓝 (uniformCube d)))
    (a b : Cube d) :
    Tendsto (fun q => rectangleFrequency (u q) (N q) a b) l (𝓝 (rectangleVolume a b)) := by
  have hB := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto ht
    (E := closedRectangle a b) (by
      change (cubeLebesgue d (frontier (closedRectangle a b))).toNNReal = 0
      rw [cubeLebesgue_frontier_closedRectangle]; rfl)
  have h := NNReal.continuous_coe.continuousAt.tendsto.comp hB
  change Tendsto (fun q => (cubeEmpirical (u q) (N q) (hN q) : Measure (Cube d)).real
    (closedRectangle a b)) l (𝓝 ((cubeLebesgue d).real (closedRectangle a b))) at h
  simpa only [cubeEmpirical_real_closedRectangle, ← rectangleVolume_eq_measure] using h

private def translateEndpoints {d : ℕ} (p : Cube d) (t : ℝ) : Cube d :=
  fun i => Set.projIcc 0 1 zero_le_one ((p i : ℝ) + t)

private theorem continuous_translateEndpoints {d : ℕ} (p : Cube d) :
    Continuous (translateEndpoints p) := by
  exact continuous_pi fun i => continuous_projIcc.comp (continuous_const.add continuous_id)

@[simp] private theorem translateEndpoints_zero {d : ℕ} (p : Cube d) :
    translateEndpoints p 0 = p := by
  ext i
  simp [translateEndpoints]

private theorem rectangleVolume_continuous {d : ℕ} :
    Continuous (fun p : Cube d × Cube d => rectangleVolume p.1 p.2) := by
  unfold rectangleVolume
  apply continuous_finsetProd
  intro i _
  exact continuous_const.max
    ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)).sub
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)))

private theorem translateEndpoints_bounds {d : ℕ} {x y : Cube d} {r : ℝ} (hx : dist y x < r) :
    ∀ i, ((translateEndpoints x (-r) i : UnitInterval) : ℝ) ≤ (y i : ℝ) ∧
      (y i : ℝ) ≤ ((translateEndpoints x r i : UnitInterval) : ℝ) := by
  intro i
  have hi : dist (y i) (x i) < r := (dist_le_pi_dist y x i).trans_lt hx
  change dist (y i : ℝ) (x i : ℝ) < r at hi
  rw [Real.dist_eq, abs_lt] at hi
  change max 0 (min 1 ((x i : ℝ) + -r)) ≤ (y i : ℝ) ∧
    (y i : ℝ) ≤ max 0 (min 1 ((x i : ℝ) + r))
  constructor
  · exact max_le (y i).property.1 ((min_le_right _ _).trans (by linarith [hi.1]))
  · exact (le_min (y i).property.2 (by linarith [hi.2])).trans (le_max_right _ _)

private theorem closedRectangle_subset {d : ℕ} {a b c e : Cube d}
    (ha : ∀ i, (c i : ℝ) ≤ a i) (hb : ∀ i, (b i : ℝ) ≤ e i) :
    closedRectangle a b ⊆ closedRectangle c e := by
  intro x hx
  apply Set.mem_univ_pi.mpr
  intro i
  have hi := Set.mem_univ_pi.mp hx i
  exact ⟨(ha i).trans hi.1, hi.2.trans (hb i)⟩

private theorem rectangleVolume_mono {d : ℕ} {a b c e : Cube d}
    (h : closedRectangle a b ⊆ closedRectangle c e) :
    rectangleVolume a b ≤ rectangleVolume c e := by
  rw [rectangleVolume_eq_measure, rectangleVolume_eq_measure]
  exact measureReal_mono h

private theorem rectangleFrequency_mono {d : ℕ} (u : ℕ → Cube d) (N : ℕ)
    {a b c e : Cube d} (h : closedRectangle a b ⊆ closedRectangle c e) :
    rectangleFrequency u N a b ≤ rectangleFrequency u N c e := by
  classical
  rw [rectangleFrequency_eq_indicator_average, rectangleFrequency_eq_indicator_average]
  apply realCesaro_mono
  intro j
  by_cases hj : u j ∈ closedRectangle a b
  · simp [hj, h hj]
  · by_cases hj' : u j ∈ closedRectangle c e <;> simp [hj, hj']

/-- Convergence on fixed closed boxes implies convergence uniformly over all boxes.
The comparison uses finite lower and upper brackets for the compact endpoint space. -/
theorem tendsto_rectangleDiscrepancy_of_frequency {d : ℕ} {ι : Type*} {l : Filter ι}
    (u : ι → ℕ → Cube d) (N : ι → ℕ)
    (hf : ∀ a b : Cube d, Tendsto (fun q => rectangleFrequency (u q) (N q) a b) l
      (𝓝 (rectangleVolume a b))) :
    Tendsto (fun q => rectangleDiscrepancy (u q) (N q)) l (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  let volDiff (p : Cube d × Cube d) (t : ℝ) : ℝ :=
    rectangleVolume (translateEndpoints p.1 (-t)) (translateEndpoints p.2 t) -
      rectangleVolume (translateEndpoints p.1 t) (translateEndpoints p.2 (-t))
  have hc (p : Cube d × Cube d) : Continuous (volDiff p) := by
    unfold volDiff
    apply Continuous.sub
    · exact rectangleVolume_continuous.comp
        (((continuous_translateEndpoints p.1).comp continuous_neg).prodMk (continuous_translateEndpoints p.2))
    · exact rectangleVolume_continuous.comp
        ((continuous_translateEndpoints p.1).prodMk ((continuous_translateEndpoints p.2).comp continuous_neg))
  have hchoose (p : Cube d × Cube d) : ∃ r : ℝ, 0 < r ∧ volDiff p r < ε/3 := by
    have hv : volDiff p 0 = 0 := by simp [volDiff]
    have hlt := (hc p).continuousAt.tendsto.eventually
      (gt_mem_nhds (show volDiff p 0 < ε/3 by rw [hv]; positivity))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp hlt
    refine ⟨δ/2, by positivity, hδ' ?_⟩
    change dist (δ/2) 0 < δ
    rw [Real.dist_eq, sub_zero, abs_of_pos (show 0 < δ/2 by positivity)]
    linarith
  choose r hr hvol using hchoose
  let U (p : Cube d × Cube d) := Metric.ball p (r p)
  have hcover : (Set.univ : Set (Cube d × Cube d)) ⊆ ⋃ p, U p :=
    fun p _ => Set.mem_iUnion.mpr ⟨p, Metric.mem_ball_self (hr p)⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  have hfe (p : Cube d × Cube d) : ∀ᶠ q in l,
      |rectangleFrequency (u q) (N q) (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p)) -
        rectangleVolume (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p))| < ε/3 ∧
      |rectangleFrequency (u q) (N q) (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p)) -
        rectangleVolume (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p))| < ε/3 := by
    have hup := (Metric.tendsto_nhds.mp
      (hf (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p)))) (ε/3) (by positivity)
    have hlo := (Metric.tendsto_nhds.mp
      (hf (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p)))) (ε/3) (by positivity)
    exact (hup.and hlo).mono (fun q h => by simpa only [Real.dist_eq] using h)
  filter_upwards [(eventually_all_finset T).2 (fun p _ => hfe p)] with q hq
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (rectangleDiscrepancy_mem_Icc _ _).1]
  suffices h : rectangleDiscrepancy (u q) (N q) ≤ 2*ε/3 by linarith
  unfold rectangleDiscrepancy
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨⟨a,b⟩, rfl⟩
  obtain ⟨p, hpT, hp⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ (a,b)))
  have hdist : max (dist a p.1) (dist b p.2) < r p := hp
  have ha := translateEndpoints_bounds (max_lt_iff.mp hdist).1
  have hb := translateEndpoints_bounds (max_lt_iff.mp hdist).2
  have hlo : closedRectangle (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p)) ⊆
      closedRectangle a b := closedRectangle_subset (fun i => (ha i).2) (fun i => (hb i).1)
  have hhi : closedRectangle a b ⊆
      closedRectangle (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p)) :=
    closedRectangle_subset (fun i => (ha i).1) (fun i => (hb i).2)
  have hvlo := rectangleVolume_mono hlo
  have hvhi := rectangleVolume_mono hhi
  have hflo := rectangleFrequency_mono (u q) (N q) hlo
  have hfhi := rectangleFrequency_mono (u q) (N q) hhi
  have hv := hvol p
  unfold volDiff at hv
  have hq' := hq p hpT
  apply abs_le.mpr
  constructor
  · linarith [(abs_lt.mp hq'.2).1]
  · linarith [(abs_lt.mp hq'.1).2]

/-- Uniform distribution on the cube implies vanishing closed-rectangle discrepancy. -/
theorem tendsto_rectangleDiscrepancy_of_equidistributed {d : ℕ} {u : ℕ → Cube d}
    (hu : Equidistributed (cubeLebesgue d) u) :
    Tendsto (rectangleDiscrepancy u) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => cubeEmpirical u (n+1) (Nat.succ_pos n)) atTop (𝓝 (uniformCube d)) := by
    apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
    intro f
    simp_rw [integral_cubeEmpirical]
    exact (hu f.toContinuousMap).comp (tendsto_add_atTop_nat 1)
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact tendsto_rectangleDiscrepancy_of_frequency (fun _ => u) (fun n => n+1)
    (tendsto_rectangleFrequency_of_empirical_tendsto ht)

/-- The finite Fourier estimate and Weyl's criterion give the converse on the
closed cube, with the torus-to-cube lift handling the endpoints. -/
theorem equidistributed_of_rectangleDiscrepancy_tendsto_zero {d : ℕ} {u : ℕ → Cube d}
    (hu : Tendsto (rectangleDiscrepancy u) atTop (𝓝 0)) :
    Equidistributed (cubeLebesgue d) u := by
  apply equidistributed_of_cubeToTorus
  apply (equidistributed_torus_iff _).2
  intro m hm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (finite_fourier_rectangle_bound m hm u) ?_
  simpa only [mul_zero] using hu.const_mul (fourierDiscrepancyConstant m)

theorem equidistributed_iff_rectangleDiscrepancy_tendsto_zero {d : ℕ} (u : ℕ → Cube d) :
    Equidistributed (cubeLebesgue d) u ↔ Tendsto (rectangleDiscrepancy u) atTop (𝓝 0) :=
  ⟨tendsto_rectangleDiscrepancy_of_equidistributed, equidistributed_of_rectangleDiscrepancy_tendsto_zero⟩

private def pullbackTorus {d : ℕ} (g : C(Torus d, ℂ)) : C(Cube d, ℂ) :=
  g.comp ⟨cubeToTorus, continuous_cubeToTorus d⟩

private def integralPullbackCLM {d : ℕ} (μ : ProbabilityMeasure (Cube d)) :
    C(Torus d, ℂ) →L[ℂ] ℂ := by
  let I : C(Torus d, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => testMean (μ : Measure (Cube d)) (pullbackTorus g)
      map_add' := fun f g => testMean_add _ (pullbackTorus f) (pullbackTorus g)
      map_smul' := fun c f => testMean_smul _ c (pullbackTorus f) }
  refine I.mkContinuous 1 fun g => ?_
  change ‖∫ x, g (cubeToTorus x) ∂(μ : Measure (Cube d))‖ ≤ 1 * ‖g‖
  simpa using norm_integral_le_of_norm_le_const (ae_of_all (μ : Measure (Cube d))
    fun x => g.norm_coe_le_norm (cubeToTorus x))

private theorem integrals_pullback_eq_of_characters {d : ℕ} (μ : ProbabilityMeasure (Cube d))
    (h : ∀ m : Fin d → ℤ, m ≠ 0 →
      testMean (μ : Measure (Cube d)) (pullbackTorus (torusCharacter m)) = 0) :
    ∀ g : C(Torus d, ℂ), testMean (μ : Measure (Cube d)) (pullbackTorus g) =
      testMean (cubeLebesgue d) (pullbackTorus g) := by
  let Δ := integralPullbackCLM μ - integralPullbackCLM (uniformCube d)
  let K := LinearMap.ker Δ.toLinearMap
  have hc : IsClosed (K : Set C(Torus d, ℂ)) := isClosed_eq Δ.continuous continuous_const
  have hs : Submodule.span ℂ (Set.range (torusCharacter (d := d))) ≤ K := by
    apply Submodule.span_le.2
    rintro _ ⟨m, rfl⟩
    change testMean (μ : Measure (Cube d)) (pullbackTorus (torusCharacter m)) -
      testMean (cubeLebesgue d) (pullbackTorus (torusCharacter m)) = 0
    apply sub_eq_zero.mpr
    by_cases hm : m = 0
    · subst m
      rw [torusCharacter_zero, show pullbackTorus (1 : C(Torus d, ℂ)) = 1 from by ext; rfl]
      simp [testMean]
    rw [h m hm]
    have hh : testMean (cubeLebesgue d) (pullbackTorus (torusCharacter m)) =
        testMean (torusHaar d) (torusCharacter m) := by
      unfold testMean
      rw [← (cubeToTorus_measurePreserving d).map_eq,
        integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable
          (torusCharacter m).continuous.stronglyMeasurable]
      rfl
    simp [hh, testMean_torusCharacter, hm]
  have htop := (Submodule.span ℂ (Set.range (torusCharacter (d := d)))).topologicalClosure_minimal hs hc
  rw [torusCharacters_dense] at htop
  intro g
  have hg := htop (Submodule.mem_top : g ∈ (⊤ : Submodule ℂ C(Torus d, ℂ)))
  change testMean (μ : Measure (Cube d)) (pullbackTorus g) -
    testMean (cubeLebesgue d) (pullbackTorus g) = 0 at hg
  exact sub_eq_zero.mp hg

private theorem measure_is_uniform_of_characters {d : ℕ} (μ : ProbabilityMeasure (Cube d))
    (h : ∀ m : Fin d → ℤ, m ≠ 0 →
      testMean (μ : Measure (Cube d)) (pullbackTorus (torusCharacter m)) = 0) : μ = uniformCube d := by
  have ht : Tendsto (fun _ : ℕ => μ) atTop (𝓝 (uniformCube d)) := by
    apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
    intro f
    let F := f.toContinuousMap
    let M : Measure (Cube d) := μ
    have hcut (K : ℕ) (g : C(Cube d, ℂ)) : testMean M (cubeCutoffTest K g) =
        testMean (cubeLebesgue d) (cubeCutoffTest K g) := by
      obtain ⟨p, hp⟩ := exists_cubeCutoff_descend K g
      have hh : pullbackTorus p = cubeCutoffTest K g := by ext x; exact hp x
      simpa only [hh] using integrals_pullback_eq_of_characters μ h p
    let e (K : ℕ) (x : Cube d) : ℝ := 1 - cubeCutoff K x
    have he (K : ℕ) : (∫ x, e K x ∂M) = ∫ x, e K x ∂cubeLebesgue d := by
      have hh := hcut K 1
      unfold testMean at hh
      change (∫ x, (1 : ℂ) * (cubeCutoff K x : ℂ) ∂M) =
        ∫ x, (1 : ℂ) * (cubeCutoff K x : ℂ) ∂cubeLebesgue d at hh
      simp only [one_mul, integral_complex_ofReal] at hh
      unfold e
      rw [integral_sub (integrable_const _)
          ((continuous_cubeCutoff K).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        integral_sub (integrable_const _)
          ((continuous_cubeCutoff K).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      rw [Complex.ofReal_injective hh]
    have hnorm (K : ℕ) :
        ‖testMean M (cubeCutoffTest K F) - testMean M F‖ ≤ ‖F‖ * ∫ x, e K x ∂M := by
      rw [norm_sub_rev, ← testMean_sub]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      apply integral_mono
      · exact (test_integrable M (F - cubeCutoffTest K F)).norm
      · exact (continuous_const.mul (continuous_const.sub (continuous_cubeCutoff K))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      intro x
      change ‖F x - cubeCutoffTest K F x‖ ≤ ‖F‖ * (1 - cubeCutoff K x)
      rw [norm_sub_cubeCutoffTest]
      exact mul_le_mul_of_nonneg_right (F.norm_coe_le_norm x) (sub_nonneg.mpr (cubeCutoff_le_one K x))
    have hlim : Tendsto (fun K => testMean M (cubeCutoffTest K F)) atTop (𝓝 (testMean M F)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.2
      have h0 := (tendsto_cutoffDeficit_integral d).const_mul ‖F‖
      rw [mul_zero] at h0
      apply squeeze_zero (fun _ => norm_nonneg _) _ h0
      intro K
      rw [← he K]
      exact hnorm K
    have hlim' := tendsto_testMean_cubeCutoffTest F
    simp_rw [hcut] at hlim
    have hf := tendsto_nhds_unique hlim hlim'
    change (∫ x, f x ∂M) = (∫ x, f x ∂cubeLebesgue d) at hf
    change Tendsto (fun _ : ℕ => ∫ x, f x ∂M) atTop (𝓝 (∫ x, f x ∂cubeLebesgue d))
    rw [← hf]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds ht

private theorem continuous_probability_test {d : ℕ} (f : C(Cube d, ℂ)) :
    Continuous (fun μ : ProbabilityMeasure (Cube d) => testMean (μ : Measure (Cube d)) f) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 tendsto_id
    ((ContinuousMap.equivBoundedOfCompact (Cube d) ℂ) f)

/-- A qualitative inverse discrepancy estimate. For every tolerance, only finitely
many Fourier coefficients are needed, with positive weights independent of the sample. -/
theorem finite_character_discrepancy_bound {d : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ((Fin d → ℤ) × ℝ), (∀ p ∈ S, p.1 ≠ 0 ∧ 0 < p.2) ∧
      ∀ (u : ℕ → Cube d) (N : ℕ), 0 < N →
      rectangleDiscrepancy u N ≤ ε + ∑ p ∈ S,
        ‖cesaro (fun n => torusCharacter p.1 (cubeToTorus (u n))) N‖ / p.2 := by
  classical
  let I := (ℕ → Cube d) × ℕ+
  let E (q : I) : ProbabilityMeasure (Cube d) := cubeEmpirical q.1 q.2.val q.2.property
  let A : Set (ProbabilityMeasure (Cube d)) :=
    E '' {q : I | ε ≤ rectangleDiscrepancy q.1 q.2.val}
  let l : Filter I := comap E (𝓝 (uniformCube d))
  have he : Tendsto E l (𝓝 (uniformCube d)) := tendsto_comap
  have hd : Tendsto (fun q : I => rectangleDiscrepancy q.1 q.2.val) l (𝓝 0) :=
    tendsto_rectangleDiscrepancy_of_frequency _ _ (tendsto_rectangleFrequency_of_empirical_tendsto he)
  have hnA : uniformCube d ∉ closure A := by
    intro hc
    have hp := eventually_comap.mp (hd.eventually (gt_mem_nhds hε))
    obtain ⟨ν, hν, hνA⟩ := (mem_closure_iff_nhds.mp hc) _ hp
    obtain ⟨q, hq, heq⟩ := hνA
    exact (not_lt_of_ge hq) (hν q heq)
  let coeff (p : Fin d → ℤ) (ν : ProbabilityMeasure (Cube d)) :=
    testMean (ν : Measure (Cube d)) (pullbackTorus (torusCharacter p))
  have hm (ν : closure A) : ∃ m : Fin d → ℤ, m ≠ 0 ∧ 0 < ‖coeff m ν.1‖ := by
    by_contra! h
    have heq := measure_is_uniform_of_characters ν.1 (fun m hm => norm_le_zero_iff.mp (h m hm))
    exact hnA (heq ▸ ν.2)
  choose m hm0 hmpos using hm
  let U (ν : closure A) : Set (ProbabilityMeasure (Cube d)) :=
    {ξ | ‖coeff (m ν) ν.1‖ / 2 < ‖coeff (m ν) ξ‖}
  have ho (ν : closure A) : IsOpen (U ν) :=
    isOpen_lt continuous_const (continuous_probability_test _).norm
  have hcover : closure A ⊆ ⋃ ν, U ν := by
    intro ξ hξ
    exact Set.mem_iUnion.mpr ⟨⟨ξ, hξ⟩, (show ‖coeff (m ⟨ξ,hξ⟩) ξ‖ / 2 < ‖coeff (m ⟨ξ,hξ⟩) ξ‖ by
      linarith only [hmpos ⟨ξ,hξ⟩])⟩
  obtain ⟨T, hT⟩ := isClosed_closure.isCompact.elim_finite_subcover U ho hcover
  let pt (ν : closure A) := (m ν, ‖coeff (m ν) ν.1‖ / 2)
  let S := T.image pt
  have hS (p : (Fin d → ℤ) × ℝ) (hp : p ∈ S) : p.1 ≠ 0 ∧ 0 < p.2 := by
    obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hm0 ν, half_pos (hmpos ν)⟩
  refine ⟨S, hS, fun u N hN => ?_⟩
  let q : I := (u, ⟨N, hN⟩)
  let V (p : (Fin d → ℤ) × ℝ) := ‖coeff p.1 (E q)‖ / p.2
  have hV (p : (Fin d → ℤ) × ℝ) :
      V p = ‖cesaro (fun n => torusCharacter p.1 (cubeToTorus (u n))) N‖ / p.2 := by
    change ‖∫ x, pullbackTorus (torusCharacter p.1) x ∂(cubeEmpirical u N hN : Measure (Cube d))‖ /
      p.2 = _
    rw [integral_cubeEmpirical]
    rfl
  simp_rw [← hV]
  have hnon : ∀ p ∈ S, 0 ≤ V p := fun p hp =>
    div_nonneg (norm_nonneg _) (hS p hp).2.le
  by_cases hbad : ε ≤ rectangleDiscrepancy u N
  · have hEA : E q ∈ closure A := subset_closure ⟨q, hbad, rfl⟩
    obtain ⟨ν, hν, hq⟩ := Set.mem_iUnion₂.mp (hT hEA)
    have hsmall : 1 ≤ V (pt ν) := (le_div_iff₀ (half_pos (hmpos ν))).2 (by
      rw [one_mul]
      exact (show ‖coeff (m ν) ν.1‖ / 2 < ‖coeff (m ν) (E q)‖ from hq).le)
    have hsum := (hsmall.trans (Finset.single_le_sum hnon (Finset.mem_image_of_mem pt hν)))
    linarith only [(rectangleDiscrepancy_mem_Icc u N).2, hsum, hε]
  · have := Finset.sum_nonneg hnon
    linarith

def lagFourierAverage {d : ℕ} (u : ℕ → ℕ → Cube d) (m : Fin d → ℤ) (h N : ℕ) : ℂ :=
  cesaro (fun n => torusCharacter m (cubeToTorus (u h n))) N

/-- The relevant Fourier means are Cesàro-small in h after every common
refinement on which the individual lag limits exist. -/
def MeanPermissibleFourierZero {d : ℕ} (u : ℕ → ℕ → Cube d) : Prop :=
  ∀ (m : Fin d → ℤ), m ≠ 0 → ∀ (M : ℕ → ℕ) (r : ℕ → ℂ), StrictMono M →
    (∀ h, Tendsto (fun q => lagFourierAverage u m h (M q)) atTop (𝓝 (r h))) →
    Tendsto (realCesaro (fun h => ‖r h‖)) atTop (𝓝 0)

theorem meanPermissibleDiscrepancyZero_of_fourier {d : ℕ} (u : ℕ → ℕ → Cube d)
    (hFourier : MeanPermissibleFourierZero u) :
    MeanPermissibleDiscrepancyZero (fun h N => rectangleDiscrepancy (u h) N) := by
  intro M δ hp
  have hδ (h : ℕ) : 0 ≤ δ h :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hp.2 h)
      (Eventually.of_forall fun q => (rectangleDiscrepancy_mem_Icc (u h) (M q)).1)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS, hb⟩ := finite_character_discrepancy_bound (d := d) (ε/2) (by positivity)
  obtain ⟨φ, r, hφ, hr⟩ := exists_common_subsequence
    (fun (q : ℕ) (i : (Fin d → ℤ) × ℕ) => lagFourierAverage u i.1 i.2 (M q))
    (fun ⟨m,h⟩ => ⟨1, zero_le_one, fun q =>
      norm_cesaro_le _ zero_le_one (fun n => (torusCharacter_norm m _).le) (M q)⟩)
  have hlig (p : (Fin d → ℤ) × ℝ) (hpS : p ∈ S) :
      Tendsto (realCesaro (fun h => ‖r (p.1,h)‖ / p.2)) atTop (𝓝 0) := by
    have hg := hFourier p.1 (hS _ hpS).1 (M ∘ φ) (fun h => r (p.1,h)) (hp.1.comp hφ)
      (fun h => hr (p.1,h))
    rw [show (fun h => ‖r (p.1,h)‖ / p.2) = (fun h => p.2⁻¹ * ‖r (p.1,h)‖) from
      funext fun h => by rw [div_eq_mul_inv, mul_comm]]
    change Tendsto (fun H => realCesaro (fun h => p.2⁻¹ * ‖r (p.1,h)‖) H) atTop (𝓝 0)
    simp_rw [realCesaro_const_mul]
    simpa only [mul_zero] using hg.const_mul p.2⁻¹
  have hδbd (h : ℕ) : δ h ≤ ε/2 + ∑ p ∈ S, ‖r (p.1,h)‖ / p.2 := by
    have hlim : Tendsto (fun q => ε/2 + ∑ p ∈ S,
        ‖lagFourierAverage u p.1 h (M (φ q))‖ / p.2) atTop
        (𝓝 (ε/2 + ∑ p ∈ S, ‖r (p.1,h)‖ / p.2)) :=
      tendsto_const_nhds.add (tendsto_finsetSum S (fun p _ => ((hr (p.1,h)).norm).div_const p.2))
    have hlimδ := (hp.2 h).comp hφ.tendsto_atTop
    apply le_of_tendsto_of_tendsto hlimδ hlim
    filter_upwards [(hp.1.comp hφ).tendsto_atTop.eventually (eventually_gt_atTop 0)] with q hq
    exact hb (u h) ((M ∘ φ) q) hq
  have hmean : Tendsto (fun H => realCesaro (fun h => ε/2 + ∑ p ∈ S, ‖r (p.1,h)‖ / p.2) H)
      atTop (𝓝 (ε/2)) := by
    simp_rw [realCesaro_add, realCesaro_sum]
    simpa only [Finset.sum_const_zero, add_zero] using
      (realCesaro_const_tendsto (ε/2)).add (tendsto_finsetSum S hlig)
  filter_upwards [hmean.eventually (gt_mem_nhds (show ε/2 < ε by linarith))] with H hH
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (realCesaro_nonneg hδ H)]
  exact (realCesaro_mono hδbd H).trans_lt hH

/-- Weak mixing implies the difference-discrepancy condition, (i) → (iv). -/
theorem thesisDifferenceDiscrepancy_of_weakMixing {d : ℕ} {x : ℕ → Cube d}
    (hx : WeaklyMixingDistribution (cubeLebesgue d) x) : ThesisDifferenceDiscrepancy x := by
  let z : ℕ → Torus d := fun n => cubeToTorus (x n)
  let u (h n : ℕ) (i : Fin d) := unitRepresentative (z (n+(h+1)) i - z n i)
  apply meanPermissibleDiscrepancyZero_of_fourier u
  intro m hm M r hM hr
  let a (n : ℕ) : ℂ := torusCharacter m (z n)
  have ha : NearlyWeakMixing a := (cube_weakMixing_iff_characters x).1 hx m hm
  let s (h : ℕ) : ℂ := Nat.casesOn h 1 r
  have hr' : CorrLimits a a M s := by
    intro h
    cases h with
    | zero =>
      have hval (q : ℕ) (hq : M q ≠ 0) : corr a a 0 (M q) = 1 := by
        simp only [corr, Nat.add_zero, a]
        have he (n : ℕ) : torusCharacter m (z n) * star (torusCharacter m (z n)) = 1 := by
          rw [show torusCharacter m (z n) * star (torusCharacter m (z n)) =
            (‖torusCharacter m (z n)‖ : ℂ)^2 from Complex.mul_conj' _, torusCharacter_norm]
          norm_num
        simp_rw [he]
        exact cesaro_const 1 (Nat.pos_of_ne_zero hq)
      exact tendsto_const_nhds.congr' ((hM.tendsto_atTop.eventually (eventually_gt_atTop 0)).mono
        (fun q hq => (hval q hq.ne').symm))
    | succ h =>
      have hZ (n : ℕ) : cubeToTorus (u h n) = z (n+(h+1)) - z n := by
        funext i
        exact unitRepresentative_coe _
      simpa only [s, a, lagFourierAverage, hZ, torusCharacter_point_sub, corr] using hr h
  have hp : PermissibleTriple a a M := ⟨ha.1, ha.1, hM, ⟨s,hr'⟩, ⟨s,hr'⟩, ⟨s,hr'⟩, ⟨s,hr'⟩⟩
  exact ha.2 a M s hp hr'

theorem thesisDifferenceDiscrepancy_iff_weakMixing {d : ℕ} (x : ℕ → Cube d) :
    ThesisDifferenceDiscrepancy x ↔ WeaklyMixingDistribution (cubeLebesgue d) x :=
  ⟨weakMixing_of_thesisDifferenceDiscrepancy, thesisDifferenceDiscrepancy_of_weakMixing⟩

/-- A weakly mixing distribution has Cesàro-small joint discrepancy against
every uniformly distributed second sequence, (i) → (ii). -/
theorem thesisCrossDiscrepancy_of_weakMixing {d : ℕ} {x : ℕ → Cube d}
    (hx : WeaklyMixingDistribution (cubeLebesgue d) x) : ThesisCrossDiscrepancy x := by
  intro e _ y hy
  apply meanPermissibleDiscrepancyZero_of_fourier (cubeLagPair x y)
  intro m hm M r hM hr
  let a (i : Fin d) := m (Fin.castAdd e i)
  let b (i : Fin e) := m (Fin.natAdd d i)
  have hab : m = Fin.addCases a b := by
    funext i
    refine Fin.addCases (motive := fun i => m i = Fin.addCases a b i) ?_ ?_ i
    · intro i; simp [a]
    · intro i; simp [b]
  let u (n : ℕ) := torusCharacter (-a) (cubeToTorus (x n))
  let v (n : ℕ) := torusCharacter b (cubeToTorus (y n))
  have hU : BoundedSeq u := bounded_test (torusCharacter (-a)) (fun n => cubeToTorus (x n))
  have hV : BoundedSeq v := bounded_test (torusCharacter b) (fun n => cubeToTorus (y n))
  have he (h N : ℕ) :
      lagFourierAverage (cubeLagPair x y) m h N = corr v u (h+1) N := by
    unfold lagFourierAverage corr
    congr 1
    funext n
    change torusCharacter m (cubeToTorus (Fin.addCases (x n) (y (n+(h+1))))) =
      v (n+(h+1)) * star (u n)
    rw [hab, pair_character_eq]
    simp only [u, v, torusCharacter_neg, ContinuousMap.star_apply, star_star, mul_comm]
  simp_rw [he] at hr
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hz
      apply hm
      rw [hab, ha, hz]
      funext i
      change ((Fin.addCases (0 : Fin d → ℤ) (0 : Fin e → ℤ)) : Fin (d+e) → ℤ) i = 0
      refine Fin.addCases (motive := fun i =>
        ((Fin.addCases (0 : Fin d → ℤ) (0 : Fin e → ℤ)) : Fin (d+e) → ℤ) i = 0) ?_ ?_ i <;> simp
    have hv0 : Tendsto (cesaro v) atTop (𝓝 0) :=
      (equidistributed_torus_iff _).1 (equidistributed_cubeToTorus hy) b hb
    have hzero (h : ℕ) : r h = 0 := by
      have hu0 : u = fun _ => 1 := by funext n; simp [u, ha]
      have hvh := tendsto_cesaro_shift hV (h+1) hM (hv0.comp hM.tendsto_atTop)
      have hh := hr h
      simp only [corr, hu0, star_one, mul_one] at hh
      exact tendsto_nhds_unique hh hvh
    simpa only [hzero, norm_zero] using realCesaro_const_tendsto 0
  have huwm : NearlyWeakMixing u :=
    (cube_weakMixing_iff_characters x).1 hx (-a) (neg_ne_zero.mpr ha)
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hU hV hM
  obtain ⟨s, hs⟩ := hp.yx
  have hEq (h : ℕ) : r h = s (h+1) :=
    tendsto_nhds_unique ((hr h).comp hφ.tendsto_atTop) (hs (h+1))
  simpa only [← hEq] using huwm.reverse_corr hp hs

/-- Theorem 2.4.17, in the closed-rectangle convention of this certificate. -/
theorem thesis_four_characterizations_weakMixing {d : ℕ} (hd : 0 < d) (x : ℕ → Cube d) :
    (WeaklyMixingDistribution (cubeLebesgue d) x ↔ ThesisCrossDiscrepancy x) ∧
    (WeaklyMixingDistribution (cubeLebesgue d) x ↔ ThesisSelfDiscrepancy x) ∧
    (WeaklyMixingDistribution (cubeLebesgue d) x ↔ ThesisDifferenceDiscrepancy x) :=
  ⟨⟨thesisCrossDiscrepancy_of_weakMixing, fun h =>
      weakMixing_of_thesisSelfDiscrepancy (thesisSelfDiscrepancy_of_cross hd h)⟩,
    ⟨fun h => thesisSelfDiscrepancy_of_cross hd (thesisCrossDiscrepancy_of_weakMixing h),
      weakMixing_of_thesisSelfDiscrepancy⟩,
    ⟨thesisDifferenceDiscrepancy_of_weakMixing, weakMixing_of_thesisDifferenceDiscrepancy⟩⟩

/-- Uniform over the starting point, the discrepancy of any irrational circle
rotation tends to zero. This qualitative estimate needs no algebraicity. -/
theorem eventually_uniform_rotation_discrepancy (α : ℝ) (hα : Irrational α)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ β : UnitAddCircle,
      rectangleDiscrepancy (fun n (_ : Fin 1) =>
        unitRepresentative (β + n • (α : UnitAddCircle))) N < ε := by
  let t : UnitAddCircle := (α : UnitAddCircle)
  let u (β : UnitAddCircle) (n : ℕ) (_ : Fin 1) := unitRepresentative (β+n • t)
  obtain ⟨S, hS, hbound⟩ := finite_character_discrepancy_bound (d := 1) (ε/2) (by positivity)
  let c (m : Fin 1 → ℤ) := 2 / ‖fourier (m 0) t - 1‖
  have hf (m : Fin 1 → ℤ) (hm : m ≠ 0) (N : ℕ) (β : UnitAddCircle) :
      ‖cesaro (fun n => torusCharacter m (cubeToTorus (u β n))) N‖ ≤ c m / (N : ℝ) := by
    have hnon : m 0 ≠ 0 := by
      intro h
      exact hm (funext fun i => by change m i = 0; rw [Fin.eq_zero i]; exact h)
    let ω : ℂ := fourier (m 0) t
    have hω1 : ‖ω‖ = 1 := by simp [ω, fourier_apply]
    have hω : ω ≠ 1 := by
      intro h
      have ht' : (m 0) • t = 0 := by
        apply AddCircle.injective_toCircle one_ne_zero
        apply Subtype.ext
        simpa [ω, fourier_apply] using h
      rw [show t = (α : UnitAddCircle) from rfl, ← AddCircle.coe_zsmul,
        AddCircle.coe_eq_zero_iff] at ht'
      obtain ⟨j, hj⟩ := ht'
      exact (irrational_iff_ne_rational _).1 hα j (m 0) hnon
        ((eq_div_iff (by exact_mod_cast hnon)).2 (by simpa [zsmul_eq_mul, mul_comm] using hj.symm))
    have hz (n : ℕ) : fourier (m 0) (n • t) = ω ^ n := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [succ_nsmul, pow_succ, ← ih]
        simp only [ω, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    have hprod (n : ℕ) : torusCharacter m (cubeToTorus (u β n)) =
        fourier (m 0) β * ω ^ n := by
      simp only [torusCharacter_apply, Fin.prod_univ_one, cubeToTorus, u, unitRepresentative_coe]
      rw [← hz]
      simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    simp_rw [hprod, cesaro_mul_const]
    rw [norm_mul]
    have hnorm : ‖fourier (T:=1) (m 0) β‖ = 1 := by simp [fourier_apply]
    rw [hnorm, one_mul, cesaro, geom_sum_eq hω, norm_div, norm_div, Complex.norm_natCast]
    have hωp : ‖ω ^ N - 1‖ ≤ 2 := by
      simpa only [norm_pow, hω1, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (ω ^ N) 1
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hωp (norm_nonneg _)) (by positivity)
  let C : ℝ := ∑ p ∈ S, c p.1 / p.2
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat C).eventually
    (gt_mem_nhds (show 0 < ε/2 by positivity)), eventually_gt_atTop 0] with N hC hN
  intro β
  change rectangleDiscrepancy (u β) N < ε
  have hb := hbound (u β) N hN
  have hc : (∑ p ∈ S, ‖cesaro (fun n => torusCharacter p.1 (cubeToTorus (u β n))) N‖ / p.2) ≤
      C / (N : ℝ) := by
    unfold C
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    rw [div_right_comm (c p.1) p.2 (N : ℝ)]
    exact div_le_div_of_nonneg_right (hf p.1 (hS _ hp).1 N β) (hS _ hp).2.le
  linarith

end
end VdC

end

end VdC_ThesisWeakMixing_Module

/- Source: VdC/DuplicationDiscrepancy.lean -/
section VdC_DuplicationDiscrepancy_Module

/-! # Duplication Discrepancy -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology

namespace VdC

noncomputable section

def duplicationRetained (request : ℕ → ℕ) (h : ℕ) : Set ℕ :=
  {n | ¬ duplicationCoincidence request h n}

theorem duplicationRetained_count (request : ℕ → ℕ) (h N : ℕ) :
    N ≤ 2 * initialCount (duplicationRetained request h) N + h := by
  classical
  let A := duplicationRetained request h
  let G := (range N).filter (· ∈ A)
  let B := (range N).filter (· ∉ A)
  have hSum : G.card + B.card = N := by
    simpa only [G, B, card_range] using card_filter_add_card_filter_not (s := range N) (· ∈ A)
  have hnear : (B.filter fun n => n+h < N).card ≤ G.card := by
    apply card_le_card_of_injOn (fun n => n+h)
    · intro n hn
      obtain ⟨hnB, hnN⟩ := mem_filter.mp hn
      have hc : duplicationCoincidence request h n := by
        simpa [B, A, duplicationRetained] using (mem_filter.mp hnB).2
      exact mem_filter.2 ⟨mem_range.2 hnN, (duplicationCoincidence_pair hc).2⟩
    · intro n _ m _ he
      change n+h = m+h at he
      omega
  have hfar : (B.filter fun n => ¬ n+h < N).card ≤ h := by
    rw [← card_range h]
    apply card_le_card_of_injOn (fun n => N-(n+1))
    · intro n hn
      obtain ⟨hnB, hnN⟩ := mem_filter.mp hn
      have hnlt := mem_range.mp (mem_filter.mp hnB).1
      simp only [card_range] at hnN
      apply mem_range.2
      change N-(n+1) < h
      omega
    · intro n hn m hm he
      have hnlt := mem_range.mp (mem_filter.mp (mem_filter.mp hn).1).1
      have hmlt := mem_range.mp (mem_filter.mp (mem_filter.mp hm).1).1
      change N-(n+1) = N-(m+1) at he
      omega
  have hcard := card_filter_add_card_filter_not (s := B) (fun n => n+h < N)
  change N ≤ 2*G.card+h
  omega

theorem duplicationRetained_positiveDensity (request : ℕ → ℕ) (h : ℕ) :
    HasPositiveLowerDensity (duplicationRetained request h) := by
  refine ⟨1/4, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2*h)] with N hN
  have hc : (N : ℝ) ≤ 2 * (initialCount (duplicationRetained request h) N : ℝ) + h := by
    exact_mod_cast duplicationRetained_count request h N
  have he : (2 : ℝ) * h ≤ N := by exact_mod_cast hN
  linarith

def duplicationDifferenceCube (request : ℕ → ℕ) (α : ℝ) (h n : ℕ) : Cube 1 :=
  fun i => unitRepresentative ((duplicationSequence request α (n+h) - duplicationSequence request α n) i)

theorem duplication_differenceCharacter (request : ℕ → ℕ) (α : ℝ) (h n : ℕ) (m : Fin 1 → ℤ) :
    torusCharacter m (cubeToTorus (duplicationDifferenceCube request α h n)) =
      phase ((m 0 : ℝ) * α *
        ((duplicationIndex request (n+h) : ℝ)^2 - (duplicationIndex request n : ℝ)^2)) := by
  have he : cubeToTorus (duplicationDifferenceCube request α h n) =
      duplicationSequence request α (n+h) - duplicationSequence request α n := by
    funext i
    exact unitRepresentative_coe _
  rw [he]
  exact torusCharacter_duplication_difference request α m h n

theorem duplication_differenceCharacter_times_retained (request : ℕ → ℕ) (α : ℝ) (h n : ℕ)
    (m : Fin 1 → ℤ) :
    torusCharacter m (cubeToTorus (duplicationDifferenceCube request α h n)) *
        selectionWeight (duplicationRetained request h) n = duplicationMaskedPhase request α (m 0) h n := by
  rw [duplication_differenceCharacter]
  by_cases hc : duplicationCoincidence request h n
  · have hm : n ∉ duplicationRetained request h := fun hn => hn hc
    simp [selectionWeight, hm, duplicationMaskedPhase, hc]
  · have hm : n ∈ duplicationRetained request h := hc
    simp [selectionWeight, hm, duplicationMaskedPhase, hc]

theorem equidistributed_duplication_retained {α : ℝ} (hα : Irrational α) {h : ℕ} (hh : 0 < h)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (hA : Set.range σ = duplicationRetained (duplicationGrowth α) h) :
    Equidistributed (cubeLebesgue 1) (duplicationDifferenceCube (duplicationGrowth α) α h ∘ σ) := by
  apply equidistributed_of_cubeToTorus
  apply (equidistributed_torus_iff _).2
  intro m hm
  have hm0 : m 0 ≠ 0 := by
    intro he
    apply hm
    funext i
    fin_cases i
    exact he
  let f n := torusCharacter m (cubeToTorus (duplicationDifferenceCube (duplicationGrowth α) α h n))
  change Tendsto (cesaro fun k => f (σ k)) atTop (𝓝 0)
  apply tendsto_cesaro_selected_zero f hσ
  · rw [hA]
    exact duplicationRetained_positiveDensity ..
  · rw [hA]
    have he : (fun n => f n * selectionWeight (duplicationRetained (duplicationGrowth α) h) n) =
        duplicationMaskedPhase (duplicationGrowth α) α (m 0) h := by
      funext n
      exact duplication_differenceCharacter_times_retained (duplicationGrowth α) α h n m
    rw [he]
    exact tendsto_cesaro_duplicationMaskedPhase_zero hα hm0 hh

theorem duplication_upper_discrepancy_eq_half {α : ℝ} (hα : Irrational α) (j : ℕ) :
    upperDifferenceDiscrepancy (duplicationSequence (duplicationGrowth α) α) j = (1 : ℝ)/2 := by
  apply le_antisymm _ (duplication_upper_discrepancy_ge_half (duplicationGrowth α) α j)
  let h := j+1
  let A := duplicationRetained (duplicationGrowth α) h
  have hden : HasPositiveLowerDensity A := duplicationRetained_positiveDensity ..
  obtain ⟨σ, hσ, hA⟩ := exists_enumeration_of_positiveLowerDensity hden
  change limsup (rectangleDiscrepancy (duplicationDifferenceCube (duplicationGrowth α) α h)) atTop ≤ (1:ℝ)/2
  refine limsup_rectangleDiscrepancy_le_erased _ hσ
    (tendsto_rectangleDiscrepancy_of_equidistributed (equidistributed_duplication_retained hα (Nat.succ_pos _) hσ hA)) ?_
  intro ε hε
  have ht := (tendsto_const_div_atTop_nhds_zero_nat ((h : ℝ)/2)).eventually (gt_mem_nhds hε)
  filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with N hN' hN
  rw [hA]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let K := (initialCount A N : ℝ)
  have hc : (N : ℝ) ≤ 2*K+h := by
    dsimp [K, A]
    exact_mod_cast duplicationRetained_count (duplicationGrowth α) h N
  have hq := div_le_div_of_nonneg_right hc hNr.le
  rw [div_self hNr.ne', add_div, mul_div_assoc] at hq
  change (h : ℝ)/2/N < ε at hN'
  have he : (h : ℝ)/N = 2*((h : ℝ)/2/N) := by ring
  rw [he] at hq
  change 1-K/(N : ℝ) ≤ (1:ℝ)/2+ε
  linarith only [hq, hN']

end
end VdC

end

end VdC_DuplicationDiscrepancy_Module

/- Source: VdC/DuplicationExample.lean -/
section VdC_DuplicationExample_Module

/-! The example motivating the use of permissible pairs. -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

/-- The doubled-square construction works for every irrational coefficient. The lag
in the discrepancy definition is `h + 1`. -/
theorem duplicationCube_example {α : ℝ} (hα : Irrational α) :
    SpectrallyLebesgueDistribution (cubeLebesgue 1) (duplicationCube α) ∧
      ∀ h : ℕ, upperDifferenceDiscrepancy (cubeToTorus ∘ duplicationCube α) h = (1 : ℝ)/2 := by
  refine ⟨duplicationCube_spectrallyLebesgue hα, ?_⟩
  intro h
  rw [cubeToTorus_duplicationCube]
  exact duplication_upper_discrepancy_eq_half hα h

/-- Orthogonality would force every positive-lag difference to have zero upper
discrepancy, whereas the doubled-square example has upper discrepancy one half. -/
theorem duplicationCube_not_orthogonal {α : ℝ} (hα : Irrational α) :
    ¬ OrthogonalDistribution (cubeLebesgue 1) (duplicationCube α) := by
  intro ho
  let x := duplicationCube α
  let y : ℕ → Cube 1 := fun n i ↦ unitRepresentative
    (cubeToTorus (x (n+1)) i - cubeToTorus (x n) i)
  have hy : Equidistributed (cubeLebesgue 1) y := by
    apply equidistributed_of_cubeToTorus
    apply (equidistributed_torus_iff _).2
    intro m hm
    let f : C(Cube 1, ℂ) := (torusCharacter m).comp ⟨cubeToTorus, continuous_cubeToTorus 1⟩
    have hf : testMean (cubeLebesgue 1) f = 0 := by
      change (∫ x, torusCharacter m (cubeToTorus x) ∂cubeLebesgue 1) = 0
      rw [← integral_map_of_stronglyMeasurable (continuous_cubeToTorus 1).measurable
        (torusCharacter m).continuous.stronglyMeasurable, (cubeToTorus_measurePreserving 1).map_eq]
      exact (testMean_torusCharacter m).trans (ite_eq_right hm)
    have ht := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test f x)).1 (ho f hf) 1 Nat.one_pos
    apply ht.congr
    intro N
    unfold corr
    congr 1
    funext n
    have he : cubeToTorus (y n) = cubeToTorus (x (n+1)) - cubeToTorus (x n) :=
      funext fun i ↦ unitRepresentative_coe _
    rw [he, torusCharacter_point_sub]
    rfl
  have hzero := (tendsto_rectangleDiscrepancy_of_equidistributed hy).limsup_eq
  change upperDifferenceDiscrepancy (cubeToTorus ∘ x) 0 = 0 at hzero
  have hhalf := (duplicationCube_example hα).2 0
  change upperDifferenceDiscrepancy (cubeToTorus ∘ x) 0 = (1 : ℝ)/2 at hhalf
  linarith only [hzero, hhalf]

/-- There is a spectrally Lebesgue sequence in the unit interval with upper
difference discrepancy exactly one half at every positive lag. -/
theorem exampleNecessitatingPermissibleTriples :
    ∃ x : ℕ → Cube 1, SpectrallyLebesgueDistribution (cubeLebesgue 1) x ∧
      ∀ h : ℕ, upperDifferenceDiscrepancy (cubeToTorus ∘ x) h = (1 : ℝ)/2 :=
  ⟨duplicationCube (Real.sqrt 2), duplicationCube_example irrational_sqrt_two⟩

end VdC

end

end VdC_DuplicationExample_Module

/- Source: VdC/ErgodicDiscrete.lean -/
section VdC_ErgodicDiscrete_Module

/-! # Ergodic Discrete -/

@[expose] public section

open Filter Finset Function MeasureTheory Set
open scoped Topology BigOperators InnerProductSpace ENNReal

namespace VdC

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- Koopman eigenvectors in the actual Mathlib L² space. -/
def koopmanLpEigenvectors (hT : MeasurePreserving T μ μ) : Set (Lp ℂ 2 μ) :=
  {v | ∃ c : ℂ, Lp.compMeasurePreserving T hT v = c • v}

/-- The usual discrete-spectrum condition that the Koopman eigenvectors span a
dense subspace of L². -/
def KoopmanDiscreteSpectrumLp (hT : MeasurePreserving T μ μ) : Prop :=
  Dense (↑(Submodule.span ℂ (koopmanLpEigenvectors hT)) : Set (Lp ℂ 2 μ))

private theorem eigenvector_unit_modulus (hT : MeasurePreserving T μ μ) {v : Lp ℂ 2 μ}
    (hv : v ∈ koopmanLpEigenvectors hT) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ Lp.compMeasurePreserving T hT v = c • v := by
  by_cases h : v = 0
  · subst v
    exact ⟨1, norm_one, by simp⟩
  obtain ⟨c, hc⟩ := hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr h
  have he : ‖v‖ = ‖c‖ * ‖v‖ :=
    (Lp.norm_compMeasurePreserving v hT).symm.trans ((congrArg norm hc).trans (norm_smul _ _))
  have hh : ‖c‖ * ‖v‖ = 1 * ‖v‖ := he.symm.trans (one_mul _).symm
  exact ⟨c, mul_right_cancel₀ hn.ne' hh, hc⟩

private theorem exists_bounded_eigen_representative (hT : Ergodic T μ) {v : Lp ℂ 2 μ}
    (hv : v ∈ koopmanLpEigenvectors hT.toMeasurePreserving) :
    ∃ e : BoundedKoopmanEigenfunction μ T, (e.value : X → ℂ) =ᵐ[μ] v := by
  classical
  obtain ⟨c, hc, hcv⟩ := eigenvector_unit_modulus hT.toMeasurePreserving hv
  let u : X → ℂ := (Lp.aestronglyMeasurable v).mk v
  have hu : Measurable u := (Lp.aestronglyMeasurable v).stronglyMeasurable_mk.measurable
  have hvu : (v : X → ℂ) =ᵐ[μ] u := (Lp.aestronglyMeasurable v).ae_eq_mk
  have hvT := Lp.coeFn_compMeasurePreserving v hT.toMeasurePreserving
  rw [hcv] at hvT
  have hEq : ∀ᵐ x ∂μ, u (T x) = c*u x := by
    filter_upwards [hvT, Lp.coeFn_smul c v, hvu,
      hT.toMeasurePreserving.quasiMeasurePreserving.ae_eq_comp hvu] with x hcomp hsmul hx hx'
    change v (T x) = u (T x) at hx'
    change (c • v) x = v (T x) at hcomp
    have hh : (c • v) x = c * v x := hsmul
    rw [← hx', ← hcomp, hh, hx]
  have hInv : (fun x => ‖u x‖) ∘ T =ᵐ[μ] (fun x => ‖u x‖) := by
    filter_upwards [hEq] with x hx
    change ‖u (T x)‖ = ‖u x‖
    rw [hx, norm_mul, hc, one_mul]
  obtain ⟨C, hC⟩ := hT.ae_eq_const_of_ae_eq_comp₀ hu.norm.nullMeasurable hInv
  let B : Set X := {x | ‖u x‖ = C}
  have hB : MeasurableSet B := measurableSet_eq_fun hu.norm measurable_const
  let g := B.indicator u
  have hgu : (g : X → ℂ) =ᵐ[μ] u := by
    filter_upwards [hC] with x hx
    exact Set.indicator_of_mem hx _
  let D := max 0 C
  have hg : BoundedObservable g := by
    refine ⟨hu.indicator hB, D, le_max_left _ _, fun x => ?_⟩
    change ‖B.indicator u x‖ ≤ D
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, show ‖u x‖ = C from hx]
      exact le_max_right _ _
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact le_max_left _ _
  have he : ∀ᵐ x ∂μ, g (T x) = c*g x := by
    filter_upwards [hEq, hgu, hT.toMeasurePreserving.quasiMeasurePreserving.ae_eq_comp hgu] with x h hx hx'
    change g (T x) = u (T x) at hx'
    rw [hx', hx, h]
  exact ⟨⟨g, hg, c, hc, he⟩, hgu.trans hvu.symm⟩

private theorem eigen_fin_sum_of_mem_span (hT : MeasurePreserving T μ μ) {v : Lp ℂ 2 μ}
    (hv : v ∈ Submodule.span ℂ (koopmanLpEigenvectors hT)) :
    ∃ (k : ℕ) (e : Fin k → Lp ℂ 2 μ), (∀ i, e i ∈ koopmanLpEigenvectors hT) ∧
      (∑ i, e i) = v := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, fun _ => v, fun _ => hv, by simp⟩
  | zero => exact ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨n, e, he, hE⟩ := hv
    obtain ⟨m, f, hf, hF⟩ := hw
    refine ⟨n+m, Fin.addCases e f, ?_, ?_⟩
    · apply Fin.addCases
      · intro i
        simpa only [Fin.addCases_left] using he i
      · intro i
        simpa only [Fin.addCases_right] using hf i
    · rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, hE, hF]
  | smul c v _ hv =>
    obtain ⟨n, e, he, hE⟩ := hv
    refine ⟨n, fun i => c • e i, fun i => ?_, ?_⟩
    · obtain ⟨d, hd⟩ := he i
      refine ⟨d, ?_⟩
      have h := (Lp.compMeasurePreservingₗ (E := ℂ) (p := 2) ℂ T hT).map_smul c (e i)
      change Lp.compMeasurePreserving T hT (c • e i) = c • Lp.compMeasurePreserving T hT (e i) at h
      rw [h, hd, smul_comm]
    · rw [← Finset.smul_sum, hE]

private theorem norm_sq_L2_eq_integral (v : Lp ℂ 2 μ) : ‖v‖^2 = ∫ x, ‖v x‖^2 ∂μ := by
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (‖v‖^2) = ⟪v, v⟫_ℂ := by
      rw [Complex.ofReal_pow]
      exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v).symm
    _ = ∫ x, ⟪v x, v x⟫_ℂ ∂μ := L2.inner_def v v
    _ = _ := by
      have h (x : X) : ⟪v x, v x⟫_ℂ = Complex.ofReal (‖v x‖^2) := by
        rw [Complex.ofReal_pow]
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (v x)
      simp_rw [h]
      exact integral_complex_ofReal

/-- From the standard dense L² eigenvector-span condition, obtain the bounded
measurable eigenfunction approximation hypothesis used for the orbit examples. -/
theorem koopmanDiscreteSpectrum_of_Lp [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (hd : KoopmanDiscreteSpectrumLp hT.toMeasurePreserving) : KoopmanDiscreteSpectrum μ T := by
  classical
  intro f hf ε hε
  obtain ⟨C, hC, hb⟩ := hf.2
  have hfp : MemLp f 2 μ := MemLp.of_bound hf.1.aestronglyMeasurable C (Eventually.of_forall hb)
  let F := hfp.toLp f
  obtain ⟨v, hv, hvDist⟩ := Metric.mem_closure_iff.mp (hd F) (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨k, u, hu, huSum⟩ := eigen_fin_sum_of_mem_span hT.toMeasurePreserving hv
  choose e he using fun i => exists_bounded_eigen_representative hT (hu i)
  let U : Lp ℂ 2 μ := ∑ i, u i
  have hcoe : (U : X → ℂ) =ᵐ[μ] fun x => ∑ i, (e i).value x := by
    refine (Lp.coeFn_fun_finsetSum univ u).trans ?_
    filter_upwards [ae_all_iff.mpr he] with x hx
    exact Finset.sum_congr rfl (fun i _ => (hx i).symm)
  have hEq : ∀ᵐ x ∂μ, (F-U) x = f x - ∑ i, (e i).value x := by
    filter_upwards [Lp.coeFn_sub F U, hfp.coeFn_toLp, hcoe] with x hsub hf' hu'
    rw [hsub]
    change F x = f x at hf'
    change F x - U x = _
    rw [hf', hu']
  refine ⟨k, e, ?_⟩
  have hcalc : (∫ x, ‖f x - ∑ i, (e i).value x‖^2 ∂μ) = ‖F - U‖^2 :=
    (integral_congr_ae (hEq.mono fun x hx => by rw [hx])).symm.trans (norm_sq_L2_eq_integral _).symm
  rw [hcalc, show U = v from huSum, ← Real.sq_sqrt hε.le]
  rw [dist_eq_norm] at hvDist
  exact pow_lt_pow_left₀ hvDist (norm_nonneg _) (by decide)

end
end VdC

end

end VdC_ErgodicDiscrete_Module

/- Source: VdC/ErgodicWeakMixing.lean -/
section VdC_ErgodicWeakMixing_Module

/-! # Ergodic Weak Mixing -/

@[expose] public section

open Filter Finset Function MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

private theorem realCesaro_sq_bound {u : ℕ → ℝ} (N : ℕ) :
    (realCesaro u N)^2 ≤ realCesaro (fun n => (u n)^2) N := by
  by_cases hN : N = 0
  · simp [realCesaro, hN]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have h : (∑ n ∈ range N, u n)^2 ≤ (N : ℝ) * ∑ n ∈ range N, (u n)^2 := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_mul_sq_le_sq_mul_sq (range N) (fun _n => (1 : ℝ)) (fun n => u n))
  rw [realCesaro, realCesaro, div_pow]
  refine (div_le_div_of_nonneg_right h (sq_nonneg (N:ℝ))).trans_eq ?_
  field_simp [hNr]

private theorem realCesaro_tendsto_zero_of_sq {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (h : Tendsto (realCesaro (fun n => (u n)^2)) atTop (𝓝 0)) :
    Tendsto (realCesaro u) atTop (𝓝 0) := by
  have ht := squeeze_zero (fun N => sq_nonneg (realCesaro u N)) (realCesaro_sq_bound (u := u)) h
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (realCesaro_nonneg hu _)] using hs

section

variable {X : Type*} [MeasurableSpace X]

/-- The usual weak-mixing hypothesis that the product system is ergodic implies
the autocorrelation Cesàro criterion used for the orbit examples. -/
theorem koopmanWeakMixing_of_prod_ergodic {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hprod : Ergodic (fun p : X × X => (T p.1, T p.2)) (μ.prod μ)) :
    KoopmanWeakMixing μ T := by
  intro f hf hmean
  obtain ⟨C, hC, hb⟩ := hf.2
  let P (p : X × X) := (T p.1, T p.2)
  let g (p : X × X) := f p.1 * star (f p.2)
  have hm : Measurable g := (hf.1.comp measurable_fst).mul
    (Complex.continuous_conj.measurable.comp (hf.1.comp measurable_snd))
  have hg (p : X × X) : ‖g p‖ ≤ C*C := by
    change ‖f p.1 * star (f p.2)‖ ≤ _
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb _) (hb _) (norm_nonneg _) hC
  have hgm : (∫ p, g p ∂(μ.prod μ)) = 0 := by
    change (∫ p : X × X, f p.1 * star (f p.2) ∂(μ.prod μ)) = 0
    rw [integral_prod_mul (μ := μ) (ν := μ) f (fun x => star (f x)), hmean, zero_mul]
  have hp : ∀ᵐ p ∂(μ.prod μ), Tendsto (cesaro (fun n => g (P^[n] p))) atTop (𝓝 0) := by
    have he := ae_tendsto_orbitCesaro hprod hm (mul_nonneg hC hC) hg
    rwa [hgm] at he
  have hIt (n : ℕ) (p : X × X) : P^[n] p = (T^[n] p.1, T^[n] p.2) := by
    induction n with
    | zero => cases p; rfl
    | succ n IH => simp only [iterate_succ_apply', IH, P]
  let F (n : ℕ) (x : X) := f (T^[n] x) * star (f x)
  let G (n : ℕ) (p : X × X) := g (P^[n] p) * star (g p)
  have hgF (n : ℕ) (p : X × X) : G n p = F n p.1 * star (F n p.2) := by
    dsimp only [F, G, g]
    rw [hIt]
    simp only [star_mul, star_star]
    ring
  have hiG (n : ℕ) : Integrable (G n) (μ.prod μ) := by
    apply Integrable.of_bound (((hm.comp (hprod.measurable.iterate n)).mul
      (Complex.continuous_conj.measurable.comp hm)).aestronglyMeasurable) ((C*C)^2)
    exact Eventually.of_forall fun p => by
      change ‖g (P^[n] p) * star (g p)‖ ≤ _
      rw [norm_mul, norm_star, pow_two]
      exact mul_le_mul (hg _) (hg _) (norm_nonneg _) (mul_nonneg hC hC)
  let r := koopmanCorrelation μ T f
  have hiCorr (n : ℕ) : (∫ p, G n p ∂(μ.prod μ)) = (‖r n‖^2 : ℝ) := by
    have hc : (∫ x, star (F n x) ∂μ) = star (∫ x, F n x ∂μ) := integral_conj
    simp_rw [hgF]
    rw [integral_prod_mul (μ := μ) (ν := μ) (F n) (fun x => star (F n x)), hc]
    change r n * star (r n) = Complex.ofReal (‖r n‖^2)
    rw [Complex.ofReal_pow]
    exact Complex.mul_conj' (r n)
  let A (N : ℕ) (p : X × X) := cesaro (fun n => G n p) N
  have hA (N : ℕ) (p : X × X) : A N p = cesaro (fun n => g (P^[n] p)) N * star (g p) := by
    simp only [A, G, cesaro, ← Finset.sum_mul]
    ring
  have hiA (N : ℕ) : AEStronglyMeasurable (A N) (μ.prod μ) := by
    have hm' : Measurable (fun p => cesaro (fun n => g (P^[n] p)) N) := by
      apply Measurable.div_const
      exact Finset.measurable_sum _ (fun n _ => hm.comp (hprod.measurable.iterate n))
    rw [funext (hA N)]
    exact (hm'.mul (Complex.continuous_conj.measurable.comp hm)).aestronglyMeasurable
  have hAt : Tendsto (fun N => ∫ p, A N p ∂(μ.prod μ)) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (μ := μ.prod μ) (F := A) (f := fun _ => (0:ℂ))
      (fun _ => (C*C)^2) hiA (integrable_const _) ?_ ?_
    · simpa only [integral_zero] using ht
    · intro N
      exact ae_of_all _ fun p => by
        rw [hA, norm_mul, norm_star, pow_two]
        apply mul_le_mul (norm_cesaro_le _ (mul_nonneg hC hC) (fun n => hg _) N) (hg p)
        · exact norm_nonneg _
        · exact mul_nonneg hC hC
    · filter_upwards [hp] with p hp'
      simpa only [hA, zero_mul] using hp'.mul_const (star (g p))
  have hsum (N : ℕ) : (∫ p, A N p ∂(μ.prod μ)) = Complex.ofReal (realCesaro (fun n => ‖r n‖^2) N) := by
    simp only [A, cesaro, div_eq_mul_inv, integral_mul_const, integral_finsetSum _ (fun i _ => hiG i), hiCorr,
      realCesaro, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_inv, Complex.ofReal_sum]
  have hsq0 : Tendsto (realCesaro (fun h => ‖r h‖^2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hsum, Complex.ofReal_re, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hAt
  have hbound (h : ℕ) : |‖r h‖^2| ≤ (C*C)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    have hi : ∀ᵐ y ∂μ, ‖F h y‖ ≤ C*C := ae_of_all _ fun y => by
      simp only [F, norm_mul, norm_star]
      exact mul_le_mul (hb _) (hb _) (norm_nonneg _) hC
    change ‖∫ y, F h y ∂μ‖ ≤ C*C
    simpa only [MeasureTheory.probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hi
  have hshift := tendsto_realCesaro_shift_sub_zero (sq_nonneg _) hbound 1
  have hsq : Tendsto (realCesaro (fun h => ‖r (h+1)‖^2)) atTop (𝓝 0) := by
    simpa only [sub_add_cancel, add_zero] using hshift.add hsq0
  exact realCesaro_tendsto_zero_of_sq (fun _ => norm_nonneg _) hsq

end
end VdC

end

end VdC_ErgodicWeakMixing_Module

/- Source: VdC/ErgodicCubeExamples.lean -/
section VdC_ErgodicCubeExamples_Module

/-! # Ergodic Cube Examples -/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped Topology

namespace VdC

private theorem ae_imp_of_imp_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {P : Prop} {Q : X → Prop} (h : P → ∀ᵐ x ∂μ, Q x) : ∀ᵐ x ∂μ, P → Q x := by
  by_cases hP : P
  · exact (h hP).mono (fun _ hq _ => hq)
  · exact Eventually.of_forall fun _ hp => (hP hp).elim

/-- All six assertions of `LemmaConstructingSequences` on the same full-measure
set. The weak-mixing hypothesis is product ergodicity and the discrete-spectrum
hypothesis is the ordinary dense L² Koopman eigenvector span. -/
theorem ae_constructingSequences_cube {d : ℕ} {T : Cube d → Cube d} {A : Set (Cube d)}
    (hT : Ergodic T (cubeLebesgue d)) (hA : MeasurableSet A) (hpos : 0 < cubeLebesgue d A) :
    ∀ᵐ x ∂cubeLebesgue d,
      (Ergodic (fun p : Cube d × Cube d => (T p.1, T p.2)) ((cubeLebesgue d).prod (cubeLebesgue d)) →
        WeaklyMixingDistribution (cubeLebesgue d) (orbitSequence T x)) ∧
      (KoopmanLebesgueSpectrum (cubeLebesgue d) T →
        SpectrallyLebesgueDistribution (cubeLebesgue d) (orbitSequence T x)) ∧
      (KoopmanDiscreteSpectrumLp hT.toMeasurePreserving → CompactDistribution (orbitSequence T x)) ∧
      (KoopmanDiscreteSpectrumLp hT.toMeasurePreserving →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
          HasPositiveLowerDensity (Set.range σ) ∧ CompactSeq (selectionWeight (Set.range σ))) ∧
      (KoopmanSingularSpectrum (cubeLebesgue d) T → SpectrallySingularDistribution (orbitSequence T x)) ∧
      (KoopmanSingularSpectrum (cubeLebesgue d) T →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
          HasPositiveLowerDensity (Set.range σ) ∧ SpectrallySingular (selectionWeight (Set.range σ))) := by
  filter_upwards [ae_imp_of_imp_ae (fun h => ae_orbit_weaklyMixing hT (koopmanWeakMixing_of_prod_ergodic h)),
    ae_imp_of_imp_ae (ae_orbit_spectrallyLebesgue hT),
    ae_imp_of_imp_ae (fun h => ae_orbit_compact hT (koopmanDiscreteSpectrum_of_Lp hT h)),
    ae_imp_of_imp_ae (fun h => ae_visits_compact hT (koopmanDiscreteSpectrum_of_Lp hT h) hA hpos),
    ae_imp_of_imp_ae (ae_orbit_spectrallySingular hT),
    ae_imp_of_imp_ae (fun h => ae_visits_spectrallySingular hT h hA hpos)] with x h₁ h₂ h₃ h₄ h₅ h₆
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

end VdC

end

end VdC_ErgodicCubeExamples_Module

/- Source: VdC/HalfFrequency.lean -/
section VdC_HalfFrequency_Module

/-! # Half Frequency -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def halfTorusMap {d : ℕ} (x : Cube d) : Torus d :=
  fun i => (((x i : ℝ) / (2 : ℝ) : ℝ) : UnitAddCircle)

theorem halfTorusMap_continuous (d : ℕ) : Continuous (halfTorusMap (d := d)) := by
  refine continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp ?_
  exact (continuous_subtype_val.comp (continuous_apply i)).div_const 2

private theorem halfTorusMap_injective (d : ℕ) : Function.Injective (halfTorusMap (d := d)) := by
  intro x y h
  funext i
  have hb (u : Cube d) : (u i : ℝ) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    have hu := (u i).property
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h' := congrArg (AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (congrFun h i)
  change AddCircle.equivIco (1 : ℝ) (0 : ℝ) (((x i : ℝ) / 2 : ℝ) : UnitAddCircle) =
    AddCircle.equivIco (1 : ℝ) (0 : ℝ) (((y i : ℝ) / 2 : ℝ) : UnitAddCircle) at h'
  rw [AddCircle.equivIco_coe_eq (hb x), AddCircle.equivIco_coe_eq (hb y)] at h'
  apply Subtype.ext
  have h'' := congrArg Subtype.val h'
  dsimp at h''
  linarith

/-- The manuscript's half-frequency character exp(π i m·x) on the closed cube. -/
def halfFrequency {d : ℕ} (m : Fin d → ℤ) : C(Cube d, ℂ) :=
  (torusCharacter m).comp ⟨halfTorusMap, halfTorusMap_continuous d⟩

private theorem halfFrequency_mul {d : ℕ} (m k : Fin d → ℤ) :
    halfFrequency (m + k) = halfFrequency m * halfFrequency k := by
  ext x
  change torusCharacter (m + k) (halfTorusMap x) = torusCharacter m (halfTorusMap x) * torusCharacter k (halfTorusMap x)
  rw [torusCharacter_mul]
  rfl

private theorem halfFrequency_neg {d : ℕ} (m : Fin d → ℤ) :
    halfFrequency (-m) = star (halfFrequency m) := by
  ext x
  change torusCharacter (-m) (halfTorusMap x) = star (torusCharacter m (halfTorusMap x))
  rw [torusCharacter_neg]
  rfl

private theorem halfFrequency_zero (d : ℕ) : halfFrequency (0 : Fin d → ℤ) = 1 := by
  ext x
  simp [halfFrequency]

private def halfFrequencyAlgebra (d : ℕ) : StarSubalgebra ℂ C(Cube d, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (halfFrequency (d := d)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (halfFrequency (d := d))) ≤ star (Algebra.adjoin ℂ _)
    apply Algebra.adjoin_le
    rintro _ ⟨m, rfl⟩
    exact Algebra.subset_adjoin ⟨-m, halfFrequency_neg m⟩

theorem halfFrequencies_dense (d : ℕ) :
    (Submodule.span ℂ (Set.range (halfFrequency (d := d)))).topologicalClosure = ⊤ := by
  have hsep : (halfFrequencyAlgebra d).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, halfTorusMap x i ≠ halfTorusMap y i := by
      contrapose! hxy
      exact halfTorusMap_injective d (funext hxy)
    refine ⟨_, ⟨halfFrequency (Pi.single i 1), Algebra.subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
    change torusCharacter (Pi.single i 1) (halfTorusMap x) ≠ torusCharacter (Pi.single i 1) (halfTorusMap y)
    rw [torusCharacter_single, torusCharacter_single, fourier_one, fourier_one]
    exact fun h => hi (AddCircle.injective_toCircle one_ne_zero (Subtype.coe_injective h))
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have had : (halfFrequencyAlgebra d).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (halfFrequency (d := d))) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans ?_ Submodule.subset_span
    intro u hu
    refine Submonoid.closure_induction (fun _ => id) ⟨0, halfFrequency_zero d⟩ ?_ hu
    rintro _ _ - - ⟨m, rfl⟩ ⟨k, rfl⟩
    exact ⟨m + k, halfFrequency_mul m k⟩
  rw [← had]
  exact congrArg (fun A : StarSubalgebra ℂ C(Cube d, ℂ) => A.toSubalgebra.toSubmodule) hd

theorem cube_property_of_halfFrequencies {d : ℕ} (x : ℕ → Cube d)
    (P : (ℕ → ℂ) → Prop) (hzero : P (fun _ => 0))
    (hadd : ∀ u v, P u → P v → P (fun n => u n + v n))
    (hsmul : ∀ u, ∀ c : ℂ, P u → P (fun n => c * u n))
    (hclosed : ∀ u, BoundedSeq u → (∀ ε : ℝ, 0 < ε → ∃ v, P v ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖u n - v n‖ ^ 2) N ≤ ε) → P u)
    (hchar : ∀ m : Fin d → ℤ, P (fun n => halfFrequency m (x n))) :
    ∀ f : C(Cube d, ℂ), P (fun n => f (x n)) := by
  intro f
  apply hclosed _ (bounded_test f x)
  intro ε hε
  let S := Submodule.span ℂ (Set.range (halfFrequency (d := d)))
  have hspan : ∀ g ∈ S, P (fun n => g (x n)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨m, rfl⟩ := hg
      exact hchar m
    | zero => exact hzero
    | add g k _ _ hg hk => exact hadd _ _ hg hk
    | smul c g _ hg => exact hsmul _ c hg
  have hf : f ∈ closure (S : Set C(Cube d, ℂ)) := by
    change f ∈ S.topologicalClosure
    rw [halfFrequencies_dense d]
    trivial
  obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp hf (Real.sqrt ε) (by positivity)
  rw [dist_eq_norm] at hd
  refine ⟨fun n => g (x n), hspan g hg, Eventually.of_forall fun N => ?_⟩
  have hsq (n : ℕ) : ‖f (x n) - g (x n)‖ ^ 2 ≤ ε := by
    rw [← Real.sq_sqrt hε.le]
    gcongr
    exact (ContinuousMap.norm_coe_le_norm (f - g) (x n)).trans hd.le
  by_cases hN : 0 < N
  · exact (realCesaro_mono hsq N).trans_eq (realCesaro_const_pos ε hN)
  · simp [realCesaro, Nat.eq_zero_of_not_pos hN, hε.le]

theorem cube_sSingular_iff_halfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    SpectrallySingularDistribution x ↔
      ∀ m : Fin d → ℤ, SpectrallySingular (fun n => halfFrequency m (x n)) := by
  constructor
  · exact fun h m => h (halfFrequency m)
  · exact cube_property_of_halfFrequencies x SpectrallySingular spectrallySingular_zero
      (fun _ _ hu hv => hu.add hv) (fun _ c hu => hu.const_mul c)
      (fun _ hu h => spectrallySingular_of_meanSquare_approximation hu h)

theorem cube_compact_iff_halfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    CompactDistribution x ↔ ∀ m : Fin d → ℤ, CompactSeq (fun n => halfFrequency m (x n)) := by
  constructor
  · exact fun h m => h (halfFrequency m)
  · exact cube_property_of_halfFrequencies x CompactSeq (compactAlong_const 0 strictMono_id)
      (fun _ _ hu hv => CompactAlong.add hu hv) (fun _ c hu => CompactAlong.const_mul hu c)
      (fun _ hu h => compactAlong_of_meanSquare_approximation hu strictMono_id h)

def centeredHalfFrequency {d : ℕ} (m : Fin d → ℤ) : C(Cube d, ℂ) :=
  center (cubeLebesgue d) (halfFrequency m)

theorem cube_sSingular_iff_centeredHalfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    SpectrallySingularDistribution x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      SpectrallySingular (fun n => centeredHalfFrequency m (x n)) := by
  constructor
  · exact fun hx m _ => hx (centeredHalfFrequency m)
  · intro h
    apply (cube_sSingular_iff_halfFrequencies x).2
    intro m
    by_cases hm : m = 0
    · subst m
      simpa only [halfFrequency_zero, ContinuousMap.one_apply] using spectrallySingular_one
    · simpa [centeredHalfFrequency, center] using
        (h m hm).add (spectrallySingular_const (testMean (cubeLebesgue d) (halfFrequency m)))

theorem cube_compact_iff_centeredHalfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    CompactDistribution x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      CompactSeq (fun n => centeredHalfFrequency m (x n)) := by
  constructor
  · exact fun hx m _ => hx (centeredHalfFrequency m)
  · intro h
    apply (cube_compact_iff_halfFrequencies x).2
    intro m
    by_cases hm : m = 0
    · subst m
      simpa only [halfFrequency_zero, ContinuousMap.one_apply, CompactSeq] using compactAlong_const 1 strictMono_id
    · simpa [centeredHalfFrequency, center, CompactSeq] using
        CompactAlong.add (h m hm) (compactAlong_const (testMean (cubeLebesgue d) (halfFrequency m)) strictMono_id)

end
end VdC

end

end VdC_HalfFrequency_Module

/- Source: VdC/OrbitRepresentation.lean -/
section VdC_OrbitRepresentation_Module

/-! The topological shift representation of a bounded sequence. -/

@[expose] public section

open Function Set TopologicalSpace

namespace VdC

/-- A bounded sequence is a continuous observation of a dense forward orbit in a
compact metrizable space, as in the first assertion of `RepresentationLemma`. -/
theorem bounded_sequence_orbit_representation {u : ℕ → ℂ} (hu : BoundedSeq u) :
    ∃ (X : Type) (_top : TopologicalSpace X),
      CompactSpace X ∧ MetrizableSpace X ∧
      ∃ (S : C(X, X)) (F : C(X, ℂ)) (x : X),
        DenseRange (fun n : ℕ ↦ S^[n] x) ∧ ∀ n : ℕ, F (S^[n] x) = u n := by
  obtain ⟨C, _, hC⟩ := hu
  let B : Type := Metric.closedBall (0 : ℂ) C
  have hB : IsCompact (Metric.closedBall (0 : ℂ) C) := isCompact_closedBall _ _
  have : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let Ω : Type := ℕ → B
  let shift : Ω → Ω := fun z n ↦ z (n + 1)
  have hshift : Continuous shift := continuous_pi fun n ↦ continuous_apply (n + 1)
  let x : Ω := fun n ↦ ⟨u n, by simpa [Metric.mem_closedBall, dist_zero_right] using hC n⟩
  let orbit : Set Ω := range fun n : ℕ ↦ shift^[n] x
  let X := closure orbit
  have hinv : MapsTo shift X X := by
    have hsub : shift '' orbit ⊆ orbit := by
      rintro y ⟨z, ⟨n, rfl⟩, rfl⟩
      exact ⟨n + 1, Function.iterate_succ_apply' shift n x⟩
    intro y hy
    exact (closure_mono hsub) (image_closure_subset_closure_image hshift ⟨y, hy, rfl⟩)
  have hcompact : CompactSpace X := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let S : C(X, X) := ⟨fun z ↦ ⟨shift z, hinv z.property⟩,
    (hshift.comp continuous_subtype_val).subtype_mk _⟩
  let F : C(X, ℂ) := ⟨fun z ↦ ((z.val 0).val : ℂ),
    continuous_subtype_val.comp ((continuous_apply 0).comp continuous_subtype_val)⟩
  let y : X := ⟨x, subset_closure ⟨0, rfl⟩⟩
  have hiter (n : ℕ) : (S^[n] y : Ω) = shift^[n] x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change shift (S^[n] y : Ω) = shift (shift^[n] x)
      rw [ih]
  have horbit : Subtype.val '' (range fun n : ℕ ↦ S^[n] y) = orbit := by
    rw [← Set.range_comp]
    change (range fun n : ℕ ↦ (S^[n] y : Ω)) = orbit
    simp only [hiter, orbit]
  have hdense : DenseRange (fun n : ℕ ↦ S^[n] y) := by
    intro z
    rw [closure_subtype, horbit]
    exact z.property
  have happly (n k : ℕ) : (shift^[n] x) k = x (k + n) := by
    induction n generalizing k with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (shift^[n] x) (k + 1) = _
      rw [ih]
      congr 1
      omega
  refine ⟨X, inferInstance, hcompact, inferInstance, S, F, y, hdense, fun n ↦ ?_⟩
  change (((S^[n] y : Ω) 0).val : ℂ) = u n
  rw [hiter, happly, zero_add]

end VdC

end

end VdC_OrbitRepresentation_Module

/- Source: VdC/PolynomialExample.lean -/
section VdC_PolynomialExample_Module

/-! The polynomial-like example in Section 4. The real expressions are interpreted
modulo one, and the two parity classes are averaged separately. -/

@[expose] public section

open Filter Function Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

noncomputable section

/-- The integer coefficient of `α` in the manuscript's polynomial-like sequence. -/
def polynomialLikeIndex (n : ℕ) : ℤ :=
  if n % 2 = 0 then (n : ℤ) ^ 2 else 2 * ((n : ℤ) - 1) ^ 2

@[simp] theorem polynomialLikeIndex_even (j : ℕ) :
    polynomialLikeIndex (2 * j) = 4 * (j : ℤ) ^ 2 := by
  simp only [polynomialLikeIndex, show (2 * j) % 2 = 0 by omega, ite_true,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

@[simp] theorem polynomialLikeIndex_odd (j : ℕ) :
    polynomialLikeIndex (2 * j + 1) = 8 * (j : ℤ) ^ 2 := by
  simp only [polynomialLikeIndex, show ¬(2 * j + 1) % 2 = 0 by omega, ite_false,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

private def squarePair (α : ℝ) (A B : ℤ) (q n : ℕ) : ℂ :=
  phase (α * ((A : ℝ) * (n : ℝ)^2 + (B : ℝ) * ((n + q : ℕ) : ℝ)^2))

private theorem squarePair_tendsto_zero {α : ℝ} (hα : Irrational α) (A B : ℤ) (q : ℕ)
    (h : A + B ≠ 0 ∨ B ≠ 0 ∧ 0 < q) :
    Tendsto (cesaro (squarePair α A B q)) atTop (𝓝 0) := by
  let L : ℤ := 2 * B * (q : ℤ)
  let C : ℤ := B * (q : ℤ)^2
  have he : squarePair α A B q = fun n : ℕ ↦
      phase (α * (((A + B : ℤ) : ℝ) * (n : ℝ)^2 + (L : ℝ) * (n : ℝ) + (C : ℝ))) := by
    funext n
    unfold squarePair L C
    congr 1
    push_cast
    ring
  rw [he]
  apply tendsto_cesaro_integer_quadratic_phase hα
  rcases h with h | ⟨hB, hq⟩
  · exact Or.inl h
  · exact Or.inr (mul_ne_zero (mul_ne_zero (by norm_num) hB) (by omega))

private theorem squarePair_tendsto_of_shift {α : ℝ} (hα : Irrational α) {A B : ℤ} {q : ℕ}
    (h : A ≠ 0 ∨ B ≠ 0) (hq : 0 < q) : Tendsto (cesaro (squarePair α A B q)) atTop (𝓝 0) := by
  apply squarePair_tendsto_zero hα
  by_cases hB : B = 0
  · exact Or.inl (by simpa only [hB, add_zero] using h.resolve_right (by simpa only [not_not] using hB))
  · exact Or.inr ⟨hB, hq⟩

private def polynomialPairPhase (α : ℝ) (a b : ℤ) (h n : ℕ) : ℂ :=
  phase (α * ((a : ℝ) * (polynomialLikeIndex n : ℝ) +
    (b : ℝ) * (polynomialLikeIndex (n + h) : ℝ)))

private theorem polynomialPairPhase_even_even (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q) (2 * n) = squarePair α (4 * a) (4 * b) q n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + 2 * q = 2 * (n + q) by omega,
    polynomialLikeIndex_even, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_odd_even (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q) (2 * n + 1) = squarePair α (8 * a) (8 * b) q n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + 1 + 2 * q = 2 * (n + q) + 1 by omega,
    polynomialLikeIndex_odd, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_even_odd (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q + 1) (2 * n) = squarePair α (4 * a) (8 * b) q n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + (2 * q + 1) = 2 * (n + q) + 1 by omega,
    polynomialLikeIndex_even, polynomialLikeIndex_odd, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_odd_odd (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q + 1) (2 * n + 1) = squarePair α (8 * a) (4 * b) (q + 1) n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + 1 + (2 * q + 1) = 2 * (n + (q + 1)) by omega,
    polynomialLikeIndex_even, polynomialLikeIndex_odd, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_bounded (α : ℝ) (a b : ℤ) (h : ℕ) :
    BoundedSeq (polynomialPairPhase α a b h) := ⟨1, zero_le_one, fun _ ↦ (norm_phase _).le⟩

private theorem tendsto_cesaro_of_two_residues {u : ℕ → ℂ} (hu : BoundedSeq u) {a b : ℂ}
    (he : Tendsto (cesaro (fun n ↦ u (2*n))) atTop (𝓝 a))
    (ho : Tendsto (cesaro (fun n ↦ u (2*n+1))) atTop (𝓝 b)) :
    Tendsto (cesaro u) atTop (𝓝 ((a + b) / 2)) := by
  have h := tendsto_cesaro_of_residue_limits (r := 2) (by decide) hu (fun t ↦ if t = 0 then a else b) (by
    intro t ht
    interval_cases t
    · simpa only [add_zero, ite_true] using he
    · simpa using ho)
  simpa [Finset.sum_range_succ] using h

private theorem polynomialPairPhase_tendsto_zero {α : ℝ} (hα : Irrational α) {a b : ℤ} {h : ℕ}
    (hnz : a ≠ 0 ∨ b ≠ 0) (hh : 1 < h) :
    Tendsto (cesaro (polynomialPairPhase α a b h)) atTop (𝓝 0) := by
  have hnz_mul {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) : c * a ≠ 0 ∨ d * b ≠ 0 :=
    hnz.imp (mul_ne_zero hc) (mul_ne_zero hd)
  have hex : ∃ q, h = 2 * q ∨ h = 2 * q + 1 := ⟨h / 2, by omega⟩
  rw [show (0 : ℂ) = (0 + 0) / 2 by norm_num]
  apply tendsto_cesaro_of_two_residues (polynomialPairPhase_bounded α a b h)
  · obtain ⟨q, rfl | rfl⟩ := hex
    · simp_rw [polynomialPairPhase_even_even]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)
    · simp_rw [polynomialPairPhase_even_odd]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)
  · obtain ⟨q, rfl | rfl⟩ := hex
    · simp_rw [polynomialPairPhase_odd_even]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)
    · simp_rw [polynomialPairPhase_odd_odd]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)

private theorem polynomialDifferencePhase_tendsto_zero {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) {h : ℕ} (hh : 0 < h) :
    Tendsto (cesaro (polynomialPairPhase α (-m) m h)) atTop (𝓝 0) := by
  by_cases he : h = 1
  · subst h
    have he' : Tendsto (cesaro (fun n ↦ polynomialPairPhase α (-m) m (2 * 0 + 1) (2*n)))
        atTop (𝓝 0) := by
      simp_rw [polynomialPairPhase_even_odd]
      exact squarePair_tendsto_zero hα _ _ _ (Or.inl (by omega))
    have ho : Tendsto (cesaro (fun n ↦ polynomialPairPhase α (-m) m (2 * 0 + 1) (2*n+1)))
        atTop (𝓝 0) := by
      simp_rw [polynomialPairPhase_odd_odd]
      exact squarePair_tendsto_of_shift hα (Or.inr (mul_ne_zero (by norm_num) hm)) (by decide)
    simpa using tendsto_cesaro_of_two_residues (polynomialPairPhase_bounded α (-m) m 1) he' ho
  · exact polynomialPairPhase_tendsto_zero hα (Or.inr hm) (by omega)

private theorem polynomialPairPhase_lagOne {α : ℝ} (hα : Irrational α) :
    Tendsto (cesaro (polynomialPairPhase α 2 (-1) 1)) atTop (𝓝 ((1 : ℂ) / 2)) := by
  have he (n : ℕ) : polynomialPairPhase α 2 (-1) 1 (2*n) = 1 := by
    change polynomialPairPhase α 2 (-1) (2*0+1) (2*n) = _
    rw [polynomialPairPhase_even_odd]
    unfold squarePair
    rw [show α * (((4 * 2 : ℤ) : ℝ) * (n : ℝ)^2 +
      ((8 * (-1) : ℤ) : ℝ) * ((n + 0 : ℕ) : ℝ)^2) = 0 by simp, phase_zero]
  have hEven : Tendsto (cesaro (fun n ↦ polynomialPairPhase α 2 (-1) 1 (2*n))) atTop (𝓝 1) := by
    simpa only [he] using cesaro_tendsto_const (1 : ℂ)
  have hOdd : Tendsto (cesaro (fun n ↦ polynomialPairPhase α 2 (-1) (2*0+1) (2*n+1))) atTop (𝓝 0) := by
    simp_rw [polynomialPairPhase_odd_odd]
    exact squarePair_tendsto_zero hα _ _ _ (Or.inl (by norm_num))
  simpa using tendsto_cesaro_of_two_residues (polynomialPairPhase_bounded α 2 (-1) 1) hEven hOdd

/-- The torus representation of the polynomial-like sequence. -/
def polynomialLikeTorus (α : ℝ) (n : ℕ) : Torus 1 :=
  fun _ ↦ ((α * (polynomialLikeIndex n : ℝ) : ℝ) : UnitAddCircle)

/-- The two-coordinate lag-pair torus sequence. -/
def polynomialLikeLagPair (α : ℝ) (h n : ℕ) : Torus 2 :=
  ![polynomialLikeTorus α n 0, polynomialLikeTorus α (n + h) 0]

private theorem polynomialLikeLagPair_character (α : ℝ) (h n : ℕ) (m : Fin 2 → ℤ) :
    torusCharacter m (polynomialLikeLagPair α h n) = polynomialPairPhase α (m 0) (m 1) h n := by
  rw [torusCharacter_apply, Fin.prod_univ_two]
  change fourier (m 0) ((α * (polynomialLikeIndex n : ℝ) : ℝ) : UnitAddCircle) *
    fourier (m 1) ((α * (polynomialLikeIndex (n + h) : ℝ) : ℝ) : UnitAddCircle) = _
  rw [phase_frequency, phase_frequency, ← phase_add]
  unfold polynomialPairPhase
  congr 1
  ring

private theorem polynomialLikeDifference_character (α : ℝ) (h n : ℕ) (m : Fin 1 → ℤ) :
    torusCharacter m (polynomialLikeTorus α (n + h) - polynomialLikeTorus α n) =
      polynomialPairPhase α (-(m 0)) (m 0) h n := by
  rw [torusCharacter_apply, Fin.prod_univ_one]
  change fourier (m 0) (((α * (polynomialLikeIndex (n + h) : ℝ) : ℝ) : UnitAddCircle) -
    ((α * (polynomialLikeIndex n : ℝ) : ℝ) : UnitAddCircle)) = _
  rw [← AddCircle.coe_sub, phase_frequency]
  unfold polynomialPairPhase
  congr 1
  push_cast
  ring

private theorem nonzero_pair_frequency {m : Fin 2 → ℤ} (hm : m ≠ 0) : m 0 ≠ 0 ∨ m 1 ≠ 0 := by
  by_contra! h
  apply hm
  ext i
  fin_cases i <;> simp [h]

/-- Every positive-lag difference of the polynomial example is uniformly distributed. -/
theorem polynomialLike_differences_equidistributed {α : ℝ} (hα : Irrational α) {h : ℕ} (hh : 0 < h) :
    Equidistributed (torusHaar 1) (fun n ↦ polynomialLikeTorus α (n + h) - polynomialLikeTorus α n) := by
  apply (equidistributed_torus_iff _).2
  intro m hm
  have hm0 : m 0 ≠ 0 := by
    intro he
    apply hm
    ext i
    fin_cases i
    exact he
  simpa only [polynomialLikeDifference_character] using polynomialDifferencePhase_tendsto_zero hα hm0 hh

/-- At lag one, the character of frequency `(2,-1)` has limiting average `1/2`. -/
theorem polynomialLike_lag_one_fourier_half {α : ℝ} (hα : Irrational α) :
    Tendsto (cesaro (fun n ↦ torusCharacter (![2, -1] : Fin 2 → ℤ) (polynomialLikeLagPair α 1 n)))
      atTop (𝓝 ((1 : ℂ) / 2)) := by
  simpa only [polynomialLikeLagPair_character, Matrix.cons_val_zero, Matrix.cons_val_one] using
    polynomialPairPhase_lagOne hα

/-- The lag pairs are uniformly distributed exactly at lags greater than one. -/
theorem polynomialLike_lag_pairs_equidistributed_iff {α : ℝ} (hα : Irrational α) (h : ℕ) :
    Equidistributed (torusHaar 2) (polynomialLikeLagPair α h) ↔ 1 < h := by
  rw [equidistributed_torus_iff]
  constructor
  · intro hUD
    by_contra! hh
    interval_cases h
    · let m : Fin 2 → ℤ := ![1, -1]
      have hm : m ≠ 0 := by intro he; have h0 := congrFun he 0; norm_num [m] at h0
      have hlim := hUD m hm
      have he (n : ℕ) : torusCharacter m (polynomialLikeLagPair α 0 n) = 1 := by
        rw [polynomialLikeLagPair_character]
        unfold m polynomialPairPhase
        simp
      have hone : Tendsto (cesaro (fun n ↦ torusCharacter m (polynomialLikeLagPair α 0 n))) atTop (𝓝 1) := by
        simpa only [he] using cesaro_tendsto_const (1 : ℂ)
      exact one_ne_zero (tendsto_nhds_unique hone hlim)
    · let m : Fin 2 → ℤ := ![2, -1]
      have hm : m ≠ 0 := by intro he; have h0 := congrFun he 0; norm_num [m] at h0
      have hlim := hUD m hm
      have hone : Tendsto (cesaro (fun n ↦ torusCharacter m (polynomialLikeLagPair α 1 n)))
          atTop (𝓝 ((1 : ℂ) / 2)) := by
        exact polynomialLike_lag_one_fourier_half hα
      have := tendsto_nhds_unique hone hlim
      norm_num at this
  · intro hh m hm
    simpa only [polynomialLikeLagPair_character] using polynomialPairPhase_tendsto_zero hα
      (nonzero_pair_frequency hm) hh

/-- The closed-interval representatives of the manuscript's sequence, reduced modulo one. -/
def polynomialLikeSequence (α : ℝ) (n : ℕ) : Cube 1 :=
  fun i ↦ unitRepresentative (polynomialLikeTorus α n i)

@[simp] theorem cubeToTorus_polynomialLikeSequence (α : ℝ) (n : ℕ) :
    cubeToTorus (polynomialLikeSequence α n) = polynomialLikeTorus α n := by
  funext i
  exact unitRepresentative_coe _

/-- The closed-cube lag pair, with the two samples as its two coordinates. -/
def polynomialLikeCubePair (α : ℝ) (h n : ℕ) : Cube 2 :=
  ![polynomialLikeSequence α n 0, polynomialLikeSequence α (n + h) 0]

@[simp] theorem cubeToTorus_polynomialLikeCubePair (α : ℝ) (h n : ℕ) :
    cubeToTorus (polynomialLikeCubePair α h n) = polynomialLikeLagPair α h n := by
  funext i
  fin_cases i <;> simp [cubeToTorus, polynomialLikeCubePair, polynomialLikeLagPair,
    polynomialLikeSequence, unitRepresentative_coe]

theorem polynomialLike_cube_pairs_equidistributed_iff {α : ℝ} (hα : Irrational α) (h : ℕ) :
    Equidistributed (cubeLebesgue 2) (polynomialLikeCubePair α h) ↔ 1 < h := by
  rw [← polynomialLike_lag_pairs_equidistributed_iff hα h]
  constructor
  · intro H
    simpa only [cubeToTorus_polynomialLikeCubePair] using equidistributed_cubeToTorus H
  · intro H
    apply equidistributed_of_cubeToTorus
    simpa only [cubeToTorus_polynomialLikeCubePair] using H

/-- The modulo-one positive-lag difference sequence in the closed interval. -/
def polynomialLikeDifference (α : ℝ) (h n : ℕ) : Cube 1 :=
  fun i ↦ unitRepresentative ((polynomialLikeTorus α (n + h) - polynomialLikeTorus α n) i)

theorem polynomialLike_cube_differences_equidistributed {α : ℝ} (hα : Irrational α)
    {h : ℕ} (hh : 0 < h) : Equidistributed (cubeLebesgue 1) (polynomialLikeDifference α h) := by
  apply equidistributed_of_cubeToTorus
  have he (n : ℕ) : cubeToTorus (polynomialLikeDifference α h n) =
      polynomialLikeTorus α (n + h) - polynomialLikeTorus α n := by
    funext i
    exact unitRepresentative_coe _
  simpa only [he] using polynomialLike_differences_equidistributed hα hh

theorem polynomialLike_spectrallyLebesgue {α : ℝ} (hα : Irrational α) :
    SpectrallyLebesgueDistribution (cubeLebesgue 1) (polynomialLikeSequence α) := by
  apply (cube_sLebesgue_iff_characters _).2
  intro m hm
  let u (n : ℕ) := torusCharacter m (polynomialLikeTorus α n)
  simp only [cubeToTorus_polynomialLikeSequence]
  change SpectrallyLebesgue u
  have hu : BoundedSeq u := bounded_test (torusCharacter m) (polynomialLikeTorus α)
  apply spectrallyLebesgue_of_limsup_square_summable hu
  have hcorr (h : ℕ) : Tendsto (corr u u (h + 1)) atTop (𝓝 0) := by
    have hep := (equidistributed_torus_iff _).1
      (polynomialLike_differences_equidistributed hα (Nat.succ_pos h)) m hm
    unfold corr
    simpa only [torusCharacter_point_sub, u, Nat.succ_eq_add_one] using hep
  have hzero (h : ℕ) : limsup (fun N ↦ ‖corr u u (h + 1) N‖ ^ 2) atTop = 0 := by
    have ht : Tendsto (fun N ↦ ‖corr u u (h + 1) N‖ ^ 2) atTop (𝓝 0) := by
      simpa using (hcorr h).norm.pow 2
    exact ht.limsup_eq
  change Summable (fun h : ℕ ↦ limsup (fun N ↦ ‖corr u u (h + 1) N‖ ^ 2) atTop)
  simpa only [hzero] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))

private def polynomialCubeCharacter (k : ℤ) : C(Cube 1, ℂ) :=
  (torusCharacter (fun _ ↦ k)).comp ⟨cubeToTorus, continuous_cubeToTorus 1⟩

private theorem testMean_polynomialCubeCharacter (k : ℤ) (hk : k ≠ 0) :
    testMean (cubeLebesgue 1) (polynomialCubeCharacter k) = 0 := by
  let g : C(Torus 1, ℂ) := torusCharacter (fun _ ↦ k)
  have hg : testMean (cubeLebesgue 1) (polynomialCubeCharacter k) = testMean (torusHaar 1) g := by
    unfold testMean
    rw [← (cubeToTorus_measurePreserving 1).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus 1).measurable g.continuous.stronglyMeasurable]
    rfl
  have hfreq : (fun _ : Fin 1 ↦ k) ≠ 0 := fun h ↦ hk (congrFun h 0)
  rw [hg]
  simp only [g, testMean_torusCharacter, ite_eq_right hfreq]

theorem polynomialLike_not_orthogonal {α : ℝ} (hα : Irrational α) :
    ¬ OrthogonalDistribution (cubeLebesgue 1) (polynomialLikeSequence α) := by
  intro ho
  have hp := (cube_orthogonal_iff_lag_pairs _).1 ho 1 (by decide)
  let f := polynomialCubeCharacter 2
  let g := polynomialCubeCharacter (-1)
  have htest := hp (productTest f g)
  have hmean : testMean ((cubeLebesgue 1).prod (cubeLebesgue 1)) (productTest f g) = 0 := by
    calc
      _ = testMean (cubeLebesgue 1) f * testMean (cubeLebesgue 1) g := integral_prod_mul _ _
      _ = 0 := by
        rw [show testMean (cubeLebesgue 1) f = 0 from testMean_polynomialCubeCharacter 2 (by norm_num), zero_mul]
  rw [hmean] at htest
  have he (n : ℕ) : productTest f g (polynomialLikeSequence α n, polynomialLikeSequence α (n + 1)) =
      polynomialPairPhase α 2 (-1) 1 n := by
    have ht := polynomialLikeLagPair_character α 1 n ![2, -1]
    simpa only [productTest_apply, f, g, polynomialCubeCharacter, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, cubeToTorus_polynomialLikeSequence, torusCharacter_apply,
      Fin.prod_univ_one, Fin.prod_univ_two, polynomialLikeLagPair, Matrix.cons_val_zero,
      Matrix.cons_val_one] using ht
  have hz : Tendsto (cesaro (polynomialPairPhase α 2 (-1) 1)) atTop (𝓝 0) := by
    simpa only [he] using htest
  have := tendsto_nhds_unique (polynomialPairPhase_lagOne hα) hz
  norm_num at this

/-- The polynomial-like example in the manuscript, including all positive-lag
differences and the exact lag-pair classification. -/
theorem polynomialLikeCounterExample {α : ℝ} (hα : Irrational α) :
    SpectrallyLebesgueDistribution (cubeLebesgue 1) (polynomialLikeSequence α) ∧
      ¬ OrthogonalDistribution (cubeLebesgue 1) (polynomialLikeSequence α) ∧
      (∀ h : ℕ, 0 < h → Equidistributed (cubeLebesgue 1) (polynomialLikeDifference α h)) ∧
      (∀ h : ℕ, Equidistributed (cubeLebesgue 2) (polynomialLikeCubePair α h) ↔ 1 < h) :=
  ⟨polynomialLike_spectrallyLebesgue hα, polynomialLike_not_orthogonal hα,
    fun _ ↦ polynomialLike_cube_differences_equidistributed hα,
    polynomialLike_cube_pairs_equidistributed_iff hα⟩

end

end VdC

end

end VdC_PolynomialExample_Module

/- Source: VdC/SpectralMixing.lean -/
section VdC_SpectralMixing_Module

/-! # Absolutely continuous spectra give weak mixing -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

/-- The mixed Fourier coefficients vanish when the first diagonal spectrum
is absolutely continuous. Restrict away from the singular support of the
second spectrum and apply polarization and Riemann–Lebesgue. -/
theorem crossFourier_tendsto_zero_of_ac
    (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle) (c : Fin 2 → Fin 2 → ℤ → ℂ)
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic c z n)
    (hac : (M (baseVector 0) : Measure UnitAddCircle) ≪ circleHaar) :
    Tendsto (fun n : ℕ => c 0 1 (n : ℤ)) atTop (𝓝 0) := by
  let v := baseVector 0
  let w := baseVector 1
  let μy := (M w : Measure UnitAddCircle)
  have : IsFiniteMeasure μy := inferInstanceAs (IsFiniteMeasure (M w : Measure UnitAddCircle))
  have : μy.HaveLebesgueDecomposition circleHaar :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure
  let ν := circleHaar.withDensity (μy.rnDeriv circleHaar)
  let σ := μy.singularPart circleHaar
  have hsing : circleHaar.MutuallySingular σ := (Measure.mutuallySingular_singularPart _ _).symm
  obtain ⟨A, hA, hHa, hσ⟩ := hsing
  have hA0 : (M v : Measure UnitAddCircle) A = 0 := hac hHa
  have hAcompl : μy.restrict Aᶜ ≪ circleHaar := by
    intro S hS
    have hSa : circleHaar (S ∩ Aᶜ) = 0 :=
      measure_mono_null Set.inter_subset_left hS
    have hdec : μy = ν + σ := (Measure.rnDeriv_add_singularPart μy circleHaar).symm
    rw [Measure.restrict_apply' hA.compl, hdec, add_apply]
    rw [withDensity_absolutelyContinuous _ _ hSa, zero_add]
    exact measure_mono_null Set.inter_subset_right hσ
  have hsame (b : Fin 2 → ℂ) (hb : M b = M w) :
      (M (v+b) : Measure UnitAddCircle).restrict A = μy.restrict A := by
    apply Measure.ext
    intro S hS
    simp only [Measure.restrict_apply hS]
    rw [add_comm v b, combinationMeasure_apply_of_null M c hM b v _ (by
      exact measure_mono_null Set.inter_subset_right hA0), hb]
  have hre (b : Fin 2 → ℂ) (hb : M b = M w) :
      (M (v+b) : Measure UnitAddCircle).restrict Aᶜ ≪ circleHaar := by
    intro S hS
    have hSa : circleHaar (S ∩ Aᶜ) = 0 :=
      measure_mono_null Set.inter_subset_left hS
    have hbS : (M b : Measure UnitAddCircle) (S ∩ Aᶜ) = 0 := by
      rw [hb, ← Measure.restrict_apply' hA.compl]
      exact hAcompl hS
    rw [Measure.restrict_apply' hA.compl,
      combinationMeasure_apply_of_null M c hM v b _ hbS]
    exact hac hSa
  have hsplit (b : Fin 2 → ℂ) (hb : M b = M w) (n : ℤ) :
      measureFourier (M (v+b)) n =
        measureFourier (μy.restrict A) n +
          measureFourier ((M (v+b) : Measure UnitAddCircle).restrict Aᶜ) n := by
    have hμ := Measure.restrict_add_restrict_compl (μ := (M (v+b) : Measure UnitAddCircle)) hA
    have h := congrArg (fun ρ : Measure UnitAddCircle => measureFourier ρ n) hμ
    rw [measureFourier_add, hsame b hb] at h
    exact h.symm
  have hmw : M (-w) = M w := combinationMeasure_neg M c hM w
  have hiw : M (Complex.I • w) = M w := combinationMeasure_mul_I M c hM w
  have hmiw : M (-(Complex.I • w)) = M w :=
    (combinationMeasure_neg M c hM (Complex.I • w)).trans hiw
  let F (b : Fin 2 → ℂ) (n : ℤ) :=
    measureFourier ((M (v+b) : Measure UnitAddCircle).restrict Aᶜ) n
  have hp (n : ℤ) : 4 * c 0 1 n =
      measureFourier (M (v+w)) n - measureFourier (M (v + -w)) n +
        Complex.I * (measureFourier (M (v + Complex.I • w)) n -
          measureFourier (M (v + -(Complex.I • w))) n) := by
    simp [hM, spectralQuadratic, Fin.sum_univ_two, v, w, baseVector, Pi.single_apply,
      Complex.I_mul_I]
    ring_nf
    simp
    ring
  have hpol (n : ℤ) : 4 * c 0 1 n =
      F w n - F (-w) n + Complex.I * (F (Complex.I • w) n - F (-(Complex.I • w)) n) := by
    rw [hp, hsplit w rfl, hsplit (-w) hmw, hsplit (Complex.I • w) hiw,
      hsplit (-(Complex.I • w)) hmiw]
    dsimp only [F]
    ring
  have hF (b : Fin 2 → ℂ) (hb : M b = M w) :
      Tendsto (fun n : ℕ => F b (n : ℤ)) atTop (𝓝 0) :=
    tendsto_measureFourier_zero_of_ac _ (hre b hb)
  have h1 := (hF w rfl).sub (hF (-w) hmw)
  have h2 := ((hF (Complex.I • w) hiw).sub (hF (-(Complex.I • w)) hmiw)).const_mul Complex.I
  have h := (h1.add h2).const_mul (1 / 4 : ℂ)
  simp only [sub_zero, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards with n
  rw [← hpol]
  ring

/-- Mixed permissible correlation limits tend to zero in the lag
when the first sequence is spectrally Lebesgue. -/
theorem SpectrallyLebesgue.cross_tendsto_zero {x y : ℕ → ℂ} (hx : SpectrallyLebesgue x)
    {N : ℕ → ℕ} {r : ℕ → ℂ} (hp : PermissibleTriple x y N) (hr : CorrLimits x y N r) :
    Tendsto r atTop (𝓝 0) := by
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hxa := pairSpectrum_ac hp.strictMono c M hc hM 0 hx
  have ht := crossFourier_tendsto_zero_of_ac M (integerCorrelation c) hM hxa
  have heq (h : ℕ) : integerCorrelation c 0 1 (h : ℤ) = r h :=
    tendsto_nhds_unique (hc 0 1 h) (hr h)
  simpa only [heq] using ht

end

end VdC

end

end VdC_SpectralMixing_Module
