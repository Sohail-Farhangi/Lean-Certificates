/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import VdC.Basic
public import VdC.Periodogram
public import VdC.Spectrum
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic.Ring

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
