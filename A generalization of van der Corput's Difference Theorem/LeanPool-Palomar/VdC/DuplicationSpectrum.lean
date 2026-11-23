/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import VdC.DuplicationEstimates
public import VdC.CubeDifference

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
