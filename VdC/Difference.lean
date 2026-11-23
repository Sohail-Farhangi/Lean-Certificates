/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Torus
public import VdC.SpectralResults
public import Mathlib.Topology.Order.LiminfLimsup

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
