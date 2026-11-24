/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconColumnMeasure

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory Set
open scoped Classical ENNReal Topology

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A test depends only on finitely many odometer digits and the layer. -/
def IsChaconPrefixTest (N : ℕ) (f : ChaconOdometer × Bool → ℂ) : Prop :=
  ∀ (x : ChaconOdometer) (b : Bool), f (x,b) = f (chaconPrefix N x,b)

theorem IsChaconPrefixTest.columnConstant {N n : ℕ} (hN : N ≤ n)
    {f : ChaconOdometer × Bool → ℂ} (hf : IsChaconPrefixTest N f)
    (l : ℕ) (hl : l < chaconTowerHeight n) (x : ChaconOdometer) :
    f (chaconColumnPoint n (l : ℤ) x) = f (chaconColumnPoint n (l : ℤ) 0) := by
  obtain ⟨r, b, hr, h⟩ := chaconColumnPoint_core n l hl
  have hval : ((r : ZMod (3^n))).val = r := ZMod.val_natCast_of_lt hr
  have h₁ := chaconScaleBranch_residue n (r : ZMod (3^n)) x
  have h₂ := chaconScaleBranch_residue n (r : ZMod (3^n)) 0
  rw [hval] at h₁ h₂
  rw [h x, h 0, hf (chaconScaleBranch n r x) b, hf (chaconScaleBranch n r 0) b]
  simp only [chaconPrefix, ← PadicInt.cast_toZModPow N n hN, h₁, h₂]

/-- The polynomial with the spacer probabilities, acting on pointwise
representatives. -/
def chaconHeightObservable (m : ℕ) (f : ChaconOdometer × Bool → ℂ)
    (x : ChaconOdometer × Bool) : ℂ :=
  ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
    f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ))) x)

theorem measurable_chaconHeightObservable (m : ℕ) {f : ChaconOdometer × Bool → ℂ}
    (hf : Measurable f) : Measurable (chaconHeightObservable m f) := by
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  exact (hf.comp (chaconTowerSystem.preserves (Multiplicative.ofAdd (-(k : ℤ)))).measurable).const_smul
    (chaconSpacerProbability m k)

theorem norm_chaconHeightObservable_le (m : ℕ) {f : ChaconOdometer × Bool → ℂ}
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : ChaconOdometer × Bool) :
    ‖chaconHeightObservable m f x‖ ≤ (m+1 : ℝ) * C := by
  have h₀ : 0 ≤ C := (norm_nonneg _).trans (hC (0, false))
  refine (norm_sum_le _ _).trans ?_
  have hs (k : ℕ) : ‖chaconSpacerProbability m k •
      f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ))) x)‖ ≤ C := by
    rw [chaconSpacerProbability, norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hC _)
    exact le_trans (MeasureTheory.measureReal_mono (Set.subset_univ _) (measure_ne_top _ _))
      (by simp)
  refine (Finset.sum_le_sum fun k _ ↦ hs k).trans_eq ?_
  simp

private theorem integral_chaconSpacerCount_select (m : ℕ) (a : ℕ → ℂ) :
    (∫ x, a (chaconSpacerCount m x) ∂chaconOdometerMeasure) =
      ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • a k := by
  let A (k : ℕ) : Set ChaconOdometer := {x | chaconSpacerCount m x = k}
  have hA (k : ℕ) : MeasurableSet (A k) :=
    measurable_chaconSpacerCount m (measurableSet_singleton k)
  have h (x : ChaconOdometer) :
      a (chaconSpacerCount m x) = ∑ k ∈ Finset.range (m+1), (A k).indicator (fun _ ↦ a k) x := by
    simp only [A, indicator, mem_ofPred_eq, Finset.sum_ite_eq,
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (chaconSpacerCount_le m x)), ite_true]
  simp_rw [h]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_indicator_const _ (hA k)]
    rfl
  · exact fun k _ ↦ (integrable_const (a k)).indicator (hA k)

/-- If the shifted level and all of its spacer corrections stay in the
main column, the high tail averages out exactly. -/
theorem integral_chaconColumn_shift_eq_heightObservable (n m l : ℕ) (r : ℤ)
    {N : ℕ} (hN : N ≤ n) {f g : ChaconOdometer × Bool → ℂ}
    (hf : IsChaconPrefixTest N f) (hg : IsChaconPrefixTest N g)
    (hl : l < chaconTowerHeight n) (hlo : (m : ℤ) ≤ r + l)
    (hhi : r + l < chaconTowerHeight n) :
    (∫ x, g (chaconColumnPoint n (l : ℤ) x) *
      f (chaconColumnPoint n ((m * chaconTowerHeight n : ℕ) + r + l) x)
      ∂chaconOdometerMeasure) =
    ∫ x, g (chaconColumnPoint n (l : ℤ) x) *
      chaconHeightObservable m f (chaconColumnPoint n (r+l) x)
      ∂chaconOdometerMeasure := by
  let a (k : ℕ) := g (chaconColumnPoint n (l : ℤ) 0) *
    f (chaconColumnPoint n (r+l-(k : ℤ)) 0)
  have hF (k : ℕ) (hk : k ≤ m) (x : ChaconOdometer) :
      f (chaconColumnPoint n (r+l-(k : ℤ)) x) =
        f (chaconColumnPoint n (r+l-(k : ℤ)) 0) := by
    have h₀ : 0 ≤ r+l-(k : ℤ) := by omega
    have he : ((r+l-(k : ℤ)).toNat : ℤ) = r+l-(k : ℤ) := Int.toNat_of_nonneg h₀
    have hh : (r+l-(k : ℤ)).toNat < chaconTowerHeight n := by omega
    rw [← he]
    exact hf.columnConstant hN _ hh x
  calc
    _ = ∫ x, a (chaconSpacerCount m x) ∂chaconOdometerMeasure := by
      apply integral_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      dsimp only
      rw [hg.columnConstant hN l hl x, chaconColumnPoint_advance,
        hF _ (chaconSpacerCount_le m x)]
    _ = ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k • a k :=
      integral_chaconSpacerCount_select m a
    _ = _ := by
      symm
      calc
        _ = ∫ _ : ChaconOdometer, ∑ k ∈ Finset.range (m+1),
            chaconSpacerProbability m k • a k ∂chaconOdometerMeasure := by
          apply integral_congr_ae
          refine ae_of_all _ fun x ↦ ?_
          dsimp only
          rw [chaconHeightObservable, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          rw [chaconColumnPoint_shift, show -(k : ℤ) + (r+l) = r+l-(k : ℤ) by ring,
            hg.columnConstant hN l hl x, hF k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
          exact (mul_smul_comm _ _ _)
        _ = _ := by simp [integral_const, measureReal_def]

end Mixing
