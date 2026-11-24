/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconReturnProbability
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The Chacon cycle forces the eigenvalue to be one -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal Topology

namespace Mixing

/-- The return-time equations on the odometer, together with positive constant
modulus, force a unit-modulus eigenvalue to equal one. -/
theorem chacon_cycle_eigenvalue_eq_one (f : ChaconOdometer → ℂ)
    (hInt : Integrable f chaconOdometerMeasure)
    (c : ℝ) (hc : 0 < c) (hAbs : ∀ᵐ x ∂chaconOdometerMeasure, ‖f x‖ = c)
    (z : ℂ) (hz : ‖z‖ = 1)
    (hCycle : ∀ m : ℕ, ∀ᵐ x ∂chaconOdometerMeasure,
      f (x + (m : ChaconOdometer)) = z^(chaconReturnSum m x) * f x) : z = 1 := by
  let μ := chaconOdometerMeasure
  let v := hInt.toL1 f
  let q (n : ℕ) : ChaconOdometer := ((3^n : ℕ) : ChaconOdometer)
  have hq (n : ℕ) : MeasurePreserving (fun x ↦ x + q n) μ μ :=
    chaconOdometer_translate_preserving (q n)
  let d (n : ℕ) := Lp.compMeasurePreserving (fun x ↦ x + q n) (hq n) v - v
  have hq₀ : Tendsto q atTop (𝓝 0) := by
    simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using tendsto_chaconOdometer_pow_three
  have htrans := (tendsto_chaconOdometer_translate_Lp_general
    (p := 1) (by norm_num) v).comp hq₀
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, Function.comp_def, sub_self] using htrans.sub (tendsto_const_nhds (x := v))
  let D (n : ℕ) (x : ChaconOdometer) : ℝ := ‖f (x + q n) - f x‖
  have hD (n : ℕ) : Integrable (D n) μ := by
    have hi : Integrable f (μ.map (fun x ↦ x + q n)) := by rw [(hq n).map_eq]; exact hInt
    exact ((hi.comp_measurable (hq n).measurable).sub hInt).norm
  have hDAE (n : ℕ) : (fun x ↦ ‖d n x‖) =ᵐ[μ] D n := by
    have hv : v =ᵐ[μ] f := hInt.coeFn_toL1
    have hout := (Lp.coeFn_compMeasurePreserving v (hq n)).trans
      ((hq n).quasiMeasurePreserving.ae_eq_comp hv)
    filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreserving (fun x ↦ x + q n) (hq n) v) v,
      hv, hout] with x hx hvx htransx
    change ‖d n x‖ = ‖f (x + q n) - f x‖
    rw [hx]
    change ‖Lp.compMeasurePreserving (fun x ↦ x + q n) (hq n) v x - v x‖ = _
    rw [htransx, hvx]
    rfl
  have hnorm (n : ℕ) : (∫ x, D n x ∂μ) = ‖d n‖ := by
    rw [L1.norm_eq_integral_norm, integral_congr_ae (hDAE n)]
  have hbound (n : ℕ) : (1 / 3) * (c * ‖z - 1‖) ≤ 2 * ‖d n‖ := by
    let E := chaconCycleGood n
    have hE := chaconCycleGood_measurable n
    have hle : ∀ᵐ x ∂μ, E.indicator (fun _ ↦ c * ‖z - 1‖) x ≤ D n x + D n (x + q n) := by
      filter_upwards [hAbs, (hq n).quasiMeasurePreserving.ae hAbs, hCycle (3^n),
        (hq n).quasiMeasurePreserving.ae (hCycle (3^n))] with x hx hx' hC hC'
      by_cases hxE : x ∈ E
      · rw [indicator_of_mem hxE]
        have hC₀ : f (x + q n) = z^(chaconReturnSum (3^n) x) * f x := hC
        have hC₁ : f ((x + q n) + q n) =
            z^(chaconReturnSum (3^n) (x + q n)) * f (x + q n) := hC'
        have hShift : chaconReturnSum (3^n) (x + q n) = chaconReturnSum (3^n) x + 1 :=
          chaconReturnSum_shift_pow_on_good n hxE
        let a := z^(chaconReturnSum (3^n) x)
        have ha : ‖a‖ = 1 := by simp [a, norm_pow, hz]
        have hv : z^(chaconReturnSum (3^n) (x + q n)) = z * a := by
          rw [hShift, pow_succ']
        have hD₀ : D n x = ‖a - 1‖ * c := by
          change ‖f (x + q n) - f x‖ = _
          rw [hC₀]
          change ‖a * f x - f x‖ = _
          rw [show a * f x - f x = (a - 1) * f x by ring, norm_mul, hx]
        have hD₁ : D n (x + q n) = ‖z * a - 1‖ * c := by
          change ‖f ((x + q n) + q n) - f (x + q n)‖ = _
          rw [hC₁, hv, show (z * a) * f (x + q n) - f (x + q n) =
            (z * a - 1) * f (x + q n) by ring, norm_mul, hx']
        have htri : ‖z - 1‖ ≤ ‖z * a - 1‖ + ‖a - 1‖ := by
          calc
            ‖z - 1‖ = ‖z * a - a‖ := by
              rw [show z * a - a = (z - 1) * a by ring, norm_mul, ha, mul_one]
            _ = ‖(z * a - 1) - (a - 1)‖ := by congr 1; ring
            _ ≤ _ := norm_sub_le _ _
        rw [hD₀, hD₁]
        calc
          c * ‖z - 1‖ = ‖z - 1‖ * c := mul_comm _ _
          _ ≤ (‖z * a - 1‖ + ‖a - 1‖) * c := mul_le_mul_of_nonneg_right htri hc.le
          _ = _ := by ring
      · rw [indicator_of_notMem hxE]
        exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hDi : Integrable (fun x ↦ D n (x + q n)) μ := by
      have hi : Integrable (D n) (μ.map (fun x ↦ x + q n)) := by rw [(hq n).map_eq]; exact hD n
      exact hi.comp_measurable (hq n).measurable
    have hs : (∫ x, D n (x + q n) ∂μ) = ∫ x, D n x ∂μ :=
      (show MeasurePreserving ((Homeomorph.addRight (q n)).toMeasurableEquiv) μ μ from hq n).integral_comp' (D n)
    have hI := integral_mono_ae ((integrable_const (c * ‖z - 1‖)).indicator hE)
      ((hD n).add hDi) hle
    rw [integral_indicator hE, setIntegral_const, smul_eq_mul, chaconCycleGood_measure_real] at hI
    change (1 / 3) * (c * ‖z - 1‖) ≤ ∫ x, D n x + D n (x + q n) ∂μ at hI
    rw [integral_add (hD n) hDi, hs, hnorm] at hI
    simpa only [two_mul] using hI
  have ht : Tendsto (fun n ↦ 2 * ‖d n‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hd.norm
  have hzero := le_of_tendsto_of_tendsto' tendsto_const_nhds ht hbound
  have hz0 : ‖z - 1‖ = 0 := by nlinarith [norm_nonneg (z - 1)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz0)

end Mixing
