/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconTower
public import Mathlib.Dynamics.Ergodic.Action.OfMinimal
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Ergodicity and rigidity of the ternary odometer -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

instance : chaconOdometerMeasure.Regular := by
  unfold chaconOdometerMeasure
  infer_instance

/-- The Haar-preserving adding machine is ergodic by density of the integers in
the additive group of 3-adic integers. -/
theorem chaconOdometerStep_ergodic : Ergodic chaconOdometerStep chaconOdometerMeasure := by
  have hd : DenseRange (fun n : ℤ ↦ n • (1 : ChaconOdometer)) := by
    simpa only [zsmul_one] using (PadicInt.denseRange_intCast (p := 3))
  change Ergodic (fun x : ChaconOdometer ↦ x + 1) chaconOdometerMeasure
  simpa only [add_comm (_ : ChaconOdometer) 1] using
    ergodic_add_left_of_denseRange_zsmul hd chaconOdometerMeasure

/-- Haar translation on the ternary odometer. -/
theorem chaconOdometer_translate_preserving (a : ChaconOdometer) :
    MeasurePreserving (fun x : ChaconOdometer ↦ x + a) chaconOdometerMeasure chaconOdometerMeasure := by
  simpa only [add_comm (_ : ChaconOdometer) a] using measurePreserving_add_left chaconOdometerMeasure a

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- As translations tend to zero, the associated operators converge strongly on
the finite-exponent complex Lp spaces of the odometer. -/
theorem tendsto_chaconOdometer_translate_Lp_general {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (v : Lp ℂ p chaconOdometerMeasure) :
    Tendsto (fun a : ChaconOdometer ↦
      Lp.compMeasurePreserving (fun x ↦ x + a) (chaconOdometer_translate_preserving a) v)
      (𝓝 0) (𝓝 v) := by
  let Q : C(ChaconOdometer × ChaconOdometer, ChaconOdometer) :=
    ⟨fun w ↦ w.2 + w.1, continuous_snd.add continuous_fst⟩
  have hQ : Tendsto Q.curry (𝓝 0) (𝓝 (Q.curry 0)) := Q.curry.continuous.tendsto _
  have hv : Tendsto (fun _ : ChaconOdometer ↦ v) (𝓝 0) (𝓝 v) := tendsto_const_nhds
  have h := hv.compMeasurePreservingLp hQ chaconOdometer_translate_preserving
    (chaconOdometer_translate_preserving 0) hp
  have hz : (Q.curry 0 : ChaconOdometer → ChaconOdometer) = id := by
    funext x
    exact add_zero x
  rw [show Lp.compMeasurePreserving (Q.curry 0) (chaconOdometer_translate_preserving 0) v = v from
    Lp.ext (by
      refine (Lp.coeFn_compMeasurePreserving v (chaconOdometer_translate_preserving 0)).trans
        (.of_forall fun x ↦ ?_)
      exact congrArg v (congrFun hz x))] at h
  exact h

/-- As translations tend to zero, the associated operators converge strongly on
the odometer's complex L² space. -/
theorem tendsto_chaconOdometer_translate_Lp (v : Lp ℂ 2 chaconOdometerMeasure) :
    Tendsto (fun a : ChaconOdometer ↦
      Lp.compMeasurePreserving (fun x ↦ x + a) (chaconOdometer_translate_preserving a) v)
      (𝓝 0) (𝓝 v) := tendsto_chaconOdometer_translate_Lp_general (by norm_num) v

/-- The displacements used in the complete odometer cycles tend to zero. -/
theorem tendsto_chaconOdometer_pow_three :
    Tendsto (fun n : ℕ ↦ (3 : ChaconOdometer)^n) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr
  change ‖((3 : ℕ) : ChaconOdometer)‖ < 1
  rw [PadicInt.norm_p]
  norm_num

/-- The translations by `3^n` tend strongly to the identity on odometer L². -/
theorem tendsto_chaconOdometer_translate_pow_Lp (v : Lp ℂ 2 chaconOdometerMeasure) :
    Tendsto (fun n : ℕ ↦ Lp.compMeasurePreserving
      (fun x ↦ x + ((3 : ChaconOdometer)^n))
      (chaconOdometer_translate_preserving ((3 : ChaconOdometer)^n)) v)
      atTop (𝓝 v) :=
  (tendsto_chaconOdometer_translate_Lp v).comp tendsto_chaconOdometer_pow_three

end Mixing
