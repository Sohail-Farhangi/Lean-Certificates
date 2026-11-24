/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconReturnDynamics
public import Mixing.ChaconEigenvalueEstimate
public import Mixing.CyclicEigenvectors
public import Mixing.Koopman
public import Mathlib.Dynamics.Ergodic.Function

/-! # Weak mixing of the explicit Chacon transformation -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal

namespace Mixing

private theorem cast_chacon_eigencharacter_pow (χ : Multiplicative ℤ →* Circle) (m : ℕ) :
    (χ (Multiplicative.ofAdd (m : ℤ)) : ℂ) =
      (χ (Multiplicative.ofAdd (1 : ℤ)) : ℂ)^m := by
  have he : Multiplicative.ofAdd (m : ℤ) = (Multiplicative.ofAdd (1 : ℤ))^m := by
    change (m : ℤ) = m • (1 : ℤ)
    simp
  rw [he, map_pow, Circle.coe_pow]

private theorem ae_chaconTower_eigen_on_bottom
    (χ : Multiplicative ℤ →* Circle) (v : Lp ℂ 2 chaconTowerSystem.measure)
    (hEig : ∀ g, chaconTowerSystem.koopmanRep g v = (χ g : ℂ) • v) :
    ∀ᵐ x ∂chaconOdometerMeasure, ∀ m : ℕ,
      v (chaconTowerSystem.act (Multiplicative.ofAdd (m : ℤ)) (x, false)) =
        (χ (Multiplicative.ofAdd (1 : ℤ)) : ℂ)^m * v (x, false) := by
  apply ae_all_iff.mpr
  intro m
  let g := Multiplicative.ofAdd (m : ℤ)
  let z := (χ (Multiplicative.ofAdd (1 : ℤ)) : ℂ)^m
  have hv := (Lp.stronglyMeasurable v).measurable
  have hm : MeasurableSet {w | v (chaconTowerSystem.act g w) = z * v w} :=
    measurableSet_eq_fun (hv.comp (chaconTowerSystem.preserves g).measurable) (measurable_const.mul hv)
  apply ae_chaconTower_bottom hm
  have he : chaconTowerSystem.koopmanRep g v =ᵐ[chaconTowerSystem.measure]
      v ∘ chaconTowerSystem.act g :=
    Lp.coeFn_compMeasurePreserving v (chaconTowerSystem.preserves g)
  rw [hEig, cast_chacon_eigencharacter_pow χ m] at he
  exact he.symm.trans ((Lp.coeFn_smul z v).mono (fun w hw ↦ by
    change (z • v : Lp ℂ 2 chaconTowerSystem.measure) w = z * v w
    exact hw))

private theorem ae_chaconTower_const_of_bottom
    (v : Lp ℂ 2 chaconTowerSystem.measure) (z a : ℂ) (ha : z * a = a)
    (hStep : ∀ᵐ x ∂chaconOdometerMeasure,
      v (chaconTowerSystem.act (Multiplicative.ofAdd 1) (x, false)) = z * v (x, false))
    (hB : ∀ᵐ x ∂chaconOdometerMeasure, v (x, false) = a) :
    ∀ᵐ w ∂chaconTowerSystem.measure, v w = a := by
  have hm : MeasurableSet {w | v w = a} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable measurable_const
  apply ae_chaconTower_of_bottom_and_top hm hB
  filter_upwards [ae_restrict_mem chaconSpacer_measurable,
    hStep.filter_mono (ae_mono Measure.restrict_le_self),
    hB.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hs hb
  rw [chaconTower_bottom_step, ite_eq_left hx, hb, ha] at hs
  exact hs

/-- The actual classical Chacon tower is weakly mixing. -/
theorem chaconTower_isWeaklyMixing : IsWeaklyMixing chaconTowerSystem.koopmanZeroRep := by
  let : Countable (Multiplicative ℤ) := by
    change Countable ℤ
    infer_instance
  by_contra h
  obtain ⟨χ, v, hv, hEig⟩ := exists_eigenvector_of_not_isWeaklyMixing chaconTowerSystem.koopmanZeroRep h
  let V : Lp ℂ 2 chaconTowerSystem.measure := (v : Lp ℂ 2 chaconTowerSystem.measure)
  let f : ChaconOdometer → ℂ := fun x ↦ V (x, false)
  let z := (χ (Multiplicative.ofAdd (1 : ℤ)) : ℂ)
  have hz : ‖z‖ = 1 := Circle.norm_coe _
  have hFV : Measurable f :=
    (Lp.stronglyMeasurable V).measurable.comp (measurable_id.prodMk measurable_const)
  have hfInt : Integrable f chaconOdometerMeasure :=
    (memLp_chaconTower_bottom (Lp.memLp V)).integrable (by norm_num)
  have hb := ae_chaconTower_eigen_on_bottom χ V fun g ↦ congrArg Subtype.val (hEig g)
  have hCycle (m : ℕ) : ∀ᵐ x ∂chaconOdometerMeasure,
      f (x + (m : ChaconOdometer)) = z^(chaconReturnSum m x) * f x := by
    filter_upwards [hb] with x hx
    have hR := hx (chaconReturnSum m x)
    rw [chaconTower_return_action] at hR
    exact hR
  have hStep : ∀ᵐ x ∂chaconOdometerMeasure,
      V (chaconTowerSystem.act (Multiplicative.ofAdd 1) (x, false)) = z * V (x, false) := by
    filter_upwards [hb] with x hx
    simpa only [pow_one, Nat.cast_one, z] using hx 1
  have hAbsInv : (fun x ↦ ‖f x‖) ∘ chaconOdometerStep =ᵐ[chaconOdometerMeasure]
      (fun x ↦ ‖f x‖) := by
    filter_upwards [hCycle 1] with x hx
    change ‖f (x + 1)‖ = ‖f x‖
    rw [show f (x + 1) = z^(chaconReturnSum 1 x) * f x by simpa only [Nat.cast_one] using hx,
      norm_mul, norm_pow, hz, one_pow, one_mul]
  obtain ⟨c, hc⟩ := chaconOdometerStep_ergodic.ae_eq_const_of_ae_eq_comp₀ hFV.norm.nullMeasurable hAbsInv
  have hcPos : 0 < c := by
    obtain ⟨x, hx⟩ := hc.exists
    change ‖f x‖ = c at hx
    have hcNonneg : 0 ≤ c := hx ▸ norm_nonneg (f x)
    refine lt_of_le_of_ne' hcNonneg ?_
    intro hc₀
    have hf₀ : ∀ᵐ x ∂chaconOdometerMeasure, f x = 0 := by
      filter_upwards [hc] with x hx
      exact norm_eq_zero.mp (hx.trans hc₀)
    have hV₀ := ae_chaconTower_const_of_bottom V z 0 (mul_zero z) hStep hf₀
    have hV₀' : V =ᵐ[chaconTowerSystem.measure] (0 : ChaconOdometer × Bool → ℂ) := hV₀
    apply hv
    apply Subtype.ext
    exact Lp.ext (hV₀'.trans (Lp.coeFn_zero ℂ 2 chaconTowerSystem.measure).symm)
  have hz₁ := chacon_cycle_eigenvalue_eq_one f hfInt c hcPos hc z hz hCycle
  have hFInv : f ∘ chaconOdometerStep =ᵐ[chaconOdometerMeasure] f := by
    filter_upwards [hCycle 1] with x hx
    change f (x + 1) = f x
    simpa only [hz₁, one_pow, one_mul, Nat.cast_one] using hx
  obtain ⟨a, ha⟩ := chaconOdometerStep_ergodic.ae_eq_const_of_ae_eq_comp₀ hFV.nullMeasurable hFInv
  have hV := ae_chaconTower_const_of_bottom V z a (by rw [hz₁, one_mul]) hStep ha
  have hInt : (∫ w, V w ∂chaconTowerSystem.measure) = 0 :=
    (mem_meanZero_iff_integral _ _).mp v.property
  have ha₀ : a = 0 := by
    rw [integral_congr_ae hV] at hInt
    simpa using hInt
  apply hv
  apply Subtype.ext
  have hV₀ : V =ᵐ[chaconTowerSystem.measure] (0 : ChaconOdometer × Bool → ℂ) :=
    hV.mono fun _ hw ↦ hw.trans ha₀
  exact Lp.ext (hV₀.trans (Lp.coeFn_zero ℂ 2 chaconTowerSystem.measure).symm)

end Mixing
