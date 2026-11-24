/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Definitions
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {K : Type*} [Group K] [MeasurableSpace K]

omit [Group K] in
/-- Two distinct probability laws whose sum is twice Haar. Given a test set
of masses `a` and `b` on the two pieces, the laws have densities `1+b,b`
and `a,1+a`, respectively. -/
theorem exists_complementary_probability_laws (m : Measure K) [IsProbabilityMeasure m]
    (A : Set K) (hA : MeasurableSet A) (ha : m A ≠ 0) (hb : m Aᶜ ≠ 0) :
    ∃ p q : Measure K, IsProbabilityMeasure p ∧ IsProbabilityMeasure q ∧
      p + q = (2 : ℝ≥0∞) • m ∧ p A ≠ q A := by
  let a := m A
  let b := m Aᶜ
  have hab : a+b = 1 := by
    change m A + m Aᶜ = 1
    rw [measure_add_measure_compl hA, measure_univ]
  let p := (1+b) • m.restrict A + b • m.restrict Aᶜ
  let q := a • m.restrict A + (1+a) • m.restrict Aᶜ
  refine ⟨p,q,⟨?_⟩,⟨?_⟩,?_,?_⟩
  · change ((1+b) • m.restrict A + b • m.restrict Aᶜ) univ = 1
    simp only [add_apply, smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    change (1+b)*a+b*b = 1
    calc
      _ = a+b*(a+b) := by ring
      _ = 1 := by rw [hab, mul_one, hab]
  · change (a • m.restrict A + (1+a) • m.restrict Aᶜ) univ = 1
    simp only [add_apply, smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    change a*a+(1+a)*b = 1
    calc
      _ = a*(a+b)+b := by ring
      _ = 1 := by rw [hab, mul_one, hab]
  · change (1+b) • m.restrict A + b • m.restrict Aᶜ +
        (a • m.restrict A + (1+a) • m.restrict Aᶜ) = (2 : ℝ≥0∞) • m
    rw [add_add_add_comm, ← add_smul, ← add_smul,
      show 1+b+a = 2 from by rw [add_assoc, add_comm b a, hab, one_add_one_eq_two],
      show b+(1+a) = 2 from by rw [add_left_comm, add_comm b a, hab, one_add_one_eq_two],
      ← smul_add, Measure.restrict_add_restrict_compl hA]
  · have ha' : a.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨ha,measure_ne_top m _⟩
    have hb' : b.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hb,measure_ne_top m _⟩
    intro he
    have h := congrArg ENNReal.toReal he
    simp only [p, q, add_apply, smul_apply, smul_eq_mul, Measure.restrict_apply hA,
      inter_self, inter_compl_self, measure_empty, mul_zero, add_zero, ENNReal.toReal_mul] at h
    change (1+b).toReal * a.toReal = a.toReal * a.toReal at h
    rw [ENNReal.toReal_add ENNReal.one_ne_top (measure_ne_top m _), ENNReal.toReal_one] at h
    have hab' := congrArg ENNReal.toReal hab
    rw [ENNReal.toReal_add (measure_ne_top m _) (measure_ne_top m _), ENNReal.toReal_one] at hab'
    have h0 : 0 < a.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg ha'.symm
    have h1 : 0 < b.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg hb'.symm
    nlinarith [mul_pos h0 h1]

variable [MeasurableMul₂ K] [MeasurableInv K]

/-- Distribution of `k l⁻¹` under two independent laws. -/
def differenceLaw (a b : Measure K) : Measure K :=
  (a.prod b).map (fun z : K × K ↦ z.1 * z.2⁻¹)

theorem measurable_difference : Measurable (fun z : K × K ↦ z.1 * z.2⁻¹) :=
  measurable_fst.mul measurable_snd.inv

instance (a b : Measure K) [IsProbabilityMeasure a] [IsProbabilityMeasure b] :
    IsProbabilityMeasure (differenceLaw a b) :=
  (Measure.isProbabilityMeasure_map_iff measurable_difference.aemeasurable).mpr inferInstance

theorem differenceLaw_haar_left (m a : Measure K) [IsProbabilityMeasure a] [IsMulRightInvariant m]
    [SFinite m] : differenceLaw m a = m := by
  ext A hA
  rw [differenceLaw, Measure.map_apply measurable_difference hA,
    Measure.prod_apply_symm (measurable_difference hA)]
  have he (z : K) : m ((fun x ↦ (x,z)) ⁻¹' ((fun w : K × K ↦ w.1*w.2⁻¹) ⁻¹' A)) = m A := by
    change m ((fun x : K ↦ x*z⁻¹) ⁻¹' A) = m A
    exact (measurePreserving_mul_right m z⁻¹).measure_preimage hA.nullMeasurableSet
  simp_rw [he]
  rw [lintegral_const, measure_univ, mul_one]

theorem differenceLaw_haar_right (m a : Measure K) [IsProbabilityMeasure a]
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [IsInvInvariant m] : differenceLaw a m = m := by
  ext A hA
  rw [differenceLaw, Measure.map_apply measurable_difference hA,
    Measure.prod_apply (measurable_difference hA)]
  have he (z : K) : m ((fun x ↦ (z,x)) ⁻¹' ((fun w : K × K ↦ w.1*w.2⁻¹) ⁻¹' A)) = m A := by
    change m ((fun x : K ↦ z*x⁻¹) ⁻¹' A) = m A
    exact ((measurePreserving_mul_left m z).comp (measurePreserving_inv m)).measure_preimage hA.nullMeasurableSet
  simp_rw [he]
  rw [lintegral_const, measure_univ, mul_one]

theorem differenceLaw_add_left (a b c : Measure K) [SFinite a] [SFinite b] [SFinite c] :
    differenceLaw (a+b) c = differenceLaw a c + differenceLaw b c := by
  unfold differenceLaw
  rw [Measure.add_prod, Measure.map_add _ _ measurable_difference]

theorem differenceLaw_add_right (a b c : Measure K) [SFinite a] [SFinite b] [SFinite c] :
    differenceLaw a (b+c) = differenceLaw a b + differenceLaw a c := by
  unfold differenceLaw
  rw [Measure.prod_add, Measure.map_add _ _ measurable_difference]

/-- For complementary input laws, the output law depends only on whether the
two signs agree. The two possible output laws sum to twice Haar. -/
theorem differenceLaw_complementary (m p q : Measure K)
    [IsProbabilityMeasure m] [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    [IsMulLeftInvariant m] [IsMulRightInvariant m] [IsInvInvariant m]
    (hpq : p+q = (2 : ℝ≥0∞) • m) :
    differenceLaw p p = differenceLaw q q ∧
      differenceLaw p q = differenceLaw q p ∧
      differenceLaw p p + differenceLaw p q = (2 : ℝ≥0∞) • m := by
  have h₂ : p+q = m+m := hpq.trans (two_smul ℝ≥0∞ m)
  have hP : differenceLaw p p + differenceLaw p q = m+m := by
    rw [← differenceLaw_add_right, h₂, differenceLaw_add_right, differenceLaw_haar_right]
  have hQ : differenceLaw q p + differenceLaw q q = m+m := by
    rw [← differenceLaw_add_right, h₂, differenceLaw_add_right, differenceLaw_haar_right]
  have hL : differenceLaw p p + differenceLaw q p = m+m := by
    rw [← differenceLaw_add_left, h₂, differenceLaw_add_left, differenceLaw_haar_left]
  have hCancel (a b c : Measure K) [IsFiniteMeasure a] (h : a+b = a+c) : b = c := by
    ext A hA
    have h' := congrArg (fun v : Measure K ↦ v A) h
    simpa only [add_apply, ENNReal.add_right_inj (measure_ne_top a _)] using h'
  have hCross : differenceLaw p q = differenceLaw q p :=
    hCancel _ _ _ (hP.trans hL.symm)
  refine ⟨?_,hCross,hP.trans (two_smul ℝ≥0∞ m).symm⟩
  apply hCancel (differenceLaw p q)
  rw [add_comm (differenceLaw p q) (differenceLaw p p), hP, hCross, hQ]

end SixProblems
