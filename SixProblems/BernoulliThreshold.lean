/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Definitions
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped ENNReal

variable {G X K : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace K]

/-- The right shift has the left action law, even when `G` is nonabelian. -/
def rightShift (a : G) (t : G → K) : G → K := fun g ↦ t (g * a)

omit [MeasurableSpace K] in
@[simp] theorem rightShift_one (t : G → K) : rightShift (1 : G) t = t := by
  funext g
  simp [rightShift]

omit [MeasurableSpace K] in
theorem rightShift_mul (a b : G) (t : G → K) :
    rightShift (a * b) t = rightShift a (rightShift b t) := by
  funext g
  exact congrArg t (mul_assoc g a b).symm

theorem measurable_rightShift (a : G) : Measurable (rightShift (K := K) a) :=
  Measurable.of_eval (fun g ↦ measurable_pi_apply (g * a))

/-- The right shift preserves every constant product probability. -/
theorem measurePreserving_rightShift (m : Measure K) [IsProbabilityMeasure m] (a : G) :
    MeasurePreserving (rightShift (K := K) a)
      (Measure.infinitePi (fun _ : G ↦ m)) (Measure.infinitePi (fun _ : G ↦ m)) := by
  refine ⟨measurable_rightShift a, ?_⟩
  let e := Equiv.mulRight a
  have he : rightShift (K := K) a = MeasurableEquiv.piCongrLeft (fun _ : G ↦ K) e.symm := by
    funext t g
    change t (e g) = MeasurableEquiv.piCongrLeft (fun _ : G ↦ K) e.symm t g
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : G ↦ K) e.symm t (e g)
    rwa [Equiv.symm_apply_apply, eq_comm] at h
  rw [he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : G ↦ m) e.symm

/-- The Bernoulli system over a probability space `K`. -/
def bernoulliShift (G : Type*) [Group G] (m : Measure K) [IsProbabilityMeasure m] :
    System G (G → K) where
  measure := Measure.infinitePi (fun _ : G ↦ m)
  probability := inferInstance
  act := rightShift
  act_one := funext rightShift_one
  act_mul a b := funext (rightShift_mul a b)
  preserves := measurePreserving_rightShift m

/-- Lebesgue probability supported on the closed unit interval. -/
def unitIntervalLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitIntervalLaw := by
  constructor
  rw [unitIntervalLaw, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

theorem unitIntervalLaw_Iic {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unitIntervalLaw (Iic x) = ENNReal.ofReal x := by
  rw [unitIntervalLaw, Measure.restrict_apply measurableSet_Iic]
  have h : Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 x := by
    ext y
    exact ⟨fun h ↦ ⟨h.2.1,h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hx1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

variable (S : System G X)

/-- The event whose Bernoulli coordinate is below the prescribed threshold. -/
def bernoulliThreshold (f : X → ℝ) : Set (X × (G → ℝ)) :=
  {z | z.2 1 ≤ f z.1}

theorem measurableSet_bernoulliThreshold {f : X → ℝ} (hf : Measurable f) :
    MeasurableSet (bernoulliThreshold (G := G) f) :=
  measurableSet_le ((measurable_pi_apply (1 : G)).comp measurable_snd) (hf.comp measurable_fst)

/-- The finite-intersection identity of Proposition 2.1. The index finset
represents any finite tuple of distinct translates. -/
theorem bernoulliThreshold_pattern
    {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (J : Finset G) :
    let T := S.prod (bernoulliShift G unitIntervalLaw)
    (T.measure {z | ∀ g ∈ J, z ∈ T.act g ⁻¹' bernoulliThreshold f}).toReal =
      ∫ x, ∏ g ∈ J, f (S.act g x) ∂S.measure := by
  classical
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let E : Set (X × (G → ℝ)) := {z | ∀ g ∈ J, z ∈ T.act g ⁻¹' bernoulliThreshold f}
  have hE : MeasurableSet E := by
    rw [show E = ⋂ g ∈ J, T.act g ⁻¹' bernoulliThreshold f by ext; simp [E]]
    exact MeasurableSet.biInter J.countable_toSet (fun g _ ↦
      (T.preserves g).measurable (measurableSet_bernoulliThreshold hf))
  have hFiber (x : X) : Prod.mk x ⁻¹' E = (J : Set G).pi (fun g ↦ Iic (f (S.act g x))) := by
    ext t
    simp [E, T, bernoulliThreshold, System.prod, System.prodAct, bernoulliShift, rightShift, Set.mem_pi]
  change (T.measure E).toReal = _
  change ((S.measure.prod (Measure.infinitePi (fun _ : G ↦ unitIntervalLaw))) E).toReal = _
  rw [Measure.prod_apply hE]
  simp_rw [hFiber, Measure.infinitePi_pi _ (fun g _ ↦ measurableSet_Iic),
    unitIntervalLaw_Iic (hf0 _) (hf1 _)]
  have hprod (x : X) : 0 ≤ ∏ g ∈ J, f (S.act g x) :=
    Finset.prod_nonneg (fun g _ ↦ hf0 _)
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun g _ ↦ hf0 (S.act g _))]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hprod)]
  exact (Finset.measurable_prod J (fun g _ ↦ hf.comp (S.preserves g).measurable)).aestronglyMeasurable

end SixProblems
