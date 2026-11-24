/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.BernoulliThreshold
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-- A sign that is positive exactly below a given threshold. -/
def thresholdSign (a t : ℝ) : ℝ := if t ≤ a then 1 else -1

theorem measurable_thresholdSign (a : ℝ) : Measurable (thresholdSign a) :=
  measurable_const.ite measurableSet_Iic measurable_const

theorem norm_thresholdSign (a t : ℝ) : ‖thresholdSign a t‖ = 1 := by
  unfold thresholdSign
  split_ifs <;> simp

theorem integral_thresholdSign {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ t, thresholdSign a t ∂unitIntervalLaw = 2*a-1 := by
  let A := Iic a
  let h := A.indicator (fun _ : ℝ ↦ (1 : ℝ))
  have hm : MeasurableSet A := measurableSet_Iic
  have hh : Integrable h unitIntervalLaw := (integrable_const _).indicator hm
  have he (t : ℝ) : thresholdSign a t = 2*h t-1 := by
    by_cases ht : t ≤ a <;> norm_num [thresholdSign, h, A, ht]
  simp_rw [he]
  rw [integral_sub (hh.const_mul _) (integrable_const _), integral_const_mul,
    integral_indicator hm, setIntegral_const, integral_const]
  simp only [smul_eq_mul, mul_one, Measure.real_def, measure_univ, ENNReal.toReal_one]
  change 2 * (unitIntervalLaw (Iic a)).toReal - 1 = _
  rw [unitIntervalLaw_Iic ha0 ha1, ENNReal.toReal_ofReal ha0]

/-- Assign a sign using the identity coordinate of the independent Bernoulli
factor. A threshold in `[0,1]` gives the expected sign `2f-1`. -/
def bernoulliSign (f : X → ℝ) (z : X × (G → ℝ)) : ℝ := thresholdSign (f z.1) (z.2 1)

theorem measurable_bernoulliSign {f : X → ℝ} (hf : Measurable f) :
    Measurable (bernoulliSign (G := G) f) :=
  measurable_const.ite (measurableSet_bernoulliThreshold hf) measurable_const

theorem integral_bernoulliSign (S : System G X) {f : X → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    let T := S.prod (bernoulliShift G unitIntervalLaw)
    ∫ z, bernoulliSign f z ∂T.measure = ∫ x, 2*f x-1 ∂S.measure := by
  let m := Measure.infinitePi (fun _ : G ↦ unitIntervalLaw)
  let s := bernoulliSign (G := G) f
  have hs : Integrable s (S.measure.prod m) := Integrable.of_bound
    (measurable_bernoulliSign hf).aestronglyMeasurable 1 (ae_of_all _ fun z ↦
      (norm_thresholdSign (f z.1) (z.2 1)).le)
  change (∫ z, s z ∂S.measure.prod m) = _
  rw [integral_prod s hs]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  change (∫ t, thresholdSign (f x) (t 1) ∂m) = _
  have h := measurePreserving_eval_infinitePi (fun _ : G ↦ unitIntervalLaw) 1
  have hI := integral_map h.measurable.aemeasurable (μ := m) (f := thresholdSign (f x))
    (measurable_thresholdSign (f x)).aestronglyMeasurable
  rw [h.map_eq, integral_thresholdSign (hf0 x) (hf1 x)] at hI
  exact hI.symm

theorem integral_bernoulliSign_correlation (S : System G X) {f : X → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (g : G) (hg : g ≠ 1) :
    let T := S.prod (bernoulliShift G unitIntervalLaw)
    ∫ z, bernoulliSign f (T.act g z) * bernoulliSign f z ∂T.measure =
      ∫ x, (2*f (S.act g x)-1)*(2*f x-1) ∂S.measure := by
  let m := Measure.infinitePi (fun _ : G ↦ unitIntervalLaw)
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let s := bernoulliSign (G := G) f
  let q (z : X × (G → ℝ)) := s (T.act g z) * s z
  have hs := measurable_bernoulliSign (G := G) hf
  have hq : Integrable q (S.measure.prod m) := Integrable.of_bound
    ((hs.comp (T.preserves g).measurable).mul hs).aestronglyMeasurable 1
    (ae_of_all _ fun z ↦ by
      change ‖thresholdSign _ _ * thresholdSign _ _‖ ≤ 1
      rw [norm_mul, norm_thresholdSign, norm_thresholdSign, one_mul])
  change (∫ z, q z ∂S.measure.prod m) = _
  rw [integral_prod q hq]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  let u := thresholdSign (f (S.act g x))
  let v := thresholdSign (f x)
  let p (t : G → ℝ) := (t g,t 1)
  have hp : MeasurePreserving p m (unitIntervalLaw.prod unitIntervalLaw) :=
    ⟨(measurable_pi_apply g).prodMk (measurable_pi_apply 1),
      Measure.infinitePi_map_eval_prod (P := fun _ : G ↦ unitIntervalLaw) hg⟩
  let k (z : ℝ × ℝ) := u z.1 * v z.2
  have hk : Measurable k := ((measurable_thresholdSign _).comp measurable_fst).mul
    ((measurable_thresholdSign _).comp measurable_snd)
  have he := integral_map hp.aemeasurable (f := k) hk.aestronglyMeasurable
  rw [hp.map_eq] at he
  have hq' (t : G → ℝ) : q (x,t) = k (p t) := by
    change thresholdSign (f (S.act g x)) (t (1*g)) * thresholdSign (f x) (t 1) = _
    simp [k, p, u, v]
  simp_rw [hq']
  rw [← he]
  change (∫ z : ℝ × ℝ, u z.1 * v z.2 ∂unitIntervalLaw.prod unitIntervalLaw) = _
  rw [integral_prod_mul, integral_thresholdSign (hf0 _) (hf1 _),
    integral_thresholdSign (hf0 _) (hf1 _)]

end SixProblems
