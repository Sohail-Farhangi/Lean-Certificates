/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.SignWitness
public import SixProblems.HaarDifferenceMixture

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Mixing Set
open scoped Classical ENNReal

variable {G X K : Type} [Group G] [MeasurableSpace X] [Group K] [MeasurableSpace K]

omit [Group G] [Group K] [MeasurableSpace K] in
private theorem integral_sign (μ : Measure X) [IsProbabilityMeasure μ] (A : Set X)
    (hA : MeasurableSet A) :
    (∫ x, A.piecewise (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) x ∂μ) = 2 * (μ A).toReal - 1 := by
  classical
  rw [integral_piecewise hA (integrable_const _).integrableOn (integrable_const _).integrableOn,
    setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one, mul_neg, Measure.real_def]
  have h := congrArg ENNReal.toReal (measure_add_measure_compl (μ := μ) hA)
  rw [measure_univ, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h
  linarith

omit [Group G] [Group K] [MeasurableSpace K] in
private theorem lintegral_two_values (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (a b : ℝ≥0∞) : (∫⁻ x, (if x ∈ A then a else b) ∂μ) = a * μ A + b * μ Aᶜ := by
  classical
  change (∫⁻ x, A.piecewise (fun _ ↦ a) (fun _ ↦ b) x ∂μ) = _
  rw [lintegral_piecewise hA.nullMeasurableSet, lintegral_const, lintegral_const,
    Measure.restrict_apply_univ, Measure.restrict_apply_univ]

section Selection

variable (p q : Measure K) [IsProbabilityMeasure p] [IsProbabilityMeasure q]

/-- Select a coordinate from a pair of samples using a real sign. -/
private def signSelect (s : ℝ) (z : K × K) : K := if s = 1 then z.1 else z.2

omit [Group G] [Group K] in
private theorem measurable_signSelect (s : ℝ) : Measurable (signSelect (K := K) s) := by
  by_cases h : s = 1
  · rw [show signSelect (K := K) s = Prod.fst from funext fun z ↦ ite_eq_left h]
    exact measurable_fst
  · rw [show signSelect (K := K) s = Prod.snd from funext fun z ↦ ite_eq_right h]
    exact measurable_snd

omit [Group G] [Group K] in
private theorem signSelect_preserving (s : ℝ) :
    MeasurePreserving (signSelect (K := K) s) (p.prod q) (if s = 1 then p else q) := by
  by_cases h : s = 1
  · rw [ite_eq_left h, show signSelect (K := K) s = Prod.fst from funext fun z ↦ ite_eq_left h]
    exact measurePreserving_fst
  · rw [ite_eq_right h, show signSelect (K := K) s = Prod.snd from funext fun z ↦ ite_eq_right h]
    exact measurePreserving_snd

omit [Group G] [Group K] in
private theorem measurable_selectedCoordinate {s : X → ℝ} (hs : Measurable s) (g : G) :
    Measurable (fun z : X × (G → K × K) ↦ signSelect (s z.1) (z.2 g)) := by
  have h₁ : Measurable (fun z : X × (G → K × K) ↦ z.2 g) :=
    (measurable_pi_apply g).comp measurable_snd
  exact h₁.fst.ite ((hs.comp measurable_fst) (measurableSet_singleton (1 : ℝ))) h₁.snd

variable [MeasurableMul₂ K] [MeasurableInv K]

private theorem selectedDifference_fiber
    (a b : ℝ) {g : G} (hg : g ≠ 1) {B : Set K} (hB : MeasurableSet B) :
    (Measure.infinitePi fun _ : G ↦ p.prod q)
      ((fun t ↦ signSelect a (t g) * (signSelect b (t 1))⁻¹) ⁻¹' B) =
    differenceLaw (if a = 1 then p else q) (if b = 1 then p else q) B := by
  let h (t : G → K × K) := (t g,t 1)
  have hh : MeasurePreserving h (Measure.infinitePi fun _ : G ↦ p.prod q)
      ((p.prod q).prod (p.prod q)) :=
    ⟨(measurable_pi_apply g).prodMk (measurable_pi_apply 1),
      Measure.infinitePi_map_eval_prod (P := fun _ : G ↦ p.prod q) hg⟩
  let k := Prod.map (signSelect (K := K) a) (signSelect (K := K) b)
  have hk : MeasurePreserving k ((p.prod q).prod (p.prod q))
      ((if a = 1 then p else q).prod (if b = 1 then p else q)) :=
    (signSelect_preserving p q a).prod (signSelect_preserving p q b)
  let d (z : K × K) := z.1 * z.2⁻¹
  have he := (hk.comp hh).measure_preimage (measurable_difference hB).nullMeasurableSet
  change _ = ((if a = 1 then p else q).prod (if b = 1 then p else q)) (d ⁻¹' B) at he
  rw [differenceLaw, Measure.map_apply measurable_difference hB]
  exact he

end Selection

variable [TopologicalSpace K] [T2Space K] [IsTopologicalGroup K] [BorelSpace K] [SecondCountableTopology K]
  [StandardBorelSpace K] [Nontrivial K]

/-- The reverse implication of Theorem 4.6. From a sign witness, independently
sample one of two complementary Haar perturbations at each time. -/
theorem isVdC_of_measureTheoreticVdC [Countable G] {R : Set G} (m : Measure K)
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [IsMulRightInvariant m]
    [IsInvInvariant m] [m.IsOpenPosMeasure] (h : IsMeasureTheoreticVdC R m) : IsVdC R := by
  classical
  by_contra hv
  obtain ⟨Y,mY,hY,S,s,hs,hsign,hCorr,hMean⟩ := lemma4_3 hv
  let := mY
  let := hY
  obtain ⟨x,y,hxy⟩ := exists_pair_ne K
  obtain ⟨U,V,hU,hV,hx,hy,hUV⟩ := t2_separation hxy
  have ha : m U ≠ 0 := (hU.measure_pos m ⟨x,hx⟩).ne'
  have hb : m Uᶜ ≠ 0 := ((hV.measure_pos m ⟨y,hy⟩).trans_le
    (measure_mono (fun z hz ↦ disjoint_left.mp hUV.symm hz))).ne'
  obtain ⟨p,q,hp,hq,hpq,hDistinct⟩ := exists_complementary_probability_laws m U hU.measurableSet ha hb
  let := hp
  let := hq
  obtain ⟨hDiag,hCross,hSum⟩ := differenceLaw_complementary m p q hpq
  let law := Measure.infinitePi (fun _ : G ↦ p.prod q)
  let T := S.prod (bernoulliShift G (p.prod q))
  let F (z : Y × (G → K × K)) := signSelect (s z.1) (z.2 1)
  have hF : Measurable F := measurable_selectedCoordinate hs 1
  have hM := h T F hF ?_
  · let A : Set Y := {y | s y = 1}
    have hA : MeasurableSet A := hs (measurableSet_singleton 1)
    have he (y : Y) : s y = A.piecewise (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) y := by
      rcases hsign y with h | h <;> norm_num [A,h]
    have hMass : (S.measure A).toReal ≠ 1/2 := by
      intro ha
      apply hMean
      simp_rw [he]
      rw [integral_sign S.measure A hA, ha]
      norm_num
    have hFmeasure : T.measure.map F U = p U * S.measure A + q U * S.measure Aᶜ := by
      rw [Measure.map_apply hF hU.measurableSet]
      change (S.measure.prod law) (F ⁻¹' U) = _
      rw [Measure.prod_apply (hF hU.measurableSet)]
      have he' (y : Y) : law (Prod.mk y ⁻¹' (F ⁻¹' U)) =
          (if y ∈ A then p U else q U) := by
        have hEval := measurePreserving_eval_infinitePi (fun _ : G ↦ p.prod q) 1
        have hc := ((signSelect_preserving p q (s y)).comp hEval).measure_preimage
          hU.measurableSet.nullMeasurableSet
        change law (Prod.mk y ⁻¹' (F ⁻¹' U)) = (if s y = 1 then p else q) U at hc
        change _ = if s y = 1 then p U else q U
        split_ifs with hy <;> simp only [hy, ite_true, ite_false] at hc <;> exact hc
      simp_rw [he']
      exact lintegral_two_values S.measure A hA _ _
    rw [hM] at hFmeasure
    have hComp := congrArg (fun ρ : Measure K ↦ ρ U) hpq
    simp only [add_apply,smul_apply,smul_eq_mul] at hComp
    have htot := congrArg ENNReal.toReal (measure_add_measure_compl (μ := S.measure) hA)
    have hFreal := congrArg ENNReal.toReal hFmeasure
    have hCreal := congrArg ENNReal.toReal hComp
    simp only [measure_univ, ENNReal.toReal_one,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at htot
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
      ENNReal.toReal_mul, ENNReal.toReal_mul] at hFreal
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_mul,
      ENNReal.toReal_ofNat] at hCreal
    have hFactor : ((p U).toReal - (q U).toReal) * ((S.measure A).toReal - 1/2) = 0 := by
      have heq := congrArg ((q U).toReal * ·) htot
      linarith only [heq, hFreal, hCreal, show ((p U).toReal - (q U).toReal) *
        ((S.measure A).toReal - 1/2) = (p U).toReal * (S.measure A).toReal -
        (q U).toReal * (S.measure A).toReal - ((p U).toReal + (q U).toReal) / 2 + (q U).toReal by ring]
    rcases mul_eq_zero.mp hFactor with hpq' | hA'
    · exact hDistinct ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
        (sub_eq_zero.mp hpq'))
    · exact hMass (sub_eq_zero.mp hA')
  · intro g hg
    have hg1 : g ≠ 1 := fun e ↦ hv (isVdC_of_one_mem (e ▸ hg))
    let A : Set Y := {y | s (S.act g y) = s y}
    have hA : MeasurableSet A := measurableSet_eq_fun (hs.comp (S.preserves g).measurable) hs
    have he (y : Y) : s (S.act g y) * s y =
        A.piecewise (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) y := by
      rcases hsign (S.act g y) with h₁ | h₁ <;> rcases hsign y with h₂ | h₂ <;>
        norm_num [A,h₁,h₂]
    have hm : (S.measure A).toReal = 1/2 := by
      have hc := hCorr g hg
      simp_rw [he] at hc
      rw [integral_sign S.measure A hA] at hc
      linarith
    have hmc : (S.measure Aᶜ).toReal = 1/2 := by
      have hc := congrArg ENNReal.toReal (measure_add_measure_compl (μ := S.measure) hA)
      rw [measure_univ, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        ENNReal.toReal_one, hm] at hc
      linarith
    have hm' : S.measure A = 1/2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
      simpa using hm
    have hmc' : S.measure Aᶜ = 1/2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
      simpa using hmc
    ext B hB
    let d (z : Y × (G → K × K)) := F (T.act g z) * (F z)⁻¹
    have hd : Measurable d := (hF.comp (T.preserves g).measurable).mul hF.inv
    change T.measure.map d B = _
    rw [Measure.map_apply hd hB]
    change (S.measure.prod law) (d ⁻¹' B) = _
    rw [Measure.prod_apply (hd hB)]
    have hFiber (y : Y) : law (Prod.mk y ⁻¹' (d ⁻¹' B)) =
        (if y ∈ A then differenceLaw p p B else differenceLaw p q B) := by
      have hEq : Prod.mk y ⁻¹' (d ⁻¹' B) =
          (fun t : G → K × K ↦ signSelect (s (S.act g y)) (t g) * (signSelect (s y) (t 1))⁻¹) ⁻¹' B := by
        ext t
        simp [d, F, T, System.prod, System.prodAct, bernoulliShift, rightShift]
      rw [hEq, selectedDifference_fiber p q _ _ hg1 hB]
      rcases hsign (S.act g y) with h₁ | h₁ <;> rcases hsign y with h₂ | h₂ <;>
        norm_num [A,h₁,h₂,← hDiag,← hCross]
    simp_rw [hFiber]
    rw [lintegral_two_values S.measure A hA, hm', hmc', ← add_mul]
    have hsB := congrArg (fun ρ : Measure K ↦ ρ B) hSum
    simp only [add_apply, smul_apply, smul_eq_mul] at hsB
    rw [hsB, mul_right_comm, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

end SixProblems
