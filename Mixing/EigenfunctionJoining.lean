module

public import Mixing.CompactRotations
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Group.Circle

@[expose] public section

noncomputable section

namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ComplexConjugate ENNReal

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- Normalized Haar probability measure on the circle group. -/
def circleHaarProbability : Measure Circle := haarMeasure ⊤

instance : IsHaarMeasure circleHaarProbability := by unfold circleHaarProbability; infer_instance

instance : IsProbabilityMeasure circleHaarProbability := ⟨haarMeasure_self⟩

private theorem circleCoeContinuous : Continuous (fun z : Circle ↦ (z : ℂ)) :=
  continuous_subtype_val

private theorem integral_circleCharacter : (∫ z : Circle, (z : ℂ) ∂circleHaarProbability) = 0 := by
  let u := (-1 : Circle)
  have hp := measurePreserving_mul_left circleHaarProbability u
  have h : (∫ z : Circle, ((u * z : Circle) : ℂ) ∂circleHaarProbability) =
      ∫ z : Circle, (z : ℂ) ∂circleHaarProbability := by
    calc
      _ = ∫ z : Circle, (z : ℂ) ∂circleHaarProbability.map (fun z ↦ u * z) :=
        (integral_map hp.measurable.aemeasurable circleCoeContinuous.aestronglyMeasurable).symm
      _ = _ := by rw [hp.map_eq]
  have he : (fun z : Circle ↦ ((u * z : Circle) : ℂ)) = fun z : Circle ↦ -(z : ℂ) := by
    funext z
    change -(1 : ℂ) * (z : ℂ) = -(z : ℂ)
    simp
  rw [he, integral_neg] at h
  exact (neg_eq_self.mp h)

/-- A bounded nonzero mean-zero eigenfunction gives a non-product joining with
the circle rotation by its eigencharacter. This proof uses a positive density
perturbation, so no ergodicity assumption or pointwise factor representative is needed. -/
theorem not_disjoint_circleRotation_of_bounded_eigenfunction
    (S : System G X) (χ : G →* Circle) (f : BoundedObservable X)
    (hmean : (∫ x, f x ∂S.measure) = 0)
    (hne : ¬ (f : X → ℂ) =ᵐ[S.measure] (fun _ ↦ 0))
    (hχ : ∀ g, ∀ᵐ x ∂S.measure, f (S.act g x) = (χ g : ℂ) * f x) :
    ¬ Disjoint S (compactRotation χ circleHaarProbability) := by
  let ν := circleHaarProbability
  let R := compactRotation χ ν
  let P := S.measure.prod ν
  let c : ℝ := (f.bound + 1)⁻¹
  have hc : 0 < c := inv_pos.mpr (by linarith [f.bound_nonneg])
  let d : X × Circle → ℝ := fun w ↦ 1 + c * (f w.1 * conj (w.2 : ℂ)).re
  let D : X × Circle → ℝ≥0∞ := fun w ↦ ENNReal.ofReal (d w)
  let joining := P.withDensity D
  have hD : Measurable D := by
    have he : Measurable (fun w : X × Circle ↦ f w.1 * conj (w.2 : ℂ)) :=
      (f.measurable.comp measurable_fst).mul (Complex.continuous_conj.measurable.comp
        (Circle.measurable_coe.comp measurable_snd))
    exact (measurable_const.add (measurable_const.mul (Complex.continuous_re.measurable.comp he))).ennreal_ofReal
  have hdnonneg (w : X × Circle) : 0 ≤ d w := by
    have hn : ‖f w.1 * conj (w.2 : ℂ)‖ ≤ f.bound := by
      rw [norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
      exact f.norm_le w.1
    have hlow : -f.bound ≤ (f w.1 * conj (w.2 : ℂ)).re :=
      (neg_le_neg hn).trans ((neg_le_neg (Complex.abs_re_le_norm _)).trans (neg_abs_le _))
    have hp : c * f.bound ≤ 1 := by
      rw [show c = 1 / (f.bound + 1) by simp [c], div_mul_eq_mul_div, one_mul,
        div_le_one (by linarith [f.bound_nonneg])]
      linarith
    change 0 ≤ 1 + c * (f w.1 * conj (w.2 : ℂ)).re
    linarith [mul_le_mul_of_nonneg_left hlow hc.le]
  have hcol (x : X) : ∫⁻ z, D (x, z) ∂ν = 1 := by
    let u : Circle → ℂ := fun z ↦ f x * conj (z : ℂ)
    have hu : Integrable u ν := by
      have huc : Continuous u := continuous_const.mul (Complex.continuous_conj.comp circleCoeContinuous)
      exact huc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hmean' : ∫ z, u z ∂ν = 0 := by
      change (∫ z : Circle, f x * conj (z : ℂ) ∂ν) = 0
      rw [integral_const_mul, integral_conj, integral_circleCharacter, map_zero, mul_zero]
    have hdInt : Integrable (fun z ↦ d (x, z)) ν := (integrable_const _).add (hu.re.const_mul c)
    rw [← ofReal_integral_eq_lintegral_ofReal hdInt (ae_of_all _ fun z ↦ hdnonneg (x, z))]
    change ENNReal.ofReal (∫ z, 1 + c * RCLike.re (u z) ∂ν) = 1
    rw [integral_add (integrable_const _) (hu.re.const_mul c),
      integral_const_mul, integral_re hu, hmean']
    simp [measureReal_def]
  have hrow (z : Circle) : ∫⁻ x, D (x, z) ∂S.measure = 1 := by
    let u : X → ℂ := fun x ↦ f x * conj (z : ℂ)
    have hu : Integrable u S.measure := (f.integrable _).mul_const _
    have hmean' : ∫ x, u x ∂S.measure = 0 := by
      change (∫ x, f x * conj (z : ℂ) ∂S.measure) = 0
      rw [integral_mul_const, hmean, zero_mul]
    have hdInt : Integrable (fun x ↦ d (x, z)) S.measure := (integrable_const _).add (hu.re.const_mul c)
    rw [← ofReal_integral_eq_lintegral_ofReal hdInt (ae_of_all _ fun x ↦ hdnonneg (x, z))]
    change ENNReal.ofReal (∫ x, 1 + c * RCLike.re (u x) ∂S.measure) = 1
    rw [integral_add (integrable_const _) (hu.re.const_mul c),
      integral_const_mul, integral_re hu, hmean']
    simp [measureReal_def]
  have hfst : MeasurePreserving Prod.fst joining S.measure := by
    refine ⟨measurable_fst, ?_⟩
    ext A hA
    rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (measurable_fst hA),
      ← lintegral_indicator (measurable_fst hA),
      lintegral_prod _ (hD.indicator (measurable_fst hA)).aemeasurable]
    have he (x : X) : (∫⁻ z, (Prod.fst ⁻¹' A).indicator D (x, z) ∂ν) =
        A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
      by_cases hx : x ∈ A
      · simpa [Set.indicator, hx] using hcol x
      · simp [hx]
    simp_rw [he]
    rw [lintegral_indicator_const hA, one_mul]
  have hsnd : MeasurePreserving Prod.snd joining ν := by
    refine ⟨measurable_snd, ?_⟩
    ext B hB
    rw [Measure.map_apply measurable_snd hB, withDensity_apply _ (measurable_snd hB),
      ← lintegral_indicator (measurable_snd hB),
      lintegral_prod_symm _ (hD.indicator (measurable_snd hB)).aemeasurable]
    have he (z : Circle) : (∫⁻ x, (Prod.snd ⁻¹' B).indicator D (x, z) ∂S.measure) =
        B.indicator (fun _ ↦ (1 : ℝ≥0∞)) z := by
      by_cases hz : z ∈ B
      · simpa [Set.indicator, hz] using hrow z
      · simp [hz]
    simp_rw [he]
    rw [lintegral_indicator_const hB, one_mul]
  have hprob : IsProbabilityMeasure joining :=
    (Measure.isProbabilityMeasure_map_iff hfst.aemeasurable).mp (hfst.map_eq.symm ▸ inferInstance)
  have hpres (g : G) : MeasurePreserving (S.prodAct R g) joining joining := by
    have hp : MeasurePreserving (S.prodAct R g) P P := (product_isJoining S R).invariant g
    have hfix : D ∘ S.prodAct R g =ᵐ[P] D := by
      filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae (hχ g)] with w hw
      have he : (χ g : ℂ) * conj (χ g : ℂ) = 1 := by
        rw [Complex.mul_conj, ← Complex.sq_norm, Circle.norm_coe, one_pow, Complex.ofReal_one]
      change ENNReal.ofReal (1 + c * (f (S.act g w.1) * conj ((χ g : ℂ) * (w.2 : ℂ))).re) = _
      rw [hw, map_mul]
      have hm : (χ g : ℂ) * f w.1 * (conj (χ g : ℂ) * conj (w.2 : ℂ)) =
          ((χ g : ℂ) * conj (χ g : ℂ)) * (f w.1 * conj (w.2 : ℂ)) := by ac_rfl
      rw [hm, he, one_mul]
    refine ⟨hp.measurable, ?_⟩
    ext A hA
    rw [Measure.map_apply hp.measurable hA, withDensity_apply _ (hp.measurable hA),
      withDensity_apply _ hA, ← lintegral_indicator (hp.measurable hA),
      ← lintegral_indicator hA, ← hp.lintegral_comp (hD.indicator hA)]
    apply lintegral_congr_ae
    filter_upwards [hfix] with w hw
    by_cases hmem : S.prodAct R g w ∈ A
    · simpa [Set.indicator, Function.comp_def, hmem] using hw.symm
    · simp [hmem]
  intro hdis
  have he := hdis joining ⟨hprob, hfst, hsnd, hpres⟩
  change P.withDensity D = P at he
  have hD' : D =ᵐ[P] (fun _ ↦ 1) := by
    apply (withDensity_eq_iff_of_sigmaFinite hD.aemeasurable measurable_const.aemeasurable).mp
    rw [he]
    exact (withDensity_one (μ := P)).symm
  apply hne
  filter_upwards [Measure.ae_ae_of_ae_prod hD'] with x hx
  have hz : (fun z : Circle ↦ (f x * conj (z : ℂ)).re) =ᵐ[ν] fun _ ↦ 0 := by
    filter_upwards [hx] with z hz
    change ENNReal.ofReal (d (x, z)) = 1 at hz
    have hr := congrArg ENNReal.toReal hz
    rw [ENNReal.toReal_ofReal (hdnonneg _), ENNReal.toReal_one] at hr
    change 1 + c * (f x * conj (z : ℂ)).re = 1 at hr
    exact (mul_eq_zero.mp (by linarith : c * (f x * conj (z : ℂ)).re = 0)).resolve_left hc.ne'
  let : ν.IsOpenPosMeasure := inferInstanceAs (circleHaarProbability.IsOpenPosMeasure)
  have hzero : (fun z : Circle ↦ (f x * conj (z : ℂ)).re) = fun _ ↦ 0 :=
    Measure.eq_of_ae_eq hz (Complex.continuous_re.comp
      (continuous_const.mul (Complex.continuous_conj.comp circleCoeContinuous))) continuous_const
  have hRe := congrFun hzero (1 : Circle)
  let i : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩
  have hIm := congrFun hzero i
  apply Complex.ext
  · simpa using hRe
  · simpa [i, Complex.mul_re] using hIm

end Mixing
