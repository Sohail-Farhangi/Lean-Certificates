module

public import Mixing.GeneratedFunctional
public import Mixing.GeneratedSigma

/-! # Density from measurable generation -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Mixing

variable {G X : Type*} [CommGroup G] [m : MeasurableSpace X]

namespace System

private theorem hasGeneratedRepresentative_bounded_map_of_image (T : System G X)
    (U : Set (Ultrafilter G)) {p : Ultrafilter G} (f : Lp ℂ 2 T.measure)
    (r : ℂ → ℝ) (hr : Continuous r) (hrBound : ∀ z, |r z| ≤ ‖z‖)
    (hR : ∀ b : BoundedObservable X,
      HasGeneratedRepresentative T U (fun x => (r (T.ultrafilterTranslate p b x) : ℂ)))
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ t, |ψ t| ≤ C) :
    HasGeneratedRepresentative T U
      (fun x => (ψ (r (ultrafilterOperator T.koopmanRep p f x)) : ℂ)) := by
  let Q := ultrafilterOperator T.koopmanRep p
  obtain ⟨u, hu, hULim⟩ := mem_closure_iff_seq_limit.mp
    (BoundedObservable.denseRange_l2 T.measure f)
  choose b hb using hu
  have hBLim : Tendsto (fun n => (b n).l2 T.measure) atTop (𝓝 f) := by
    simpa only [hb] using hULim
  have hQLim : Tendsto (fun n => Q ((b n).l2 T.measure)) atTop (𝓝 (Q f)) :=
    (Q.continuous.tendsto f).comp hBLim
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hQLim).exists_seq_tendsto_ae
  let v (n : ℕ) := T.ultrafilterTranslate p (b (φ n))
  have hReps : ∀ᵐ x ∂T.measure, ∀ n, v n x = Q ((b (φ n)).l2 T.measure) x :=
    ae_all_iff.mpr fun n => T.ultrafilterTranslate_ae p (b (φ n))
  let w : BoundedObservable X :=
    ⟨fun x => ψ (r (Q f x)), Complex.continuous_ofReal.measurable.comp
      (hψ.measurable.comp (hr.measurable.comp (Lp.stronglyMeasurable (Q f)).measurable)),
      C, hC₀, fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC (r (Q f x))⟩
  have hV (n : ℕ) :
      HasGeneratedRepresentative T U (fun x => (ψ (r (v n x)) : ℂ)) :=
    (hR (b (φ n))).continuous_real (hr.measurable.comp (v n).measurable)
      (fun x => (hrBound _).trans ((v n).norm_le x)) ψ hψ hC₀ hC
  have hLim : ∀ᵐ x ∂T.measure,
      Tendsto (fun n => (ψ (r (v n x)) : ℂ)) atTop (𝓝 (w x)) := by
    filter_upwards [hφ, hReps] with x hx hRep
    simp only [hRep]
    exact (Complex.continuous_ofReal.tendsto _).comp ((hψ.tendsto _).comp ((hr.tendsto _).comp hx))
  exact HasGeneratedRepresentative.of_ae_tendsto w hV
    (fun n x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC (r (v n x))) hLim

private def ramp (a : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 ((n : ℝ) * (a - t)))

private theorem continuous_ramp (a : ℝ) (n : ℕ) : Continuous (ramp a n) :=
  continuous_const.max (continuous_const.min (continuous_const.mul (continuous_const.sub continuous_id)))

private theorem abs_ramp_le (a : ℝ) (n : ℕ) (t : ℝ) : |ramp a n t| ≤ 1 := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)

private theorem tendsto_ramp (a t : ℝ) :
    Tendsto (fun n => ((ramp a n t : ℝ) : ℂ)) atTop
      (𝓝 ((Iio a).indicator (fun _ => (1 : ℂ)) t)) := by
  classical
  by_cases ht : t < a
  · have hPos : 0 < a - t := sub_pos.mpr ht
    have hEv : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * (a - t) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_ge_atTop (1 / (a - t))) |>.mono
          fun n hn => (div_le_iff₀ hPos).mp hn
    apply tendsto_const_nhds.congr'
    filter_upwards [hEv] with n hn
    simp [ramp, ht, min_eq_left hn]
  · have hNonpos : a - t ≤ 0 := sub_nonpos.mpr (le_of_not_gt ht)
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n => by
      have hMul : (n : ℝ) * (a - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hNonpos
      simp [ramp, ht, min_eq_right (hMul.trans zero_le_one), max_eq_left hMul]

private noncomputable def indicatorObs (s : Set X) (hs : MeasurableSet s) : BoundedObservable X where
  toFun := s.indicator (fun _ => 1)
  measurable := measurable_const.indicator hs
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    classical
    by_cases h : x ∈ s <;> simp [h]

private theorem hasGeneratedRepresentative_threshold (T : System G X)
    (U : Set (Ultrafilter G)) {p : Ultrafilter G} (f : Lp ℂ 2 T.measure)
    (r : ℂ → ℝ) (hr : Continuous r) (hrBound : ∀ z, |r z| ≤ ‖z‖)
    (hR : ∀ b : BoundedObservable X,
      HasGeneratedRepresentative T U (fun x => (r (T.ultrafilterTranslate p b x) : ℂ)))
    (a : ℝ) : HasGeneratedRepresentative T U
      ((fun x => r (ultrafilterOperator T.koopmanRep p f x)) ⁻¹' Iio a |>.indicator (fun _ => 1)) := by
  let v (x : X) := r (ultrafilterOperator T.koopmanRep p f x)
  let s := v ⁻¹' Iio a
  have hs : MeasurableSet s :=
    (hr.measurable.comp (Lp.stronglyMeasurable _).measurable) measurableSet_Iio
  let w := indicatorObs s hs
  have hRamp (n : ℕ) : HasGeneratedRepresentative T U (fun x => (ramp a n (v x) : ℂ)) :=
    T.hasGeneratedRepresentative_bounded_map_of_image U f r hr hrBound hR
      (ramp a n) (continuous_ramp a n) zero_le_one (abs_ramp_le a n)
  exact HasGeneratedRepresentative.of_ae_tendsto w hRamp
    (fun n x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_ramp_le a n (v x))
    (Eventually.of_forall fun x => tendsto_ramp a (v x))

private def prefixUnion (s : ℕ → Set X) : ℕ → Set X
  | 0 => ∅
  | n + 1 => prefixUnion s n ∪ s n

omit m in
private theorem prefixUnion_mono (s : ℕ → Set X) : Monotone (prefixUnion s) :=
  monotone_nat_of_le_succ (fun _ => subset_union_left)

omit m in
private theorem prefixUnion_subset_iUnion (s : ℕ → Set X) (n : ℕ) :
    prefixUnion s n ⊆ ⋃ i, s i := by
  induction n with
  | zero => exact empty_subset _
  | succ n ih => exact union_subset ih (subset_iUnion s n)

omit m in
private theorem tendsto_indicator_prefixUnion (s : ℕ → Set X) (x : X) :
    Tendsto (fun n => (prefixUnion s n).indicator (fun _ => (1 : ℂ)) x) atTop
      (𝓝 ((⋃ i, s i).indicator (fun _ => 1) x)) := by
  classical
  apply tendsto_const_nhds.congr'
  by_cases h : x ∈ ⋃ i, s i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp h
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    have hmem : x ∈ prefixUnion s n :=
      prefixUnion_mono s hn (mem_union_right _ hi)
    simp [h, hmem]
  · exact Eventually.of_forall fun n => by
      have hn : x ∉ prefixUnion s n := fun hx => h (prefixUnion_subset_iUnion s n hx)
      simp [h, hn]

private theorem generated_indicator_compl (T : System G X) (U : Set (Ultrafilter G))
    {s : Set X} (h : HasGeneratedRepresentative T U (s.indicator (fun _ => 1))) :
    HasGeneratedRepresentative T U (sᶜ.indicator (fun _ => 1)) := by
  classical
  convert (HasGeneratedRepresentative.const 1).sub h using 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

private theorem generated_indicator_union (T : System G X) (U : Set (Ultrafilter G))
    {s t : Set X} (hs : HasGeneratedRepresentative T U (s.indicator (fun _ => 1)))
    (ht : HasGeneratedRepresentative T U (t.indicator (fun _ => 1))) :
    HasGeneratedRepresentative T U ((s ∪ t).indicator (fun _ => 1)) := by
  classical
  have hS := T.generated_indicator_compl U hs
  have hT := T.generated_indicator_compl U ht
  convert (HasGeneratedRepresentative.const 1).sub (hS.mul hT) using 1
  funext x
  by_cases hx : x ∈ s <;> by_cases hy : x ∈ t <;> simp [hx, hy]

/-- The σ-algebra whose measurable sets have indicators in the product span closure. -/
@[instance_reducible]
private def productSigma (T : System G X) (U : Set (Ultrafilter G)) : MeasurableSpace X where
  MeasurableSet' s := MeasurableSet s ∧ HasGeneratedRepresentative T U (s.indicator (fun _ => 1))
  measurableSet_empty := ⟨MeasurableSet.empty, by simpa using
    (HasGeneratedRepresentative.const (T := T) (U := U) 0)⟩
  measurableSet_compl s hs := ⟨hs.1.compl, T.generated_indicator_compl U hs.2⟩
  measurableSet_iUnion s hs := by
    let w := indicatorObs (⋃ n, s n) (MeasurableSet.iUnion fun i => (hs i).1)
    refine ⟨MeasurableSet.iUnion fun i => (hs i).1, ?_⟩
    have hPrefix (n : ℕ) :
        HasGeneratedRepresentative T U ((prefixUnion s n).indicator (fun _ => 1)) := by
      induction n with
      | zero => simpa [prefixUnion] using (HasGeneratedRepresentative.const (T := T) (U := U) 0)
      | succ n ih => exact T.generated_indicator_union U ih (hs n).2
    refine HasGeneratedRepresentative.of_ae_tendsto w hPrefix (C := 1) ?_
      (Eventually.of_forall fun x => tendsto_indicator_prefixUnion s x)
    intro n x
    classical
    by_cases h : x ∈ prefixUnion s n <;> simp [h]

private theorem generatedSigma_le_productSigma (T : System G X) (U : Set (Ultrafilter G)) :
    T.generatedSigma U ≤ T.productSigma U := by
  apply MeasurableSpace.generateFrom_le
  rintro s (⟨hs, hμs⟩ | ⟨p, hp, f, B, hB, rfl⟩)
  · refine ⟨hs, ?_⟩
    apply (HasGeneratedRepresentative.const (T := T) (U := U) 0).ae_eq (indicatorObs s hs)
    have hAE : ∀ᵐ x ∂T.measure, x ∉ s := by
      simpa only [ae_iff, Classical.not_not, Set.ofPred_mem_eq] using hμs
    filter_upwards [hAE] with x hx
    simp [indicatorObs, hx]
  · let v := ultrafilterOperator T.koopmanRep p f
    have hSource : Measurable (v : X → ℂ) := (Lp.stronglyMeasurable v).measurable
    have hRe : @Measurable X ℝ (T.productSigma U) _ (fun x => (v x).re) := by
      apply measurable_of_Iio
      intro a
      exact ⟨(Complex.continuous_re.measurable.comp hSource) measurableSet_Iio,
        T.hasGeneratedRepresentative_threshold U f Complex.re Complex.continuous_re
          Complex.abs_re_le_norm (fun b => T.hasGeneratedRepresentative_ultrafilterTranslate_re U hp b) a⟩
    have hIm : @Measurable X ℝ (T.productSigma U) _ (fun x => (v x).im) := by
      apply measurable_of_Iio
      intro a
      exact ⟨(Complex.continuous_im.measurable.comp hSource) measurableSet_Iio,
        T.hasGeneratedRepresentative_threshold U f Complex.im Complex.continuous_im
          Complex.abs_im_le_norm (fun b => T.hasGeneratedRepresentative_ultrafilterTranslate_im U hp b) a⟩
    have hMeas : @Measurable X ℂ (T.productSigma U) _ v := by
      have he : (fun x => ((v x).re : ℂ) + ((v x).im : ℂ) * Complex.I) = (v : X → ℂ) :=
        funext fun x => Complex.re_add_im (v x)
      rw [← he]
      exact (Complex.continuous_ofReal.measurable.comp hRe).add
        ((Complex.continuous_ofReal.measurable.comp hIm).mul measurable_const)
    exact hMeas hB

/-- Full σ-algebra generation implies L² density of the linear span of the products
of bounded Koopman ultrafilter translates. -/
theorem isUGenerated_of_generatedSigma_eq (T : System G X) (U : Set (Ultrafilter G))
    (hGen : T.generatedSigma U = m) : T.IsUGenerated U := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  change T.generatedProductsClosure U = ⊤
  apply top_unique
  intro v _
  refine Lp.induction (μ := T.measure) (p := 2) (by norm_num)
    (fun v => v ∈ T.generatedProductsClosure U) ?_ ?_ ?_ v
  · intro c s hs hμs
    have hSet := T.generatedSigma_le_productSigma U s (hGen.symm ▸ hs)
    obtain ⟨b, hb, hB⟩ := hSet.2
    let v := Lp.simpleFunc.indicatorConst (E := ℂ) (μ := T.measure) 2 hs hμs.ne c
    have hv := (Lp.simpleFunc.toSimpleFunc_eq_toFun v).symm.trans
      (Lp.simpleFunc.toSimpleFunc_indicatorConst hs hμs.ne c)
    have he : (v : Lp ℂ 2 T.measure) = ((BoundedObservable.const c).mul b).l2 T.measure := by
      apply Lp.ext
      filter_upwards [hv, ((BoundedObservable.const c).mul b).coe_l2 T.measure] with x hx hy
      rw [hx, hy, BoundedObservable.mul_apply, BoundedObservable.const_apply, congrFun hb x]
      classical
      by_cases h : x ∈ s <;> simp [h]
    change (v : Lp ℂ 2 T.measure) ∈ T.generatedProductsClosure U
    rw [he, BoundedObservable.l2_const_mul]
    exact (T.generatedProductsClosure U).smul_mem c hB
  · intro f g hf hg _ hF hG
    exact (T.generatedProductsClosure U).add_mem hF hG
  · exact T.isClosed_generatedProductsClosure U

end System

end Mixing
