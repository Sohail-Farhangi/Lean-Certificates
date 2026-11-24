module

public import Mixing.JoiningCorrelation
public import Mixing.Koopman
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # Bounded observables and weak Koopman limits -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Topology

namespace Mixing

variable {G X A : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace A]

private def aeNormBounded (μ : Measure X) (C : ℝ) : Set (Lp ℂ 2 μ) :=
  {f | ∀ᵐ x ∂μ, ‖f x‖ ≤ C}

private theorem convex_aeNormBounded (μ : Measure X) (C : ℝ) :
    Convex ℝ (aeNormBounded μ C) := by
  intro f hf g hg a b ha hb hab
  change ∀ᵐ x ∂μ, ‖(a • f + b • g : Lp ℂ 2 μ) x‖ ≤ C
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hfx hgx hAdd hAf hBg
  change ‖f x‖ ≤ C at hfx
  change ‖g x‖ ≤ C at hgx
  rw [hAdd, Pi.add_apply, hAf, hBg, Pi.smul_apply, Pi.smul_apply]
  calc
    _ ≤ ‖a • f x‖ + ‖b • g x‖ := norm_add_le _ _
    _ = a * ‖f x‖ + b * ‖g x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * C + b * C :=
      add_le_add (mul_le_mul_of_nonneg_left hfx ha) (mul_le_mul_of_nonneg_left hgx hb)
    _ = C := by rw [← add_mul, hab, one_mul]

private theorem isClosed_aeNormBounded (μ : Measure X) (C : ℝ) :
    IsClosed (aeNormBounded μ C) := by
  apply IsSeqClosed.isClosed
  intro f v hf hv
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hAll : ∀ᵐ x ∂μ, ∀ n, ‖f n x‖ ≤ C := ae_all_iff.mpr hf
  change ∀ᵐ x ∂μ, ‖v x‖ ≤ C
  filter_upwards [hφ, hAll] with x hLim hBound
  exact le_of_tendsto' hLim.norm fun n => hBound (φ n)

namespace BoundedObservable

/-- Clip a measurable L² representative to obtain a pointwise bounded version. -/
noncomputable def ofLp {μ : Measure X} {q : ENNReal} (f : Lp ℂ q μ) (C : ℝ) (hC : 0 ≤ C) :
    BoundedObservable X where
  toFun x := if ‖f x‖ ≤ C then f x else 0
  measurable := Measurable.ite
    (measurableSet_le (Lp.stronglyMeasurable f).measurable.norm measurable_const)
      (Lp.stronglyMeasurable f).measurable measurable_const
  bound := C
  bound_nonneg := hC
  norm_le x := by split_ifs with h <;> simpa

theorem ofLp_ae {μ : Measure X} {q : ENNReal} (f : Lp ℂ q μ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    BoundedObservable.ofLp f C hC =ᵐ[μ] f := by
  filter_upwards [h] with x hx
  exact ite_eq_left hx

theorem l2_ofLp {μ : Measure X} [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    (BoundedObservable.ofLp f C hC).l2 μ = f := by
  apply Lp.ext
  exact ((BoundedObservable.ofLp f C hC).coe_l2 μ).trans (ofLp_ae f C hC h)

/-- A pointwise bounded representative of an arbitrary L∞ class. -/
noncomputable def ofLInf {μ : Measure X} (f : Lp ℂ ⊤ μ) : BoundedObservable X :=
  ofLp f (lpNorm f ⊤ μ) lpNorm_nonneg

theorem ofLInf_ae {μ : Measure X} (f : Lp ℂ ⊤ μ) : ofLInf f =ᵐ[μ] f :=
  ofLp_ae f _ _ (ae_le_lpNorm_exponent_top (Lp.memLp f))

private noncomputable def ofSimpleFunc (f : SimpleFunc X ℂ) : BoundedObservable X where
  toFun := f
  measurable := f.measurable
  bound := ∑ c ∈ f.range, ‖c‖
  bound_nonneg := Finset.sum_nonneg (fun c _ => norm_nonneg c)
  norm_le x := Finset.single_le_sum (fun c _ => norm_nonneg c) (f.mem_range_self x)

/-- Bounded measurable observables are dense in L² on a finite measure space. -/
theorem denseRange_l2 (μ : Measure X) [IsFiniteMeasure μ] :
    DenseRange (fun f : BoundedObservable X => f.l2 μ) := by
  have h : Dense (range (fun f : Lp.simpleFunc ℂ 2 μ => (f : Lp ℂ 2 μ))) :=
    Lp.simpleFunc.denseRange (by norm_num)
  apply h.mono
  rintro _ ⟨f, rfl⟩
  refine ⟨ofSimpleFunc (Lp.simpleFunc.toSimpleFunc f), ?_⟩
  apply Lp.ext
  exact ((ofSimpleFunc (Lp.simpleFunc.toSimpleFunc f)).coe_l2 μ).trans
    (Lp.simpleFunc.toSimpleFunc_eq_toFun f)

end BoundedObservable

namespace System

/-- The translated observable represents the Koopman vector. -/
theorem koopman_ae_observable (T : System G X) (g : G) (f : BoundedObservable X) :
    T.koopmanRep g (f.l2 T.measure) =ᵐ[T.measure] T.translated g f := by
  exact (Lp.coeFn_compMeasurePreserving (f.l2 T.measure) (T.preserves g)).trans
    ((T.preserves g).quasiMeasurePreserving.ae_eq_comp (f.coe_l2 T.measure))

/-- Weak Koopman limits preserve the essential uniform bound. -/
theorem ultrafilterOperator_ae_bound (T : System G X) (p : Ultrafilter G)
    (f : BoundedObservable X) :
    ∀ᵐ x ∂T.measure, ‖ultrafilterOperator T.koopmanRep p (f.l2 T.measure) x‖ ≤ f.bound := by
  let C := aeNormBounded T.measure f.bound
  have hC : IsClosed ((toWeakSpace ℂ (Lp ℂ 2 T.measure)) '' C) := by
    have h := (convex_aeNormBounded T.measure f.bound).toWeakSpace_closure ℂ
    rw [(isClosed_aeNormBounded T.measure f.bound).closure_eq] at h
    rw [h]
    exact isClosed_closure
  have hlim := tendsto_weakSpace_of_tendsto_inner
    (fun z => tendsto_ultrafilterOperator_coeff T.koopmanRep p z (f.l2 T.measure))
  have hMem := hC.mem_of_tendsto hlim (Eventually.of_forall fun g => by
    refine ⟨_, ?_, rfl⟩
    change ∀ᵐ x ∂T.measure, ‖T.koopmanRep g (f.l2 T.measure) x‖ ≤ f.bound
    filter_upwards [T.koopman_ae_observable g f] with x hx
    rw [hx]
    exact f.norm_le _)
  obtain ⟨v, hv, heq⟩ := hMem
  exact (toWeakSpace ℂ (Lp ℂ 2 T.measure)).injective heq ▸ hv

/-- A bounded representative of the weak Koopman limit, written Tᵖf in the paper. -/
noncomputable def ultrafilterTranslate (T : System G X) (p : Ultrafilter G)
    (f : BoundedObservable X) : BoundedObservable X :=
  BoundedObservable.ofLp (ultrafilterOperator T.koopmanRep p (f.l2 T.measure))
    f.bound f.bound_nonneg

theorem ultrafilterTranslate_ae (T : System G X) (p : Ultrafilter G)
    (f : BoundedObservable X) :
    T.ultrafilterTranslate p f =ᵐ[T.measure] ultrafilterOperator T.koopmanRep p (f.l2 T.measure) :=
  BoundedObservable.ofLp_ae _ _ _ (T.ultrafilterOperator_ae_bound p f)

theorem l2_ultrafilterTranslate (T : System G X) (p : Ultrafilter G)
    (f : BoundedObservable X) :
    (T.ultrafilterTranslate p f).l2 T.measure = ultrafilterOperator T.koopmanRep p (f.l2 T.measure) :=
  BoundedObservable.l2_ofLp _ _ _ (T.ultrafilterOperator_ae_bound p f)

/-- Pairing with a pulled-back observable gives the associated weighted integral. -/
theorem inner_pullback_observable
    {μ : Measure A} {ν : Measure X} [IsFiniteMeasure μ]
    {π : A → X} (hπ : MeasurePreserving π μ ν)
    (B : BoundedObservable A) (f : BoundedObservable X)
    {v : Lp ℂ 2 ν} (hv : v =ᵐ[ν] f) :
    inner ℂ (B.conjugate.l2 μ) (Lp.compMeasurePreserving π hπ v) =
      ∫ a, B a * f (π a) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [B.conjugate.coe_l2 μ, Lp.coeFn_compMeasurePreserving v hπ,
    hπ.quasiMeasurePreserving.ae_eq_comp hv] with a hB hp hf
  rw [hB, hp]
  change inner ℂ (B.conjugate a) (v (π a)) = _
  rw [show v (π a) = f (π a) from hf]
  simp only [RCLike.inner_apply', BoundedObservable.conjugate_apply]
  exact congrArg (· * f (π a)) (starRingEnd_self_apply (B a))

/-- A weak Koopman limit can be taken inside a joining integral with a fixed bounded factor. -/
theorem tendsto_integral_mul_translated (T : System G X)
    {μ : Measure A} [IsFiniteMeasure μ] {π : A → X}
    (hπ : MeasurePreserving π μ T.measure)
    (B : BoundedObservable A) (p : Ultrafilter G) (f : BoundedObservable X) :
    Tendsto (fun g => ∫ a, B a * f (T.act g (π a)) ∂μ) (p : Filter G)
      (𝓝 (∫ a, B a * T.ultrafilterTranslate p f (π a) ∂μ)) := by
  let d : Lp ℂ 2 T.measure →L[ℂ] Lp ℂ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℂ π hπ).toContinuousLinearMap
  have h := tendsto_ultrafilterOperator_coeff T.koopmanRep p
    (d.adjoint (B.conjugate.l2 μ)) (f.l2 T.measure)
  simp only [ContinuousLinearMap.adjoint_inner_left] at h
  have hTranslate (g : G) :
      inner ℂ (B.conjugate.l2 μ) (d (T.koopmanRep g (f.l2 T.measure))) =
        ∫ a, B a * f (T.act g (π a)) ∂μ :=
    inner_pullback_observable hπ B (T.translated g f) (T.koopman_ae_observable g f)
  have hLimit :
      inner ℂ (B.conjugate.l2 μ) (d (ultrafilterOperator T.koopmanRep p (f.l2 T.measure))) =
        ∫ a, B a * T.ultrafilterTranslate p f (π a) ∂μ :=
    inner_pullback_observable hπ B (T.ultrafilterTranslate p f)
      (T.ultrafilterTranslate_ae p f).symm
  simpa only [hTranslate, hLimit] using h

/-- Complex conjugation commutes with the weak Koopman limits, up to null sets. -/
theorem ultrafilterTranslate_conjugate_ae (T : System G X) (p : Ultrafilter G)
    (f : BoundedObservable X) :
    T.ultrafilterTranslate p f.conjugate =ᵐ[T.measure]
      (T.ultrafilterTranslate p f).conjugate := by
  let u := T.ultrafilterTranslate p f.conjugate
  let v := (T.ultrafilterTranslate p f).conjugate
  have hTest (B : BoundedObservable X) :
      (∫ x, B x * u x ∂T.measure) = ∫ x, B x * v x ∂T.measure := by
    have h₁ := T.tendsto_integral_mul_translated (MeasurePreserving.id T.measure) B p f.conjugate
    have h₂ := T.tendsto_integral_mul_translated (MeasurePreserving.id T.measure) B.conjugate p f
    have hAct (g : G) :
        conj (∫ x, B.conjugate x * f (T.act g x) ∂T.measure) =
          ∫ x, B x * f.conjugate (T.act g x) ∂T.measure := by
      rw [← integral_conj]
      simp only [BoundedObservable.conjugate_apply, map_mul, starRingEnd_self_apply]
    have hLim :
        conj (∫ x, B.conjugate x * T.ultrafilterTranslate p f x ∂T.measure) =
          ∫ x, B x * v x ∂T.measure := by
      rw [← integral_conj]
      simp only [v, BoundedObservable.conjugate_apply, map_mul, starRingEnd_self_apply]
    exact tendsto_nhds_unique h₁ (by
      simpa only [Function.comp_def, id_eq, hAct, hLim] using
        (Complex.continuous_conj.tendsto _).comp h₂)
  let D := u.sub v
  have hu : Integrable (fun x => D.conjugate x * u x) T.measure :=
    (D.conjugate.mul u).integrable _
  have hv : Integrable (fun x => D.conjugate x * v x) T.measure :=
    (D.conjugate.mul v).integrable _
  have hInner : inner ℂ (D.l2 T.measure) (D.l2 T.measure) = 0 := by
    rw [D.inner_l2]
    change (∫ x, D.conjugate x * (u x - v x) ∂T.measure) = 0
    simp_rw [mul_sub]
    rw [integral_sub hu hv, hTest D.conjugate, sub_self]
  have hz : D.l2 T.measure = 0 := inner_self_eq_zero.mp hInner
  have hD := D.coe_l2 T.measure
  rw [hz] at hD
  filter_upwards [hD, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := T.measure)] with x hx hzero
  exact sub_eq_zero.mp (hx.symm.trans hzero)

/-- Successive weak limits of the separate translate variables in a finite product. -/
theorem tendsto_integral_prod_translated (T : System G X)
    {μ : Measure A} [IsFiniteMeasure μ] {π : A → X}
    (hπ : MeasurePreserving π μ T.measure)
    {n : ℕ} (p : Fin n → Ultrafilter G) (f : Fin n → BoundedObservable X)
    (B : BoundedObservable A) :
    Tendsto (fun g : Fin n → G => ∫ a, B a * (∏ i, f i (T.act (g i) (π a))) ∂μ)
      (coordinateUltrafilter p : Filter _)
      (𝓝 (∫ a, B a * (∏ i, T.ultrafilterTranslate (p i) (f i) (π a)) ∂μ)) := by
  induction n generalizing B with
  | zero => simp
  | succ n ih =>
    let Bnext (g : G) := B.mul ((T.translated g (f 0)).comp π hπ.measurable)
    let Bouter := B.mul (BoundedObservable.prod Finset.univ (fun i : Fin n =>
      (T.ultrafilterTranslate (p i.succ) (f i.succ)).comp π hπ.measurable))
    have hInner (g₀ : G) := ih (Fin.tail p) (Fin.tail f) (Bnext g₀)
    have hOuter := T.tendsto_integral_mul_translated hπ Bouter (p 0) (f 0)
    have hInside (g₀ : G) :
        (∫ a, Bnext g₀ a *
          (∏ i : Fin n, T.ultrafilterTranslate (p i.succ) (f i.succ) (π a)) ∂μ) =
        ∫ a, Bouter a * f 0 (T.act g₀ (π a)) ∂μ := by
      apply integral_congr_ae
      refine Eventually.of_forall fun a => ?_
      simp only [Bnext, Bouter, BoundedObservable.mul_apply, BoundedObservable.comp_apply,
        BoundedObservable.prod_apply, System.translated_apply]
      ring
    have hInner' (g₀ : G) :
        Tendsto (fun g : Fin n → G => ∫ a, Bnext g₀ a *
          (∏ i : Fin n, f i.succ (T.act (g i) (π a))) ∂μ) (coordinateUltrafilter (Fin.tail p) : Filter _)
          (𝓝 (∫ a, Bouter a * f 0 (T.act g₀ (π a)) ∂μ)) := by
      simpa only [Fin.tail, hInside] using hInner g₀
    have h := tendsto_fubiniUltrafilter (f := fun v : G × (Fin n → G) =>
      ∫ a, Bnext v.1 a * (∏ i : Fin n, f i.succ (T.act (v.2 i) (π a))) ∂μ) hInner' hOuter
    rw [coordinateUltrafilter, Ultrafilter.coe_map, tendsto_map'_iff]
    have hTail : Fin.tail p = fun i : Fin n => p i.succ := rfl
    simpa only [Bnext, Bouter, BoundedObservable.mul_apply, BoundedObservable.comp_apply,
      BoundedObservable.prod_apply, System.translated_apply, Function.comp_def,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hTail, mul_left_comm, mul_comm, mul_assoc] using h

end System

section Lemma11

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/-- Lemma 11, equation (25). The ultrafilter translates are bounded representatives of
the weak Koopman limits, and the mixing hypothesis is expressed in terms of bounded
observable correlations. -/
theorem integral_prod_ultrafilterTranslate_joining
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    {U : Set (Ultrafilter G)} (hMix : HasMixingCorrelations R U) (hDisjoint : Disjoint S R)
    {n : ℕ} (p : Fin n → Ultrafilter G) (hp : ∀ i, p i ∈ U)
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z) :
    (∫ w, H w.2 * F w.1.2 * (∏ i, T.ultrafilterTranslate (p i) (f i) w.1.1) ∂τ) =
      (∫ w, F w.2 * (∏ i, T.ultrafilterTranslate (p i) (f i) w.1) ∂σ) *
        ∫ z, H z ∂R.measure := by
  let := hσ.probability
  let := hτ.probability
  let B := (H.comp Prod.snd (measurable_snd (α := X × Y))).mul
    (F.comp (fun w : (X × Y) × Z => w.1.2) (measurable_snd.comp measurable_fst))
  have h₃ : Tendsto (joiningCorrelation₃ T τ f F H) (coordinateUltrafilter p : Filter _)
      (𝓝 (∫ w, H w.2 * F w.1.2 * (∏ i, T.ultrafilterTranslate (p i) (f i) w.1.1) ∂τ)) := by
    convert T.tendsto_integral_prod_translated (hσ.fst.comp hτ.fst) p f B using 1
    · funext g
      simp only [joiningCorrelation₃, B, BoundedObservable.mul_apply, BoundedObservable.comp_apply,
        Function.comp_def, mul_left_comm, mul_comm, mul_assoc]
    · rfl
  let B' := F.comp Prod.snd (measurable_snd (α := X))
  have h₂ : Tendsto (joiningCorrelation T σ f F) (coordinateUltrafilter p : Filter _)
      (𝓝 (∫ w, F w.2 * (∏ i, T.ultrafilterTranslate (p i) (f i) w.1) ∂σ)) := by
    convert T.tendsto_integral_prod_translated hσ.fst p f B' using 1
    · funext g
      simp only [joiningCorrelation, B', BoundedObservable.comp_apply, mul_comm]
    · rfl
  have hFactor := tendsto_joiningCorrelation₃ hτ hMix hDisjoint p hp f F H
  exact tendsto_nhds_unique h₃ (by simpa only [scalarUltralimit, h₂.limUnder_eq] using hFactor)

end Lemma11

end Mixing
