module

public import Mixing.BoundedKoopman
public import Mixing.SystemMixing

/-! # The multiplier theorem from the finite-product density criterion -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Mixing

variable {G X Y Z : Type*} [CommGroup G]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Lemma 11 for arbitrary L∞ classes. The occurrences of L∞ functions in the displayed
integrals use their bounded measurable representatives. -/
theorem lemma11
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    {U : Set (Ultrafilter G)} (hMix : R.IsUMixing U) (hDisjoint : Disjoint S R)
    {n : ℕ} (p : Fin n → Ultrafilter G) (hp : ∀ i, p i ∈ U)
    (f : Fin n → Lp ℂ ⊤ T.measure) (F : Lp ℂ ⊤ S.measure) (H : Lp ℂ ⊤ R.measure) :
    (∫ w, BoundedObservable.ofLInf H w.2 * BoundedObservable.ofLInf F w.1.2 *
        (∏ i, T.ultrafilterTranslate (p i) (BoundedObservable.ofLInf (f i)) w.1.1) ∂τ) =
      (∫ w, BoundedObservable.ofLInf F w.2 *
        (∏ i, T.ultrafilterTranslate (p i) (BoundedObservable.ofLInf (f i)) w.1) ∂σ) *
        ∫ z, BoundedObservable.ofLInf H z ∂R.measure :=
  integral_prod_ultrafilterTranslate_joining hτ (System.hasMixingCorrelations hMix) hDisjoint p hp
    (fun i => BoundedObservable.ofLInf (f i)) (BoundedObservable.ofLInf F)
      (BoundedObservable.ofLInf H)

namespace System

/-- A finite product of ultrafilter translates of bounded observables. -/
noncomputable def ultrafilterProduct (T : System G X) {n : ℕ}
    (p : Fin n → Ultrafilter G) (f : Fin n → BoundedObservable X) :
    BoundedObservable X :=
  BoundedObservable.prod Finset.univ (fun i => T.ultrafilterTranslate (p i) (f i))

/-- The finite products attached to a family of ultrafilters, viewed in complex L². -/
def generatedProducts (T : System G X) (U : Set (Ultrafilter G)) :
    Set (Lp ℂ 2 T.measure) :=
  {v | ∃ (n : ℕ) (p : Fin n → Ultrafilter G) (f : Fin n → BoundedObservable X),
    (∀ i, p i ∈ U) ∧ v = (T.ultrafilterProduct p f).l2 T.measure}

/-- The L² density formulation of U-generation by finite products. -/
def IsUGenerated (T : System G X) (U : Set (Ultrafilter G)) : Prop :=
  Dense (Submodule.span ℂ (T.generatedProducts U) : Set (Lp ℂ 2 T.measure))

/-- Hilbert generation of the full Koopman representation implies generation by
products of bounded observables. Single-factor products already have dense span. -/
theorem isUGenerated_of_koopmanIsUGenerated (T : System G X) (U : Set (Ultrafilter G))
    (hGen : Mixing.IsUGenerated T.koopmanRep U) : T.IsUGenerated U := by
  let M := (Submodule.span ℂ (T.generatedProducts U)).topologicalClosure
  have hM : IsClosed (M : Set (Lp ℂ 2 T.measure)) :=
    (Submodule.span ℂ (T.generatedProducts U)).isClosed_topologicalClosure
  have hProduct (p : Ultrafilter G) (hp : p ∈ U) (f : BoundedObservable X) :
      ultrafilterOperator T.koopmanRep p (f.l2 T.measure) ∈ T.generatedProducts U := by
    refine ⟨1, fun _ => p, fun _ => f, fun _ => hp, ?_⟩
    rw [← T.l2_ultrafilterTranslate p f]
    apply Lp.ext
    filter_upwards [(T.ultrafilterTranslate p f).coe_l2 T.measure,
      (T.ultrafilterProduct (fun _ : Fin 1 => p) (fun _ => f)).coe_l2 T.measure] with x h₁ h₂
    rw [h₁, h₂]
    simp [ultrafilterProduct]
  have hRange (p : Ultrafilter G) (hp : p ∈ U) (v : Lp ℂ 2 T.measure) :
      ultrafilterOperator T.koopmanRep p v ∈ M := by
    let Q := ultrafilterOperator T.koopmanRep p
    have hDense : Dense (range (fun f : BoundedObservable X => f.l2 T.measure)) :=
      BoundedObservable.denseRange_l2 T.measure
    have hR : range (fun f : BoundedObservable X => f.l2 T.measure) ⊆ Q ⁻¹' (M : Set _) := by
      rintro _ ⟨f, rfl⟩
      exact (Submodule.span ℂ (T.generatedProducts U)).le_topologicalClosure
        (Submodule.subset_span (hProduct p hp f))
    have hAll := closure_minimal hR (hM.preimage Q.continuous)
    rw [hDense.closure_eq] at hAll
    exact hAll (Set.mem_univ v)
  have hSpan :
      Submodule.span ℂ (⋃ p : U, ((ultrafilterOperator T.koopmanRep p).range :
        Set (Lp ℂ 2 T.measure))) ≤ M := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_iUnion.mp hv with ⟨p, w, rfl⟩
    exact hRange p p.property w
  have hTop := Submodule.topologicalClosure_minimal _ hSpan hM
  change _ = ⊤ at hGen
  rw [hGen] at hTop
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (top_unique hTop)

end System

private theorem joining_integral_factorization_of_generated
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    {U : Set (Ultrafilter G)} (hGen : T.IsUGenerated U)
    (hMix : HasMixingCorrelations R U) (hDisjoint : Disjoint S R)
    (f : BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z) :
    (∫ w, H w.2 * F w.1.2 * f w.1.1 ∂τ) =
      (∫ w, F w.2 * f w.1 ∂σ) * ∫ z, H z ∂R.measure := by
  let := hσ.probability
  let := hτ.probability
  let W₃ := (H.comp Prod.snd (measurable_snd (α := X × Y))).mul
    (F.comp (fun w : (X × Y) × Z => w.1.2) (measurable_snd.comp measurable_fst))
  let W₂ := F.comp Prod.snd (measurable_snd (α := X))
  let d₃ : Lp ℂ 2 T.measure →L[ℂ] Lp ℂ 2 τ :=
    (Lp.compMeasurePreservingₗᵢ ℂ _ (hσ.fst.comp hτ.fst)).toContinuousLinearMap
  let d₂ : Lp ℂ 2 T.measure →L[ℂ] Lp ℂ 2 σ :=
    (Lp.compMeasurePreservingₗᵢ ℂ _ hσ.fst).toContinuousLinearMap
  let v₃ := d₃.adjoint (W₃.conjugate.l2 τ)
  let v₂ := d₂.adjoint (W₂.conjugate.l2 σ)
  let c := ∫ z, H z ∂R.measure
  let Ψ : Lp ℂ 2 T.measure →L[ℂ] ℂ := InnerProductSpace.toDual ℂ _ v₃ -
    c • InnerProductSpace.toDual ℂ _ v₂
  have hEval (b : BoundedObservable X) :
      Ψ (b.l2 T.measure) =
        (∫ w, H w.2 * F w.1.2 * b w.1.1 ∂τ) - (∫ w, F w.2 * b w.1 ∂σ) * c := by
    change inner ℂ v₃ (b.l2 T.measure) - c * inner ℂ v₂ (b.l2 T.measure) = _
    rw [show v₃ = d₃.adjoint (W₃.conjugate.l2 τ) from rfl,
      show v₂ = d₂.adjoint (W₂.conjugate.l2 σ) from rfl,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    have h₃ := System.inner_pullback_observable (hσ.fst.comp hτ.fst) W₃ b (b.coe_l2 T.measure)
    have h₂ := System.inner_pullback_observable hσ.fst W₂ b (b.coe_l2 T.measure)
    change inner ℂ (W₃.conjugate.l2 τ) (d₃ (b.l2 T.measure)) = _ at h₃
    change inner ℂ (W₂.conjugate.l2 σ) (d₂ (b.l2 T.measure)) = _ at h₂
    rw [h₃, h₂, mul_comm c]
    rfl
  have hSpan : Submodule.span ℂ (T.generatedProducts U) ≤ Ψ.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, p, obs, hp, rfl⟩
    change Ψ ((T.ultrafilterProduct p obs).l2 T.measure) = 0
    rw [hEval]
    apply sub_eq_zero.mpr
    exact integral_prod_ultrafilterTranslate_joining hτ hMix hDisjoint p hp obs F H
  have hKer : IsClosed (Ψ.ker : Set (Lp ℂ 2 T.measure)) := Ψ.isClosed_ker
  have hClosed := closure_minimal (show
    (Submodule.span ℂ (T.generatedProducts U) : Set (Lp ℂ 2 T.measure)) ⊆ _ from hSpan) hKer
  have hDense : Dense (Submodule.span ℂ (T.generatedProducts U) : Set (Lp ℂ 2 T.measure)) := hGen
  rw [hDense.closure_eq] at hClosed
  have hZero : Ψ (f.l2 T.measure) = 0 := hClosed (Set.mem_univ _)
  rw [hEval] at hZero
  exact sub_eq_zero.mp hZero

private noncomputable def indicatorOne {B : Type*} [MeasurableSpace B]
    (s : Set B) (hs : MeasurableSet s) : BoundedObservable B where
  toFun := s.indicator (fun _ => 1)
  measurable := measurable_const.indicator hs
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    classical
    by_cases hx : x ∈ s <;> simp [hx]

/-- Triple products of bounded observables determine whether a joining is the product. -/
theorem joining_eq_prod_of_integrals {σ : Measure (X × Y)} {ρ : Measure Z}
    {τ : Measure ((X × Y) × Z)} [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure τ]
    (h : ∀ (f : BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z),
      (∫ w, H w.2 * F w.1.2 * f w.1.1 ∂τ) =
        (∫ w, F w.2 * f w.1 ∂σ) * ∫ z, H z ∂ρ) :
    τ = σ.prod ρ := by
  apply Measure.ext_prod₃_iff'.2
  intro s t u hs ht hu
  classical
  have hId₃ :
      (fun w : (X × Y) × Z => indicatorOne u hu w.2 *
        indicatorOne t ht w.1.2 * indicatorOne s hs w.1.1) =
      ((s ×ˢ t) ×ˢ u).indicator (fun _ => (1 : ℂ)) := by
    funext w
    change (u.indicator (fun _ => (1 : ℂ)) w.2) * (t.indicator (fun _ => (1 : ℂ)) w.1.2) *
      (s.indicator (fun _ => (1 : ℂ)) w.1.1) =
      ((s ×ˢ t) ×ˢ u).indicator (fun _ => (1 : ℂ)) w
    by_cases h₁ : w.1.1 ∈ s <;> by_cases h₂ : w.1.2 ∈ t <;>
      by_cases h₃ : w.2 ∈ u <;> simp [h₁, h₂, h₃]
  have hId₂ :
      (fun w : X × Y => indicatorOne t ht w.2 * indicatorOne s hs w.1) =
      (s ×ˢ t).indicator (fun _ => (1 : ℂ)) := by
    funext w
    change (t.indicator (fun _ => (1 : ℂ)) w.2) * (s.indicator (fun _ => (1 : ℂ)) w.1) = _
    by_cases h₁ : w.1 ∈ s <;> by_cases h₂ : w.2 ∈ t <;> simp [h₁, h₂]
  have hId₁ : (fun z => indicatorOne u hu z) = u.indicator (fun _ => (1 : ℂ)) := rfl
  have hEq := h (indicatorOne s hs) (indicatorOne t ht) (indicatorOne u hu)
  rw [hId₃, hId₂, hId₁, integral_indicator_const _ ((hs.prod ht).prod hu),
    integral_indicator_const _ (hs.prod ht), integral_indicator_const _ hu] at hEq
  have hRe := congrArg Complex.re hEq
  simp only [Complex.real_smul, mul_one, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hRe
  have hReal : (τ ((s ×ˢ t) ×ˢ u)).toReal = ((σ.prod ρ) ((s ×ˢ t) ×ˢ u)).toReal := by
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    exact hRe
  simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using congrArg ENNReal.ofReal hReal

/-- Every joining of the generated system with a system disjoint from the mixing system
is disjoint from that mixing system. This is the multiplier conclusion of Theorem 6.3,
with U-generation expressed by L² density of finite products. -/
theorem System.disjoint_joining_of_isUGenerated
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} (hσ : IsJoining T S σ)
    {U : Set (Ultrafilter G)} (hGen : T.IsUGenerated U)
    (hMix : R.IsUMixing U) (hDisjoint : Disjoint S R) :
    Disjoint hσ.system R := by
  intro τ hτ
  let := hσ.probability
  let := hτ.probability
  exact joining_eq_prod_of_integrals
    (joining_integral_factorization_of_generated hτ hGen (System.hasMixingCorrelations hMix) hDisjoint)

/-- The disjointness consequence of the multiplier theorem, obtained with a one-point
auxiliary system. This is (iii) to (ii) in Theorem 1.3 under the L² generation criterion. -/
theorem System.disjoint_of_isUGenerated
    {T : System G X} {R : System G Z} {U : Set (Ultrafilter G)}
    (hGen : T.IsUGenerated U) (hMix : R.IsUMixing U) : Disjoint T R := by
  let : MeasurableSpace Unit := ⊤
  let ν := T.measure.map (fun _ => ())
  have hν : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    (measurable_const (a := ())).aemeasurable).2 T.probability
  let S : System G Unit :=
    ⟨ν, hν, fun _ => id, rfl, fun _ _ => rfl, fun _ => MeasurePreserving.id ν⟩
  have hS : Disjoint S R := by
    intro ξ hξ
    let := hξ.probability
    apply Measure.ext_prod
    intro s t hs ht
    by_cases h : () ∈ s
    · have he : s = univ := Set.eq_univ_of_forall fun x => by cases x; exact h
      rw [he, Measure.prod_prod, measure_univ, one_mul]
      have he' : (univ : Set Unit) ×ˢ t = Prod.snd ⁻¹' t := by ext x; simp
      rw [he']
      exact hξ.snd.measure_preimage ht.nullMeasurableSet
    · have he : s = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x => by cases x; exact h
      simp [he]
  let f : FactorMap T S := ⟨fun _ => (), ⟨measurable_const, rfl⟩, fun _ => rfl⟩
  let σ := T.measure.map (fun x => (x, ()))
  let hσ : IsJoining T S σ := f.graph_isJoining
  let i : FactorMap T hσ.system :=
    ⟨fun x => (x, ()), ⟨measurable_id.prodMk measurable_const, rfl⟩, fun _ => rfl⟩
  let idR : FactorMap R R := ⟨id, MeasurePreserving.id _, fun _ => rfl⟩
  intro η hη
  let j := Prod.map i.toFun idR.toFun
  have hj : Measurable j := i.preserves.measurable.prodMap idR.preserves.measurable
  let k : ((X × Unit) × Z) → X × Z := Prod.map Prod.fst id
  have hk : Measurable k := measurable_fst.prodMap measurable_id
  have hτ : IsJoining hσ.system R (η.map j) := hη.map i idR
  have he := System.disjoint_joining_of_isUGenerated hσ hGen hMix hS _ hτ
  calc
    η = (η.map j).map k := by rw [Measure.map_map hk hj]; exact Measure.map_id.symm
    _ = (σ.prod R.measure).map k := congrArg (Measure.map k) he
    _ = T.measure.prod R.measure := (hσ.fst.prod (MeasurePreserving.id R.measure)).map_eq

/-- Swapping the coordinates gives a joining of the swapped systems. -/
theorem IsJoining.swap {T : System G X} {R : System G Z}
    {ξ : Measure (Z × X)} (hξ : IsJoining R T ξ) : IsJoining T R (ξ.map Prod.swap) := by
  refine ⟨(Measure.isProbabilityMeasure_map_iff measurable_swap.aemeasurable).2 hξ.probability,
    ⟨measurable_fst, ?_⟩, ⟨measurable_snd, ?_⟩, fun g => ⟨?_, ?_⟩⟩
  · rw [Measure.map_map measurable_fst measurable_swap]
    exact hξ.snd.map_eq
  · rw [Measure.map_map measurable_snd measurable_swap]
    exact hξ.fst.map_eq
  · exact (T.preserves g).measurable.prodMap (R.preserves g).measurable
  · have hact : Measurable (T.prodAct R g) :=
      (T.preserves g).measurable.prodMap (R.preserves g).measurable
    have he : T.prodAct R g ∘ Prod.swap = Prod.swap ∘ R.prodAct T g := rfl
    rw [Measure.map_map hact measurable_swap, he,
      ← Measure.map_map measurable_swap (hξ.invariant g).measurable, (hξ.invariant g).map_eq]

/-- Disjointness is symmetric. -/
theorem Disjoint.symm {T : System G X} {R : System G Z} (hd : Disjoint T R) :
    Disjoint R T := by
  intro ξ hξ
  have he := hd _ hξ.swap
  calc
    ξ = (ξ.map Prod.swap).map Prod.swap := by
      rw [Measure.map_map measurable_swap measurable_swap]
      exact Measure.map_id.symm
    _ = (T.measure.prod R.measure).map Prod.swap := congrArg (Measure.map Prod.swap) he
    _ = R.measure.prod T.measure := Measure.prod_swap

/-- Theorem 1.3, (iii) implies (ii), under the L² finite-product generation criterion. -/
theorem theorem1_3_iii_ii (R : System G Z) (U : Set (Ultrafilter G)) (hMix : R.IsUMixing U)
    (T : System G X) (hGen : T.IsUGenerated U) : Disjoint R T :=
  (System.disjoint_of_isUGenerated hGen hMix).symm

end Mixing
