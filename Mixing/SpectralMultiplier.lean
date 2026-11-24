module

public import Mixing.GeneratedMultiplier
public import Mixing.FourierUniqueness
public import Mixing.SpectralMeasureClass
public import Mixing.SpectralOrthogonality
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

noncomputable section

namespace Mixing

open MeasureTheory MeasureTheory.Measure Set
open scoped ComplexConjugate

variable {G X Y Z : Type*} [CommGroup G] [Countable G]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The product of two bounded observables on separate coordinate spaces. -/
def pairObservable (f : BoundedObservable X) (h : BoundedObservable Y) :
    BoundedObservable (X × Y) :=
  (f.comp Prod.fst measurable_fst).mul (h.comp Prod.snd measurable_snd)

omit [Countable G] in
private theorem System.coeff_observable (T : System G X) (g : G) (f : BoundedObservable X) :
    inner ℂ (f.l2 T.measure) (T.koopmanRep g (f.l2 T.measure)) =
      ∫ x, conj (f x) * f (T.act g x) ∂T.measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coe_l2 T.measure, T.koopman_ae_observable g f] with x hx hg
  rw [hx, hg, RCLike.inner_apply']
  rfl

/-- Equality (18) for the independent product of two systems. -/
theorem dualVectorSpectralMeasure_pairObservable (S : System G X) (T : System G Y)
    (f : BoundedObservable X) (h : BoundedObservable Y) :
    dualVectorSpectralMeasure (S.prod T).koopmanRep ((pairObservable f h).l2 (S.prod T).measure) =
      dualVectorSpectralMeasure S.koopmanRep (f.l2 S.measure) ∗ₘ
        dualVectorSpectralMeasure T.koopmanRep (h.l2 T.measure) := by
  apply dualVectorSpectralMeasure_eq_mconv_of_coefficients
  intro g
  simp only [System.coeff_observable]
  have he : (fun x : X × Y ↦ conj (pairObservable f h x) *
      pairObservable f h ((S.prod T).act g x)) =
      fun x ↦ (conj (f x.1) * f (S.act g x.1)) * (conj (h x.2) * h (T.act g x.2)) := by
    funext x
    change conj (f x.1 * h x.2) * (f (S.act g x.1) * h (T.act g x.2)) = _
    rw [map_mul]
    ac_rfl
  rw [he]
  exact integral_prod_mul (fun x ↦ conj (f x) * f (S.act g x))
    (fun y ↦ conj (h y) * h (T.act g y))

omit [Countable G] in
private theorem spectralMeasure_isometricIntertwiner
    {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K] [InnerProductSpace ℂ H]
    [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K)) (J : H →ₗᵢ[ℂ] K)
    (hJ : Intertwines U V J.toContinuousLinearMap) (f : H) :
    dualVectorSpectralMeasure V (J f) = dualVectorSpectralMeasure U f := by
  apply eq_of_spectralFourier_eq
  intro g
  simp only [spectralFourier_dualVectorSpectralMeasure]
  have h := hJ g f
  change J (U g f) = V g (J f) at h
  rw [← h, J.inner_map_map]

private def FactorMap.identityMap (R : System G Z) : FactorMap R R :=
  ⟨id, MeasurePreserving.id _, fun _ ↦ rfl⟩

private def IsJoining.middleRightFactor
    {S : System G X} {T : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining S T σ} (hτ : IsJoining hσ.system R τ)
    (hdis : Disjoint T R) : FactorMap hτ.system (T.prod R) := by
  let f := hσ.sndFactor
  let e := FactorMap.identityMap R
  have hmap := hτ.map f e
  exact ⟨Prod.map Prod.snd id,
    ⟨measurable_snd.prodMap measurable_id, hdis _ hmap⟩, fun _ ↦ rfl⟩

set_option maxHeartbeats 1200000 in
/-- The spectral multiplier argument of Theorem 6.2, stated directly for the
positive vector spectral measures. The only ideal operation used is closure
under convolution against an arbitrary positive finite measure. -/
theorem theorem6_2_vectorSpectra
    {S : System G X} {T : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {hσ : IsJoining S T σ}
    (I : Set (Measure (DiscreteDual G)))
    (hI : ∀ {μ ν : Measure (DiscreteDual G)} [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ν ∈ I → μ ∗ₘ ν ∈ I)
    (hS : ∀ f : Lp ℂ 2 S.measure, (∫ x, f x ∂S.measure) = 0 →
      ∀ μ ∈ I, dualVectorSpectralMeasure S.koopmanRep f ⟂ₘ μ)
    (hR : ∀ h : Lp ℂ 2 R.measure, (∫ z, h z ∂R.measure) = 0 →
      dualVectorSpectralMeasure R.koopmanRep h ∈ I)
    (hTR : Disjoint T R) : Disjoint hσ.system R := by
  intro τ hτ
  have : IsProbabilityMeasure σ := hσ.probability
  have : IsProbabilityMeasure τ := hτ.probability
  let F := hσ.fstFactor.comp hτ.fstFactor
  let K := IsJoining.middleRightFactor hτ hTR
  have hzero (f : BoundedObservable X) (k : BoundedObservable Y) (h : BoundedObservable Z)
      (hf : (∫ x, f x ∂S.measure) = 0) (hh : (∫ z, h z ∂R.measure) = 0) :
      ∫ w, h w.2 * k w.1.2 * f w.1.1 ∂τ = 0 := by
    let f' := f.conjugate.l2 S.measure
    let h' := h.l2 R.measure
    let k' := (pairObservable k h).l2 (T.prod R).measure
    have hmeanf : ∫ x, f' x ∂S.measure = 0 := by
      rw [integral_congr_ae (f.conjugate.coe_l2 S.measure)]
      change (∫ x, conj (f x) ∂S.measure) = 0
      rw [integral_conj, hf, map_zero]
    have hmeanh : ∫ z, h' z ∂R.measure = 0 :=
      (integral_congr_ae (h.coe_l2 R.measure)).trans hh
    have hIn : dualVectorSpectralMeasure (T.prod R).koopmanRep k' ∈ I := by
      change dualVectorSpectralMeasure (T.prod R).koopmanRep
        ((pairObservable k h).l2 (T.prod R).measure) ∈ I
      rw [dualVectorSpectralMeasure_pairObservable T R k h]
      exact hI (hR h' hmeanh)
    have hSing := hS f' hmeanf _ hIn
    have hF := spectralMeasure_isometricIntertwiner S.koopmanRep hτ.system.koopmanRep
      F.pullback F.intertwines_pullback f'
    have hK := spectralMeasure_isometricIntertwiner (T.prod R).koopmanRep hτ.system.koopmanRep
      K.pullback K.intertwines_pullback k'
    have hSing' : dualVectorSpectralMeasure hτ.system.koopmanRep (F.pullback f') ⟂ₘ
        dualVectorSpectralMeasure hτ.system.koopmanRep (K.pullback k') := by
      rwa [hF, hK]
    have hOrth := inner_eq_zero_of_dualVectorSpectralMeasure_mutuallySingular hτ.system.koopmanRep
      (F.pullback f') (K.pullback k') hSing'
    rw [L2.inner_def] at hOrth
    refine (integral_congr_ae ?_).trans hOrth
    have hff := (Lp.coeFn_compMeasurePreserving f' F.preserves).trans
      (F.preserves.quasiMeasurePreserving.ae_eq_comp (f.conjugate.coe_l2 S.measure))
    have hkk := (Lp.coeFn_compMeasurePreserving k' K.preserves).trans
      (K.preserves.quasiMeasurePreserving.ae_eq_comp ((pairObservable k h).coe_l2 _))
    filter_upwards [hff, hkk] with w hw₁ hw₂
    change F.pullback f' w = _ at hw₁
    change K.pullback k' w = _ at hw₂
    rw [hw₁, hw₂]
    change h w.2 * k w.1.2 * f w.1.1 = inner ℂ (conj (f w.1.1)) (k w.1.2 * h w.2)
    rw [RCLike.inner_apply', starRingEnd_self_apply]
    ac_rfl
  apply joining_eq_prod_of_integrals (σ := σ) (ρ := R.measure) (τ := τ)
  intro f k h
  let h₀ := h.sub (BoundedObservable.const (∫ z, h z ∂R.measure))
  let f₀ := f.sub (BoundedObservable.const (∫ x, f x ∂S.measure))
  have hmean : ∫ z, h₀ z ∂R.measure = 0 := by
    simp [h₀, integral_sub (h.integrable _) (integrable_const _), measureReal_def]
  have fmean : ∫ x, f₀ x ∂S.measure = 0 := by
    simp [f₀, integral_sub (f.integrable _) (integrable_const _), measureReal_def]
  have hYZ : ∫ w, h₀ w.2 * k w.1.2 ∂τ = 0 := by
    have he := (pairObservable k h₀).integral_comp_of_preserving K.preserves
    change (∫ w, k w.1.2 * h₀ w.2 ∂τ) =
      ∫ x : Y × Z, k x.1 * h₀ x.2 ∂T.measure.prod R.measure at he
    rw [integral_prod_mul, hmean, mul_zero] at he
    simpa only [mul_comm] using he
  have hI₁ : Integrable (fun w : (X × Y) × Z ↦ h₀ w.2 * k w.1.2) τ :=
    ((pairObservable h₀ k).comp
      (fun w : (X × Y) × Z ↦ (w.2, w.1.2)) (measurable_snd.prodMk
        (measurable_snd.comp measurable_fst))).integrable τ
  have hI₂ : Integrable (fun w : (X × Y) × Z ↦ h₀ w.2 * k w.1.2 * f w.1.1) τ :=
    (((pairObservable h₀ k).comp (fun w : (X × Y) × Z ↦ (w.2, w.1.2))
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
      (f.comp (fun w : (X × Y) × Z ↦ w.1.1) (measurable_fst.comp measurable_fst))).integrable τ
  have hcenter : ∫ w, h₀ w.2 * k w.1.2 * f w.1.1 ∂τ = 0 := by
    have htest := hzero f₀ k h₀ fmean hmean
    simp only [f₀, BoundedObservable.sub_apply, BoundedObservable.const_apply, mul_sub] at htest
    rwa [integral_sub hI₂ (hI₁.mul_const _), integral_mul_const, hYZ, zero_mul, sub_zero] at htest
  have hI₃ : Integrable (fun w : (X × Y) × Z ↦ k w.1.2 * f w.1.1) τ :=
    ((pairObservable k f).comp (fun w : (X × Y) × Z ↦ (w.1.2, w.1.1))
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_fst))).integrable τ
  have hI₄ : (∫ w, k w.1.2 * f w.1.1 ∂τ) = ∫ w : X × Y, k w.2 * f w.1 ∂σ := by
    exact ((pairObservable k f).comp Prod.swap measurable_swap).integral_comp_of_preserving hτ.fst
  have hsplit : ∀ w : (X × Y) × Z, h w.2 * k w.1.2 * f w.1.1 =
      h₀ w.2 * k w.1.2 * f w.1.1 + (k w.1.2 * f w.1.1) * ∫ z, h z ∂R.measure := by
    intro w
    simp only [h₀, BoundedObservable.sub_apply, BoundedObservable.const_apply]
    ring
  simp only [hsplit, integral_add hI₂ (hI₃.mul_const _), integral_mul_const,
    hcenter, zero_add, hI₄]

/-- Corollary 6 in positive-vector spectral form. A system whose centered
spectral measures are singular to Haar measure is a multiplier for the
disjointness class of systems with absolutely continuous spectrum. -/
theorem corollary6_vectorSpectra
    {S : System G X} {T : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {hσ : IsJoining S T σ}
    (m : Measure (DiscreteDual G)) [IsMulLeftInvariant m]
    (hS : ∀ f : Lp ℂ 2 S.measure, (∫ x, f x ∂S.measure) = 0 →
      dualVectorSpectralMeasure S.koopmanRep f ⟂ₘ m)
    (hR : ∀ h : Lp ℂ 2 R.measure, (∫ z, h z ∂R.measure) = 0 →
      dualVectorSpectralMeasure R.koopmanRep h ≪ m)
    (hTR : Disjoint T R) : Disjoint hσ.system R := by
  apply theorem6_2_vectorSpectra {μ | μ ≪ m} ?_ ?_ hR hTR
  · intros
    exact mconv_absolutelyContinuous (by assumption)
  · intro f hf μ hμ
    exact (hS f hf).mono_ac Measure.AbsolutelyContinuous.rfl hμ

omit [Countable G] in
/-- Passing between the mean-zero and full Koopman spaces preserves the
spectral measure of a mean-zero vector. -/
theorem dualVectorSpectralMeasure_koopmanZero (S : System G X) (v : meanZero S.measure) :
    dualVectorSpectralMeasure S.koopmanZeroRep v =
      dualVectorSpectralMeasure S.koopmanRep (v : Lp ℂ 2 S.measure) := by
  apply eq_of_spectralFourier_eq
  intro g
  simp only [spectralFourier_dualVectorSpectralMeasure]
  rfl

/-- Theorem 6.2 using representatives of the two maximal spectral types.
The positive part of an L-ideal has the convolution and absolute-continuity
closure properties stated here. -/
theorem theorem6_2_of_maximalSpectralVectors
    {S : System G X} {T : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {hσ : IsJoining S T σ}
    (I : Set (Measure (DiscreteDual G)))
    (hI : ∀ {μ ν : Measure (DiscreteDual G)} [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ν ∈ I → μ ∗ₘ ν ∈ I)
    (hAc : ∀ {μ ν : Measure (DiscreteDual G)} [IsFiniteMeasure μ], ν ∈ I → μ ≪ ν → μ ∈ I)
    (x : meanZero S.measure) (z : meanZero R.measure)
    (hx : IsMaximalSpectralVector S.koopmanZeroRep x)
    (hz : IsMaximalSpectralVector R.koopmanZeroRep z)
    (hS : ∀ μ ∈ I, dualVectorSpectralMeasure S.koopmanZeroRep x ⟂ₘ μ)
    (hR : dualVectorSpectralMeasure R.koopmanZeroRep z ∈ I)
    (hTR : Disjoint T R) : Disjoint hσ.system R := by
  apply theorem6_2_vectorSpectra I hI _ _ hTR
  · intro f hf μ hμ
    let f₀ : meanZero S.measure := ⟨f, (mem_meanZero_iff_integral _ _).mpr hf⟩
    have he := dualVectorSpectralMeasure_koopmanZero S f₀
    change dualVectorSpectralMeasure S.koopmanZeroRep f₀ =
      dualVectorSpectralMeasure S.koopmanRep f at he
    rw [← he]
    exact (hS μ hμ).mono_ac (hx f₀) Measure.AbsolutelyContinuous.rfl
  · intro f hf
    let f₀ : meanZero R.measure := ⟨f, (mem_meanZero_iff_integral _ _).mpr hf⟩
    have he := dualVectorSpectralMeasure_koopmanZero R f₀
    change dualVectorSpectralMeasure R.koopmanZeroRep f₀ =
      dualVectorSpectralMeasure R.koopmanRep f at he
    rw [← he]
    exact hAc hR (hz f₀)

/-- Corollary 6 using maximal spectral types, with Haar as the reference measure. -/
theorem corollary6_of_maximalSpectralVectors
    {S : System G X} {T : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {hσ : IsJoining S T σ}
    (m : Measure (DiscreteDual G)) [IsMulLeftInvariant m]
    (x : meanZero S.measure) (z : meanZero R.measure)
    (hx : IsMaximalSpectralVector S.koopmanZeroRep x)
    (hz : IsMaximalSpectralVector R.koopmanZeroRep z)
    (hS : dualVectorSpectralMeasure S.koopmanZeroRep x ⟂ₘ m)
    (hR : dualVectorSpectralMeasure R.koopmanZeroRep z ≪ m)
    (hTR : Disjoint T R) : Disjoint hσ.system R := by
  apply theorem6_2_of_maximalSpectralVectors {μ | μ ≪ m} _ _ x z hx hz _ hR hTR
  · intro μ ν _ _ hν
    exact mconv_absolutelyContinuous hν
  · intro μ ν _ hν hμ
    exact hμ.trans hν
  · intro μ hμ
    exact hS.mono_ac Measure.AbsolutelyContinuous.rfl hμ

end Mixing
