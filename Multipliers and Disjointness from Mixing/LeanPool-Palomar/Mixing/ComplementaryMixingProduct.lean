/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorProductGeneration
public import Mixing.IdentityDisjointness
public import Mixing.MaximalSpectralVector
public import Mixing.RigidRepresentations
public import Mixing.SpectralMultiplier

/-! # The product argument in Example 4 -/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace Mixing Topology

namespace Mixing

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable (S : System G X) (T : System G Y)

private theorem System.isUMixing_singleton_of_correlations_on (R : System G X) (D : Set G)
    (r : Ultrafilter G) (hr : r ∈ freeUltrafilters G) (hD : D ∈ r)
    (hCorr : ∀ x y : meanZero R.measure,
      Tendsto (fun g => ⟪x, R.koopmanZeroRep g y⟫_ℂ) (cofinite ⊓ 𝓟 D) (𝓝 0)) :
    R.IsUMixing {r} := by
  intro p hp
  have he : p = r := Set.mem_singleton_iff.mp hp
  subst p
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [zero_apply, inner_zero_right]
  exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff R.koopmanZeroRep r x y)
    ((hCorr x y).mono_left (le_inf hr (Filter.le_principal_iff.mpr hD)))

/-- Mixing on complementary sets gives the ultrafilter alternative used in Example 4. -/
theorem complementary_ultrafilter_mixing_of_correlations (D : Set G)
    (hS : ∀ x y : meanZero S.measure,
      Tendsto (fun g => ⟪x, S.koopmanZeroRep g y⟫_ℂ) (cofinite ⊓ 𝓟 D) (𝓝 0))
    (hT : ∀ x y : meanZero T.measure,
      Tendsto (fun g => ⟪x, T.koopmanZeroRep g y⟫_ℂ) (cofinite ⊓ 𝓟 Dᶜ) (𝓝 0)) :
    ∀ r ∈ freeUltrafilters G, S.IsUMixing {r} ∨ T.IsUMixing {r} := by
  intro r hr
  rcases r.mem_or_compl_mem D with hD | hDc
  · exact Or.inl (S.isUMixing_singleton_of_correlations_on D r hr hD hS)
  · exact Or.inr (T.isUMixing_singleton_of_correlations_on Dᶜ r hr hDc hT)

/-- If each free ultrafilter mixes at least one coordinate, each centered
product observable has a strongly mixing scalar spectral measure. -/
theorem example4_pairObservable_rajchman [Countable G]
    (hCover : ∀ r ∈ freeUltrafilters G, S.IsUMixing {r} ∨ T.IsUMixing {r})
    (f : BoundedObservable X) (h : BoundedObservable Y)
    (hf : ∫ x, f x ∂S.measure = 0) (hh : ∫ y, h y ∂T.measure = 0) :
    Tendsto (spectralFourier (dualVectorSpectralMeasure (S.prod T).koopmanRep
      ((pairObservable f h).l2 (S.prod T).measure))) cofinite (𝓝 0) := by
  rw [dualVectorSpectralMeasure_pairObservable]
  simp_rw [funext (spectralFourier_mconv
    (dualVectorSpectralMeasure S.koopmanRep (f.l2 S.measure))
    (dualVectorSpectralMeasure T.koopmanRep (h.l2 T.measure))),
    spectralFourier_dualVectorSpectralMeasure]
  apply (Filter.tendsto_iff_ultrafilter _ _ _).mpr
  intro p hp
  let a := f.l2 S.measure
  let b := h.l2 T.measure
  have hLa := tendsto_ultrafilterOperator_coeff S.koopmanRep p a a
  have hLb := tendsto_ultrafilterOperator_coeff T.koopmanRep p b b
  rcases hCover p hp with hMix | hMix
  · have hlim := (S.isUMixing_iff_lp_correlations {p}).mp hMix p (Set.mem_singleton p) a a
    rw [integral_congr_ae (f.coe_l2 S.measure), hf, mul_zero] at hlim
    simpa only [zero_mul] using hlim.mul hLb
  · have hlim := (T.isUMixing_iff_lp_correlations {p}).mp hMix p (Set.mem_singleton p) b b
    rw [integral_congr_ae (h.coe_l2 T.measure), hh, mul_zero] at hlim
    simpa only [mul_zero] using hLa.mul hlim

set_option maxHeartbeats 1200000 in
/-- A vector with cofinite decay of its diagonal coefficient generates a
strongly mixing closed cyclic subspace. -/
theorem isStronglyMixing_cyclicClosedSubmodule {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (U : G →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hDiag : Tendsto (fun g => ⟪x, U g x⟫_ℂ) cofinite (𝓝 0)) :
    IsStronglyMixing (unitarySubmoduleAction U (cyclicClosedSubmodule U x).toSubmodule
      (cyclicClosedSubmodule_invariant U x)) := by
  let C := cyclicClosedSubmodule U x
  let C₀ := C.toSubmodule
  let _ : CompleteSpace C₀ := C.isClosed.completeSpace_coe
  let hC := cyclicClosedSubmodule_invariant U x
  let V := unitarySubmoduleAction U C₀ hC
  let x₀ : C₀ := ⟨x, mem_cyclicClosedSubmodule U x⟩
  let hIn := intertwines_unitarySubmoduleAction U C₀ hC
  apply (isStronglyMixing_iff_isUMixing_free V).mpr
  intro p hp
  let Q := ultrafilterOperator U p
  have hx : Q x ∈ C₀ := by
    have he := hIn.ultrafilter p x₀
    change (↑(ultrafilterOperator V p x₀) : H) = Q x at he
    rw [← he]
    exact (ultrafilterOperator V p x₀).property
  have hTest (g : G) : ⟪U g x, Q x⟫_ℂ = 0 := by
    have hinj : Function.Injective (fun a : G ↦ g⁻¹ * a) := fun _ _ h => mul_left_cancel h
    have hTranslate : Tendsto (fun a : G ↦ g⁻¹ * a) cofinite cofinite := hinj.tendsto_cofinite
    have hlim := (hDiag.comp hTranslate).mono_left hp
    apply tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p (U g x) x)
    refine hlim.congr' (.of_forall fun a => ?_)
    change ⟪x, U (g⁻¹ * a) x⟫_ℂ = ⟪U g x, U a x⟫_ℂ
    rw [map_mul]
    have hgg : U g (U g⁻¹ (U a x)) = U a x := by
      change (U g * U g⁻¹) (U a x) = U a x
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    exact ((U g).inner_map_map x (U g⁻¹ (U a x))).symm.trans (by rw [hgg])
  let D := Submodule.span ℂ (Set.range fun g : G => U g x)
  let L := innerSL ℂ (Q x)
  have hL : D ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change ⟪Q x, U g x⟫_ℂ = 0
    rw [← inner_conj_symm, hTest, map_zero]
  have hZero : Q x = 0 := by
    have h := Submodule.topologicalClosure_minimal _ hL L.isClosed_ker hx
    exact inner_self_eq_zero.mp h
  have hKer : D ≤ Q.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change Q (U g x) = 0
    rw [← ultrafilterOperator_commute U p, hZero, map_zero]
  have hAll : C₀ ≤ Q.ker := Submodule.topologicalClosure_minimal _ hKer Q.isClosed_ker
  ext z
  exact (hIn.ultrafilter p z).trans (hAll z.property)

/-- The cyclic subspace of every centered product observable is strongly mixing. -/
theorem example4_pairObservable_cyclic_stronglyMixing [Countable G]
    (hCover : ∀ r ∈ freeUltrafilters G, S.IsUMixing {r} ∨ T.IsUMixing {r})
    (f : BoundedObservable X) (h : BoundedObservable Y)
    (hf : ∫ x, f x ∂S.measure = 0) (hh : ∫ y, h y ∂T.measure = 0) :
    let U := (S.prod T).koopmanRep
    let x := (pairObservable f h).l2 (S.prod T).measure
    IsStronglyMixing (unitarySubmoduleAction U (cyclicClosedSubmodule U x).toSubmodule
      (cyclicClosedSubmodule_invariant U x)) := by
  apply isStronglyMixing_cyclicClosedSubmodule
  have hLim := example4_pairObservable_rajchman S T hCover f h hf hh
  rw [funext (spectralFourier_dualVectorSpectralMeasure _ _)] at hLim
  exact hLim

/-- The bounded observable associated to a measurable event. -/
noncomputable def BoundedObservable.eventIndicator {A : Type*} [MeasurableSpace A]
    (B : Set A) (hB : MeasurableSet B) : BoundedObservable A where
  toFun := B.indicator fun _ => (1 : ℂ)
  measurable := measurable_const.indicator hB
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x := by
    classical
    by_cases hx : x ∈ B <;> simp [hx]

/-- Any event of intermediate probability supplies a nonzero centered bounded observable. -/
theorem exists_nonzero_centered_observable {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (B : Set A) (hB : MeasurableSet B)
    (hB₀ : 0 < μ B) (hB₁ : μ B < 1) :
    ∃ f : BoundedObservable A, (∫ x, f x ∂μ) = 0 ∧ f.l2 μ ≠ 0 := by
  let h := BoundedObservable.eventIndicator B hB
  let c : ℂ := μ.real B
  let f := h.sub (BoundedObservable.const c)
  refine ⟨f, ?_, ?_⟩
  · change (∫ x, h x - c ∂μ) = 0
    rw [integral_sub (h.integrable μ) (integrable_const c)]
    change (∫ x, B.indicator (fun _ => (1 : ℂ)) x ∂μ) - (∫ _, c ∂μ) = 0
    rw [integral_indicator hB, setIntegral_const, integral_const]
    simp [c, Complex.real_smul, measureReal_def]
  · intro hZero
    have hAE := f.coe_l2 μ
    rw [hZero] at hAE
    have hf0 : f =ᵐ[μ] (0 : A → ℂ) := hAE.symm.trans (Lp.coeFn_zero ℂ 2 μ)
    have hc : c ≠ 1 := by
      intro he
      have hlt : μ.real B < 1 := by
        rw [measureReal_def, ← ENNReal.toReal_one]
        exact (ENNReal.toReal_lt_toReal (measure_ne_top μ B) ENNReal.one_ne_top).mpr hB₁
      exact hlt.ne (by simpa [c] using congrArg Complex.re he)
    have hSupp : ∀ᵐ x ∂μ, x ∉ B := by
      filter_upwards [hf0] with x hx hBx
      change (B.indicator (fun _ => (1 : ℂ)) x - c : ℂ) = 0 at hx
      rw [Set.indicator_of_mem hBx, sub_eq_zero] at hx
      exact hc hx.symm
    have hNull : μ B = 0 := by simpa using (ae_iff.mp hSupp)
    exact hB₀.ne' hNull

/-- A product of two nonzero observables is nonzero in the product Hilbert space. -/
theorem pairObservable_l2_ne_zero [Countable G] (f : BoundedObservable X) (h : BoundedObservable Y)
    (hf₀ : f.l2 S.measure ≠ 0) (hh₀ : h.l2 T.measure ≠ 0) :
    (pairObservable f h).l2 (S.prod T).measure ≠ 0 := by
  let x := (pairObservable f h).l2 (S.prod T).measure
  intro hx
  change x = 0 at hx
  have he := spectralFourier_mconv (dualVectorSpectralMeasure S.koopmanRep (f.l2 S.measure))
    (dualVectorSpectralMeasure T.koopmanRep (h.l2 T.measure)) (1 : G)
  rw [← dualVectorSpectralMeasure_pairObservable S T f h] at he
  simp only [spectralFourier_dualVectorSpectralMeasure, map_one] at he
  change ⟪x, x⟫_ℂ = ⟪f.l2 S.measure, f.l2 S.measure⟫_ℂ *
    ⟪h.l2 T.measure, h.l2 T.measure⟫_ℂ at he
  rw [hx, inner_zero_left] at he
  exact (mul_eq_zero.mp he.symm).elim (fun hf' => hf₀ (inner_self_eq_zero.mp hf'))
    (fun hh' => hh₀ (inner_self_eq_zero.mp hh'))

/-- The spectral component in Example 4 contains a nonzero cyclic strongly
mixing representation when both coordinate systems are nontrivial. -/
theorem example4_exists_nonzero_stronglyMixing_cyclic [Countable G]
    (hCover : ∀ r ∈ freeUltrafilters G, S.IsUMixing {r} ∨ T.IsUMixing {r})
    {A : Set X} (hA : MeasurableSet A) (hA₀ : 0 < S.measure A) (hA₁ : S.measure A < 1)
    {B : Set Y} (hB : MeasurableSet B) (hB₀ : 0 < T.measure B) (hB₁ : T.measure B < 1) :
    let U := (S.prod T).koopmanRep
    ∃ x : Lp ℂ 2 (S.prod T).measure, x ≠ 0 ∧
      IsStronglyMixing (unitarySubmoduleAction U (cyclicClosedSubmodule U x).toSubmodule
        (cyclicClosedSubmodule_invariant U x)) := by
  obtain ⟨f, hf, hf₀⟩ := exists_nonzero_centered_observable S.measure A hA hA₀ hA₁
  obtain ⟨h, hh, hh₀⟩ := exists_nonzero_centered_observable T.measure B hB hB₀ hB₁
  exact ⟨_, pairObservable_l2_ne_zero S T f h hf₀ hh₀,
    example4_pairObservable_cyclic_stronglyMixing S T hCover f h hf hh⟩

private theorem System.isUGenerated_singleton_of_operator_eq_one {A : Type*} [MeasurableSpace A]
    (R : System G A) (p : Ultrafilter G) (h : ultrafilterOperator R.koopmanRep p = 1) :
    R.IsUGenerated {p} := by
  apply R.isUGenerated_of_koopmanIsUGenerated
  apply top_unique
  intro z _
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine Set.mem_iUnion.mpr ⟨⟨p, Set.mem_singleton p⟩, ⟨z, ?_⟩⟩
  rw [h]
  rfl

/-- The generation and non-generation conclusions of Example 4, from the
two rigid coordinate systems with complementary mixing. -/
theorem example4_product_of_complementary_mixing
    (hRigidS : IsRigidRepresentation S.koopmanRep) (hRigidT : IsRigidRepresentation T.koopmanRep)
    (hCover : ∀ r ∈ freeUltrafilters G, S.IsUMixing {r} ∨ T.IsUMixing {r})
    {A : Set X} (hA : MeasurableSet A) (hA₀ : 0 < S.measure A) (hA₁ : S.measure A < 1)
    {B : Set Y} (hB : MeasurableSet B) (hB₀ : 0 < T.measure B) (hB₁ : T.measure B < 1) :
    (∃ p ∈ freeIdempotentUltrafilters G, ∃ q ∈ freeIdempotentUltrafilters G,
      p ≠ q ∧ (S.prod T).IsUGenerated ({p} ∪ {q})) ∧
      (∀ r ∈ freeUltrafilters G, ¬ (S.prod T).IsUGenerated {r}) ∧
      ¬ IsRigidRepresentation (S.prod T).koopmanRep := by
  have hNot (r : Ultrafilter G) (hr : r ∈ freeUltrafilters G) : ¬ (S.prod T).IsUGenerated {r} := by
    intro hGen
    rcases hCover r hr with hMix | hMix
    · exact (product_isJoining S T).fstFactor.not_disjoint_of_event hA hA₀ hA₁
        (theorem1_3_iii_ii S {r} hMix (S.prod T) hGen).symm
    · exact (product_isJoining S T).sndFactor.not_disjoint_of_event hB hB₀ hB₁
        (theorem1_3_iii_ii T {r} hMix (S.prod T) hGen).symm
  obtain ⟨p, hp, hpId⟩ := exists_freeIdempotent_operator_eq_one_of_rigid S.koopmanRep hRigidS
  obtain ⟨q, hq, hqId⟩ := exists_freeIdempotent_operator_eq_one_of_rigid T.koopmanRep hRigidT
  have hGen := S.isUGenerated_prod_union T {p} {q}
    (S.isUGenerated_singleton_of_operator_eq_one p hpId) (T.isUGenerated_singleton_of_operator_eq_one q hqId)
  refine ⟨⟨p, hp, q, hq, ?_, hGen⟩, hNot, ?_⟩
  · intro he
    apply hNot p hp.1
    simpa [← he] using hGen
  · intro hRigid
    obtain ⟨r, hr, hrId⟩ := exists_freeIdempotent_operator_eq_one_of_rigid (S.prod T).koopmanRep hRigid
    exact hNot r hr.1 ((S.prod T).isUGenerated_singleton_of_operator_eq_one r hrId)

end Mixing
