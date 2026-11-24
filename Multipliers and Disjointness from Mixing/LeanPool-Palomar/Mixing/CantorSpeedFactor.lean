/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorSpeedEigenvectors
public import Mixing.CantorSumNongeneration
public import Mixing.CantorGenerated
public import Mixing.GenerationAgreement

/-! # The non-generated Cantor factor in Example 5 -/

@[expose] public section

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Mixing

local notation "𝕋" => UnitAddCircle
local notation "𝕏" => (UnitAddCircle × UnitAddCircle)
local notation "haar" => (AddCircle.haarAddCircle : Measure 𝕋)

/-- The factor of the Cantor skew rotation obtained by doubling the fibre coordinate. -/
noncomputable def example5_doubledFactor :
    FactorMap example5CantorSystem (circleSkew cantorCircleMeasure 2) :=
  circleSkew_doubleFactor cantorCircleMeasure

/-- Doubling the fibre once more yields the speed-four factor in Example 5. -/
noncomputable def example5_evenFibreFactor :
    FactorMap (circleSkew cantorCircleMeasure 2) (circleSkew cantorCircleMeasure 4) where
  toFun x := (x.1, (2 : ℤ) • x.2)
  preserves := (circleSkew_doubleFactor cantorCircleMeasure).preserves
  equivariant g := by
    funext x
    change (x.1, (2 : ℤ) • (x.2 + (g.toAdd * 2) • x.1)) =
      (x.1, (2 : ℤ) • x.2 + (g.toAdd * 4) • x.1)
    rw [zsmul_add, smul_smul, show (2 : ℤ) * (g.toAdd * 2) = g.toAdd * 4 by ring]

private theorem evenFibreCharacter_mem_pullback (n : Fin 2 → ℤ) (k : ℤ) (hn : n 1 = 2 * k) :
    circlePairFourierLp (circleSkew cantorCircleMeasure 2).measure n ∈
      example5_evenFibreFactor.pullback.toLinearMap.range := by
  let T := circleSkew cantorCircleMeasure 2
  let R := circleSkew cantorCircleMeasure 4
  let m : Fin 2 → ℤ := ![n 0, k]
  refine ⟨circlePairFourierLp R.measure m, Lp.ext ?_⟩
  have h :=
    (Lp.coeFn_compMeasurePreserving (circlePairFourierLp R.measure m)
      example5_evenFibreFactor.preserves).trans
      (example5_evenFibreFactor.preserves.quasiMeasurePreserving.ae_eq_comp
        (circlePairFourierLp_ae_eq R.measure m))
  change example5_evenFibreFactor.pullback (circlePairFourierLp R.measure m) =ᵐ[T.measure] _ at h
  have hpoint : (example5CantorCharacter (m 0) (m 1) ∘ example5_evenFibreFactor.toFun) =ᵐ[T.measure]
      example5CantorCharacter (n 0) (n 1) := Eventually.of_forall fun x ↦ by
    change fourier (n 0) x.1 * fourier k ((2 : ℤ) • x.2) =
      fourier (n 0) x.1 * fourier (n 1) x.2
    rw [fourier_circle_zsmul, hn, mul_comm k 2]
  exact h.trans (hpoint.trans (circlePairFourierLp_ae_eq T.measure n).symm)

/-- In the speed-two factor all ultrafilter images are measurable with respect to
the further doubling of the fibre coordinate. -/
theorem example5_doubledFactor_ultrafilter_range_le
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    (ultrafilterOperator (circleSkew cantorCircleMeasure 2).koopmanRep p).range ≤
      example5_evenFibreFactor.pullback.toLinearMap.range := by
  let T := circleSkew cantorCircleMeasure 2
  let U := ultrafilterOperator T.koopmanRep p
  let K := example5_evenFibreFactor.pullback.toLinearMap.range
  have hclosed : IsClosed (K : Set (Lp ℂ 2 T.measure)) :=
    example5_evenFibreFactor.pullback.isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℂ (Set.range (circlePairFourierLp T.measure)) ≤
      K.comap U.toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change U (circlePairFourierLp T.measure n) ∈ K
    have heig := cantorSpeed_ultrafilter_eigenvector 2 n p hp hsupp
    change U (circlePairFourierLp T.measure n) =
      cantorFourier ((-(n 1) * 2 : ℤ) : ℝ) • circlePairFourierLp T.measure n at heig
    rw [heig]
    by_cases h : n 1 % 2 = 0
    · exact K.smul_mem _ (evenFibreCharacter_mem_pullback n (n 1 / 2) (by omega))
    · have hz : cantorFourier ((-(n 1) * 2 : ℤ) : ℝ) = 0 := by
        have hArg : -(n 1) * 2 = 4 * (-(n 1 / 2) - 1) + 2 := by omega
        rw [hArg]
        exact cantorFourier_eq_zero_mod_four_two _
      rw [hz, zero_smul]
      exact K.zero_mem
  have ht := Submodule.topologicalClosure_minimal _ hspan (hclosed.preimage U.continuous)
  rw [circlePairFourierLp_closure_span] at ht
  rintro _ ⟨f, rfl⟩
  exact ht Submodule.mem_top

private noncomputable def speedTwoFibreFlip (x : 𝕏) : 𝕏 := (x.1, x.2 + ((1 / 2 : ℝ) : 𝕋))

private theorem speedTwoFibreFlip_preserving :
    MeasurePreserving speedTwoFibreFlip (circleSkew cantorCircleMeasure 2).measure
      (circleSkew cantorCircleMeasure 2).measure :=
  (MeasurePreserving.id cantorCircleMeasure).prod
    (measurePreserving_add_right haar ((1 / 2 : ℝ) : 𝕋))

private theorem evenFibreFactor_flip (x : 𝕏) :
    example5_evenFibreFactor.toFun (speedTwoFibreFlip x) =
      example5_evenFibreFactor.toFun x := by
  have hh : (2 : ℤ) • ((1 / 2 : ℝ) : 𝕋) = 0 := by
    rw [← AddCircle.coe_zsmul]
    rw [show (2 : ℤ) • (1 / 2 : ℝ) = 1 by norm_num [zsmul_eq_mul]]
    exact AddCircle.coe_period (1 : ℝ)
  change (x.1, (2 : ℤ) • (x.2 + ((1 / 2 : ℝ) : 𝕋))) = (x.1, (2 : ℤ) • x.2)
  rw [zsmul_add, hh, add_zero]

/-- The speed-four subfactor is proper inside the speed-two factor. -/
theorem example5_evenFibreFactor_proper :
    example5_evenFibreFactor.pullback.toLinearMap.range ≠ ⊤ := by
  let T := circleSkew cantorCircleMeasure 2
  let n : Fin 2 → ℤ := ![0, 1]
  intro htop
  have hv : circlePairFourierLp T.measure n ∈ example5_evenFibreFactor.pullback.toLinearMap.range :=
    htop ▸ Submodule.mem_top
  obtain ⟨f, hf⟩ := hv
  have hr : (f ∘ example5_evenFibreFactor.toFun) =ᵐ[T.measure] example5CantorCharacter 0 1 := by
    have hc := (Lp.coeFn_compMeasurePreserving f example5_evenFibreFactor.preserves).symm
    change (f ∘ example5_evenFibreFactor.toFun) =ᵐ[T.measure] example5_evenFibreFactor.pullback f at hc
    rw [show example5_evenFibreFactor.pullback f = circlePairFourierLp T.measure n from hf] at hc
    exact hc.trans (circlePairFourierLp_ae_eq T.measure n)
  have hr' := speedTwoFibreFlip_preserving.quasiMeasurePreserving.ae_eq_comp hr
  obtain ⟨x, hx, hx'⟩ := (hr.and hr').exists
  change f (example5_evenFibreFactor.toFun x) = example5CantorCharacter 0 1 x at hx
  change f (example5_evenFibreFactor.toFun (speedTwoFibreFlip x)) =
    example5CantorCharacter 0 1 (speedTwoFibreFlip x) at hx'
  rw [evenFibreFactor_flip, hx] at hx'
  change fourier 0 x.1 * fourier 1 x.2 =
    fourier 0 x.1 * fourier 1 (x.2 + ((1 / 2 : ℝ) : 𝕋)) at hx'
  simp only [fourier_zero, one_mul] at hx'
  have hneg := fourier_add_half_inv_index (T := 1) (n := 1) one_ne_zero zero_lt_one x.2
  have he : fourier 1 x.2 = -fourier 1 x.2 := hx'.trans (by simpa only [Int.cast_one, div_one] using hneg)
  have hz : fourier 1 x.2 = 0 := by linear_combination (1 / 2 : ℂ) * he
  have hn : ‖fourier 1 x.2‖ = 1 := Circle.norm_coe _
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

/-- The factor in Example 5 does not inherit p-generation. -/
theorem example5_doubledFactor_not_isUGenerated
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    ¬ (circleSkew cantorCircleMeasure 2).IsUGenerated {p} :=
  example5_evenFibreFactor.not_isUGenerated_of_pullback_range {p}
    (fun _ hq ↦ (Set.mem_singleton_iff.mp hq).symm ▸
      example5_doubledFactor_ultrafilter_range_le p hp hsupp) example5_evenFibreFactor_proper


private theorem speedFour_ultrafilterOperator_eq
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    ultrafilterOperator (circleSkew cantorCircleMeasure 4).koopmanRep p =
      ultrafilterOperator example5CantorSystem.koopmanRep p := by
  let μ := example5CantorSystem.measure
  let U : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    ultrafilterOperator (circleSkew cantorCircleMeasure 4).koopmanRep p
  let V : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := ultrafilterOperator example5CantorSystem.koopmanRep p
  let D := U - V
  have hs : Submodule.span ℂ (Set.range (circlePairFourierLp μ)) ≤ D.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change U (circlePairFourierLp μ n) - V (circlePairFourierLp μ n) = 0
    have hu := cantorSpeed_ultrafilter_eigenvector 4 n p hp hsupp
    have hv := example5_cantor_ultrafilter_eigenvector n p hp hsupp
    change U (circlePairFourierLp μ n) =
      cantorFourier ((-(n 1) * 4 : ℤ) : ℝ) • circlePairFourierLp μ n at hu
    change V (circlePairFourierLp μ n) =
      cantorFourier ((-(n 1) : ℤ) : ℝ) • circlePairFourierLp μ n at hv
    have hCoeff : cantorFourier ((-(n 1) * 4 : ℤ) : ℝ) = cantorFourier ((-(n 1) : ℤ) : ℝ) := by
      rw [mul_comm, Int.cast_mul, Int.cast_ofNat, cantorFourier_four_mul]
    rw [hu, hv, hCoeff, sub_self]
  have ht := Submodule.topologicalClosure_minimal _ hs D.isClosed_ker
  rw [circlePairFourierLp_closure_span] at ht
  change U = V
  apply ContinuousLinearMap.ext
  intro f
  exact sub_eq_zero.mp (ht Submodule.mem_top)

/-- The speed-four subfactor of Example 5 is generated by the original ultrafilter. -/
theorem example5_speedFour_isUGenerated
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    (circleSkew cantorCircleMeasure 4).IsUGenerated {p} := by
  let T := circleSkew cantorCircleMeasure 4
  have htranslate (f : BoundedObservable 𝕏) :
      T.ultrafilterTranslate p f = example5CantorSystem.ultrafilterTranslate p f := by
    unfold System.ultrafilterTranslate
    change BoundedObservable.ofLp
        (ultrafilterOperator T.koopmanRep p (f.l2 T.measure)) f.bound f.bound_nonneg = _
    rw [speedFour_ultrafilterOperator_eq p hp hsupp]
    rfl
  have hsub : example5CantorSystem.generatedProducts {p} ⊆ T.generatedProducts {p} := by
    rintro _ ⟨n, q, f, hq, rfl⟩
    have he : q = fun _ ↦ p := funext fun i ↦ Set.mem_singleton_iff.mp (hq i)
    subst q
    refine ⟨n, fun _ ↦ p, f, fun _ ↦ rfl, ?_⟩
    unfold System.ultrafilterProduct
    simp_rw [htranslate]
    rfl
  exact (example5_cantor_isUGenerated p hp hsupp).mono (Submodule.span_mono hsub)

/-- The p-generated σ-algebra of the speed-two factor is precisely the σ-algebra pulled
back from its speed-four factor, with the measurable null sets adjoined. -/
theorem example5_doubledFactor_generatedSigma_eq
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    (circleSkew cantorCircleMeasure 2).generatedSigma {p} =
      MeasurableSpace.comap example5_evenFibreFactor.toFun (inferInstance : MeasurableSpace 𝕏) ⊔
        MeasurableSpace.generateFrom
          {A : Set 𝕏 | MeasurableSet A ∧ (circleSkew cantorCircleMeasure 2).measure A = 0} := by
  let T := circleSkew cantorCircleMeasure 2
  let R := circleSkew cantorCircleMeasure 4
  let π := example5_evenFibreFactor
  let σ : MeasurableSpace 𝕏 × MeasurableSpace 𝕏 :=
    (MeasurableSpace.comap π.toFun (inferInstance : MeasurableSpace 𝕏),
      MeasurableSpace.generateFrom {A : Set 𝕏 | MeasurableSet A ∧ T.measure A = 0})
  change T.generatedSigma {p} = σ.1 ⊔ σ.2
  have hnull {A : Set 𝕏} (hm : MeasurableSet A) (hn : T.measure A = 0) :
      @MeasurableSet 𝕏 (σ.1 ⊔ σ.2) A :=
    (show σ.2 ≤ σ.1 ⊔ σ.2 from le_sup_right) A
      (MeasurableSpace.measurableSet_generateFrom ⟨hm, hn⟩)
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro A (⟨hA, ha⟩ | ⟨q, hq, v, B, hB, rfl⟩)
    · exact hnull hA ha
    · have hqp : q = p := Set.mem_singleton_iff.mp hq
      subst q
      let x := ultrafilterOperator T.koopmanRep p v
      have hx : x ∈ π.pullback.toLinearMap.range :=
        example5_doubledFactor_ultrafilter_range_le p hp hsupp (LinearMap.mem_range_self _ v)
      obtain ⟨f, hf⟩ := hx
      have heq : x =ᵐ[T.measure] f ∘ π.toFun := by
        change π.pullback f = x at hf
        rw [← hf]
        exact Lp.coeFn_compMeasurePreserving f π.preserves
      let A := x ⁻¹' B
      let C := (f ∘ π.toFun) ⁻¹' B
      have hAm : MeasurableSet A := (Lp.stronglyMeasurable x).measurable hB
      have hFm : MeasurableSet (f ⁻¹' B) := (Lp.stronglyMeasurable f).measurable hB
      have hCm : MeasurableSet C := π.preserves.measurable hFm
      have hC : @MeasurableSet 𝕏 (σ.1 ⊔ σ.2) C :=
        (show σ.1 ≤ σ.1 ⊔ σ.2 from le_sup_left) C ⟨f ⁻¹' B, hFm, rfl⟩
      have hAC : T.measure (A \ C) = 0 := by
        apply measure_mono_null _ (ae_iff.mp heq)
        intro w hw he
        apply hw.2
        change (f ∘ π.toFun) w ∈ B
        rw [← he]
        exact hw.1
      have hCA : T.measure (C \ A) = 0 := by
        apply measure_mono_null _ (ae_iff.mp heq)
        intro w hw he
        apply hw.2
        change x w ∈ B
        rw [he]
        exact hw.1
      have hSet : A = (A \ C) ∪ (C \ (C \ A)) := by
        ext w
        simp only [Set.mem_union, Set.mem_sdiff]
        tauto
      change @MeasurableSet 𝕏 (σ.1 ⊔ σ.2) A
      rw [hSet]
      exact (hnull (hAm.diff hCm) hAC).union (hC.diff (hnull (hCm.diff hAm) hCA))
  · apply sup_le
    · have hm := π.measurable_generatedSigma (P := {p}) (Q := {p}) (fun _ h ↦ h)
      rw [R.generatedSigma_eq_of_isUGenerated (example5_speedFour_isUGenerated p hp hsupp)] at hm
      exact measurable_iff_comap_le.mp hm
    · apply MeasurableSpace.generateFrom_le
      rintro A ⟨hA, hAn⟩
      exact T.generatedSigma_measurableSet_null {p} hA hAn

end Mixing
