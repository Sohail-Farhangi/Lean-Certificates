/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorSpectral
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # The sum-coordinate factor of the Cantor skew products -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Mixing

local notation "𝕋" => UnitAddCircle
local notation "haar" => (AddCircle.haarAddCircle : Measure 𝕋)

/-- The base translation angle in the factor of Example 6. -/
def example6Angle (x : 𝕋 × 𝕋) : 𝕋 := x.1 + (2 : ℤ) • x.2

@[fun_prop]
theorem example6Angle_continuous : Continuous example6Angle := by
  unfold example6Angle
  fun_prop

/-- The two independent Cantor base coordinates. -/
noncomputable def example6Base : Measure (𝕋 × 𝕋) := cantorCircleMeasure.prod cantorCircleMeasure

instance : IsProbabilityMeasure example6Base := by
  unfold example6Base
  infer_instance

/-- The sum-fibre factor from Example 6, over the unchanged pair of Cantor base coordinates. -/
noncomputable def example6SumSystem : System (Multiplicative ℤ) ((𝕋 × 𝕋) × 𝕋) where
  measure := example6Base.prod haar
  probability := inferInstance
  act g x := (x.1, x.2 + g.toAdd • example6Angle x.1)
  act_one := by
    funext x
    simp
  act_mul g h := by
    funext x
    change (x.1, x.2 + (g.toAdd + h.toAdd) • example6Angle x.1) =
      (x.1, x.2 + h.toAdd • example6Angle x.1 + g.toAdd • example6Angle x.1)
    rw [add_zsmul]
    congr 1
    abel
  preserves g := by
    refine (MeasurePreserving.id example6Base).skew_product
      (g := fun x y ↦ y + g.toAdd • example6Angle x) (by fun_prop) ?_
    exact ae_of_all _ fun x ↦ (measurePreserving_add_right haar
      (g.toAdd • example6Angle x)).map_eq

/-- Grouping the two Cantor coordinates and the two Haar coordinates preserves the product law. -/
theorem measurePreserving_reorder_cantor_haar :
    MeasurePreserving (fun x : (𝕋 × 𝕋) × (𝕋 × 𝕋) ↦ ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      ((cantorCircleMeasure.prod haar).prod (cantorCircleMeasure.prod haar))
      (example6Base.prod ((haar).prod haar)) := by
  let ν := cantorCircleMeasure
  let m := haar
  have h₁ := measurePreserving_prodAssoc ν m (ν.prod m)
  have h₂ := (MeasurePreserving.id ν).prod
    ((measurePreserving_prodAssoc m ν m).symm MeasurableEquiv.prodAssoc)
  have h₃ := (MeasurePreserving.id ν).prod
    ((Measure.measurePreserving_swap (μ := m) (ν := ν)).prod (MeasurePreserving.id m))
  have h₄ := (MeasurePreserving.id ν).prod (measurePreserving_prodAssoc ν m m)
  have h₅ := (measurePreserving_prodAssoc ν ν (m.prod m)).symm MeasurableEquiv.prodAssoc
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

/-- The map retaining the two base coordinates and summing the two fibre coordinates
is the factor map used in Example 6. -/
noncomputable def example6SumFactor : FactorMap example6CantorSystem example6SumSystem where
  toFun x := ((x.1.1, x.2.1), x.1.2 + x.2.2)
  preserves :=
    ((MeasurePreserving.id example6Base).prod
      (measurePreserving_fst.comp (measurePreserving_add_prod haar haar))).comp
        measurePreserving_reorder_cantor_haar
  equivariant g := by
    funext x
    change ((x.1.1, x.2.1),
        x.1.2 + (g.toAdd * 1) • x.1.1 + (x.2.2 + (g.toAdd * 2) • x.2.1)) =
      ((x.1.1, x.2.1), x.1.2 + x.2.2 +
        g.toAdd • (x.1.1 + (2 : ℤ) • x.2.1))
    rw [mul_one, zsmul_add, smul_smul]
    congr 1
    abel

/-- The same sum-coordinate factor is a factor of the product of two copies of the
speed-one Cantor skew rotation, as asserted in Example 7. -/
noncomputable def example7SumFactor :
    FactorMap ((circleSkew cantorCircleMeasure 1).prod (circleSkew cantorCircleMeasure 1))
      example6SumSystem :=
  example6SumFactor.comp (example7_productFactor cantorCircleMeasure)

private noncomputable def continuousCircleIntegral (μ : Measure 𝕋) [IsFiniteMeasure μ] :
    C(𝕋, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp (E := ℂ) 1 μ ℂ)

private theorem continuousCircleIntegral_apply (μ : Measure 𝕋) [IsFiniteMeasure μ] (f : C(𝕋, ℂ)) :
    continuousCircleIntegral μ f = ∫ x, f x ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp (E := ℂ) 1 μ ℂ f) = _
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 1) μ f)

theorem circleMeasure_eq_of_fourier_eq (μ ν : Measure 𝕋)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℤ, (∫ x, fourier n x ∂μ) = ∫ x, fourier n x ∂ν) : μ = ν := by
  let Ψ := continuousCircleIntegral μ - continuousCircleIntegral ν
  have hspan : Submodule.span ℂ (Set.range (fourier (T := 1))) ≤ Ψ.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change continuousCircleIntegral μ (fourier n) - continuousCircleIntegral ν (fourier n) = 0
    rw [continuousCircleIntegral_apply, continuousCircleIntegral_apply, h, sub_self]
  have ht := Submodule.topologicalClosure_minimal _ hspan Ψ.isClosed_ker
  rw [span_fourier_closure_eq_top] at ht
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : C(𝕋, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hg : continuousCircleIntegral μ g - continuousCircleIntegral ν g = 0 := ht Submodule.mem_top
  rw [continuousCircleIntegral_apply, continuousCircleIntegral_apply] at hg
  change (∫ x, (f x : ℂ) ∂μ) - (∫ x, (f x : ℂ) ∂ν) = 0 at hg
  have hμ : (∫ x, (f x : ℂ) ∂μ) = ((∫ x, f x ∂μ : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ) (μ := μ) (f := fun x ↦ f x)
  have hν : (∫ x, (f x : ℂ) ∂ν) = ((∫ x, f x ∂ν : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ) (μ := ν) (f := fun x ↦ f x)
  exact Complex.ofReal_injective ((hμ.symm.trans (sub_eq_zero.mp hg)).trans hν)

theorem integral_haar_fourier_zero (n : ℤ) (hn : n ≠ 0) :
    (∫ x, fourier n x ∂haar) = 0 :=
  integral_eq_zero_of_add_right_eq_neg (μ := haar) (fourier_add_half_inv_index hn (by norm_num))

/-- The translation angle in the sum-coordinate factor is Haar distributed. -/
theorem example6Angle_measurePreserving : MeasurePreserving example6Angle example6Base haar := by
  have hm := example6Angle_continuous.measurable
  let _ : IsProbabilityMeasure (example6Base.map example6Angle) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  refine ⟨hm, circleMeasure_eq_of_fourier_eq _ _ fun n ↦ ?_⟩
  rw [integral_map hm.aemeasurable (fourier (T := 1) n).continuous.aestronglyMeasurable]
  by_cases hn : n = 0
  · subst n
    simp only [fourier_zero, integral_const, probReal_univ, one_smul]
  · rw [integral_haar_fourier_zero n hn]
    have hpoint (x : 𝕋 × 𝕋) : fourier n (example6Angle x) =
        fourier n x.1 * fourier (2 * n) x.2 := by
      simp only [example6Angle, fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
        smul_smul, mul_comm n 2]
    simpa only [hpoint, example6Base] using example6_base_fourier_integral_zero n hn


open scoped ComplexConjugate InnerProductSpace in
/-- Every L² weight on the Cantor base has vanishing Fourier coefficients after
transfer to the Haar-distributed translation angle. -/
theorem example6_weighted_angle_fourier_tendsto (h : Lp ℂ 2 example6Base) :
    Tendsto (fun n : ℤ ↦ ∫ x, conj (h x) * fourier n (example6Angle x) ∂example6Base)
      cofinite (𝓝 0) := by
  let W : Lp ℂ 2 haar →ₗᵢ[ℂ] Lp ℂ 2 example6Base :=
    Lp.compMeasurePreservingₗᵢ ℂ example6Angle example6Angle_measurePreserving
  let v (n : ℤ) := W (fourierLp (T := 1) 2 n)
  have hON : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪W (fourierLp (T := 1) 2 i), W (fourierLp (T := 1) 2 j)⟫_ℂ = _
    rw [W.inner_map_map]
    exact (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) i j
  have hs (n : ℤ) : Real.sqrt (‖⟪v n, h⟫_ℂ‖ ^ 2) = ‖⟪h, v n⟫_ℂ‖ := by
    rw [Real.sqrt_sq (norm_nonneg _), norm_inner_symm]
  have ht : Tendsto (fun n ↦ ⟪h, v n⟫_ℂ) cofinite (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
      (hON.inner_products_summable h).tendsto_cofinite_zero
    change Tendsto (fun n : ℤ ↦ Real.sqrt (‖⟪v n, h⟫_ℂ‖ ^ 2)) cofinite
      (𝓝 (Real.sqrt 0)) at hsqrt
    simpa only [hs, Real.sqrt_zero] using hsqrt
  have hv (n : ℤ) : v n =ᵐ[example6Base] fun x ↦ fourier n (example6Angle x) :=
    (Lp.coeFn_compMeasurePreserving _ example6Angle_measurePreserving).trans
      (example6Angle_measurePreserving.quasiMeasurePreserving.ae_eq_comp
        (coeFn_fourierLp (T := 1) 2 n))
  have heq (n : ℤ) : ⟪h, v n⟫_ℂ =
      ∫ x, conj (h x) * fourier n (example6Angle x) ∂example6Base := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv n] with x hx
    rw [hx, RCLike.inner_apply']
  simpa only [heq] using ht

open scoped ComplexConjugate in
/-- The weighted decay holds on each nonzero fibre Fourier mode. -/
theorem example6_weighted_fibre_fourier_tendsto (h : Lp ℂ 2 example6Base)
    (t : ℤ) (ht : t ≠ 0) :
    Tendsto (fun n : ℤ ↦ ∫ x, conj (h x) * fourier (t * n) (example6Angle x) ∂example6Base)
      cofinite (𝓝 0) := by
  have hinj : Function.Injective (fun n : ℤ ↦ t * n) := fun _ _ h ↦ mul_left_cancel₀ ht h
  exact (example6_weighted_angle_fourier_tendsto h).comp hinj.tendsto_cofinite

end Mixing
