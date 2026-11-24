module

public import Mixing.GeneratedMultiplier
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The closed span of products of ultrafilter translates -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Topology

namespace Mixing

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

namespace BoundedObservable

theorem l2_eq_of_ae_eq {μ : Measure X} [IsFiniteMeasure μ] {f g : BoundedObservable X}
    (h : f =ᵐ[μ] g) : f.l2 μ = g.l2 μ :=
  Lp.ext ((f.coe_l2 μ).trans (h.trans (g.coe_l2 μ).symm))

/-- Sums of bounded measurable functions. -/
def add (f g : BoundedObservable X) : BoundedObservable X where
  toFun x := f x + g x
  measurable := f.measurable.add g.measurable
  bound := f.bound + g.bound
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  norm_le x := (norm_add_le _ _).trans (add_le_add (f.norm_le x) (g.norm_le x))

@[simp] theorem add_apply (f g : BoundedObservable X) (x : X) : f.add g x = f x + g x := rfl

theorem l2_add (f g : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    (f.add g).l2 μ = f.l2 μ + g.l2 μ := by
  apply Lp.ext
  filter_upwards [(f.add g).coe_l2 μ, f.coe_l2 μ, g.coe_l2 μ,
    Lp.coeFn_add (f.l2 μ) (g.l2 μ)] with x hfg hf hg hAdd
  rw [hfg, hAdd, Pi.add_apply, hf, hg, add_apply]

theorem l2_sub (f g : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    (f.sub g).l2 μ = f.l2 μ - g.l2 μ := by
  apply Lp.ext
  filter_upwards [(f.sub g).coe_l2 μ, f.coe_l2 μ, g.coe_l2 μ,
    Lp.coeFn_sub (f.l2 μ) (g.l2 μ)] with x hfg hf hg hSub
  rw [hfg, hSub, Pi.sub_apply, hf, hg, sub_apply]

theorem l2_const_mul (c : ℂ) (f : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    ((const c).mul f).l2 μ = c • f.l2 μ := by
  apply Lp.ext
  filter_upwards [((const c).mul f).coe_l2 μ, f.coe_l2 μ,
    Lp.coeFn_smul c (f.l2 μ)] with x hcf hf hs
  rw [hcf, hs, Pi.smul_apply, hf, mul_apply, const_apply, smul_eq_mul]

/-- Pointwise multiplication by a bounded observable is a bounded linear map on L². -/
noncomputable def mulL2 (f : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 ((f.memLp μ ⊤).toLp f)

theorem mulL2_l2 (f g : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    f.mulL2 μ (g.l2 μ) = (f.mul g).l2 μ := by
  apply Lp.ext
  have hMul := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((f.memLp μ ⊤).toLp f) (g.l2 μ)
  change f.mulL2 μ (g.l2 μ) =ᵐ[μ] _ at hMul
  filter_upwards [hMul, (f.memLp μ ⊤).coeFn_toLp, g.coe_l2 μ, (f.mul g).coe_l2 μ]
    with x hM hf hg hfg
  rw [hM, hfg, hf, hg]
  rfl

theorem norm_l2_sq (f : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    ‖f.l2 μ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hi := f.inner_l2 f μ
  have hf : Integrable (fun x => conj (f x) * f x) μ :=
    (f.conjugate.mul f).integrable μ
  have hr := congrArg Complex.re hi
  change RCLike.re (inner ℂ (f.l2 μ) (f.l2 μ)) =
    RCLike.re (∫ x, conj (f x) * f x ∂μ) at hr
  rw [← integral_re hf, inner_self_eq_norm_sq] at hr
  refine hr.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
  change RCLike.re (conj (f x) * f x) = ‖f x‖ ^ 2
  rw [← RCLike.inner_apply', inner_self_eq_norm_sq]

/-- Uniformly bounded almost-everywhere convergence implies L² convergence. -/
theorem tendsto_l2_of_ae_tendsto (μ : Measure X) [IsFiniteMeasure μ]
    (f : ℕ → BoundedObservable X) (g : BoundedObservable X)
    {C : ℝ} (hC : ∀ n x, ‖f n x‖ ≤ C)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (f n).l2 μ) atTop (𝓝 (g.l2 μ)) := by
  have hDom (n : ℕ) (x : X) : ‖‖f n x - g x‖ ^ 2‖ ≤ (C + g.bound) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_sub_le _ _).trans (add_le_add (hC n x) (g.norm_le x))) _
  have hn : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 (∫ _ : X, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (C + g.bound) ^ 2)
    · exact fun n => (((f n).measurable.sub g.measurable).norm.pow_const _).aestronglyMeasurable
    · exact integrable_const _
    · exact fun n => Eventually.of_forall (hDom n)
    · exact hfg.mono fun x hx => by
        simpa using (hx.sub (tendsto_const_nhds (x := g x))).norm.pow 2
  have hn' : Tendsto (fun n => ‖(f n).l2 μ - g.l2 μ‖ ^ 2) atTop (𝓝 0) := by
    simpa only [← l2_sub, norm_l2_sq, sub_apply, integral_zero] using hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto _).comp hn'

end BoundedObservable

namespace System

/-- The closed linear span of all finite products of ultrafilter translates. -/
noncomputable def generatedProductsClosure (T : System G X) (U : Set (Ultrafilter G)) :
    Submodule ℂ (Lp ℂ 2 T.measure) :=
  (Submodule.span ℂ (T.generatedProducts U)).topologicalClosure

theorem isClosed_generatedProductsClosure (T : System G X) (U : Set (Ultrafilter G)) :
    IsClosed (T.generatedProductsClosure U : Set (Lp ℂ 2 T.measure)) :=
  (Submodule.span ℂ (T.generatedProducts U)).isClosed_topologicalClosure

theorem ultrafilterProduct_mem_generatedProductsClosure (T : System G X) (U : Set (Ultrafilter G))
    {n : ℕ} (p : Fin n → Ultrafilter G) (hp : ∀ i, p i ∈ U)
    (f : Fin n → BoundedObservable X) :
    (T.ultrafilterProduct p f).l2 T.measure ∈ T.generatedProductsClosure U :=
  (Submodule.span ℂ (T.generatedProducts U)).le_topologicalClosure
    (Submodule.subset_span ⟨n, p, f, hp, rfl⟩)

theorem const_mem_generatedProductsClosure (T : System G X) (U : Set (Ultrafilter G)) (c : ℂ) :
    (BoundedObservable.const c).l2 T.measure ∈ T.generatedProductsClosure U := by
  let p : Fin 0 → Ultrafilter G := Fin.elim0
  let f : Fin 0 → BoundedObservable X := Fin.elim0
  have h := (T.generatedProductsClosure U).smul_mem c
    (T.ultrafilterProduct_mem_generatedProductsClosure U p (fun i => Fin.elim0 i) f)
  rw [← BoundedObservable.l2_const_mul] at h
  convert h using 1
  apply BoundedObservable.l2_eq_of_ae_eq
  exact Eventually.of_forall fun x => by simp [ultrafilterProduct]

theorem ultrafilterTranslate_mem_generatedProductsClosure (T : System G X)
    (U : Set (Ultrafilter G)) {p : Ultrafilter G} (hp : p ∈ U) (f : BoundedObservable X) :
    (T.ultrafilterTranslate p f).l2 T.measure ∈ T.generatedProductsClosure U := by
  have h := T.ultrafilterProduct_mem_generatedProductsClosure U
    (n := 1) (fun _ => p) (fun _ => hp) (fun _ => f)
  convert h using 1
  apply BoundedObservable.l2_eq_of_ae_eq
  exact Eventually.of_forall fun x => by simp [ultrafilterProduct]

private theorem gen_product_mul (T : System G X) (U : Set (Ultrafilter G))
    {n k : ℕ} (p : Fin n → Ultrafilter G) (q : Fin k → Ultrafilter G)
    (hp : ∀ i, p i ∈ U) (hq : ∀ i, q i ∈ U)
    (f : Fin n → BoundedObservable X) (g : Fin k → BoundedObservable X) :
    ((T.ultrafilterProduct p f).mul (T.ultrafilterProduct q g)).l2 T.measure ∈
      T.generatedProducts U := by
  refine ⟨n + k, Fin.addCases p q, Fin.addCases f g, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hp j
    · simpa only [Fin.addCases_right] using hq j
  · apply BoundedObservable.l2_eq_of_ae_eq
    exact Eventually.of_forall fun x => by
      simp only [ultrafilterProduct, BoundedObservable.mul_apply, BoundedObservable.prod_apply,
        Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]

private theorem mulL2_mem_of_maps_products (T : System G X) (U : Set (Ultrafilter G))
    (f : BoundedObservable X)
    (h : MapsTo (f.mulL2 T.measure) (T.generatedProducts U)
      (T.generatedProductsClosure U : Set _)) :
    MapsTo (f.mulL2 T.measure) (T.generatedProductsClosure U : Set _)
      (T.generatedProductsClosure U : Set _) := by
  let M := T.generatedProductsClosure U
  let L := f.mulL2 T.measure
  have hSpan : Submodule.span ℂ (T.generatedProducts U) ≤ M.comap (L : _ →ₗ[ℂ] _) :=
    Submodule.span_le.mpr h
  exact closure_minimal hSpan ((T.isClosed_generatedProductsClosure U).preimage L.continuous)

theorem mul_mem_generatedProductsClosure (T : System G X) (U : Set (Ultrafilter G))
    (f g : BoundedObservable X)
    (hf : f.l2 T.measure ∈ T.generatedProductsClosure U)
    (hg : g.l2 T.measure ∈ T.generatedProductsClosure U) :
    (f.mul g).l2 T.measure ∈ T.generatedProductsClosure U := by
  have hGen (n : ℕ) (p : Fin n → Ultrafilter G) (hp : ∀ i, p i ∈ U)
      (b : Fin n → BoundedObservable X) :
      MapsTo ((T.ultrafilterProduct p b).mulL2 T.measure) (T.generatedProductsClosure U : Set _)
        (T.generatedProductsClosure U : Set _) := by
    apply T.mulL2_mem_of_maps_products U
    rintro _ ⟨k, q, c, hq, rfl⟩
    rw [BoundedObservable.mulL2_l2]
    exact (Submodule.span ℂ (T.generatedProducts U)).le_topologicalClosure
      (Submodule.subset_span (T.gen_product_mul U p q hp hq b c))
  rw [← BoundedObservable.mulL2_l2]
  apply T.mulL2_mem_of_maps_products U f _ hg
  rintro _ ⟨n, p, b, hp, rfl⟩
  have h := hGen n p hp b hf
  rw [BoundedObservable.mulL2_l2] at h ⊢
  convert h using 1
  apply BoundedObservable.l2_eq_of_ae_eq
  exact Eventually.of_forall fun _ => mul_comm _ _

end System

end Mixing
