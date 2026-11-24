/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.FactorJoiningLift
public import Mixing.RelativeFiniteFrameDisjointness
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate InnerProductSpace ProbabilityTheory Topology

/-- Coordinates in an orthonormal finite family, allowing zero slots. -/
theorem sum_inner_smul_eq_of_mem_span
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
    (v : Fin n → H) (hNorm : ∀ i, v i = 0 ∨ ‖v i‖ = 1)
    (hOrth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0)
    {w : H} (hw : w ∈ Submodule.span ℂ (range v)) :
    (∑ i, inner ℂ (v i) w • v i) = w := by
  let L : H →L[ℂ] H := ∑ i, (InnerProductSpace.toDual ℂ H (v i)).smulRight (v i)
  have hL (z : H) : L z = ∑ i, inner ℂ (v i) z • v i := by
    simp only [L, sum_apply, ContinuousLinearMap.smulRight_apply,
      InnerProductSpace.toDual_apply_apply]
  have hSpan : Submodule.span ℂ (range v) ≤ (L - ContinuousLinearMap.id ℂ H).ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    change L (v i) - v i = 0
    apply sub_eq_zero.mpr
    rw [hL, Finset.sum_eq_single i]
    · rcases hNorm i with h | h
      · simp [h]
      · simp [inner_self_eq_norm_sq_to_K, h]
    · intro j _ hj
      rw [hOrth j i hj, zero_smul]
    · simp
  have he : L w - w = 0 := hSpan hw
  rw [hL] at he
  exact sub_eq_zero.mp he

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable {E : System G X} {B : System G Y}

/-- Passing from finite L² sums to measurable representatives commutes with
scalar multiplication and summation, almost everywhere. -/
theorem ae_coe_toLp_sum_smul {μ : Measure X} {n : ℕ} {v : Fin n → X → ℂ}
    (h : ∀ j, MemLp (v j) 2 μ) (a : Fin n → ℂ) :
    (∑ j, a j • (h j).toLp (v j) : Lp ℂ 2 μ) =ᵐ[μ] fun x => ∑ j, a j * v j x := by
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hAll : ∀ᵐ x ∂μ, ∀ j : Fin n, (a j • (h j).toLp (v j)) x = a j * v j x := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_smul (a j) ((h j).toLp (v j)), (h j).coeFn_toLp] with x hx hV
    rw [hx, Pi.smul_apply, hV, smul_eq_mul]
  filter_upwards [hAll] with x hx
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hx j)

/-- An invariant conditional L² span given by orthonormal slots, with zero
slots permitted for fibres where its rank is smaller. The equations refer
to the specified kernel on the base and do not assume globally bounded
representatives of the slots. -/
structure ConditionalOrthogonalFrame (π : FactorMap E B) (κ : Kernel Y X) (n : ℕ) where
  vector : Fin n → Lp ℂ 2 E.measure
  fibre : ∀ᵐ y ∂B.measure, ∃ h : ∀ i, MemLp (vector i) 2 (κ y),
    (∀ i, (h i).toLp (vector i) = 0 ∨ ‖(h i).toLp (vector i)‖ = 1) ∧
    ∀ i j, i ≠ j → inner ℂ ((h i).toLp (vector i)) ((h j).toLp (vector j)) = 0
  invariant : ∀ g i, ∀ᵐ y ∂B.measure,
    ∃ (h : ∀ j, MemLp (vector j) 2 (κ y))
      (h' : MemLp (fun x => vector i (E.act g x)) 2 (κ y)),
      h'.toLp (fun x => vector i (E.act g x)) ∈
        Submodule.span ℂ (range fun j => (h j).toLp (vector j))

/-- The usual invariance equation for a finitely generated base module
implies fibrewise invariance of the slot span after disintegration. The
fibre orthonormality is supplied explicitly. -/
theorem ConditionalOrthogonalFrame.exists_of_measurable_module
    {π : FactorMap E B} {κ : Kernel Y X} {n : ℕ} (v : Fin n → Lp ℂ 2 E.measure)
    (hMarginal : κ ∘ₘ B.measure = E.measure)
    (hFibre : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    (hOrth : ∀ᵐ y ∂B.measure, ∃ h : ∀ i, MemLp (v i) 2 (κ y),
      (∀ i, (h i).toLp (v i) = 0 ∨ ‖(h i).toLp (v i)‖ = 1) ∧
      ∀ i j, i ≠ j → inner ℂ ((h i).toLp (v i)) ((h j).toLp (v j)) = 0)
    (hTranslate : ∀ g i, ∃ a : Fin n → Y → ℂ,
      ∀ᵐ x ∂E.measure, v i (E.act g x) = ∑ j, a j (π.toFun x) * v j x) :
    ∃ A : ConditionalOrthogonalFrame π κ n, A.vector = v := by
  refine ⟨⟨v, hOrth, ?_⟩, rfl⟩
  intro g i
  obtain ⟨a, he⟩ := hTranslate g i
  have hAE : ae (κ ∘ₘ B.measure) = ae E.measure := congrArg ae hMarginal
  rw [← hAE] at he
  filter_upwards [Measure.ae_ae_of_ae_comp he, hFibre, hOrth] with y hA hF hO
  obtain ⟨h, _, _⟩ := hO
  let q : Lp ℂ 2 (κ y) := ∑ j, a j y • (h j).toLp (v j)
  have hq : q =ᵐ[κ y] fun x => v i (E.act g x) := by
    filter_upwards [ae_coe_toLp_sum_smul h (fun j => a j y), hA, hF] with x hx hAx hFx
    change q x = _ at hx
    rw [hx, hAx, hFx]
  have hMem := (memLp_congr_ae hq).mp (Lp.memLp q)
  have hToLp : hMem.toLp (fun x => v i (E.act g x)) = q :=
    Lp.ext (hMem.coeFn_toLp.trans hq.symm)
  refine ⟨h, hMem, ?_⟩
  rw [hToLp]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

private def conditionalCoefficient {π : FactorMap E B} {κ : Kernel Y X} {n : ℕ}
    (A : ConditionalOrthogonalFrame π κ n) (g : G) (i j : Fin n) (y : Y) : ℂ :=
  ∫ x, conj (A.vector j x) * A.vector i (E.act g x) ∂κ y

private theorem measurable_conditionalCoefficient {π : FactorMap E B} {κ : Kernel Y X} {n : ℕ}
    (A : ConditionalOrthogonalFrame π κ n) (g : G) (i j : Fin n) :
    Measurable (conditionalCoefficient A g i j) := by
  let f (x : X) := conj (A.vector j x) * A.vector i (E.act g x)
  have hF : Measurable f :=
    (Complex.continuous_conj.measurable.comp (Lp.stronglyMeasurable (A.vector j)).measurable).mul
      ((Lp.stronglyMeasurable (A.vector i)).measurable.comp (E.preserves g).measurable)
  exact (hF.stronglyMeasurable.integral_kernel (κ := κ)).measurable

private def clippedConditionalCoefficient {π : FactorMap E B} {κ : Kernel Y X} {n : ℕ}
    (A : ConditionalOrthogonalFrame π κ n) (g : G) (i j : Fin n) : BoundedObservable Y where
  toFun y := if ‖conditionalCoefficient A g i j y‖ ≤ 1 then conditionalCoefficient A g i j y else 0
  measurable := (measurable_conditionalCoefficient A g i j).ite
    (measurableSet_le (measurable_conditionalCoefficient A g i j).norm measurable_const)
    measurable_const
  bound := 1
  bound_nonneg := zero_le_one
  norm_le y := by split_ifs with h <;> simp [h]

private theorem ae_conditionalCoefficient_bounds_and_expansion
    {π : FactorMap E B} {κ : Kernel Y X} {n : ℕ}
    (A : ConditionalOrthogonalFrame π κ n)
    (hEq : ∀ g, ∀ᵐ y ∂B.measure, MeasurePreserving (E.act g) (κ y) (κ (B.act g y)))
    (g : G) (i : Fin n) :
    ∀ᵐ y ∂B.measure, (∀ j, ‖conditionalCoefficient A g i j y‖ ≤ 1) ∧
      ∀ᵐ x ∂κ y, A.vector i (E.act g x) =
        ∑ j, conditionalCoefficient A g i j y * A.vector j x := by
  filter_upwards [A.fibre, A.invariant g i, (B.preserves g).quasiMeasurePreserving.ae A.fibre,
    hEq g] with y hy hinv hgy hyEq
  obtain ⟨h, hNorm, hOrth⟩ := hy
  obtain ⟨_, hMem, hSpan⟩ := hinv
  obtain ⟨h', hNorm', _⟩ := hgy
  let u (j : Fin n) := (h j).toLp (A.vector j)
  let q := hMem.toLp (fun x => A.vector i (E.act g x))
  let v := (h' i).toLp (A.vector i)
  have hq : q = Lp.compMeasurePreserving (E.act g) hyEq v := by
    apply Lp.ext
    exact hMem.coeFn_toLp.trans
      (((Lp.coeFn_compMeasurePreserving v hyEq).trans
        (hyEq.quasiMeasurePreserving.ae_eq_comp (h' i).coeFn_toLp)).symm)
  have hNormLe (j : Fin n) : ‖u j‖ ≤ 1 := by
    rcases hNorm j with hZero | hOne
    · rw [show u j = 0 from hZero, norm_zero]
      exact zero_le_one
    · exact hOne.le
  have hqLe : ‖q‖ ≤ 1 := by
    rw [hq, Lp.norm_compMeasurePreserving]
    rcases hNorm' i with hZero | hOne
    · rw [show v = 0 from hZero, norm_zero]
      exact zero_le_one
    · exact hOne.le
  have hInner (j : Fin n) : inner ℂ (u j) q = conditionalCoefficient A g i j y := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(h j).coeFn_toLp, hMem.coeFn_toLp] with z hz hqz
    change u j z = A.vector j z at hz
    change q z = A.vector i (E.act g z) at hqz
    rw [hz, hqz, RCLike.inner_apply']
  refine ⟨fun j => ?_, ?_⟩
  · rw [← hInner j]
    exact (norm_inner_le_norm (u j) q).trans (by
      simpa only [mul_one] using mul_le_mul (hNormLe j) hqLe (norm_nonneg _) zero_le_one)
  · have hExp : (∑ j, conditionalCoefficient A g i j y • u j) = q := by
      have he := sum_inner_smul_eq_of_mem_span u hNorm hOrth (w := q) hSpan
      simpa only [hInner] using he
    have hu : (∑ j, conditionalCoefficient A g i j y • u j) =ᵐ[κ y]
        fun x => ∑ j, conditionalCoefficient A g i j y * A.vector j x := by
      exact ae_coe_toLp_sum_smul h (fun j => conditionalCoefficient A g i j y)
    rw [hExp] at hu
    exact hMem.coeFn_toLp.symm.trans hu

/-- Conditional orthonormality and invariance of the fibrewise span produce
an explicit bounded-coefficient relative frame. The coefficients are the
conditional inner products, clipped only at exceptional base points. -/
theorem ConditionalOrthogonalFrame.exists_relativeFiniteFrame
    {π : FactorMap E B} {κ : Kernel Y X} {n : ℕ} (A : ConditionalOrthogonalFrame π κ n)
    (hMarginal : κ ∘ₘ B.measure = E.measure)
    (hFibre : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    (hEq : ∀ g, ∀ᵐ y ∂B.measure, MeasurePreserving (E.act g) (κ y) (κ (B.act g y))) :
    ∃ F : RelativeFiniteFrame π n, F.vector = A.vector := by
  refine ⟨⟨A.vector, clippedConditionalCoefficient A, 1, (fun _ _ _ => le_rfl), ?_⟩, rfl⟩
  intro g i
  have hm₁ : Measurable (fun x => A.vector i (E.act g x)) :=
    (Lp.stronglyMeasurable (A.vector i)).measurable.comp (E.preserves g).measurable
  have hm₂ : Measurable (fun x => ∑ j,
      clippedConditionalCoefficient A g i j (π.toFun x) * A.vector j x) :=
    Finset.measurable_fun_sum _ fun j _ =>
      (((clippedConditionalCoefficient A g i j).measurable.comp π.preserves.measurable).mul
        (Lp.stronglyMeasurable (A.vector j)).measurable)
  have hAE : ae (κ ∘ₘ B.measure) = ae E.measure := congrArg ae hMarginal
  rw [← hAE]
  apply Measure.ae_comp_of_ae_ae (measurableSet_eq_fun hm₁ hm₂)
  filter_upwards [hFibre, ae_conditionalCoefficient_bounds_and_expansion A hEq g i] with y hy hA
  filter_upwards [hy, hA.2] with x hx hExp
  rw [hx, hExp]
  apply Finset.sum_congr rfl
  intro j _
  change conditionalCoefficient A g i j y * A.vector j x =
    (if ‖conditionalCoefficient A g i j y‖ ≤ 1 then conditionalCoefficient A g i j y else 0) *
      A.vector j x
  rw [ite_eq_left (hA.1 j)]

/-- For the canonical disintegration, the conditional frame bridge uses the
factor map's kernel equivariance and fibre support theorems. -/
theorem ConditionalOrthogonalFrame.exists_relativeFiniteFrame_of_factor
    [StandardBorelSpace X] [Nonempty X] [MeasurableEq Y]
    {π : FactorMap E B} {n : ℕ} (A : ConditionalOrthogonalFrame π π.conditionalKernel n) :
    ∃ F : RelativeFiniteFrame π n, F.vector = A.vector := by
  refine A.exists_relativeFiniteFrame π.comp_conditionalKernel π.ae_conditionalKernel_fibre ?_
  intro g
  filter_upwards [π.ae_conditionalKernel_equivariant g] with y hy
  exact ⟨(E.preserves g).measurable, hy⟩

/-- Products of bounded base functions with slots of invariant orthonormal
conditional families for the canonical factor kernel. -/
def FactorMap.conditionalFrameGenerators [StandardBorelSpace X] [Nonempty X]
    (π : FactorMap E B) : Set (Lp ℂ 2 E.measure) :=
  {v | ∃ (n : ℕ) (A : ConditionalOrthogonalFrame π π.conditionalKernel n)
      (i : Fin n) (b : BoundedObservable Y),
    v = (b.comp π.toFun π.preserves.measurable).mulL2 E.measure (A.vector i)}

/-- Fibrewise orthonormal invariant families with dense module span suffice
for the relative finite-frame spanning condition. -/
theorem FactorMap.hasDenseRelativeFrames_of_conditionalFrameGenerators
    [StandardBorelSpace X] [Nonempty X] [MeasurableEq Y] (π : FactorMap E B)
    (hDense : Dense (Submodule.span ℂ π.conditionalFrameGenerators : Set (Lp ℂ 2 E.measure))) :
    π.HasDenseRelativeFrames := by
  apply hDense.mono
  apply Submodule.span_mono
  rintro _ ⟨n, A, i, b, rfl⟩
  obtain ⟨F, hF⟩ := A.exists_relativeFiniteFrame_of_factor
  exact ⟨n, F, i, b, by rw [congrFun hF i]⟩

/-- The squared L² norm is the integral of the pointwise squared norm. -/
theorem lp_two_norm_sq_eq_integral {μ : Measure X} (v : Lp ℂ 2 μ) :
    ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
  have he := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def v v)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)] at he
  simpa only [inner_self_eq_norm_sq] using he

/-- Multiplication of a frame slot by an unbounded measurable base function
still belongs to the closed span of the bounded frame products whenever
the resulting product is in L². -/
theorem FactorMap.mem_relativeFrameClosure_of_measurable_coefficient
    {π : FactorMap E B} {n : ℕ} (A : RelativeFiniteFrame π n) (i : Fin n)
    (a : Y → ℂ) (ha : Measurable a) (u : Lp ℂ 2 E.measure)
    (hu : u =ᵐ[E.measure] fun x => a (π.toFun x) * A.vector i x) :
    u ∈ (Submodule.span ℂ π.relativeFrameGenerators).topologicalClosure := by
  let b (n : ℕ) : BoundedObservable Y :=
    ⟨fun y => if ‖a y‖ ≤ n then a y else 0,
      ha.ite (measurableSet_le ha.norm measurable_const) measurable_const,
      n, Nat.cast_nonneg _, by intro y; split_ifs with h <;> simp [h]⟩
  let v (n : ℕ) := ((b n).comp π.toFun π.preserves.measurable).mulL2 E.measure (A.vector i)
  have hDiff (n : ℕ) : (v n - u) =ᵐ[E.measure] fun x =>
      if ‖a (π.toFun x)‖ ≤ n then 0 else -u x := by
    filter_upwards [hu, Lp.coeFn_sub (v n) u,
      ((b n).comp π.toFun π.preserves.measurable).ae_mulL2 (A.vector i)] with x hx hSub hV
    change v n x = (b n) (π.toFun x) * A.vector i x at hV
    rw [hSub, Pi.sub_apply, hV]
    by_cases h : ‖a (π.toFun x)‖ ≤ n <;> simp [b, h, hx]
  have hBd (n : ℕ) : ∀ᵐ x ∂E.measure, ‖‖(v n - u) x‖ ^ 2‖ ≤ ‖u x‖ ^ 2 := by
    filter_upwards [hDiff n] with x hx
    rw [hx]
    by_cases h : ‖a (π.toFun x)‖ ≤ n <;> simp [h]
  have hPt : ∀ᵐ x ∂E.measure, Tendsto (fun n => ‖(v n - u) x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr hDiff] with x hx
    obtain ⟨N, hN⟩ := exists_nat_ge ‖a (π.toFun x)‖
    apply tendsto_const_nhds.congr'
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    change (0 : ℝ) = ‖(v n - u) x‖ ^ 2
    rw [hx n, ite_eq_left (hN.trans (Nat.cast_le.mpr hn)), norm_zero, zero_pow (by decide)]
  have hInt : Integrable (fun x => ‖u x‖ ^ 2) E.measure :=
    (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable u).aestronglyMeasurable).mp (Lp.memLp u)
  have hLim := tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ ^ 2)
    (fun n => ((Lp.stronglyMeasurable (v n - u)).measurable.norm.pow_const _).aestronglyMeasurable)
    hInt hBd hPt
  have hSq : Tendsto (fun n => ‖v n - u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [lp_two_norm_sq_eq_integral, integral_zero] using hLim
  have hv : Tendsto v atTop (𝓝 u) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero]
      using (Real.continuous_sqrt.tendsto _).comp hSq
  exact (Submodule.span ℂ π.relativeFrameGenerators).isClosed_topologicalClosure.mem_of_tendsto hv
    (Eventually.of_forall fun k => (Submodule.span ℂ π.relativeFrameGenerators).le_topologicalClosure
      (Submodule.subset_span ⟨n, A, i, b k, rfl⟩))

end Mixing
