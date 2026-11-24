/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ConditionalRelativeFrames
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate InnerProductSpace ProbabilityTheory

section HilbertStep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

private def gramResidual (u : Fin n → H) (v : H) : H :=
  v - ∑ j, inner ℂ (u j) v • u j

private def gramNormalized (r : H) : H :=
  ((‖r‖ : ℂ)⁻¹ : ℂ) • r

private theorem gramNormalized_zero_or_unit (r : H) :
    gramNormalized r = 0 ∨ ‖gramNormalized r‖ = 1 := by
  rcases eq_or_ne r 0 with h | h
  · exact Or.inl (by simp [gramNormalized, h])
  right
  rw [gramNormalized, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg r), inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

private theorem smul_gramNormalized (r : H) : (‖r‖ : ℂ) • gramNormalized r = r := by
  rcases eq_or_ne r 0 with h | h
  · simp [gramNormalized, h]
  unfold gramNormalized
  rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)), one_smul]

private theorem inner_gramResidual_eq_zero (u : Fin n → H)
    (hNorm : ∀ i, u i = 0 ∨ ‖u i‖ = 1)
    (hOrth : ∀ i j, i ≠ j → inner ℂ (u i) (u j) = 0) (v : H) (i : Fin n) :
    inner ℂ (u i) (gramResidual u v) = 0 := by
  rcases hNorm i with h | h
  · simp [h]
  rw [gramResidual, inner_sub_right, inner_sum, Finset.sum_eq_single i]
  · simp [inner_smul_right, inner_self_eq_norm_sq_to_K, h]
  · intro j _ hj
    rw [inner_smul_right, hOrth i j hj.symm, mul_zero]
  · simp

private theorem span_gramNormalized_snoc (u : Fin n → H) (v : H) :
    Submodule.span ℂ (range (Fin.snoc u (gramNormalized (gramResidual u v)))) =
      Submodule.span ℂ (range (Fin.snoc u v)) := by
  rw [Fin.range_snoc, Fin.range_snoc]
  let r := gramResidual u v
  let w := gramNormalized r
  have hsum (s : H) : (∑ j, inner ℂ (u j) v • u j) ∈
      Submodule.span ℂ (insert s (range u)) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (mem_insert_of_mem _ (mem_range_self j)))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro a ha
    rcases mem_insert_iff.mp ha with h | he
    · subst a
      change w ∈ _
      apply Submodule.smul_mem
      exact Submodule.sub_mem _ (Submodule.subset_span (mem_insert _ _)) (hsum v)
    · exact Submodule.subset_span (mem_insert_of_mem _ he)
  · apply Submodule.span_le.mpr
    intro a ha
    rcases mem_insert_iff.mp ha with h | he
    · subst a
      have heq : v = (‖r‖ : ℂ) • w + ∑ j, inner ℂ (u j) v • u j := by
        rw [show (‖r‖ : ℂ) • w = r from smul_gramNormalized r]
        exact (sub_add_cancel _ _).symm
      change v ∈ Submodule.span ℂ (insert w (range u))
      rw [heq]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (mem_insert _ _)))
        (hsum w)
    · exact Submodule.subset_span (mem_insert_of_mem _ he)

end HilbertStep

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable {E : System G X} {B : System G Y}

/-- A function in L² of a kernel's barycentre belongs to almost every
conditional L² space. -/
theorem ae_memLp_two_of_kernel_average {κ : Kernel Y X}
    (hκ : κ ∘ₘ B.measure = E.measure) (v : Lp ℂ 2 E.measure) :
    ∀ᵐ y ∂B.measure, MemLp v 2 (κ y) := by
  have hInt := (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable v).aestronglyMeasurable).mp
    (Lp.memLp v)
  have hK : Integrable (fun x : X => ‖v x‖ ^ 2) (κ ∘ₘ B.measure) :=
    (congrArg (fun μ => Integrable (fun x : X => ‖v x‖ ^ 2) μ) hκ).mpr hInt
  filter_upwards [((Measure.integrable_comp_iff hK.1).mp hK).1] with y hy
  exact (memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable v).aestronglyMeasurable).mpr hy

/-- An orthogonal family of unit or zero L² slots on almost every fibre. -/
def FibreOrthonormal (κ : Kernel Y X) (ν : Measure Y) {n : ℕ}
    (u : Fin n → Lp ℂ 2 E.measure) : Prop :=
  ∀ᵐ y ∂ν, ∃ h : ∀ j, MemLp (u j) 2 (κ y),
    (∀ j, (h j).toLp (u j) = 0 ∨ ‖(h j).toLp (u j)‖ = 1) ∧
    ∀ i j, i ≠ j → inner ℂ ((h i).toLp (u i)) ((h j).toLp (u j)) = 0

/-- Equality of the complex linear spans of two finite families restricted
to almost every conditional fibre. -/
def FibreSpanEq (κ : Kernel Y X) (ν : Measure Y) {n m : ℕ}
    (u : Fin n → Lp ℂ 2 E.measure) (v : Fin m → Lp ℂ 2 E.measure) : Prop :=
  ∀ᵐ y ∂ν, ∃ (hu : ∀ j, MemLp (u j) 2 (κ y)) (hv : ∀ j, MemLp (v j) 2 (κ y)),
    Submodule.span ℂ (range fun j => (hu j).toLp (u j)) =
      Submodule.span ℂ (range fun j => (hv j).toLp (v j))

private theorem exists_toLp_family_of_ae_eq {μ : Measure X} {n : ℕ}
    {f : Fin n → X → ℂ} (v : Fin n → Lp ℂ 2 μ) (h : ∀ j, v j =ᵐ[μ] f j) :
    ∃ hf : ∀ j, MemLp (f j) 2 μ, (fun j => (hf j).toLp (f j)) = v := by
  let hf j := MemLp.ae_eq (h j) (Lp.memLp (v j))
  exact ⟨hf, funext fun j => Lp.ext ((hf j).coeFn_toLp.trans (h j).symm)⟩

set_option maxHeartbeats 1200000 in
/-- A measurable conditional Gram–Schmidt step. The added slot is a unit
vector or zero on each fibre, and adding it preserves the span obtained by
adding the original vector. -/
theorem exists_conditionalGramSchmidt_step (π : FactorMap E B) (κ : Kernel Y X)
    (hκ : κ ∘ₘ B.measure = E.measure)
    (hFibre : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    {n : ℕ} (u : Fin n → Lp ℂ 2 E.measure) (hU : FibreOrthonormal κ B.measure u)
    (v : Lp ℂ 2 E.measure) :
    ∃ w : Lp ℂ 2 E.measure, FibreOrthonormal κ B.measure (Fin.snoc u w) ∧
      FibreSpanEq κ B.measure (Fin.snoc u w) (Fin.snoc u v) := by
  let c (j : Fin n) (y : Y) := ∫ x, conj (u j x) * v x ∂κ y
  have hC (j : Fin n) : Measurable (c j) := by
    have hm : Measurable (fun x : X => conj (u j x) * v x) :=
      (Complex.continuous_conj.measurable.comp (Lp.stronglyMeasurable (u j)).measurable).mul
        (Lp.stronglyMeasurable v).measurable
    exact (hm.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  let r (x : X) := v x - ∑ j, c j (π.toFun x) * u j x
  have hR : Measurable r := (Lp.stronglyMeasurable v).measurable.sub
    (Finset.measurable_fun_sum _ fun j _ => ((hC j).comp π.preserves.measurable).mul
      (Lp.stronglyMeasurable (u j)).measurable)
  let d (y : Y) := Real.sqrt (∫ x, ‖r x‖ ^ 2 ∂κ y)
  have hD : Measurable d := Real.continuous_sqrt.measurable.comp
    ((hR.norm.pow_const _).stronglyMeasurable.integral_kernel (κ := κ)).measurable
  let w (x : X) := ((d (π.toFun x) : ℂ)⁻¹ : ℂ) • r x
  have hW : Measurable w :=
    (Complex.continuous_ofReal.measurable.comp (hD.comp π.preserves.measurable)).inv.smul hR
  have hPacket : ∀ᵐ y ∂B.measure,
      ∃ (hu : ∀ j, MemLp (u j) 2 (κ y)) (hv : MemLp v 2 (κ y)),
      (∀ j, (hu j).toLp (u j) = 0 ∨ ‖(hu j).toLp (u j)‖ = 1) ∧
      (∀ i j, i ≠ j → inner ℂ ((hu i).toLp (u i)) ((hu j).toLp (u j)) = 0) ∧
      w =ᵐ[κ y] fun x => gramNormalized (H := Lp ℂ 2 (κ y))
        (gramResidual (fun j => (hu j).toLp (u j)) (hv.toLp v)) x := by
    filter_upwards [hU, hFibre, ae_memLp_two_of_kernel_average hκ v] with y hy hF hyV
    obtain ⟨hu, hNorm, hOrth⟩ := hy
    let u' j := (hu j).toLp (u j)
    let v' := hyV.toLp v
    let r' := gramResidual u' v'
    have hInner (j : Fin n) : inner ℂ (u' j) v' = c j y := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hu j).coeFn_toLp, hyV.coeFn_toLp] with x hx hvx
      change u' j x = u j x at hx
      change v' x = v x at hvx
      rw [hx, hvx, RCLike.inner_apply']
    have hRLp : r =ᵐ[κ y] r' := by
      have hSum := ae_coe_toLp_sum_smul hu (fun j => inner ℂ (u' j) v')
      have hDiff := Lp.coeFn_sub v' (∑ j, inner ℂ (u' j) v' • u' j)
      filter_upwards [hF, hSum, hDiff, hyV.coeFn_toLp] with x hx hS hSub hV
      change r' x = _ at hSub
      change v' x = v x at hV
      rw [hSub, Pi.sub_apply, hS, hV]
      simp only [r, hx, hInner]
    have hDy : d y = ‖r'‖ := by
      have heInt : (∫ x, ‖r x‖ ^ 2 ∂κ y) = ‖r'‖ ^ 2 :=
        (integral_congr_ae (hRLp.mono fun x hx => by rw [hx])).trans
          (lp_two_norm_sq_eq_integral r').symm
      change Real.sqrt (∫ x, ‖r x‖ ^ 2 ∂κ y) = ‖r'‖
      rw [heInt, Real.sqrt_sq (norm_nonneg _)]
    refine ⟨hu, hyV, hNorm, hOrth, ?_⟩
    have hSmul := Lp.coeFn_smul ((‖r'‖ : ℂ)⁻¹) r'
    filter_upwards [hF, hRLp, hSmul] with x hx hRx hS
    change w x = gramNormalized r' x
    change gramNormalized r' x = _ at hS
    rw [hS, Pi.smul_apply]
    change ((d (π.toFun x) : ℂ)⁻¹ : ℂ) • r x = _
    rw [hx, hDy, hRx]
  have hInt :
      Integrable (fun x => ‖w x‖ ^ 2) (κ ∘ₘ B.measure) := by
    apply (Measure.integrable_comp_iff (hW.norm.pow_const _).aestronglyMeasurable).mpr
    refine ⟨?_, ?_⟩
    · filter_upwards [hPacket] with y hy
      obtain ⟨hu, hv, _, _, hw⟩ := hy
      let q := gramNormalized (gramResidual (fun j => (hu j).toLp (u j)) (hv.toLp v))
      have hm := MemLp.ae_eq hw.symm (Lp.memLp q)
      exact (memLp_two_iff_integrable_sq_norm (hW.aestronglyMeasurable)).mp hm
    · apply (integrable_const (1 : ℝ)).mono
        (((hW.norm.pow_const _).norm.stronglyMeasurable.integral_kernel (κ := κ)).aestronglyMeasurable)
      filter_upwards [hPacket] with y hy
      obtain ⟨hu, hv, _, _, hw⟩ := hy
      let q := gramNormalized (gramResidual (fun j => (hu j).toLp (u j)) (hv.toLp v))
      have he : (∫ x, ‖‖w x‖ ^ 2‖ ∂κ y) = ‖q‖ ^ 2 := by
        calc
          _ = ∫ x, ‖q x‖ ^ 2 ∂κ y := by
            apply integral_congr_ae
            filter_upwards [hw] with x hx
            change w x = q x at hx
            rw [hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          _ = _ := (lp_two_norm_sq_eq_integral q).symm
      change ‖∫ x, ‖‖w x‖ ^ 2‖ ∂κ y‖ ≤ ‖(1 : ℝ)‖
      rw [he, norm_one]
      rcases gramNormalized_zero_or_unit
        (gramResidual (fun j => (hu j).toLp (u j)) (hv.toLp v)) with h | h
      · rw [show q = 0 from h]
        simp
      · rw [show ‖q‖ = 1 from h]
        norm_num
  have hMem : MemLp w 2 E.measure :=
    (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mpr
      ((congrArg (fun μ => Integrable (fun x => ‖w x‖ ^ 2) μ) hκ).mp hInt)
  let wG := hMem.toLp w
  have hG : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, wG x = w x := by
    have he : wG =ᵐ[E.measure] w := hMem.coeFn_toLp
    rw [← congrArg ae hκ] at he
    exact Measure.ae_ae_of_ae_comp he
  let uG : Fin (n + 1) → Lp ℂ 2 E.measure := Fin.snoc u wG
  let vG : Fin (n + 1) → Lp ℂ 2 E.measure := Fin.snoc u v
  have hBoth : ∀ᵐ y ∂B.measure,
      (∃ h : ∀ j, MemLp (uG j) 2 (κ y),
        (∀ j, (h j).toLp (uG j) = 0 ∨ ‖(h j).toLp (uG j)‖ = 1) ∧
        ∀ i j, i ≠ j → inner ℂ ((h i).toLp (uG i)) ((h j).toLp (uG j)) = 0) ∧
      ∃ (hu : ∀ j, MemLp (uG j) 2 (κ y)) (hv : ∀ j, MemLp (vG j) 2 (κ y)),
        Submodule.span ℂ (range fun j => (hu j).toLp (uG j)) =
          Submodule.span ℂ (range fun j => (hv j).toLp (vG j)) := by
    filter_upwards [hPacket, hG] with y hy hwG
    obtain ⟨hu, hv, hNorm, hOrth, hw⟩ := hy
    let a (j : Fin n) := (hu j).toLp (u j)
    let z := hv.toLp v
    let q := gramNormalized (gramResidual a z)
    have hQ : q =ᵐ[κ y] wG :=
      (Filter.EventuallyEq.trans (show wG =ᵐ[κ y] w from hwG) (show w =ᵐ[κ y] q from hw)).symm
    have hNew (j : Fin (n + 1)) :
        Fin.snoc (α := fun _ => Lp ℂ 2 (κ y)) a q j =ᵐ[κ y] uG j := by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [uG, Fin.snoc_last] using hQ
      · simpa only [uG, Fin.snoc_castSucc] using (hu j).coeFn_toLp
    have hOld (j : Fin (n + 1)) :
        Fin.snoc (α := fun _ => Lp ℂ 2 (κ y)) a z j =ᵐ[κ y] vG j := by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [vG, Fin.snoc_last] using hv.coeFn_toLp
      · simpa only [vG, Fin.snoc_castSucc] using (hu j).coeFn_toLp
    obtain ⟨hN, hNE⟩ := exists_toLp_family_of_ae_eq _ hNew
    obtain ⟨hV, hVE⟩ := exists_toLp_family_of_ae_eq _ hOld
    have hLast (i : Fin n) : inner ℂ (a i) q = 0 := by
      simp only [q, gramNormalized, inner_smul_right, inner_gramResidual_eq_zero a hNorm hOrth, mul_zero]
    refine ⟨⟨hN, ?_, ?_⟩, ⟨hN, hV, ?_⟩⟩
    · intro j
      have hj := congrFun hNE j
      rw [hj]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.snoc_last] using gramNormalized_zero_or_unit (gramResidual a z)
      · simpa only [Fin.snoc_castSucc] using hNorm j
    · intro i j
      rw [congrFun hNE i, congrFun hNE j]
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases (fun h => (h rfl).elim) (fun j _ => ?_) j
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact (inner_eq_zero_symm (𝕜 := ℂ)).mp (hLast j)
      · refine Fin.lastCases (fun _ => ?_) (fun j h => ?_) j
        · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hLast i
        · simpa only [Fin.snoc_castSucc] using hOrth i j (fun he => h (congrArg Fin.castSucc he))
    · rw [hNE, hVE]
      exact span_gramNormalized_snoc a z
  exact ⟨wG, hBoth.mono fun _ h => h.1, hBoth.mono fun _ h => h.2⟩

theorem FibreSpanEq.trans {κ : Kernel Y X} {ν : Measure Y} {n m k : ℕ}
    {u : Fin n → Lp ℂ 2 E.measure} {v : Fin m → Lp ℂ 2 E.measure}
    {w : Fin k → Lp ℂ 2 E.measure} (h₁ : FibreSpanEq κ ν u v) (h₂ : FibreSpanEq κ ν v w) :
    FibreSpanEq κ ν u w := by
  filter_upwards [h₁, h₂] with y hhy₁ hhy₂
  obtain ⟨hu, hv, he₁⟩ := hhy₁
  obtain ⟨hv', hw, he₂⟩ := hhy₂
  exact ⟨hu, hw, he₁.trans he₂⟩

theorem FibreSpanEq.snoc {κ : Kernel Y X} {n m : ℕ}
    {u : Fin n → Lp ℂ 2 E.measure} {v : Fin m → Lp ℂ 2 E.measure}
    (h : FibreSpanEq κ B.measure u v) (hκ : κ ∘ₘ B.measure = E.measure)
    (w : Lp ℂ 2 E.measure) :
    FibreSpanEq κ B.measure (Fin.snoc u w) (Fin.snoc v w) := by
  filter_upwards [h, ae_memLp_two_of_kernel_average hκ w] with y hyy hyw
  obtain ⟨hu, hv, he⟩ := hyy
  let u' (j : Fin n) := (hu j).toLp (u j)
  let v' (j : Fin m) := (hv j).toLp (v j)
  let w' := hyw.toLp w
  let uG : Fin (n + 1) → Lp ℂ 2 E.measure := Fin.snoc u w
  let vG : Fin (m + 1) → Lp ℂ 2 E.measure := Fin.snoc v w
  have hU (j : Fin (n + 1)) :
      Fin.snoc (α := fun _ => Lp ℂ 2 (κ y)) u' w' j =ᵐ[κ y] uG j := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [uG, Fin.snoc_last] using hyw.coeFn_toLp
    · simpa only [uG, Fin.snoc_castSucc] using (hu j).coeFn_toLp
  have hV (j : Fin (m + 1)) :
      Fin.snoc (α := fun _ => Lp ℂ 2 (κ y)) v' w' j =ᵐ[κ y] vG j := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [vG, Fin.snoc_last] using hyw.coeFn_toLp
    · simpa only [vG, Fin.snoc_castSucc] using (hv j).coeFn_toLp
  obtain ⟨hU', hUE⟩ := exists_toLp_family_of_ae_eq _ hU
  obtain ⟨hV', hVE⟩ := exists_toLp_family_of_ae_eq _ hV
  refine ⟨hU', hV', ?_⟩
  rw [hUE, hVE, Fin.range_snoc, Fin.range_snoc, Set.insert_eq, Set.insert_eq,
    Submodule.span_union, Submodule.span_union]
  exact congrArg ((Submodule.span ℂ {w'}) ⊔ ·) he

/-- Conditional Gram–Schmidt produces measurable global L² slots with the
same conditional span as the given finite family. Rank changes across fibres
are handled by allowing zero slots. -/
theorem exists_conditionalGramSchmidt (π : FactorMap E B) (κ : Kernel Y X)
    (hκ : κ ∘ₘ B.measure = E.measure)
    (hFibre : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    {n : ℕ} (v : Fin n → Lp ℂ 2 E.measure) :
    ∃ u : Fin n → Lp ℂ 2 E.measure,
      FibreOrthonormal κ B.measure u ∧ FibreSpanEq κ B.measure u v := by
  induction n with
  | zero =>
    exact ⟨v, Eventually.of_forall fun _ =>
      ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      Eventually.of_forall fun _ => ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, rfl⟩⟩
  | succ n ih =>
    obtain ⟨u, hu, he⟩ := ih (Fin.init v)
    obtain ⟨w, hOrtho, hStep⟩ := exists_conditionalGramSchmidt_step π κ hκ hFibre u hu
      (v (Fin.last n))
    refine ⟨Fin.snoc u w, hOrtho, ?_⟩
    have h := hStep.trans (he.snoc hκ (v (Fin.last n)))
    rwa [Fin.snoc_init_self] at h

end Mixing
