/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrenceTruncation
public import SixProblems.Koopman
public import SixProblems.BoundedObservableRepresentative
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

namespace SixProblems

noncomputable section

open MeasureTheory Mixing Set Matrix
open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal

variable {G : Type} [Group G]

/-- The measurable bounded representatives in Definition 4.1 give the same test
    as the essentially bounded functions in the paper. -/
theorem isVdC_iff_memLp_top {H : Set G} : IsVdC H ↔
    ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X] (S : System G X) (f : X → ℂ),
      MemLp f ∞ S.measure → (∀ h ∈ H, correlation S f h = 0) → ∫ x, f x ∂S.measure = 0 := by
  constructor
  · intro h X _ _ S f hf hc
    obtain ⟨b,hb,hEq,hB⟩ := MemLp_exists_measurable_bounded_aeEq hf
    exact (integral_congr_ae hEq).trans
      (h S b hb hB (fun g hg ↦ (correlation_congr_ae S hEq g).symm.trans (hc g hg)))
  · intro h X _ _ S f hf ⟨C, hC⟩ hc
    exact h S f (memLp_top_of_bound hf.aestronglyMeasurable C (.of_forall hC)) hc

/-- Complex positive definiteness is tested on finite group-indexed matrices. -/
def ComplexPositiveDefinite (φ : G → ℂ) : Prop :=
  ∀ I : Finset G, (Matrix.of fun i j : I ↦ φ ((i : G) * (j : G)⁻¹)).PosSemidef

theorem ComplexPositiveDefinite.realPart {φ : G → ℂ} (hφ : ComplexPositiveDefinite φ) :
    RealPositiveDefinite (fun g ↦ (φ g).re) := by
  intro I
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext fun i j ↦ by
      have he := congrArg Complex.re ((hφ I).isHermitian.apply i j)
      simpa only [Matrix.of_apply, Complex.star_def, Complex.conj_re] using he
  intro a
  have h := (hφ I).re_dotProduct_nonneg (fun i ↦ (a i : ℂ))
  change 0 ≤ Complex.re _ at h
  have hSum (f : I → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, hSum, star_trivial,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] using h

/-- The correlation of an L² observable is positive definite, with no commutativity
    assumption on the group. -/
theorem correlation_complexPositiveDefinite {X : Type*} [MeasurableSpace X]
    (S : System G X) {f : X → ℂ} (hf : MemLp f 2 S.measure) :
    ComplexPositiveDefinite (correlation S f) := by
  intro I
  let U := systemKoopman S
  let x := hf.toLp f
  let v (i : I) := U ((i : G)⁻¹) x
  convert (Matrix.posSemidef_gram ℂ v).transpose using 1
  ext i j
  change correlation S f ((i : G) * (j : G)⁻¹) = ⟪v j, v i⟫_ℂ
  symm
  rw [← (U (j : G)).inner_map_map]
  change ⟪(U (j : G) * U ((j : G)⁻¹)) x, (U (j : G) * U ((i : G)⁻¹)) x⟫_ℂ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  change ⟪x, U ((j : G)*(i : G)⁻¹) x⟫_ℂ = _
  rw [inner_systemKoopman_of_memLp, _root_.mul_inv_rev, inv_inv]

/-- The L² correlation test for operatorial recurrence in Theorem 5.3(b). -/
def IsOperatoriallyRecurrent (H : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (f : X → ℂ), MemLp f 2 S.measure →
      (∀ h ∈ H, correlation S f h = 0) → ∫ x, f x ∂S.measure = 0

/-- The positive-definite obstruction in Theorem 5.3(c). -/
def NoConstantNegativePositiveDefinite (H : Set G) : Prop :=
  ¬∃ (φ : G → ℂ), ComplexPositiveDefinite φ ∧
    ∃ r : ℝ, r < 0 ∧ ∀ h ∈ H, φ h = r

theorem IsOperatoriallyRecurrent.isVdC {H : Set G} (hH : IsOperatoriallyRecurrent H) : IsVdC H :=
  fun S f hf hB hC ↦ hH S f (bounded_measurable_memLp S hf hB) hC

private theorem correlation_add_const_of_mean_zero {X : Type*} [MeasurableSpace X]
    (S : System G X) {f : X → ℂ} (hf : MemLp f 2 S.measure)
    (hm : (∫ x, f x ∂S.measure) = 0) (c : ℂ) (g : G) :
    correlation S (fun x ↦ f x + c) g = correlation S f g + (‖c‖ ^ 2 : ℝ) := by
  have hfg := hf.comp_measurePreserving (S.preserves g)
  have hs : MemLp (fun x ↦ conj (f x)) 2 S.measure := hf.star
  have h₁ : Integrable (fun x ↦ f (S.act g x) * conj (f x)) S.measure := hfg.integrable_mul hs
  have h₂ : Integrable (fun x ↦ f (S.act g x) * conj c) S.measure :=
    (hfg.integrable (by norm_num)).mul_const _
  have h₃ : Integrable (fun x ↦ c * conj (f x)) S.measure :=
    (hs.integrable (by norm_num)).const_mul _
  have hj : (∫ x, f (S.act g x) ∂S.measure) = 0 :=
    (integral_comp_preserving (S.preserves g) hf.aestronglyMeasurable).trans hm
  unfold correlation
  have hExp : (fun x ↦ (f (S.act g x) + c) * conj (f x + c)) =
      fun x ↦ (f (S.act g x) * conj (f x) + f (S.act g x) * conj c) +
        (c * conj (f x) + c * conj c) := funext fun _ ↦ by rw [map_add]; ring
  have hk : Integrable (fun _ : X ↦ c * conj c) S.measure := integrable_const _
  rw [hExp, integral_add (h₁.fun_add h₂) (h₃.fun_add hk), integral_add h₁ h₂,
    integral_add h₃ hk, integral_mul_const, integral_const_mul,
    integral_conj, hj, hm, map_zero, zero_mul, mul_zero, add_zero, zero_add, integral_const,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [Measure.real]

theorem operatorial_of_noConstantNegativePD {H : Set G}
    (hh : NoConstantNegativePositiveDefinite H) : IsOperatoriallyRecurrent H := by
  intro X _ _ S f hf hcorr
  set a := ∫ x, f x ∂S.measure with ha
  by_contra hne
  let f₀ : X → ℂ := fun x ↦ f x - a
  have hf₀ : MemLp f₀ 2 S.measure := hf.sub (memLp_const a)
  have hm : (∫ x, f₀ x ∂S.measure) = 0 := by
    unfold f₀
    rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _), integral_const, ← ha]
    simp [Measure.real]
  apply hh
  refine ⟨correlation S f₀, correlation_complexPositiveDefinite S hf₀, -(‖a‖ ^ 2),
    neg_lt_zero.mpr (pow_pos (norm_pos_iff.mpr hne) 2), fun g hg ↦ ?_⟩
  have h := correlation_add_const_of_mean_zero S hf₀ hm a g
  have he : (fun x ↦ f₀ x + a) = f := funext fun x ↦ sub_add_cancel _ _
  rw [he, hcorr g hg] at h
  push_cast
  push_cast at h
  linear_combination -h

theorem noConstantNegativePD_of_vdC [Countable G] {H : Set G} (hne : H.Nonempty)
    (hH : IsVdC H) : NoConstantNegativePositiveDefinite H := by
  rintro ⟨φ, hφ, r, hr, hneg⟩
  exact not_vdC_of_negative_constant_real hne (fun g ↦ (φ g).re) hφ.realPart r hr
    (fun g hg ↦ by rw [hneg g hg, Complex.ofReal_re]) hH

/-- Theorem 5.3. The bounded and square-integrable tests are equivalent, and each
    is equivalent to the absence of a constant negative positive-definite witness. -/
theorem theorem5_3 [Countable G] {H : Set G} (hne : H.Nonempty) :
    (IsVdC H ↔ IsOperatoriallyRecurrent H) ∧
      (IsVdC H ↔ NoConstantNegativePositiveDefinite H) := by
  have hac := noConstantNegativePD_of_vdC hne
  exact ⟨⟨fun h ↦ operatorial_of_noConstantNegativePD (hac h),
    IsOperatoriallyRecurrent.isVdC⟩,
    ⟨hac, fun h ↦ IsOperatoriallyRecurrent.isVdC (operatorial_of_noConstantNegativePD h)⟩⟩

end

end SixProblems
