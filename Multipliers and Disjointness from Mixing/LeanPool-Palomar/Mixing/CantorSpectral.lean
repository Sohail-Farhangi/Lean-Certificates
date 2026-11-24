/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorFourier
public import Mixing.CircleSkew
public import Mixing.UltrafilterLimits

/-! # The Cantor skew-product Fourier computations -/

@[expose] public section

open MeasureTheory

namespace Mixing

/-- The uniform Cantor measure viewed as a measure on the circle. -/
noncomputable def cantorCircleMeasure : Measure UnitAddCircle :=
  cantorMeasure.map fun x : ℝ ↦ (x : UnitAddCircle)

instance : IsProbabilityMeasure cantorCircleMeasure :=
  (Measure.isProbabilityMeasure_map_iff
    (AddCircle.continuous_mk' (1 : ℝ)).measurable.aemeasurable).mpr inferInstance

/-- The relation between Mathlib's positive-sign Fourier characters and the paper's transform. -/
theorem cantorCircleMeasure_integral_fourier (n : ℤ) :
    (∫ x, fourier n x ∂cantorCircleMeasure) = cantorFourier ((-n : ℤ) : ℝ) := by
  have h : Measurable (fun x : ℝ ↦ (x : UnitAddCircle)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).measurable
  rw [cantorCircleMeasure, cantorFourier,
    integral_map h.aemeasurable (fourier (T := 1) n).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  change fourier n (x : UnitAddCircle) = cantorCharacter (((-n : ℤ) : ℝ) * x)
  rw [fourier_coe_apply, cantorCharacter]
  congr 1
  push_cast
  simp only [div_one]
  ring

/-- The two Cantor factors in the correlation in (13) have zero product at a nonzero
integer frequency. -/
theorem example6_cantorFourier_mul_double_zero (n : ℤ) (hn : n ≠ 0) :
    cantorFourier n * cantorFourier ((2 * n : ℤ) : ℝ) = 0 := by
  have hNat (r : ℕ) (hr : r ≠ 0) :
      cantorFourier ((r : ℤ) : ℝ) = 0 ∨ cantorFourier ((2 * (r : ℤ) : ℤ) : ℝ) = 0 := by
    rcases example6_baseFour_digit_two r hr with ⟨k, b, hb⟩ | ⟨k, b, hb⟩
    · exact Or.inl ((cantorFourier_zero_iff _).mpr ⟨k, b, by exact_mod_cast hb⟩)
    · exact Or.inr ((cantorFourier_zero_iff _).mpr ⟨k, b, by exact_mod_cast hb⟩)
  have hnonzero : n.natAbs ≠ 0 := by
    intro h
    exact hn (Int.natAbs_eq_zero.mp h)
  have hsign : n = (n.natAbs : ℤ) ∨ n = -(n.natAbs : ℤ) := by
    cases n with
    | ofNat r => exact Or.inl rfl
    | negSucc r => exact Or.inr rfl
  refine mul_eq_zero.mpr ?_
  rcases hsign with h | h
  · rw [h]
    exact hNat n.natAbs hnonzero
  · rw [h, mul_neg, cantorFourier_neg_eq_zero_iff, cantorFourier_neg_eq_zero_iff]
    exact hNat n.natAbs hnonzero

/-- The product-base integral in the middle of (13), using the circle version of the
uniform Cantor measure. -/
theorem example6_base_fourier_integral_zero (n : ℤ) (hn : n ≠ 0) :
    (∫ x : UnitAddCircle × UnitAddCircle, fourier n x.1 * fourier (2 * n) x.2
      ∂cantorCircleMeasure.prod cantorCircleMeasure) = 0 := by
  rw [integral_prod_mul, cantorCircleMeasure_integral_fourier, cantorCircleMeasure_integral_fourier]
  simpa only [mul_neg] using example6_cantorFourier_mul_double_zero (-n) (neg_ne_zero.mpr hn)


/-- The product of the Cantor skew rotations with speeds one and two in Example 6. -/
noncomputable def example6CantorSystem :
    System (Multiplicative ℤ) ((UnitAddCircle × UnitAddCircle) ×
      (UnitAddCircle × UnitAddCircle)) :=
  (circleSkew cantorCircleMeasure 1).prod (circleSkew cantorCircleMeasure 2)

/-- The character of the sum of the two fibre coordinates in Example 6. -/
noncomputable def example6CantorCharacter (t : ℤ)
    (x : (UnitAddCircle × UnitAddCircle) × (UnitAddCircle × UnitAddCircle)) : ℂ :=
  fourier t (x.1.2 + x.2.2)

theorem fourier_circle_add (t : ℤ) (x y : UnitAddCircle) :
    fourier t (x + y) = fourier t x * fourier t y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_circle_zsmul (t n : ℤ) (x : UnitAddCircle) :
    fourier t (n • x) = fourier (t * n) x := by
  simp only [fourier_apply, smul_smul]

open scoped ComplexConjugate in
/-- Equation (13), with the zero-frequency case included. The autocorrelations of
the nonconstant fibre characters are the Fourier coefficients of normalized Haar measure. -/
theorem example6_cantorCharacter_autocorrelation (t n : ℤ) :
    (∫ x, conj (example6CantorCharacter t x) *
      example6CantorCharacter t (example6CantorSystem.act (Multiplicative.ofAdd n) x)
      ∂example6CantorSystem.measure) = if t * n = 0 then 1 else 0 := by
  have hpoint (x : (UnitAddCircle × UnitAddCircle) × (UnitAddCircle × UnitAddCircle)) :
      conj (example6CantorCharacter t x) *
        example6CantorCharacter t (example6CantorSystem.act (Multiplicative.ofAdd n) x) =
      fourier (t * n) x.1.1 * fourier (2 * (t * n)) x.2.1 := by
    unfold example6CantorCharacter
    have hx : (example6CantorSystem.act (Multiplicative.ofAdd n) x).1.2 +
        (example6CantorSystem.act (Multiplicative.ofAdd n) x).2.2 =
        (x.1.2 + x.2.2) + (n • x.1.1 + (n * 2) • x.2.1) := by
      change (x.1.2 + (n * 1) • x.1.1) + (x.2.2 + (n * 2) • x.2.1) = _
      rw [mul_one]
      abel
    rw [hx, fourier_circle_add t (x.1.2 + x.2.2) (n • x.1.1 + (n * 2) • x.2.1),
      ← mul_assoc, ← fourier_neg, ← fourier_add, neg_add_cancel,
      fourier_zero, one_mul, fourier_circle_add, fourier_circle_zsmul, fourier_circle_zsmul]
    rw [show t * (n * 2) = 2 * (t * n) by ring]
  simp_rw [hpoint]
  let μ := cantorCircleMeasure.prod (AddCircle.haarAddCircle : Measure UnitAddCircle)
  change (∫ x : (UnitAddCircle × UnitAddCircle) × (UnitAddCircle × UnitAddCircle),
    fourier (t * n) x.1.1 * fourier (2 * (t * n)) x.2.1 ∂μ.prod μ) = _
  rw [integral_prod_mul (fun x : UnitAddCircle × UnitAddCircle ↦ fourier (t * n) x.1)
    (fun x : UnitAddCircle × UnitAddCircle ↦ fourier (2 * (t * n)) x.1)]
  unfold μ
  rw [integral_fun_fst (fun x : UnitAddCircle ↦ fourier (t * n) x),
    integral_fun_fst (fun x : UnitAddCircle ↦ fourier (2 * (t * n)) x),
    show (AddCircle.haarAddCircle : Measure UnitAddCircle).real Set.univ = 1 by simp]
  simp only [one_smul, cantorCircleMeasure_integral_fourier]
  split_ifs with h
  · simp [h]
  · simpa only [mul_neg] using
      example6_cantorFourier_mul_double_zero (-(t * n)) (neg_ne_zero.mpr h)


/-- A character of the base and fibre coordinates of the Cantor skew product. -/
noncomputable def example5CantorCharacter (a b : ℤ) (x : UnitAddCircle × UnitAddCircle) : ℂ :=
  fourier a x.1 * fourier b x.2

/-- The finite two-character correlation used in Example 5. -/
theorem example5_cantor_character_correlation (a b c d n : ℤ) :
    (∫ x, example5CantorCharacter a b x *
      example5CantorCharacter d c
        ((circleSkew cantorCircleMeasure 1).act (Multiplicative.ofAdd n) x)
      ∂(circleSkew cantorCircleMeasure 1).measure) =
      cantorFourier (((-c * n - (a + d) : ℤ)) : ℝ) *
        (∫ y : UnitAddCircle, fourier (b + c) y ∂AddCircle.haarAddCircle) := by
  have hpoint (x : UnitAddCircle × UnitAddCircle) :
      example5CantorCharacter a b x *
        example5CantorCharacter d c
          ((circleSkew cantorCircleMeasure 1).act (Multiplicative.ofAdd n) x) =
      fourier (a + d + c * n) x.1 * fourier (b + c) x.2 := by
    change (fourier a x.1 * fourier b x.2) *
      (fourier d x.1 * fourier c (x.2 + (n * 1) • x.1)) = _
    rw [mul_one, fourier_circle_add, fourier_circle_zsmul]
    calc
      _ = (fourier a x.1 * fourier d x.1 * fourier (c * n) x.1) *
          (fourier b x.2 * fourier c x.2) := by ring
      _ = _ := by simp_rw [← fourier_add]
  simp_rw [hpoint]
  change (∫ x : UnitAddCircle × UnitAddCircle, fourier (a + d + c * n) x.1 *
    fourier (b + c) x.2 ∂cantorCircleMeasure.prod AddCircle.haarAddCircle) = _
  rw [integral_prod_mul, cantorCircleMeasure_integral_fourier]
  rw [show -(a + d + c * n) = -c * n - (a + d) by ring]

open Filter in
open scoped Topology in
/-- The scalar correlation limit for the Cantor skew product along the powers of four. -/
theorem example5_cantor_character_correlation_tendsto (a b c d : ℤ) :
    Tendsto (fun j : ℕ ↦
      ∫ x, example5CantorCharacter a b x *
        example5CantorCharacter d c
          ((circleSkew cantorCircleMeasure 1).act (Multiplicative.ofAdd ((4 : ℤ)^j)) x)
        ∂(circleSkew cantorCircleMeasure 1).measure)
      atTop (𝓝 (cantorFourier ((-(a + d) : ℤ) : ℝ) *
        cantorFourier ((-c : ℤ) : ℝ) *
        (∫ y : UnitAddCircle, fourier (b + c) y ∂AddCircle.haarAddCircle))) := by
  simpa only [example5_cantor_character_correlation, sub_eq_add_neg] using
    (cantorFourier_tendsto_four_pow_add (-c) (-(a + d))).mul
      (tendsto_const_nhds
        (x := ∫ y : UnitAddCircle, fourier (b + c) y ∂AddCircle.haarAddCircle))

open Filter in
open scoped Topology in
/-- The Example 5 correlation has the same limit along every free ultrafilter
supported on the powers of four. -/
theorem example5_cantor_character_correlation_tendsto_ultrafilter (a b c d : ℤ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    Tendsto (fun g : Multiplicative ℤ ↦
      ∫ x, example5CantorCharacter a b x *
        example5CantorCharacter d c ((circleSkew cantorCircleMeasure 1).act g x)
        ∂(circleSkew cantorCircleMeasure 1).measure)
      (p : Filter (Multiplicative ℤ)) (𝓝 (cantorFourier ((-(a + d) : ℤ) : ℝ) *
        cantorFourier ((-c : ℤ) : ℝ) *
        (∫ y : UnitAddCircle, fourier (b + c) y ∂AddCircle.haarAddCircle))) := by
  have hi : Function.Injective (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 4)).injective
  refine (tendsto_injective_sequence_iff _ hi (fun g ↦
    ∫ x, example5CantorCharacter a b x *
      example5CantorCharacter d c ((circleSkew cantorCircleMeasure 1).act g x)
      ∂(circleSkew cantorCircleMeasure 1).measure) _).mp ?_ p hp hsupp
  exact example5_cantor_character_correlation_tendsto a b c d

end Mixing
