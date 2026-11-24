/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrence
public import SixProblems.NiceOperatorial

@[expose] public section

namespace SixProblems

noncomputable section

open MeasureTheory Mixing Set
open scoped InnerProductSpace ComplexOrder

variable {G : Type} [Group G]

/-- Operatorial recurrence stated in terms of the invariant projection of a unitary
    representation, as in the introduction. -/
def IsHilbertOperatoriallyRecurrent (H : Set G) : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : G →* (E ≃ₗᵢ[ℂ] E)) (x : E),
    (∀ h ∈ H, ⟪U h x, x⟫_ℂ = 0) → invariantProjection U x = 0

theorem complexPositiveDefinite_coefficient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* (E ≃ₗᵢ[ℂ] E)) (x : E) :
    ComplexPositiveDefinite (fun g ↦ ⟪x, U g x⟫_ℂ) := by
  intro I
  let v (i : I) := U ((i : G)⁻¹) x
  convert Matrix.posSemidef_gram ℂ v using 1
  ext i j
  change ⟪x, U ((i : G) * (j : G)⁻¹) x⟫_ℂ = ⟪v i, v j⟫_ℂ
  symm
  rw [← (U (i : G)).inner_map_map]
  change ⟪(U (i : G) * U ((i : G)⁻¹)) x, (U (i : G) * U ((j : G)⁻¹)) x⟫_ℂ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem hilbertOperatorial_of_noConstantNegativePD {H : Set G}
    (hH : NoConstantNegativePositiveDefinite H) : IsHilbertOperatoriallyRecurrent H := by
  intro E _ _ _ U x hx
  let P := invariantVectors U
  let u := P.starProjection x
  let v := x - u
  have hu : u ∈ P := P.starProjection_apply_mem x
  have hv : v ∈ Pᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have huv : ⟪v, u⟫_ℂ = 0 := inner_eq_zero_symm.mp (hv _ hu)
  change u = 0
  by_contra hne
  apply hH
  refine ⟨fun g ↦ ⟪v, U g v⟫_ℂ, complexPositiveDefinite_coefficient U v, -(‖u‖ ^ 2),
    neg_lt_zero.mpr (pow_pos (norm_pos_iff.mpr hne) 2), fun g hg ↦ ?_⟩
  have hgu : U g u = u := hu g
  have hOrtho : ⟪u, U g v⟫_ℂ = 0 := by
    rw [← hgu, (U g).inner_map_map]
    exact hv _ hu
  have hSplit : ⟪x, U g x⟫_ℂ = ⟪u, u⟫_ℂ + ⟪v, U g v⟫_ℂ := by
    rw [show x = u + v from (add_sub_cancel u x).symm, map_add, hgu,
      inner_add_left, inner_add_right, inner_add_right, hOrtho, huv, add_zero, zero_add]
  rw [inner_eq_zero_symm.mpr (hx g hg), inner_self_eq_norm_sq_to_K] at hSplit
  change 0 = (‖u‖ : ℂ) ^ 2 + ⟪v, U g v⟫_ℂ at hSplit
  push_cast
  linear_combination -hSplit

theorem operatorial_of_hilbertOperatorial {H : Set G}
    (hH : IsHilbertOperatoriallyRecurrent H) : IsOperatoriallyRecurrent H := by
  intro X _ _ S f hf hcorr
  let U := systemKoopman S
  let v := hf.toLp f
  let one := constantOne S.measure
  have hOne : one ∈ invariantVectors U := systemKoopman_constantOne S
  have hp := hH U v (fun h hh ↦ by
    have he := inner_systemKoopman_of_memLp S hf h⁻¹
    rw [inv_inv, hcorr h hh] at he
    change ⟪v, U h⁻¹ v⟫_ℂ = 0 at he
    rw [← (U h).inner_map_map] at he
    change ⟪U h v, (U h * U h⁻¹) v⟫_ℂ = 0 at he
    rw [← map_mul, mul_inv_cancel, map_one] at he
    exact he)
  have hv := (invariantVectors U).sub_starProjection_mem_orthogonal v
  change v - invariantProjection U v ∈ (invariantVectors U)ᗮ at hv
  rw [hp, sub_zero] at hv
  exact (integral_congr_ae hf.coeFn_toLp).symm.trans
    ((inner_constantOne_left S.measure v).symm.trans (hv _ hOne))

/-- The introductory invariant-projection test and the L² test of Theorem 5.3(b)
    are equivalent. -/
theorem hilbertOperatorial_iff_operatorial [Countable G] {H : Set G} (hne : H.Nonempty) :
    IsHilbertOperatoriallyRecurrent H ↔ IsOperatoriallyRecurrent H :=
  ⟨operatorial_of_hilbertOperatorial, fun h ↦ hilbertOperatorial_of_noConstantNegativePD
    (noConstantNegativePD_of_vdC hne (IsOperatoriallyRecurrent.isVdC h))⟩

end

end SixProblems
