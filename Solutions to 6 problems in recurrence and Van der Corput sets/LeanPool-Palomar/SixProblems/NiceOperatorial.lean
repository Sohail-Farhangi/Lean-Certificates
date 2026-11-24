/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Koopman
public import SixProblems.PositiveDefinite

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped InnerProductSpace

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The common fixed subspace of a unitary representation. -/
def invariantVectors (U : G →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H where
  carrier := {x | ∀ g, U g x = x}
  zero_mem' := fun g ↦ map_zero (U g)
  add_mem' := fun hx hy g ↦ by simp [map_add, hx g, hy g]
  smul_mem' := fun c _ hx g ↦ by simp [map_smul, hx g]

theorem isClosed_invariantVectors (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsClosed (invariantVectors U : Set H) := by
  rw [show (invariantVectors U : Set H) = ⋂ g : G, {x | U g x = x} by ext x; simp [invariantVectors]]
  exact isClosed_iInter (fun g ↦ isClosed_eq (U g).continuous continuous_id)

instance [CompleteSpace H] (U : G →* (H ≃ₗᵢ[ℂ] H)) : CompleteSpace (invariantVectors U) :=
  (isClosed_invariantVectors U).completeSpace_coe

/-- The orthogonal projection of Theorem 2.2(c), as an operator on the
ambient Hilbert space. -/
def invariantProjection [CompleteSpace H] (U : G →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  (invariantVectors U).starProjection

/-- The unitary test in Theorem 2.2(c). -/
def NiceOperatorialRecurrence {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (ε : ℝ), 0 < ε → ∃ r ∈ R,
      ‖invariantProjection U x‖ ^ 2 - ε ≤ ‖⟪x, U r x⟫_ℂ‖

theorem niceOperatorialRecurrence_of_nonnegativePD {G : Type} [Group G]
    {R : Set G} (hR : NonnegativeOnPositiveDefinite R) : NiceOperatorialRecurrence R := by
  intro H _ _ _ U x ε hε
  let P := invariantVectors U
  let u := P.starProjection x
  let v := x-u
  have hu : u ∈ P := P.starProjection_apply_mem x
  have hv : v ∈ Pᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hX : x = u+v := (add_sub_cancel u x).symm
  obtain ⟨r,hr,hvR⟩ := hR _ (realPositiveDefinite_re_coefficient U v) ε hε
  have hgu : U r u = u := hu r
  have hOrtho : ⟪u, U r v⟫_ℂ = 0 := by
    rw [← hgu, (U r).inner_map_map]
    exact hv _ hu
  have hOrtho' : ⟪v,u⟫_ℂ = 0 := inner_eq_zero_symm.mp (hv _ hu)
  have hSplit : ⟪x, U r x⟫_ℂ = ⟪u,u⟫_ℂ + ⟪v,U r v⟫_ℂ := by
    rw [hX, map_add, hgu, inner_add_left, inner_add_right, inner_add_right,
      hOrtho, hOrtho', add_zero, zero_add]
  refine ⟨r,hr,le_trans ?_ (Complex.re_le_norm _)⟩
  change ‖u‖ ^ 2 - ε ≤ _
  rw [hSplit, Complex.add_re]
  change ‖u‖ ^ 2 - ε ≤ RCLike.re (⟪u,u⟫_ℂ) + (⟪v,U r v⟫_ℂ).re
  rw [inner_self_eq_norm_sq]
  linarith

theorem niceVdC_of_niceOperatorialRecurrence {G : Type} [Group G]
    {R : Set G} (hR : NiceOperatorialRecurrence R) : NiceVdC R := by
  intro X _ _ S f hf hbound ε hε
  let U := systemKoopman S
  let P := invariantVectors U
  let hL := bounded_measurable_memLp S hf hbound
  let v := hL.toLp f
  let y := P.starProjection v
  let one := constantOne S.measure
  have hOne : one ∈ P := systemKoopman_constantOne S
  have hv : ⟪one,v-y⟫_ℂ = 0 := (Submodule.sub_starProjection_mem_orthogonal v : v-y ∈ Pᗮ) _ hOne
  have hY : ⟪one,y⟫_ℂ = ∫ x, f x ∂S.measure := by
    rw [inner_sub_right, sub_eq_zero] at hv
    rw [← hv, inner_constantOne_left]
    exact integral_congr_ae hL.coeFn_toLp
  have hn : ‖one‖ = 1 := by
    have h := congrArg Complex.re (inner_constantOne_self S.measure)
    change RCLike.re (⟪one,one⟫_ℂ) = 1 at h
    rw [inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp (by simpa only [Complex.one_re, one_pow] using h)
  have hboundY := norm_inner_le_norm (𝕜 := ℂ) one y
  rw [hY, hn, one_mul] at hboundY
  obtain ⟨r, hr, hr'⟩ := hR U v ε hε
  refine ⟨r, hr, ?_⟩
  have hcoef := inner_systemKoopman_of_memLp S hL r
  change ‖y‖ ^ 2 - ε ≤ ‖⟪v,U r v⟫_ℂ‖ at hr'
  change ⟪v,U r v⟫_ℂ = _ at hcoef
  rw [hcoef] at hr'
  exact le_trans (sub_le_sub_right (pow_le_pow_left₀ (norm_nonneg _) hboundY 2) _) hr'

end SixProblems
