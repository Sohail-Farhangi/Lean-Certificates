/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.MaximalSpectralVector
public import Mixing.SpectralDisjointness
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # A cyclic intertwiner from matching matrix coefficients -/

@[expose] public section

open scoped InnerProductSpace Topology

namespace Mixing

variable {G H K : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
private theorem orbit_inner_eq_diagonal (U : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (i j : G) :
    ⟪U i x, U j x⟫_ℂ = ⟪x, U (i⁻¹ * j) x⟫_ℂ := by
  calc
    _ = ⟪U i⁻¹ (U i x), U i⁻¹ (U j x)⟫_ℂ := ((U i⁻¹).inner_map_map _ _).symm
    _ = _ := by
      change ⟪(U i⁻¹ * U i) x, (U i⁻¹ * U j) x⟫_ℂ = _
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one]
      rfl

omit [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
private theorem orbit_linearCombination_shift (U : G →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (g : G) (a : G →₀ ℂ) :
    Finsupp.linearCombination ℂ (fun j ↦ U j x) (Finsupp.mapDomain (fun j ↦ g * j) a) =
      U g (Finsupp.linearCombination ℂ (fun j ↦ U j x) a) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [Finsupp.mapDomain_add, ha, hb]
  | single j c =>
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, map_smul, map_mul]
    rfl

/-- The cyclic space of `y` embeds isometrically in the other representation
when its generator has the same diagonal matrix coefficients as `x`. -/
theorem exists_cyclicIntertwiningIsometry_of_equal_diagonal_coefficients
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K))
    (x : H) (y : K)
    (h : ∀ g, ⟪x, U g x⟫_ℂ = ⟪y, V g y⟫_ℂ) :
      ∃ J : (cyclicClosedSubmodule V y).toSubmodule →ₗᵢ[ℂ] H,
        Intertwines (unitarySubmoduleAction V _ (cyclicClosedSubmodule_invariant V y))
          U J.toContinuousLinearMap ∧ J ⟨y, mem_cyclicClosedSubmodule V y⟩ = x := by
  let A := Finsupp.linearCombination ℂ (fun g ↦ V g y)
  let B := Finsupp.linearCombination ℂ (fun g ↦ U g x)
  let W := (cyclicClosedSubmodule V y).toSubmodule
  have hWA : W = A.range.topologicalClosure := by
    change (Submodule.span ℂ (Set.range (fun g ↦ V g y))).topologicalClosure = _
    rw [show A.range = _ from Finsupp.range_linearCombination ℂ]
  let e : (G →₀ ℂ) →ₗ[ℂ] W := A.codRestrict W
    (fun a ↦ hWA.symm ▸ A.range.le_topologicalClosure (LinearMap.mem_range_self A a))
  have hWclosed : IsClosed (W : Set K) := (cyclicClosedSubmodule V y).isClosed
  let _ : CompleteSpace W := hWclosed.completeSpace_coe
  have heDense : DenseRange e := by
    intro v
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hv : (v : K) ∈ closure (A.range : Set K) := by
      rw [← Submodule.topologicalClosure_coe, ← hWA]
      exact v.property
    obtain ⟨a, ha, hv⟩ := Metric.mem_closure_iff.mp hv ε hε
    obtain ⟨c, rfl⟩ := ha
    exact ⟨e c, ⟨c, rfl⟩, hv⟩
  have hnorm (a : G →₀ ℂ) : ‖B a‖ = ‖e a‖ := by
    change ‖B a‖ = ‖A a‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    congr 1
    simp only [A, B, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner,
      inner_sum, inner_smul_left, inner_smul_right, orbit_inner_eq_diagonal, h]
  let J := B.extendOfIsometry heDense hnorm
  have hJ (a : G →₀ ℂ) : J (e a) = B a := LinearMap.extendOfIsometry_eq _ _ _ a
  have hW : IsInvariantSubmodule V W := cyclicClosedSubmodule_invariant V y
  let Vw := unitarySubmoduleAction V W hW
  have hJV : Intertwines Vw U J.toContinuousLinearMap := by
    intro g w
    have he (a : G →₀ ℂ) :
        Vw g (e a) = e (Finsupp.mapDomain (fun j ↦ g * j) a) := by
      apply Subtype.ext
      change V g (A a) = A (Finsupp.mapDomain (fun j ↦ g * j) a)
      exact (orbit_linearCombination_shift V y g a).symm
    have hEq : (fun z ↦ J (Vw g z)) ∘ e = (fun z ↦ U g (J z)) ∘ e := by
      funext a
      change J (Vw g (e a)) = U g (J (e a))
      rw [he, hJ, hJ]
      exact orbit_linearCombination_shift U x g a
    exact congrFun (heDense.equalizer (J.continuous.comp (Vw g).continuous)
      ((U g).continuous.comp J.continuous) hEq) w
  refine ⟨J, hJV, ?_⟩
  have heOne : (⟨y, mem_cyclicClosedSubmodule V y⟩ : W) = e (Finsupp.single 1 1) := by
    apply Subtype.ext
    change y = A (Finsupp.single 1 1)
    simp [A, Finsupp.linearCombination_single]
  rw [heOne, hJ]
  simp [B, Finsupp.linearCombination_single]

/-- Matching diagonal coefficients of nonzero generators give a nonzero
bounded intertwiner between the ambient representations. -/
theorem not_spectrallyDisjoint_of_equal_diagonal_coefficients
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K))
    (x : H) (y : K) (hx : x ≠ 0)
    (h : ∀ g, ⟪x, U g x⟫_ℂ = ⟪y, V g y⟫_ℂ) :
      ¬ SpectrallyDisjoint U V := by
  obtain ⟨J, hJV, hJy⟩ := exists_cyclicIntertwiningIsometry_of_equal_diagonal_coefficients U V x y h
  let W := (cyclicClosedSubmodule V y).toSubmodule
  let : CompleteSpace W := (cyclicClosedSubmodule V y).isClosed.completeSpace_coe
  have hW : IsInvariantSubmodule V W := cyclicClosedSubmodule_invariant V y
  let Vw := unitarySubmoduleAction V W hW
  let P := W.subtypeL.adjoint
  have hP : Intertwines V Vw P := (intertwines_unitarySubmoduleAction V W hW).adjoint
  let F := J.toContinuousLinearMap.comp P
  have hF : Intertwines V U F := by
    intro g z
    change J (P (V g z)) = U g (J (P z))
    rw [hP g z]
    exact hJV g (P z)
  let yW : W := ⟨y, mem_cyclicClosedSubmodule V y⟩
  have hPy : P y = yW := by
    apply ext_inner_left ℂ
    intro w
    change ⟪w, W.subtypeL.adjoint y⟫_ℂ = ⟪w, yW⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right]
    rfl
  have hFy : F y = x := by
    change J (P y) = x
    rw [hPy]
    exact hJy
  intro hdisj
  have hf0 := hdisj F hF
  rw [hf0, zero_apply] at hFy
  exact hx hFy.symm

end Mixing
