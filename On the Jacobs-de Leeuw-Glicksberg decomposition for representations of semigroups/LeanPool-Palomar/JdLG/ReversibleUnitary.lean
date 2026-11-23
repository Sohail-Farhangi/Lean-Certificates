/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Stable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.MeasureTheory.Group.Integral

/-! # Finite-dimensional subrepresentations of a compact group -/

@[expose] public section

open Filter InnerProductSpace MeasureTheory Module.End Set
open scoped InnerProductSpace

namespace JdLG

section Unitary

variable {G 𝕜 H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The average of the rank-one operators of a vector over a compact group orbit. -/
noncomputable def averagedRankOne (U : G →* (H ≃ₗᵢ[𝕜] H)) (x : H) : H →L[𝕜] H := by
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  letI : IsScalarTower ℝ 𝕜 H := IsScalarTower.restrictScalars ℝ 𝕜 H
  exact ∫ g, rankOne 𝕜 (U g x) (U g x) ∂normalizedHaar G

omit [CompleteSpace H] in
private theorem continuous_rankOne_self {X : Type*} [TopologicalSpace X] {v : X → H}
    (hv : Continuous v) : Continuous fun a ↦ rankOne 𝕜 (v a) (v a) := by
  simp only [rankOne_def']
  exact ((ContinuousLinearMap.toSpanSingletonLIE 𝕜 H).continuous.comp hv).clm_comp
    ((innerSL 𝕜).continuous.comp hv)

/-- A compact-group unitary action on a nonzero Hilbert space has a nonzero
finite-dimensional invariant subspace. The averaged rank-one operator supplies
a nonzero eigenvalue whose eigenspace is invariant. -/
theorem exists_finiteDimensional_invariant_of_compact_unitary
    (U : G →* (H ≃ₗᵢ[𝕜] H)) (hU : ∀ x, Continuous fun g ↦ U g x)
    {x : H} (hx : x ≠ 0) :
    ∃ V : Submodule 𝕜 H, V ≠ ⊥ ∧ FiniteDimensional 𝕜 V ∧
      ∀ g : G, ∀ y ∈ V, U g y ∈ V := by
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  let : IsScalarTower ℝ 𝕜 H := IsScalarTower.restrictScalars ℝ 𝕜 H
  let μ := normalizedHaar G
  let R : G → H →L[𝕜] H := fun g ↦ rankOne 𝕜 (U g x) (U g x)
  let T := averagedRankOne U x
  have hR : Continuous R := continuous_rankOne_self (hU x)
  have hRi : Integrable R μ :=
    hR.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTintegral : T = ∫ g, R g ∂μ := rfl
  have hTc : IsCompactOperator T := by
    let V := compactOperator (RingHom.id 𝕜) H H
    have hclosed : IsClosed (V : Set (H →L[𝕜] H)) := isClosed_setOfPred_isCompactOperator
    have hmem (g : G) : R g ∈ V := by
      change IsCompactOperator (rankOne 𝕜 (U g x) (U g x))
      change IsCompactOperator ((ContinuousLinearMap.toSpanSingleton 𝕜 (U g x)) ∘
        (innerSL 𝕜 (U g x)))
      exact (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 (U g x))).clm_comp _
    change T ∈ V
    rw [hTintegral]
    exact (V.restrictScalars ℝ).convex.integral_mem hclosed (Eventually.of_forall hmem) hRi
  have hTs : T.IsSymmetric := by
    rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    apply ContinuousLinearMap.isSelfAdjoint_iff'.2
    let e := ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := H) (F := H)
    let adj := e.toContinuousLinearEquiv.toContinuousLinearMap
    rw [hTintegral]
    change adj (∫ g, R g ∂μ) = ∫ g, R g ∂μ
    have h := adj.integral_comp_commSL RCLike.conj_smul hRi
    rw [← h]
    apply integral_congr_ae
    exact Eventually.of_forall fun g ↦ adjoint_rankOne _ _
  have hTnz : T ≠ 0 := by
    intro hTzero
    let f : G → ℝ := fun g ↦ RCLike.re (inner 𝕜 x (R g x))
    have hf : Continuous f :=
      RCLike.continuous_re.comp ((innerSL 𝕜 x).continuous.comp (hR.clm_apply continuous_const))
    have hfn (g : G) : f g = ‖inner 𝕜 x (U g x)‖ ^ 2 := by
      change RCLike.re (inner 𝕜 x (rankOne 𝕜 (U g x) (U g x) x)) = _
      simp only [inner_right_rankOne_apply, ← inner_conj_symm (U g x) x,
        RCLike.mul_conj, RCLike.re_ofReal_pow]
    have hfi : Integrable f μ :=
      hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi : ∫ g, f g ∂μ = 0 := by
      let L : (H →L[𝕜] H) →L[ℝ] ℝ :=
        RCLike.reCLM.comp (ContinuousLinearMap.restrictScalars ℝ
          ((innerSL 𝕜 x).comp (ContinuousLinearMap.apply 𝕜 H x)))
      change (∫ g, L (R g) ∂μ) = 0
      have heq : L (∫ g, R g ∂μ) = 0 := by
        rw [← hTintegral, hTzero, map_zero]
      exact (L.integral_comp_comm hRi).trans heq
    have hae := (integral_eq_zero_iff_of_nonneg (show 0 ≤ f from fun g ↦ hfn g ▸ sq_nonneg _)
      hfi).mp hi
    have hfz := (hf.ae_eq_iff_eq (μ := μ) continuous_const).mp hae
    have hxzero := congrFun hfz 1
    change f 1 = 0 at hxzero
    rw [hfn, map_one] at hxzero
    exact (pow_ne_zero 2 (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hx))) hxzero
  have hcomm (g : G) (y : H) : T (U g y) = U g (T y) := by
    let A := (U g).toContinuousLinearEquiv.toContinuousLinearMap
    change T (A y) = A (T y)
    have hev : Integrable (fun a ↦ R a y) μ :=
      (ContinuousLinearMap.apply 𝕜 H y).integrable_comp hRi
    calc
      T (A y) = ∫ a, R a (A y) ∂μ := hTintegral ▸ ContinuousLinearMap.integral_apply hRi _
      _ = ∫ a, R (g * a) (A y) ∂μ :=
        (integral_mul_left_eq_self (fun a ↦ R a (A y)) g).symm
      _ = ∫ a, A (R a y) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun a ↦ by
          change rankOne 𝕜 (U (g * a) x) (U (g * a) x) (U g y) =
            U g (rankOne 𝕜 (U a x) (U a x) y)
          simp only [map_mul]
          change rankOne 𝕜 (U g (U a x)) (U g (U a x)) (U g y) =
            U g (rankOne 𝕜 (U a x) (U a x) y)
          simp [LinearIsometryEquiv.inner_map_map]
      _ = A (∫ a, R a y ∂μ) := A.integral_comp_comm hev
      _ = A (T y) := by rw [hTintegral, ContinuousLinearMap.integral_apply hRi]
  have hex : ∃ a : 𝕜, HasEigenvalue T.toLinearMap a ∧ a ≠ 0 := by
    by_contra! h
    exact hTnz ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp h)
  obtain ⟨a, ha, ha0⟩ := hex
  refine ⟨eigenspace T.toLinearMap a, hasEigenvalue_iff.mp ha,
    ContinuousLinearMap.finite_dimensional_eigenspace hTc a ha0, ?_⟩
  intro g y hy
  rw [mem_eigenspace_iff] at hy ⊢
  change T y = a • y at hy
  change T (U g y) = a • U g y
  rw [hcomm, hy, map_smul]

end Unitary

end JdLG
