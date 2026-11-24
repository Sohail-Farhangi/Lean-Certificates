/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.IntegerRegularShift
public import Mixing.PurePointLebesgue
public import Mixing.RotationSpectralDecay

/-! # Embedding regular shifts using mutually orthogonal Haar cyclic orbits -/

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped Classical ENNReal InnerProductSpace

variable {G I H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]

/-- Each coordinate generator of the bilateral shift has exactly Haar spectral measure. -/
theorem dualVectorSpectralMeasure_regularShift (I : Type*) (i : I) :
    dualVectorSpectralMeasure (regularShiftRep I (Multiplicative ℤ))
      (regularShiftBasis I (Multiplicative ℤ) (i, 1)) = integerDualHaar := by
  let : integerDualHaar.Regular := Measure.Regular.map integerDualHomeomorph.symm
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_dualVectorSpectralMeasure, spectralFourier_integerDualHaar,
    regularShiftRep_basis, mul_one]
  simpa only [Prod.mk.injEq, true_and, eq_comm] using
    orthonormal_iff_ite.mp (regularShiftBasis I (Multiplicative ℤ)).orthonormal (i, 1) (i, g)

omit [CompleteSpace H] in
/-- The span of joint eigenvectors is invariant under each group element. -/
theorem regularEmbedding_purePointPart_invariant (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsInvariantSubmodule U (purePointPart U) := by
  intro g
  let P := purePointPart U
  have h : P ≤ P.comap (U g).toLinearMap := by
    apply Submodule.topologicalClosure_minimal _ _ ((isClosed_purePointPart U).preimage (U g).continuous)
    apply Submodule.span_le.mpr
    rintro x ⟨χ, hx⟩
    have hxP : x ∈ P := Submodule.le_topologicalClosure _
      (Submodule.subset_span (show x ∈ unitaryEigenvectors U from ⟨χ, hx⟩))
    change U g x ∈ P
    rw [hx]
    exact P.smul_mem _ hxP
  exact fun _ hx ↦ h hx

/-- The time representation on the orthogonal complement of the pure point part. -/
def purePointOrthogonalRep (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    G →* ((purePointPart U)ᗮ ≃ₗᵢ[ℂ] (purePointPart U)ᗮ) :=
  unitarySubmoduleAction U _ (regularEmbedding_purePointPart_invariant U).orthogonal

omit [CompleteSpace H] in
private theorem orbit_mem_purePoint_orthogonal_of_orthonormal [Infinite G]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hX : Orthonormal ℂ fun g : G ↦ U g x)
    (g : G) : U g x ∈ (purePointPart U)ᗮ := by
  have hEigen : unitaryEigenvectors U ⊆ (innerSL ℂ (U g x)).ker := by
    rintro y ⟨χ, hχ⟩
    have hEq (a : G) : ‖⟪U a x, y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖ := by
      have hInv : U a⁻¹ (U a x) = x := by
        change (U a⁻¹ * U a) x = x
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [← (U a⁻¹).inner_map_map, hInv, hχ, inner_smul_right, norm_mul, Circle.norm_coe, one_mul]
    have hSum := hX.inner_products_summable y
    simp_rw [hEq] at hSum
    have hz : ‖⟪x, y⟫_ℂ‖ ^ 2 = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hSum.tendsto_cofinite_zero
    exact norm_eq_zero.mp ((hEq g).trans (sq_eq_zero_iff.mp hz))
  have hAll : purePointPart U ≤ (innerSL ℂ (U g x)).ker :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hEigen) (innerSL ℂ _).isClosed_ker
  exact fun y hy ↦ inner_eq_zero_symm.mp (hAll hy : ⟪U g x, y⟫_ℂ = 0)

/-- Mutually orthogonal orbits with Haar vector measures embed the regular
shift of their indexed multiplicity into the continuous spectrum. -/
theorem exists_regularShiftEmbedding_of_haarOrbits
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) (x : I → H)
    (hHaar : ∀ i, dualVectorSpectralMeasure U (x i) = integerDualHaar)
    (hCross : ∀ ⦃i j : I⦄, i ≠ j → ∀ g h : Multiplicative ℤ, ⟪U g (x i), U h (x j)⟫_ℂ = 0) :
    ∃ J : RegularShiftSpace I (Multiplicative ℤ) →ₗᵢ[ℂ] (purePointPart U)ᗮ,
      Intertwines (regularShiftRep I (Multiplicative ℤ)) (purePointOrthogonalRep U)
        J.toContinuousLinearMap := by
  let Gₘ := Multiplicative ℤ
  let : Infinite Gₘ := by change Infinite ℤ; infer_instance
  let P := (purePointPart U)ᗮ
  let : CompleteSpace P := (Submodule.isClosed_orthogonal _).completeSpace_coe
  let v (i : I × Gₘ) := U i.2 (x i.1)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, g⟩ ⟨j, h⟩
    by_cases hij : i = j
    · subst j
      change ⟪U g (x i), U h (x i)⟫_ℂ = _
      rw [← (U g⁻¹).inner_map_map]
      change ⟪(U g⁻¹ * U g) (x i), (U g⁻¹ * U h) (x i)⟫_ℂ = _
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one]
      change ⟪x i, U (g⁻¹ * h) (x i)⟫_ℂ = _
      rw [← spectralFourier_dualVectorSpectralMeasure, hHaar, spectralFourier_integerDualHaar]
      simp only [Prod.mk.injEq, true_and, inv_mul_eq_one]
    · have hn : (i, g) ≠ (j, h) := fun he ↦ hij (congrArg Prod.fst he)
      rw [ite_eq_right hn]
      exact hCross hij g h
  have hvP (i : I × Gₘ) : v i ∈ P :=
    orbit_mem_purePoint_orthogonal_of_orthonormal U (x i.1)
      (hv.comp (fun g : Gₘ ↦ (i.1, g)) (fun _ _ he ↦ congrArg Prod.snd he)) i.2
  let w (i : I × Gₘ) : P := ⟨v i, hvP i⟩
  have hw : Orthonormal ℂ w := orthonormal_iff_ite.mpr (orthonormal_iff_ite.mp hv)
  let J := hw.orthogonalFamily.linearIsometry
  have hJ (i : I × Gₘ) : J (regularShiftBasis I Gₘ i) = w i := by
    rw [regularShiftBasis_apply, OrthogonalFamily.linearIsometry_apply_single,
      LinearIsometry.toSpanSingleton_apply, one_smul]
  refine ⟨J, fun g z ↦ ?_⟩
  let A := J.toContinuousLinearMap.comp
    (regularShiftRep I Gₘ g).toContinuousLinearEquiv.toContinuousLinearMap
  let B := (purePointOrthogonalRep U g).toContinuousLinearEquiv.toContinuousLinearMap.comp
    J.toContinuousLinearMap
  have hAB : A = B := regularShift_ext fun i ↦ by
    change J (regularShiftRep I Gₘ g (regularShiftBasis I Gₘ i)) =
      purePointOrthogonalRep U g (J (regularShiftBasis I Gₘ i))
    rw [regularShiftRep_basis, hJ, hJ]
    apply Subtype.ext
    change U (g * i.2) (x i.1) = U g (U i.2 (x i.1))
    rw [map_mul]
    rfl
  exact congrArg (fun F : RegularShiftSpace I Gₘ →L[ℂ] P ↦ F z) hAB

end Mixing
