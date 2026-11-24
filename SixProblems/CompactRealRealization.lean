/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CompactOrthogonalGroup
public import SixProblems.RealCompactAverage
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Lagrange

/-! # Bounded Haar realization of finite-dimensional real matrix coefficients -/

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Set Mixing Mixing.JdLGBridge Polynomial InnerProductSpace
open scoped InnerProductSpace

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem polynomial_symmetric {A : Module.End ℝ E} (hA : A.IsSymmetric) (p : ℝ[X]) :
    (aeval A p).IsSymmetric := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (hA.pow n).smul (by simp)

private theorem commute_aeval_of_commute {A B : Module.End ℝ E} (h : Commute A B) (p : ℝ[X]) :
    Commute A (aeval B p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    have hc : Commute A (algebraMap ℝ (Module.End ℝ E) c) := (Algebra.commutes c A).symm
    exact hc.mul_right (h.pow_right n)

variable [FiniteDimensional ℝ E]

/-- If a nonnegative self-adjoint operator has no zero-eigenvalue component on
`v`, a polynomial in the operator acts as its inverse square root on `v`. -/
private theorem exists_normalizing_polynomial (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (hnonneg : ∀ x, 0 ≤ ⟪x,A x⟫_ℝ) (v : E)
    (hzero : ∀ x, A x = 0 → ⟪x,v⟫_ℝ = 0) :
    ∃ q : ℝ[X], aeval A q (A (aeval A q v)) = v := by
  classical
  let d := Module.finrank ℝ E
  let b := hA.eigenvectorBasis (n := d) rfl
  let eigenvalue : Fin d → ℝ := hA.eigenvalues rfl
  let s := Finset.univ.image eigenvalue
  let c (t : ℝ) := (Real.sqrt t)⁻¹
  let q := Lagrange.interpolate s id c
  have heigenvalue (i : Fin d) : 0 ≤ eigenvalue i := by
    apply eigenvalue_nonneg_of_nonneg (hA.hasEigenvalue_eigenvalues rfl i)
    exact hnonneg
  have hq (i : Fin d) : q.eval (eigenvalue i) = c (eigenvalue i) :=
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ he ↦ he) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let B := aeval A q
  have hB := polynomial_symmetric hA q
  have hAb (i : Fin d) : A (b i) = eigenvalue i • b i := hA.apply_eigenvectorBasis rfl i
  have hBb (i : Fin d) : B (b i) = c (eigenvalue i) • b i := by
    rw [show B (b i) = q.eval (eigenvalue i) • b i from Module.End.aeval_apply_of_mem_apply_eq_smul (hAb i), hq]
  have hAinner (i : Fin d) (w : E) : ⟪b i, A w⟫_ℝ = eigenvalue i * ⟪b i,w⟫_ℝ := by
    rw [← hA, hAb, real_inner_smul_left]
  have hBinner (i : Fin d) (w : E) : ⟪b i, B w⟫_ℝ = c (eigenvalue i) * ⟪b i,w⟫_ℝ := by
    rw [← hB, hBb, real_inner_smul_left]
  refine ⟨q, b.repr.injective ?_⟩
  change b.repr (B (A (B v))) = b.repr v
  ext i
  simp only [b.repr_apply_apply]
  rw [hBinner, hAinner, hBinner]
  by_cases h0 : eigenvalue i = 0
  · have hz : A (b i) = 0 := by rw [hAb, h0, zero_smul]
    rw [hzero _ hz, mul_zero, mul_zero, mul_zero]
  · have hpos : 0 < eigenvalue i := lt_of_le_of_ne (heigenvalue i) (fun he ↦ h0 he.symm)
    have hsqrt : Real.sqrt (eigenvalue i) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    have he : c (eigenvalue i) * (eigenvalue i * c (eigenvalue i)) = 1 := by
      dsimp [c]
      calc
        _ = (Real.sqrt (eigenvalue i))⁻¹ * ((Real.sqrt (eigenvalue i)) ^ 2 * (Real.sqrt (eigenvalue i))⁻¹) :=
          congrArg (fun t ↦ (Real.sqrt (eigenvalue i))⁻¹ * (t * (Real.sqrt (eigenvalue i))⁻¹)) (Real.sq_sqrt (heigenvalue i)).symm
        _ = 1 := by field_simp [hsqrt]
    rw [← mul_assoc, ← mul_assoc, mul_assoc (c (eigenvalue i)) (eigenvalue i), he, one_mul]

end Normalization

section Realization

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The coefficient of a vector in a finite-dimensional orthogonal representation
of a compact group is a correlation of a continuous real function on that group. -/
theorem exists_continuous_haar_realization (m : Measure K) [IsProbabilityMeasure m]
    [IsMulLeftInvariant m] [m.IsOpenPosMeasure] (ρ : K →* (E ≃ₗᵢ[ℝ] E))
    (hρ : ∀ x, Continuous fun k ↦ ρ k x) (v : E) :
    ∃ f : C(K, ℝ), (∃ C : ℝ, ∀ k, ‖f k‖ ≤ C) ∧
      ∀ a, (∫ k, f (a * k) * f k ∂m) = ⟪v, ρ a v⟫_ℝ := by
  let A := RealRepresentation.compactRepresentationAverage m ρ v
  have hA (x y : E) : ⟪x,A y⟫_ℝ = ∫ k, ⟪x,ρ k v⟫_ℝ * ⟪y,ρ k v⟫_ℝ ∂m :=
    by
      rw [RealRepresentation.inner_compactRepresentationAverage m ρ v (hρ v)]
      apply integral_congr_ae
      exact ae_of_all _ fun k ↦ by
        change ⟪x,rankOne ℝ (ρ k v) (ρ k v) y⟫_ℝ = ⟪x,ρ k v⟫_ℝ * ⟪y,ρ k v⟫_ℝ
        rw [rankOne_apply, real_inner_smul_right, real_inner_comm (ρ k v) y, mul_comm]
  have hAs : A.toLinearMap.IsSymmetric :=
    RealRepresentation.isSymmetric_compactRepresentationAverage m ρ v (hρ v)
  have hAn (x : E) : 0 ≤ ⟪x,A x⟫_ℝ := by
    rw [hA]
    exact integral_nonneg (fun _ ↦ mul_self_nonneg _)
  have hAz (x : E) (hx : A x = 0) : ⟪x,v⟫_ℝ = 0 := by
    by_contra hne
    let u (k : K) := ⟪x,ρ k v⟫_ℝ ^ 2
    have hc : Continuous u := (continuous_const.inner (hρ v)).pow 2
    have hne' : u 1 ≠ 0 := by
      dsimp [u]
      rw [map_one]
      exact pow_ne_zero _ hne
    have hp := hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := m)
      (HasCompactSupport.of_compactSpace _) (fun k ↦ sq_nonneg ⟪x,ρ k v⟫_ℝ) hne'
    have hz := hA x x
    rw [hx, inner_zero_right] at hz
    exact hp.ne' (by simpa only [u, pow_two] using hz.symm)
  obtain ⟨q,hq⟩ := exists_normalizing_polynomial A.toLinearMap hAs hAn v hAz
  let B := aeval A.toLinearMap q
  have hB := polynomial_symmetric hAs q
  have hAB (a : K) (y : E) : ρ a (B y) = B (ρ a y) := by
    have hcomm : Commute (ρ a).toLinearMap A.toLinearMap := by
      apply LinearMap.ext
      exact RealRepresentation.compactRepresentationAverage_commutes m ρ v (hρ v) a
    exact DFunLike.congr_fun (commute_aeval_of_commute hcomm q).eq y
  let f : C(K, ℝ) := ⟨fun k ↦ ⟪B v,ρ k v⟫_ℝ, continuous_const.inner (hρ v)⟩
  have hmove (a : K) (x y : E) : ⟪ρ a⁻¹ x,y⟫_ℝ = ⟪x,ρ a y⟫_ℝ := by
    rw [← (ρ a).inner_map_map (ρ a⁻¹ x) y]
    change ⟪(ρ a * ρ a⁻¹) x,ρ a y⟫_ℝ = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨f, ⟨‖B v‖ * ‖v‖, fun k ↦ ?_⟩, fun a ↦ ?_⟩
  · change ‖⟪B v,ρ k v⟫_ℝ‖ ≤ _
    simpa only [LinearIsometryEquiv.norm_map] using norm_inner_le_norm (B v) (ρ k v)
  · calc
      _ = ∫ k, ⟪ρ a⁻¹ (B v),ρ k v⟫_ℝ * ⟪B v,ρ k v⟫_ℝ ∂m := by
        apply integral_congr_ae
        exact ae_of_all _ fun k ↦ by
          change ⟪B v,ρ (a * k) v⟫_ℝ * ⟪B v,ρ k v⟫_ℝ =
            ⟪ρ a⁻¹ (B v),ρ k v⟫_ℝ * ⟪B v,ρ k v⟫_ℝ
          rw [hmove, map_mul]
          rfl
      _ = ⟪ρ a⁻¹ (B v),A (B v)⟫_ℝ := (hA _ _).symm
      _ = ⟪ρ a⁻¹ v,v⟫_ℝ := by rw [hAB, hB, show B (A (B v)) = v from hq]
      _ = _ := hmove a v v

end Realization

set_option maxHeartbeats 1200000 in
/-- Every finite-dimensional real orthogonal coefficient has an exact realization
by a bounded measurable real function on a standard Borel ergodic system. -/
theorem exists_ergodic_realization_of_finiteDimensional
    {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (U : G →* (E ≃ₗᵢ[ℝ] E)) (v : E) :
    ∃ (X : Type) (_mX : MeasurableSpace X) (_ : StandardBorelSpace X)
      (S : System G X) (f : X → ℝ),
      S.IsErgodic ∧ Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
      ∀ g, (∫ x, f (S.act g x) * f x ∂S.measure) = ⟪v,U g v⟫_ℝ := by
  let : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let K := orthogonalClosure U
  let : PolishSpace (E →L[ℝ] E) := inferInstance
  let : PolishSpace (unitary (E →L[ℝ] E)) := isClosed_unitary.polishSpace
  let : PolishSpace K := (Subgroup.isClosed_topologicalClosure (orthogonalUnitaryHom U).range).polishSpace
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : StandardBorelSpace K := inferInstance
  let m := normalizedHaar K
  let ρ := orthogonalClosureRep U
  let α := orthogonalClosureHom U
  obtain ⟨f,hBound,hCorr⟩ := exists_continuous_haar_realization m ρ
    (continuous_orthogonalClosureRep_apply U) v
  let S := haarRotation α
  have hS : S.IsErgodic := haarRotation_isErgodic α (denseRange_orthogonalClosureHom U)
  refine ⟨K, ‹MeasurableSpace K›, ‹StandardBorelSpace K›, S, f, hS, f.continuous.measurable, hBound, ?_⟩
  intro g
  change (∫ k, f (α g * k) * f k ∂m) = _
  rw [hCorr, orthogonalClosureRep_apply_hom U g]

end SixProblems
