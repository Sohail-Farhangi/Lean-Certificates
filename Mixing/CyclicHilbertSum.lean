/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.MaximalSpectralVector
public import Mixing.SpectralDisjointness
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Orthogonal cyclic decomposition of separable unitary representations -/

@[expose] public section
noncomputable section

namespace Mixing

open Function Set TopologicalSpace
open scoped ENNReal InnerProductSpace lp

variable {G H W : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- Coordinatewise isometric embeddings induce an isometric embedding
of the Hilbert sums. -/
def hilbertSumCoordinateIsometry {I : Type*} {E F : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (A : ∀ i, E i →ₗᵢ[ℂ] F i) : lp E 2 →ₗᵢ[ℂ] lp F 2 where
  toFun x := ⟨fun i ↦ A i (x i), Memℓp.of_norm (by
    simpa only [LinearIsometry.norm_map] using (lp.memℓp x).norm)⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change A i (x i + y i) = A i (x i) + A i (y i)
    exact (A i).map_add _ _
  map_smul' c x := by
    apply lp.ext
    funext i
    change A i (c • x i) = c • A i (x i)
    exact (A i).map_smul _ _
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 2
    funext i
    change ‖A i (x i)‖ ^ (2 : ℝ≥0∞).toReal = ‖x i‖ ^ (2 : ℝ≥0∞).toReal
    rw [(A i).norm_map]

@[simp]
theorem hilbertSumCoordinateIsometry_apply {I : Type*} {E F : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (A : ∀ i, E i →ₗᵢ[ℂ] F i) (x : lp E 2) (i : I) :
    hilbertSumCoordinateIsometry A x i = A i (x i) := rfl

/-- The unitary action on an external Hilbert sum acts on each coordinate. -/
def hilbertSumUnitaryRep {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (U : ∀ i, G →* (E i ≃ₗᵢ[ℂ] E i)) : G →* (lp E 2 ≃ₗᵢ[ℂ] lp E 2) where
  toFun g := {
    __ := hilbertSumCoordinateIsometry (fun i ↦ (U i g).toLinearIsometry)
    invFun := hilbertSumCoordinateIsometry (fun i ↦ (U i g).symm.toLinearIsometry)
    left_inv x := by
      apply lp.ext; funext i
      exact (U i g).symm_apply_apply (x i)
    right_inv x := by
      apply lp.ext; funext i
      exact (U i g).apply_symm_apply (x i) }
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    apply lp.ext; funext i
    change U i 1 (x i) = x i
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    apply lp.ext; funext i
    change U i (g * h) (x i) = U i g (U i h (x i))
    rw [map_mul]
    rfl

@[simp]
theorem hilbertSumUnitaryRep_apply {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (U : ∀ i, G →* (E i ≃ₗᵢ[ℂ] E i)) (g : G) (x : lp E 2) (i : I) :
    hilbertSumUnitaryRep U g x i = U i g (x i) := rfl

theorem hilbertSumUnitaryRep_single {I : Type*} [DecidableEq I] {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (U : ∀ i, G →* (E i ≃ₗᵢ[ℂ] E i)) (g : G) (i : I) (x : E i) :
    hilbertSumUnitaryRep U g (lp.single 2 i x) = lp.single 2 i (U i g x) := by
  apply lp.ext
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp only [hilbertSumUnitaryRep_apply, lp.single_apply, Pi.single_eq_of_ne h, map_zero]

/-- The isometry associated to an orthogonal family of intertwining embeddings
intertwines the coordinate action on the Hilbert sum and the target action. -/
theorem hilbertSumOrthogonalIsometry_intertwines {I : Type*} {E : I → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : ∀ i, G →* (E i ≃ₗᵢ[ℂ] E i))
    (A : ∀ i, E i →ₗᵢ[ℂ] H) (hA : OrthogonalFamily ℂ E A)
    (hInv : ∀ i g x, A i (V i g x) = U g (A i x)) (g : G) (x : lp E 2) :
    hA.linearIsometry (hilbertSumUnitaryRep V g x) = U g (hA.linearIsometry x) := by
  have hmap := (U g).toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (hA.hasSum_linearIsometry x)
  change HasSum (fun i ↦ U g (A i (x i))) (U g (hA.linearIsometry x)) at hmap
  exact (hA.hasSum_linearIsometry _).unique (by simpa only [hilbertSumUnitaryRep_apply, hInv] using hmap)

/-- The product of the coordinate index and a Hilbert-basis index gives a
Hilbert basis of the external sum of copies of that space. -/
def hilbertSumProductBasis {I J : Type*} [DecidableEq I] [CompleteSpace W]
    (b : HilbertBasis J ℂ W) : HilbertBasis (I × J) ℂ (lp (fun _ : I ↦ W) 2) := by
  classical
  let f : I × J → lp (fun _ : I ↦ W) 2 := fun p ↦ lp.single 2 p.1 (b p.2)
  have hF : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, j⟩ ⟨k, l⟩
    change ⟪lp.single (E := fun _ : I ↦ W) 2 i (b j), lp.single 2 k (b l)⟫_ℂ =
      if (i, j) = (k, l) then 1 else 0
    rw [lp.inner_single_left, lp.single_apply]
    by_cases h : i = k
    · subst k
      simp [orthonormal_iff_ite.mp b.orthonormal]
    · simp [h, Pi.single_eq_of_ne]
  refine HilbertBasis.mkOfOrthogonalEqBot hF (le_antisymm ?_ bot_le)
  intro x hx
  rw [Submodule.mem_orthogonal] at hx
  change x = 0
  apply lp.ext
  funext i
  apply b.repr.injective
  apply lp.ext
  funext j
  rw [HilbertBasis.repr_apply_apply]
  have he := hx (f (i, j)) (Submodule.subset_span (Set.mem_range_self (i, j)))
  rw [show f (i, j) = lp.single 2 i (b j) from rfl, lp.inner_single_left] at he
  exact he.trans (by simp)

@[simp]
theorem hilbertSumProductBasis_apply {I J : Type*} [DecidableEq I] [CompleteSpace W]
    (b : HilbertBasis J ℂ W) (i : I) (j : J) :
    hilbertSumProductBasis b (i, j) = lp.single 2 i (b j) := by
  unfold hilbertSumProductBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (v : ℕ → H)

/-- The cyclic subspaces generated by the successive orthogonal residuals
of a dense sequence form an internal Hilbert sum. -/
theorem orthogonalCyclicResidual_isHilbertSum (hv : DenseRange v) :
    let C (n : ℕ) : Submodule ℂ H :=
      (cyclicClosedSubmodule U (orthogonalCyclicResidual U v n)).toSubmodule
    IsHilbertSum ℂ (fun n ↦ C n) (fun n ↦ (C n).subtypeₗᵢ) := by
  let C (n : ℕ) := (cyclicClosedSubmodule U (orthogonalCyclicResidual U v n)).toSubmodule
  let : ∀ n : ℕ, CompleteSpace (C n) := fun n ↦
    (cyclicClosedSubmodule U (orthogonalCyclicResidual U v n)).isClosed.completeSpace_coe
  have hBefore (i j : ℕ) (hij : i < j) : C i ≤ (partialCyclicSubmodule U v j).toSubmodule := by
    have hi : cyclicClosedSubmodule U (orthogonalCyclicResidual U v i) ≤
        partialCyclicSubmodule U v (i + 1) := by
      rw [partialCyclicSubmodule_succ]
      exact le_sup_right
    exact hi.trans (partialCyclicSubmodule_monotone U v (Nat.succ_le_of_lt hij))
  have hOrtho : OrthogonalFamily ℂ (fun n ↦ C n) (fun n ↦ (C n).subtypeₗᵢ) := by
    intro i j hij x y
    change ⟪(x : H), (y : H)⟫_ℂ = 0
    rcases lt_or_gt_of_ne hij with h | h
    · have hy := cyclicClosedSubmodule_residual_le_orthogonal U v j y.property
      rw [Submodule.mem_orthogonal] at hy
      exact hy x (hBefore i j h x.property)
    · have hx := cyclicClosedSubmodule_residual_le_orthogonal U v i x.property
      rw [Submodule.mem_orthogonal] at hx
      rw [← inner_conj_symm, hx y (hBefore j i h y.property), map_zero]
  apply IsHilbertSum.mkInternal C hOrtho
  let D := (⨆ n, C n).topologicalClosure
  let D' : ClosedSubmodule ℂ H := ⟨D, Submodule.isClosed_topologicalClosure _⟩
  have hLe (n : ℕ) : partialCyclicSubmodule U v n ≤ D' := by
    induction n with
    | zero => exact bot_le
    | succ n ih =>
      rw [partialCyclicSubmodule_succ]
      exact sup_le ih ((le_iSup C n).trans (Submodule.le_topologicalClosure _))
  have hRange : Set.range v ⊆ D := by
    rintro _ ⟨n, rfl⟩
    have hp : (partialCyclicSubmodule U v n).toSubmodule.starProjection (v n) ∈ D :=
      hLe n (Submodule.starProjection_apply_mem _ _)
    have hr : orthogonalCyclicResidual U v n ∈ D :=
      Submodule.le_topologicalClosure (⨆ n, C n) (Submodule.mem_iSup_of_mem n
        (mem_cyclicClosedSubmodule U _))
    have he := D.add_mem hp hr
    change (partialCyclicSubmodule U v n).toSubmodule.starProjection (v n) +
      (v n - (partialCyclicSubmodule U v n).toSubmodule.starProjection (v n)) ∈ D at he
    rwa [add_sub_cancel] at he
  intro x _
  exact closure_minimal hRange D'.isClosed (hv x)

/-- If every cyclic subrepresentation embeds into a fixed unitary
representation, the entire separable representation embeds into its
countable Hilbert sum. -/
theorem exists_hilbertSumIntertwiningIsometry [SeparableSpace H]
    (V : G →* (W ≃ₗᵢ[ℂ] W))
    (hCyclic : ∀ x : H, ∃ A : cyclicClosedSubmodule U x →ₗᵢ[ℂ] W,
      ∀ (g : G) (y : cyclicClosedSubmodule U x),
        A ⟨U g y, cyclicClosedSubmodule_invariant U x g y y.property⟩ = V g (A y)) :
    ∃ A : H →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ W) 2, ∀ (g : G) (x : H) (i : ℕ),
      A (U g x) i = V g (A x i) := by
  obtain ⟨v, hv⟩ := exists_dense_seq H
  let C (n : ℕ) := (cyclicClosedSubmodule U (orthogonalCyclicResidual U v n)).toSubmodule
  let a := (orthogonalCyclicResidual_isHilbertSum U v hv)
  let e := a.linearIsometryEquiv
  choose F hF using fun n : ℕ ↦ hCyclic (orthogonalCyclicResidual U v n)
  let hInv (n : ℕ) := cyclicClosedSubmodule_invariant U (orthogonalCyclicResidual U v n)
  let U' (n : ℕ) := unitarySubmoduleAction U (C n) (hInv n)
  let D (g : G) : lp (fun n ↦ C n) 2 →ₗᵢ[ℂ] lp (fun n ↦ C n) 2 :=
    hilbertSumCoordinateIsometry (fun n ↦ (U' n g).toLinearIsometry)
  have he (g : G) (x : H) : e (U g x) = D g (e x) := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    have hx := a.hasSum_linearIsometryEquiv_symm (e x)
    have hy := a.hasSum_linearIsometryEquiv_symm (D g (e x))
    have hmap := (U g).toContinuousLinearEquiv.toContinuousLinearMap.hasSum hx
    rw [e.symm_apply_apply] at hmap
    exact hmap.unique hy
  refine ⟨(hilbertSumCoordinateIsometry F).comp e.toLinearIsometry, fun g x n ↦ ?_⟩
  change hilbertSumCoordinateIsometry F (e (U g x)) n =
    V g (hilbertSumCoordinateIsometry F (e x) n)
  rw [he]
  exact hF n g (e x n)

end Mixing
