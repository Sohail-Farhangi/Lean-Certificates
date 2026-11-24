/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SixProblems

open scoped InnerProductSpace

variable {G : Type*} [Group G]

/-- A real positive-definite function on a group. Right differences make
each covariance matrix invariant under simultaneous right translation. -/
def RealPositiveDefinite (φ : G → ℝ) : Prop :=
  ∀ I : Finset G, (Matrix.of fun i j : I ↦ φ ((i : G) * (j : G)⁻¹)).PosSemidef

/-- The finite-matrix and finitely supported quadratic-form definitions agree. -/
theorem realPositiveDefinite_iff_posSemidef {φ : G → ℝ} :
    RealPositiveDefinite φ ↔ (Matrix.of fun g h : G ↦ φ (g * h⁻¹)).PosSemidef :=
  (Matrix.posSemidef_iff_submatrix_finset (M := Matrix.of fun g h : G ↦ φ (g * h⁻¹))).symm

namespace RealPositiveDefinite

/-- Reindexing the covariance matrix allows repeated group elements. -/
theorem reindex {φ : G → ℝ} (hφ : RealPositiveDefinite φ) {I : Type*} (g : I → G) :
    (Matrix.of fun i j ↦ φ (g i * (g j)⁻¹)).PosSemidef :=
  (realPositiveDefinite_iff_posSemidef.mp hφ).submatrix g

theorem inv_eq {φ : G → ℝ} (hφ : RealPositiveDefinite φ) (g : G) :
    φ g⁻¹ = φ g := by
  let u : Bool → G := fun b ↦ if b then g else 1
  simpa [u] using (hφ.reindex u).isHermitian.apply true false

theorem one_nonneg {φ : G → ℝ} (hφ : RealPositiveDefinite φ) : 0 ≤ φ 1 := by
  have h := (hφ.reindex (fun _ : Unit ↦ (1 : G))).diag_nonneg (i := ())
  simpa using h

/-- Every value of a real positive-definite function is bounded in absolute
value by the value at the identity. The two-point tests use the vectors
`(1, 1)` and `(1, -1)`. -/
theorem abs_le_one {φ : G → ℝ} (hφ : RealPositiveDefinite φ) (g : G) :
    |φ g| ≤ φ 1 := by
  let u : Bool → G := fun b ↦ if b then g else 1
  let v : Bool → ℝ := fun b ↦ if b then 1 else -1
  have hu := (hφ.reindex u).dotProduct_mulVec_nonneg (fun _ ↦ (1 : ℝ))
  have hv := (hφ.reindex u).dotProduct_mulVec_nonneg v
  simp [u, Matrix.mulVec, dotProduct, hφ.inv_eq g] at hu
  simp [u, v, Matrix.mulVec, dotProduct, hφ.inv_eq g] at hv
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end RealPositiveDefinite

/-- Real coefficients of unitary representations are positive definite.
The Gram vectors here are the inverse translates of `x`. -/
theorem realPositiveDefinite_coefficient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    RealPositiveDefinite (fun g ↦ ⟪x, U g x⟫_ℝ) := by
  intro I
  let v (i : I) := U ((i : G)⁻¹) x
  have hgram := Matrix.posSemidef_gram ℝ v
  convert hgram using 1
  ext i j
  change ⟪x, U ((i : G) * (j : G)⁻¹) x⟫_ℝ = ⟪v i, v j⟫_ℝ
  -- Apply the same unitary to both entries of the Gram coefficient.
  symm
  rw [← (U (i : G)).inner_map_map]
  change ⟪(U (i : G) * U ((i : G)⁻¹)) x, (U (i : G) * U ((j : G)⁻¹)) x⟫_ℝ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- Real parts of complex unitary coefficients are real positive definite.
They are Gram matrices for the realification of the Hilbert space. -/
theorem realPositiveDefinite_re_coefficient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* (E ≃ₗᵢ[ℂ] E)) (x : E) :
    RealPositiveDefinite (fun g ↦ (⟪x, U g x⟫_ℂ).re) := by
  intro I
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let v (i : I) := U ((i : G)⁻¹) x
  convert Matrix.posSemidef_gram ℝ v using 1
  ext i j
  change (⟪x, U ((i : G) * (j : G)⁻¹) x⟫_ℂ).re = (⟪v i, v j⟫_ℂ).re
  congr 1
  symm
  rw [← (U (i : G)).inner_map_map]
  change ⟪(U (i : G) * U ((i : G)⁻¹)) x, (U (i : G) * U ((j : G)⁻¹)) x⟫_ℂ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The epsilon formulation of the nonnegative-supremum criterion, including
the empty set convention. This is Theorem 2.2(d). -/
def NonnegativeOnPositiveDefinite (R : Set G) : Prop :=
  ∀ φ : G → ℝ, RealPositiveDefinite φ →
    ∀ ε > 0, ∃ r ∈ R, -ε ≤ φ r

/-- For a nonempty set, the epsilon formulation is precisely the supremum
formulation of Theorem 2.2(d). -/
theorem nonnegativeOnPositiveDefinite_iff_sSup {R : Set G} (hR : R.Nonempty) :
    NonnegativeOnPositiveDefinite R ↔ ∀ φ : G → ℝ, RealPositiveDefinite φ →
      0 ≤ sSup (φ '' R) := by
  constructor
  · intro h φ hφ
    by_contra! hneg
    have hbdd : BddAbove (φ '' R) :=
      ⟨φ 1, fun _ ⟨g, _, hg⟩ ↦ hg ▸ (abs_le.mp (hφ.abs_le_one g)).2⟩
    obtain ⟨g, hg, hval⟩ := h φ hφ (-(sSup (φ '' R)) / 2) (by linarith)
    have hs := le_csSup hbdd (Set.mem_image_of_mem _ hg)
    linarith
  · intro h φ hφ ε hε
    by_contra! hneg
    have hs : sSup (φ '' R) ≤ -ε := csSup_le (hR.image φ) (by
      rintro _ ⟨g, hg, rfl⟩
      exact (hneg g hg).le)
    linarith [h φ hφ]

end SixProblems
