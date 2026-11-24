/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralDisjointness
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # The regular bilateral shift with an arbitrary space of indices -/

@[expose] public section
noncomputable section

namespace Mixing

open Set
open scoped Classical ENNReal InnerProductSpace

abbrev RegularShiftSpace (I G : Type*) := lp (fun _ : I × G ↦ ℂ) 2

/-- The usual coordinate basis of the Hilbert space of the regular shift. -/
def regularShiftBasis (I G : Type*) : HilbertBasis (I × G) ℂ (RegularShiftSpace I G) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- Translation of the group coordinate, leaving the multiplicity coordinate fixed. -/
def regularShiftPerm {I G : Type*} [Group G] (g : G) : I × G ≃ I × G where
  toFun i := (i.1, g * i.2)
  invFun i := (i.1, g⁻¹ * i.2)
  left_inv i := by simp [← mul_assoc]
  right_inv i := by simp [← mul_assoc]

/-- The coordinate basis in the order determined by a regular translation. -/
def regularShiftPermutedBasis (I : Type*) {G : Type*} [Group G] (g : G) :
    HilbertBasis (I × G) ℂ (RegularShiftSpace I G) :=
  HilbertBasis.mk ((regularShiftBasis I G).orthonormal.comp
    (regularShiftPerm g) (regularShiftPerm g).injective) (by
      have he : range (regularShiftBasis I G ∘ regularShiftPerm g) =
          range (regularShiftBasis I G) := (regularShiftPerm g).surjective.range_comp _
      rw [he, (regularShiftBasis I G).dense_span])

/-- The unitary operator induced by a regular translation of the basis. -/
def regularShiftOperator (I : Type*) {G : Type*} [Group G] (g : G) :
    RegularShiftSpace I G ≃ₗᵢ[ℂ] RegularShiftSpace I G :=
  (regularShiftPermutedBasis I g).repr.symm

theorem regularShiftBasis_apply {I G : Type*} (i : I × G) :
    regularShiftBasis I G i = lp.single 2 i (1 : ℂ) := by
  rw [← (regularShiftBasis I G).repr_symm_single i]
  rfl

private theorem regularShiftOperator_basis {I G : Type*} [Group G] (g : G) (i : I × G) :
    regularShiftOperator I g (regularShiftBasis I G i) =
      regularShiftBasis I G (i.1, g * i.2) := by
  rw [regularShiftBasis_apply i, regularShiftOperator,
    HilbertBasis.repr_symm_single, regularShiftPermutedBasis, HilbertBasis.coe_mk]
  rfl

/-- Two continuous linear maps on the regular shift space agree if they agree
on every coordinate basis vector. -/
theorem regularShift_ext {I G H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {A B : RegularShiftSpace I G →L[ℂ] H}
    (h : ∀ i, A (regularShiftBasis I G i) = B (regularShiftBasis I G i)) : A = B := by
  apply lp.ext_continuousLinearMap (p := 2) ENNReal.ofNat_ne_top
  intro i
  apply ContinuousLinearMap.ext
  intro c
  change A (lp.single 2 i c) = B (lp.single 2 i c)
  have he : lp.single 2 i c = c • regularShiftBasis I G i := by
    rw [regularShiftBasis_apply, ← lp.single_smul, smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul, h i]

/-- The left regular representation with multiplicity indexed by `I`. -/
def regularShiftRep (I G : Type*) [Group G] :
    G →* (RegularShiftSpace I G ≃ₗᵢ[ℂ] RegularShiftSpace I G) where
  toFun := regularShiftOperator I
  map_one' := by
    apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
    apply ContinuousLinearEquiv.coe_injective
    apply regularShift_ext
    intro i
    change regularShiftOperator I (1 : G) (regularShiftBasis I G i) = regularShiftBasis I G i
    rw [regularShiftOperator_basis, one_mul]
  map_mul' g h := by
    apply LinearIsometryEquiv.toContinuousLinearEquiv_injective
    apply ContinuousLinearEquiv.coe_injective
    apply regularShift_ext
    intro i
    change regularShiftOperator I (g * h) (regularShiftBasis I G i) =
      regularShiftOperator I g (regularShiftOperator I h (regularShiftBasis I G i))
    rw [regularShiftOperator_basis, regularShiftOperator_basis, regularShiftOperator_basis, mul_assoc]

theorem regularShiftRep_basis {I G : Type*} [Group G] (g : G) (j : I) (n : G) :
    regularShiftRep I G g (regularShiftBasis I G (j, n)) = regularShiftBasis I G (j, g * n) :=
  regularShiftOperator_basis g (j, n)

end Mixing
