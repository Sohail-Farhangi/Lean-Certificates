/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EquivariantHilbertSchroederBernstein
public import Mixing.IntegerRegularShift
public import Mixing.CyclicHilbertSum
public import Mixing.PurePointLebesgue

/-! # A bilateral-shift basis from two isometric embeddings -/

@[expose] public section
noncomputable section

namespace Mixing

variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The regular shift with countable multiplicity, written as an external sum
of countably many copies of the multiplicity-one regular shift. -/
def countableRegularShiftSum (G : Type*) [Group G] :
    G →* (lp (fun _ : ℕ ↦ RegularShiftSpace Unit G) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : ℕ ↦ RegularShiftSpace Unit G) 2) :=
  hilbertSumUnitaryRep (fun _ : ℕ ↦ regularShiftRep Unit G)

/-- The basis of the regular shift of multiplicity one, indexed by the group. -/
def regularShiftUnitBasis (G : Type*) : HilbertBasis G ℂ (RegularShiftSpace Unit G) := by
  let e : G ≃ Unit × G :=
    { toFun := fun g ↦ ((), g)
      invFun := Prod.snd
      left_inv := fun _ ↦ rfl
      right_inv := by rintro ⟨⟨⟩, _⟩; rfl }
  let b := regularShiftBasis Unit G
  refine HilbertBasis.mk (b.orthonormal.comp e e.injective) ?_
  rw [e.surjective.range_comp, b.dense_span]

omit [Group G] in
private theorem regularShiftUnitBasis_apply (g : G) :
    regularShiftUnitBasis G g = regularShiftBasis Unit G ((), g) := by
  rw [regularShiftUnitBasis, HilbertBasis.coe_mk]
  rfl

/-- The product basis of the countable external sum of regular shifts. -/
def countableRegularShiftSumBasis (G : Type*) :
    HilbertBasis (ℕ × G) ℂ (lp (fun _ : ℕ ↦ RegularShiftSpace Unit G) 2) :=
  hilbertSumProductBasis (regularShiftUnitBasis G)

private theorem countableRegularShiftSum_basis (g : G) (j : ℕ) (n : G) :
    countableRegularShiftSum G g (countableRegularShiftSumBasis G (j, n)) =
      countableRegularShiftSumBasis G (j, g * n) := by
  unfold countableRegularShiftSum countableRegularShiftSumBasis
  rw [hilbertSumProductBasis_apply, hilbertSumProductBasis_apply, hilbertSumUnitaryRep_single,
    regularShiftUnitBasis_apply, regularShiftUnitBasis_apply, regularShiftRep_basis]

/-- Identifies the countable sum of regular shifts with a single regular-shift
space whose multiplicity index is `ℕ`. -/
def countableRegularShiftSumEquiv (G : Type*) :
    lp (fun _ : ℕ ↦ RegularShiftSpace Unit G) 2 ≃ₗᵢ[ℂ] RegularShiftSpace ℕ G :=
  (countableRegularShiftSumBasis G).repr

theorem countableRegularShiftSumEquiv_intertwines (G : Type*) [Group G] :
    Intertwines (countableRegularShiftSum G) (regularShiftRep ℕ G)
      (countableRegularShiftSumEquiv G).toLinearIsometry.toContinuousLinearMap := by
  let E := countableRegularShiftSumEquiv G
  let S := countableRegularShiftSum G
  let R := regularShiftRep ℕ G
  have hInv (g : G) (x : RegularShiftSpace ℕ G) : E.symm (R g x) = S g (E.symm x) := by
    let A := E.symm.toLinearIsometry.toContinuousLinearMap.comp
      (R g).toLinearIsometry.toContinuousLinearMap
    let B := (S g).toLinearIsometry.toContinuousLinearMap.comp
      E.symm.toLinearIsometry.toContinuousLinearMap
    have he : A = B := by
      apply regularShift_ext
      rintro ⟨j, n⟩
      change E.symm (R g (regularShiftBasis ℕ G (j, n))) =
        S g (E.symm (regularShiftBasis ℕ G (j, n)))
      rw [show R g (regularShiftBasis ℕ G (j, n)) = regularShiftBasis ℕ G (j, g * n) from
        regularShiftRep_basis g j n]
      exact (countableRegularShiftSum_basis g j n).symm
    exact DFunLike.congr_fun he x
  intro g x
  change E (S g x) = R g (E x)
  apply E.symm.injective
  rw [E.symm_apply_apply, hInv, E.symm_apply_apply]

/-- Equivariant isometric embeddings in both directions supply a bilateral
shift basis on the orthogonal complement of the pure point part. -/
theorem hasLebesgueComplement_of_regularShift_embeddings {I : Type*}
    (U : G →* (H ≃ₗᵢ[ℂ] H))
    (hW : IsInvariantSubmodule U (purePointPart U)ᗮ)
    (J : (purePointPart U)ᗮ →ₗᵢ[ℂ] RegularShiftSpace I G)
    (L : RegularShiftSpace I G →ₗᵢ[ℂ] (purePointPart U)ᗮ)
    (hJ : Intertwines (unitarySubmoduleAction U (purePointPart U)ᗮ hW)
      (regularShiftRep I G) J.toContinuousLinearMap)
    (hL : Intertwines (regularShiftRep I G)
      (unitarySubmoduleAction U (purePointPart U)ᗮ hW) L.toContinuousLinearMap) :
    HasLebesgueComplement U I := by
  let W := (purePointPart U)ᗮ
  let V := unitarySubmoduleAction U W hW
  let R := regularShiftRep I G
  let : CompleteSpace W := (Submodule.isClosed_orthogonal (purePointPart U)).completeSpace_coe
  obtain ⟨F, hF⟩ := equivariant_hilbert_schroeder_bernstein V R J L hJ hL
  let b : HilbertBasis (I × G) ℂ W := HilbertBasis.ofRepr F
  refine ⟨b, fun g j n ↦ ?_⟩
  have he : V g (b (j, n)) = b (j, g * n) := by
    apply F.injective
    change F (V g (F.symm (regularShiftBasis I G (j, n)))) =
      F (F.symm (regularShiftBasis I G (j, g * n)))
    rw [show F (V g (F.symm (regularShiftBasis I G (j, n)))) =
      R g (F (F.symm (regularShiftBasis I G (j, n)))) from hF g _,
      F.apply_symm_apply, F.apply_symm_apply]
    exact regularShiftRep_basis g j n
  exact congrArg Subtype.val he

/-- The same basis criterion with the forward embedding given into an external
sum and the reverse embedding given on the direct regular-shift model. -/
theorem hasLebesgueComplement_of_countable_shift_embeddings
    (U : G →* (H ≃ₗᵢ[ℂ] H))
    (hW : IsInvariantSubmodule U (purePointPart U)ᗮ)
    (J : (purePointPart U)ᗮ →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ RegularShiftSpace Unit G) 2)
    (L : RegularShiftSpace ℕ G →ₗᵢ[ℂ] (purePointPart U)ᗮ)
    (hJ : Intertwines (unitarySubmoduleAction U (purePointPart U)ᗮ hW)
      (countableRegularShiftSum G) J.toContinuousLinearMap)
    (hL : Intertwines (regularShiftRep ℕ G)
      (unitarySubmoduleAction U (purePointPart U)ᗮ hW) L.toContinuousLinearMap) :
    HasLebesgueComplement U ℕ := by
  let E := countableRegularShiftSumEquiv G
  refine hasLebesgueComplement_of_regularShift_embeddings U hW
    (E.toLinearIsometry.comp J) L ?_ hL
  intro g x
  change E (J (unitarySubmoduleAction U (purePointPart U)ᗮ hW g x)) =
    regularShiftRep ℕ G g (E (J x))
  rw [show J (unitarySubmoduleAction U (purePointPart U)ᗮ hW g x) =
    countableRegularShiftSum G g (J x) from hJ g x]
  exact countableRegularShiftSumEquiv_intertwines G g (J x)

end Mixing
