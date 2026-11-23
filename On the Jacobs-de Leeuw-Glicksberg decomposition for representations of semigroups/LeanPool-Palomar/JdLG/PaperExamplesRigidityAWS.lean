/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.HilbertCompactness
public import JdLG.ReversibleUnitarization
public import JdLG.ReversibleUnitary
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Absence of eigenvectors implies almost weak stability

For a unitary integer action, any nonzero reversible subspace would give
a nonzero finite-dimensional invariant component, hence an eigenvector.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A unitary integer action presented as a continuous-linear-operator
representation. -/
def unitaryIntegerAction (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) :
    Multiplicative ℤ →ₙ* (H →L[ℂ] H) where
  toFun n := (U n).toLinearIsometry.toContinuousLinearMap
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    change U (a * b) x = U a (U b x)
    rw [map_mul]
    rfl

theorem unitaryIntegerAction_admissible (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) :
    IsJdLGAdmissible (unitaryIntegerAction U) := by
  apply admissible_of_commutative
  · apply compact_weakOperatorClosure_hilbert_contractions
    intro n
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖U n x‖ ≤ 1 * ‖x‖
    rw [LinearIsometryEquiv.norm_map, one_mul]
  · intro a b
    rw [← map_mul, ← map_mul, mul_comm]

set_option maxHeartbeats 2000000 in
-- The finite-dimensional spectral restriction requires nested subspace instances.
/-- If a unitary generator has no nonzero eigenvectors, every vector belongs
to the almost weakly stable part of the JDlG decomposition. -/
theorem all_aws_of_no_unitary_eigenvectors (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ (c : ℂ) (x : H), U (Multiplicative.ofAdd 1) x = c • x → x = 0) :
    ∀ x : H, IsAlmostWeaklyStable (closureAction (unitaryIntegerAction U)) x := by
  let π := unitaryIntegerAction U
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible (unitaryIntegerAction_admissible U)
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  have hcg := K.continuous_reversibleGroupAction_apply hK
  have hwot : Continuous fun g ↦ ContinuousLinearMapWOT.ofCLM (K.reversibleGroupAction g) :=
    ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x f ↦ f.continuous.comp (hcg x)
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot _ hwot
  obtain ⟨Y, hY, U', J, hJ, hU'⟩ :=
    equivalent_unitary_of_compact_group K.reversibleGroupAction hcg hC hbound
  let : CompleteSpace Y := hY.completeSpace_coe
  have htrivial (x : K.reversibleSubmodule) : x = 0 := by
    by_contra hx
    have hx' : J x ≠ 0 := fun h ↦ hx (J.injective (h.trans (map_zero _).symm))
    obtain ⟨V, hV, hfd, hInv⟩ := exists_finiteDimensional_invariant_of_compact_unitary
      (G := K.carrier) (𝕜 := ℂ) (H := Y) U' hU' hx'
    let : FiniteDimensional ℂ V := hfd
    let : Nontrivial V := Submodule.nontrivial_iff_ne_bot.2 hV
    let s : Multiplicative ℤ := Multiplicative.ofAdd 1
    let a := K.groupRetraction (closureInclusion π s)
    let T : Module.End ℂ V := (U' a).toLinearEquiv.toLinearMap.restrict
      (fun {z} hz ↦ hInv a z hz)
    obtain ⟨c, hc⟩ := T.exists_eigenvalue
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv' : U' a (v : Y) = c • (v : Y) :=
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 hv.1)
    let y := J.symm (v : Y)
    have hy : J y = (v : Y) := J.apply_symm_apply _
    have hi : K.reversibleGroupAction a y = K.reversibleAction s y := by
      rw [K.reversibleAction_eq_comp]
      rfl
    have hEq : K.reversibleAction s y = c • y := by
      apply J.injective
      calc
        J (K.reversibleAction s y) = J (K.reversibleGroupAction a y) := congrArg J hi.symm
        _ = U' a (J y) := (hJ a y).symm
        _ = U' a (v : Y) := congrArg (U' a) hy
        _ = c • (v : Y) := hv'
        _ = c • J y := congrArg (fun z : Y ↦ c • z) hy.symm
        _ = J (c • y) := (map_smul J c y).symm
    have hEq' : U (Multiplicative.ofAdd 1) (y : H) = c • (y : H) :=
      congrArg Subtype.val hEq
    have hy0 : y = 0 := Subtype.ext (hU c y hEq')
    have hzeroJ : J y = (0 : Y) := (congrArg (fun z : K.reversibleSubmodule ↦ J z) hy0).trans
      (map_zero J)
    have hvzero : (v : Y) = (0 : Y) := hy.symm.trans hzeroJ
    exact hv.2 (Subtype.ext hvzero)
  intro x
  apply (K.stable_iff_projection_eq_zero (closureAction π) x).2
  let y : K.reversibleSubmodule := ⟨K.projection (closureAction π) x,
    (K.mem_reversibleSubmodule _).2 (K.projection_apply_apply (closureAction π) x)⟩
  exact congrArg Subtype.val (htrivial y)

end JdLG.PaperExamplesRigid
