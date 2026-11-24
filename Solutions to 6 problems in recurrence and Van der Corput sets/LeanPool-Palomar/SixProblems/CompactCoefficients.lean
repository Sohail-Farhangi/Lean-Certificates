/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OrthogonalDecomposition
public import SixProblems.RealCompactDensity
public import Mixing.SupportingJdLG.ReversibleTopology
public import Mixing.SupportingJdLG.Stable

@[expose] public section
noncomputable section

namespace SixProblems

open Filter MeasureTheory Mixing.JdLGBridge Set RealRepresentation
open scoped InnerProductSpace Topology

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section GroupIdeal

variable (U : G →* (E ≃ₗᵢ[ℝ] E))
  (K : GroupIdeal (weakOperatorClosure (orthogonalActionCLM U).toMulHom))

local notation "π" => MonoidHom.toMulHom (orthogonalActionCLM U)
local notation "P" => K.projection (closureAction π)

theorem groupIdealOperator_mem_range (a : K.carrier) (x : E) :
    K.operatorAction a x ∈ (P).range := by
  refine ⟨K.operatorAction a x,?_⟩
  change (closureAction π K.identity * closureAction π a.val) x = closureAction π a.val x
  rw [← map_mul, K.identity_mul a.property]

private theorem groupIdealProjection_eq_self (x : (P).range) : P x = (x : E) := by
  obtain ⟨y,hy⟩ := x.property
  change P y = (x : E) at hy
  rw [← hy, K.projection_apply_apply]

variable [CompleteSpace E]

/-- On the range of the group-ideal identity, the compact group acts by
orthogonal operators. Both an operator and its group inverse are contractions. -/
def groupIdealOrthogonalAction : K.carrier →* ((P).range ≃ₗᵢ[ℝ] (P).range) where
  toFun a :=
    { toLinearEquiv :=
        { (K.operatorAction a).toLinearMap.restrict (fun x _ ↦ groupIdealOperator_mem_range U K a x) with
          invFun := fun x ↦ ⟨K.operatorAction a⁻¹ x, groupIdealOperator_mem_range U K a⁻¹ x⟩
          left_inv := by
            intro x
            apply Subtype.ext
            change (K.operatorAction a⁻¹ * K.operatorAction a) x = (x : E)
            rw [← map_mul, inv_mul_cancel]
            exact groupIdealProjection_eq_self U K x
          right_inv := by
            intro x
            apply Subtype.ext
            change (K.operatorAction a * K.operatorAction a⁻¹) x = (x : E)
            rw [← map_mul, mul_inv_cancel]
            exact groupIdealProjection_eq_self U K x }
      norm_map' := by
        intro x
        change ‖K.operatorAction a x‖ = ‖(x : E)‖
        apply le_antisymm (orthogonalAction_closure_contractive U a.val x)
        calc
          ‖(x : E)‖ = ‖K.operatorAction a⁻¹ (K.operatorAction a x)‖ := by
            congr 1
            change (x : E) = (K.operatorAction a⁻¹ * K.operatorAction a) x
            rw [← map_mul, inv_mul_cancel]
            exact (groupIdealProjection_eq_self U K x).symm
          _ ≤ _ := orthogonalAction_closure_contractive U (a⁻¹).val _ }
  map_one' := by
    ext x
    exact groupIdealProjection_eq_self U K x
  map_mul' a b := by
    ext x
    change K.operatorAction (a*b) x = (K.operatorAction a * K.operatorAction b) x
    rw [map_mul]

/-- The original action on the range agrees with its image in the compact
group ideal. -/
theorem groupIdealOrthogonalAction_retraction (g : G) (x : (P).range) :
    ((groupIdealOrthogonalAction U K (K.groupRetraction (closureInclusion π g))) x : E) = U g x := by
  change closureAction π (K.identity * closureInclusion π g) x = _
  rw [K.identity_mul_eq_mul_identity, map_mul]
  change U g (P x) = _
  rw [groupIdealProjection_eq_self U K x]

/-- Approximation of the projected vector by a vector in a finite-dimensional
invariant real subspace, with a uniform bound on its coefficient error. -/
theorem exists_finite_approximation_of_groupIdeal (hK : IsCompact K.carrier)
    (v : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ (V : Submodule ℝ E), FiniteDimensional ℝ V ∧ IsInvariantSubmodule U V ∧
      ∃ w : V, ∀ g, |⟪P v,U g (P v)⟫_ℝ - ⟪(w : E),U g w⟫_ℝ| < ε := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel _
  let : BorelSpace K.carrier := ⟨rfl⟩
  let ρ := groupIdealOrthogonalAction U K
  have hρ (x : (P).range) : Continuous fun k ↦ ρ k x :=
    (K.continuous_norm_eval hK (x : E)).subtype_mk _
  let u : (P).range := ⟨P v,⟨v,rfl⟩⟩
  let : CompleteSpace (P).range := K.isClosed_range_projection (closureAction π) |>.completeSpace_coe
  let δ := min 1 (ε / (2*‖P v‖+2))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  obtain ⟨W,hW,hWI,w,hw⟩ := exists_finiteInvariant_approximation
    (normalizedHaar K.carrier) ρ hρ u δ hδ
  let V := W.map (P).range.subtype
  have hVI : IsInvariantSubmodule U V := by
    rintro g _ ⟨x,hx,rfl⟩
    refine ⟨ρ (K.groupRetraction (closureInclusion π g)) x,hWI _ _ hx,?_⟩
    exact groupIdealOrthogonalAction_retraction U K g x
  have hV : FiniteDimensional ℝ V := by
    let := hW
    have he : ((P).range.subtype.comp W.subtype).range = V := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    exact he ▸ inferInstanceAs (FiniteDimensional ℝ ((P).range.subtype.comp W.subtype).range)
  let z : V := ⟨(w : E),⟨w,w.property,rfl⟩⟩
  refine ⟨V,hV,hVI,z,fun g ↦ ?_⟩
  let a := P v
  let b := (z : E)
  have hab : ‖a-b‖ < δ := hw
  have hb : ‖b‖ ≤ ‖a‖ + ‖a-b‖ := by
    calc
      _ = ‖a + -(a-b)‖ := congrArg norm (by abel)
      _ ≤ _ := by grw [norm_add_le, norm_neg]
  have hsum : ‖a‖ + ‖b‖ ≤ 2*‖a‖+2 := by
    have h₁ : δ ≤ 1 := min_le_left _ _
    linarith
  have herr : |⟪a,U g a⟫_ℝ - ⟪b,U g b⟫_ℝ| ≤ ‖a-b‖*(‖a‖+‖b‖) := by
    rw [show ⟪a,U g a⟫_ℝ - ⟪b,U g b⟫_ℝ = ⟪a-b,U g a⟫_ℝ + ⟪b,U g (a-b)⟫_ℝ by
      simp only [inner_sub_left, map_sub, inner_sub_right]; ring]
    apply (abs_add_le _ _).trans
    have h₁ := norm_inner_le_norm (𝕜 := ℝ) (a-b) (U g a)
    have h₂ := norm_inner_le_norm (𝕜 := ℝ) b (U g (a-b))
    rw [LinearIsometryEquiv.norm_map] at h₁ h₂
    simpa only [Real.norm_eq_abs, mul_add, mul_comm ‖a-b‖ ‖b‖] using add_le_add h₁ h₂
  calc
    _ ≤ ‖a-b‖*(‖a‖+‖b‖) := herr
    _ ≤ ‖a-b‖*(2*‖a‖+2) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ < δ*(2*‖a‖+2) := mul_lt_mul_of_pos_right hab (by positivity)
    _ ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)

end GroupIdeal

end SixProblems
