/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.HilbertWeakCompactness
public import Mixing.SupportingJdLG.ReversibleAction
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section

namespace SixProblems

open Mixing.JdLGBridge Set
open scoped InnerProductSpace

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Group G]

theorem contractive_projection_orthogonal (P : E →L[ℝ] E) (hC : ∀ x, ‖P x‖ ≤ ‖x‖)
    {u v : E} (hu : P u = u) (hv : P v = 0) : ⟪u,v⟫_ℝ = 0 := by
  have hpoly (t : ℝ) : ‖v‖^2 * (t*t) + (2*⟪u,v⟫_ℝ) * t + 0 ≥ 0 := by
    have h := hC (u+t • v)
    rw [map_add, map_smul, hu, hv, smul_zero, add_zero] at h
    have h' := pow_le_pow_left₀ (norm_nonneg u) h 2
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h'
    linarith only [h', show ‖v‖^2 * (t*t) + (2*⟪u,v⟫_ℝ)*t + 0 =
      2 * (t * ⟪u,v⟫_ℝ) + t ^ 2 * ‖v‖ ^ 2 by ring]
  have hh := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hh
  nlinarith [sq_nonneg (2 * ⟪u,v⟫_ℝ)]

theorem contractive_projection_symmetric (P : E →L[ℝ] E) (hC : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hId : ∀ x, P (P x) = P x) : P.IsSymmetric := by
  intro x y
  have h (u v : E) : ⟪P u,v - P v⟫_ℝ = 0 :=
    contractive_projection_orthogonal P hC (hId u) (by rw [map_sub, hId, sub_self])
  change ⟪P x,y⟫_ℝ = ⟪x,P y⟫_ℝ
  have hx := h x y
  have hy := h y x
  rw [inner_sub_right] at hx hy
  rw [real_inner_comm x (P y), real_inner_comm (P x) (P y)] at hy
  linarith

/-- The norm of an orthogonal projection attains the norm of a vector exactly
when the projection fixes the vector. -/
theorem contractive_projection_fixes_of_norm_eq (P : E →L[ℝ] E)
    (hC : ∀ x, ‖P x‖ ≤ ‖x‖) (hId : ∀ x, P (P x) = P x)
    {x : E} (h : ‖P x‖ = ‖x‖) : P x = x := by
  have ho : ⟪P x,x - P x⟫_ℝ = 0 :=
    contractive_projection_orthogonal P hC (hId x) (by rw [map_sub, hId, sub_self])
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
  rw [show P x + (x - P x) = x by abel, h] at he
  have hn : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

/-- The continuous linear representation underlying an orthogonal action. -/
def orthogonalActionCLM (U : G →* (E ≃ₗᵢ[ℝ] E)) : G →* (E →L[ℝ] E) where
  toFun g := (U g).toLinearIsometry.toContinuousLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul]

variable [CompleteSpace E]

theorem orthogonalAction_isCompact_closure (U : G →* (E ≃ₗᵢ[ℝ] E)) :
    IsCompact (weakOperatorClosure (orthogonalActionCLM U).toMulHom : Set (E →WOT[ℝ] E)) := by
  apply (isCompact_wot_contractions (E := E)).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro _ ⟨g,rfl⟩
    exact (U g).toLinearIsometry.norm_toContinuousLinearMap_le
  · exact (isCompact_wot_contractions (E := E)).isClosed

theorem orthogonalAction_closure_contractive (U : G →* (E ≃ₗᵢ[ℝ] E))
    (a : weakOperatorClosure (orthogonalActionCLM U).toMulHom) (x : E) :
    ‖closureAction (orthogonalActionCLM U).toMulHom a x‖ ≤ ‖x‖ := by
  have hs : (weakOperatorClosure (orthogonalActionCLM U).toMulHom : Set (E →WOT[ℝ] E)) ⊆
      {A | ‖A.toCLM‖ ≤ 1} := closure_minimal (by
    rintro _ ⟨g,rfl⟩
    exact (U g).toLinearIsometry.norm_toContinuousLinearMap_le) isCompact_wot_contractions.isClosed
  change ‖a.val.toCLM x‖ ≤ ‖x‖
  simpa only [one_mul] using a.val.toCLM.le_of_opNorm_le (hs a.property) x

/-- WOT closure of an orthogonal representation has a compact group ideal.
The identity of a minimal left ideal is a contractive projection. Minimality
forces its range to be invariant, so the projection commutes with the closure. -/
theorem orthogonalAction_exists_groupIdeal (U : G →* (E ≃ₗᵢ[ℝ] E)) :
    ∃ K : GroupIdeal (weakOperatorClosure (orthogonalActionCLM U).toMulHom), IsCompact K.carrier := by
  let π := (orthogonalActionCLM U).toMulHom
  let W := weakOperatorClosure π
  let : CompactSpace W := isCompact_iff_compactSpace.mp (orthogonalAction_isCompact_closure U)
  let : Nonempty W := ⟨closureInclusion π (1 : G)⟩
  obtain ⟨L,hLc,hL⟩ := exists_compact_minimalLeftIdeal (S := W) continuous_mul_const
  obtain ⟨e,he,hee⟩ := exists_idempotent_in_compact_subsemigroup continuous_mul_const
    L hL.1 hLc (fun a _ _ hb ↦ hL.2.1 a hb)
  let P := closureAction π e
  have hId (x : E) : P (P x) = P x := by
    change (closureAction π e * closureAction π e) x = _
    rw [← map_mul, hee]
  have hC : ∀ x, ‖P x‖ ≤ ‖x‖ := orthogonalAction_closure_contractive U e
  have hS (x y : E) : ⟪P x,y⟫_ℝ = ⟪x,P y⟫_ℝ :=
    contractive_projection_symmetric P hC hId x y
  have hInvariant (g : G) (x : E) : P (U g (P x)) = U g (P x) := by
    let a := e * closureInclusion π g * e
    have ha : a ∈ L := hL.2.1 _ he
    obtain ⟨b,hb⟩ : e ∈ range (· * a) := (principal_eq_of_minimalLeftIdeal hL ha).symm ▸ he
    change b * (e * closureInclusion π g * e) = e at hb
    have hbe : closureAction π b (P (U g (P x))) = P x := by
      change (closureAction π b * (closureAction π e * closureAction π (closureInclusion π g) *
        closureAction π e)) x = _
      rw [← map_mul, ← map_mul, ← map_mul, hb]
    apply contractive_projection_fixes_of_norm_eq P hC hId
    apply le_antisymm (hC _)
    calc
      ‖U g (P x)‖ = ‖P x‖ := (U g).norm_map _
      _ = ‖closureAction π b (P (U g (P x)))‖ := congrArg norm hbe.symm
      _ ≤ _ := orthogonalAction_closure_contractive U b _
  have hcomm (g : G) (x : E) : P (U g x) = U g (P x) := by
    have hU (u v : E) : ⟪u,U g v⟫_ℝ = ⟪U g⁻¹ u,v⟫_ℝ := by
      rw [← (U g).inner_map_map (U g⁻¹ u) v]
      change _ = ⟪(U g * U g⁻¹) u,U g v⟫_ℝ
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have hz : P (U g (x - P x)) = 0 := by
      apply ext_inner_left ℝ
      intro y
      rw [inner_zero_right, ← hS, hU]
      exact contractive_projection_orthogonal P hC (hInvariant g⁻¹ y)
        (by rw [map_sub, hId, sub_self])
    rwa [map_sub, map_sub, hInvariant, sub_eq_zero] at hz
  have hcentral (a : W) : e * a = a * e := by
    refine (denseRange_closureInclusion π).induction_on a
      (isClosed_eq (continuous_const_mul e) (continuous_mul_const e)) ?_
    intro g
    apply Subtype.ext
    apply ContinuousLinearMapWOT.toCLM_injective
    apply ContinuousLinearMap.ext
    exact hcomm g
  have hLprincipal : range (· * e) = L := principal_eq_of_minimalLeftIdeal hL he
  have hright {a : W} (ha : a ∈ L) (b : W) : a*b ∈ L := by
    obtain ⟨c,rfl⟩ : a ∈ range (· * e) := hLprincipal.symm ▸ ha
    rw [mul_assoc, hcentral b, ← mul_assoc]
    exact hL.2.1 _ he
  have hOneRight {a : W} (ha : a ∈ L) : a*e = a := by
    obtain ⟨b,rfl⟩ : a ∈ range (· * e) := hLprincipal.symm ▸ ha
    rw [mul_assoc, hee]
  refine ⟨⟨L,e,he,hL.2.1,hright,fun {a} ha ↦ (hcentral a).trans (hOneRight ha),
    hOneRight,?_⟩,hLc⟩
  intro a ha
  obtain ⟨b,hb⟩ : e ∈ range (· * a) := (principal_eq_of_minimalLeftIdeal hL ha).symm ▸ he
  change b*a = e at hb
  let c := b*e
  have hc : c ∈ L := hL.2.1 _ he
  have hca : c*a = e := by
    dsimp [c]
    rw [mul_assoc, hcentral a, hOneRight ha, hb]
  obtain ⟨d,hd⟩ : e ∈ range (· * c) := (principal_eq_of_minimalLeftIdeal hL hc).symm ▸ he
  change d*c = e at hd
  have hda : d*e = a := by
    calc
      d*e = d*(c*a) := by rw [hca]
      _ = e*a := by rw [← mul_assoc, hd]
      _ = a := (hcentral a).trans (hOneRight ha)
  refine ⟨c,hc,hca,?_⟩
  rw [← hda, mul_assoc, hcentral c, hOneRight hc, hd]

end SixProblems
