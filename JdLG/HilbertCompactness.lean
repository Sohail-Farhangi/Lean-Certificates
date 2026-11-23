/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Compactness.Compact

/-!
# Weak operator compactness for Hilbert-space contractions

Transport Banach–Alaoglu through the Riesz isometry for the vector balls.
The product of the vector balls is compact, and the equations for a
linear operator cut out a closed subset.
-/

@[expose] public section

open Set
open scoped ComplexConjugate Topology

namespace JdLG

section HilbertBalls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isCompact_weakHilbert_ball (r : ℝ) :
    IsCompact {u : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm u‖ ≤ r} := by
  let R := InnerProductSpace.toDual ℂ E
  let inverse (f : WeakDual ℂ E) : WeakSpace ℂ E :=
    toWeakSpace ℂ E (R.symm (WeakDual.toStrongDual f))
  have hcont : Continuous inverse := by
    apply WeakBilin.continuous_of_continuous_eval
    intro y
    let v := R.symm y
    have h (f : WeakDual ℂ E) : y (R.symm (WeakDual.toStrongDual f)) = conj (f v) := by
      calc
        _ = inner ℂ v (R.symm (WeakDual.toStrongDual f)) :=
          InnerProductSpace.toDual_symm_apply.symm
        _ = conj (inner ℂ (R.symm (WeakDual.toStrongDual f)) v) :=
          (inner_conj_symm v _).symm
        _ = conj (f v) := congrArg (starRingEnd ℂ)
          (InnerProductSpace.toDual_symm_apply (x := v) (y := WeakDual.toStrongDual f))
    change Continuous (fun f : WeakDual ℂ E ↦ y (R.symm (WeakDual.toStrongDual f)))
    simp_rw [h]
    exact Complex.continuous_conj.comp (WeakBilin.eval_continuous _ v)
  have hset : inverse '' (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r) =
      {u : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm u‖ ≤ r} := by
    ext u
    constructor
    · rintro ⟨f, hf, rfl⟩
      change dist (WeakDual.toStrongDual f) 0 ≤ r at hf
      change ‖R.symm (WeakDual.toStrongDual f)‖ ≤ r
      rw [R.symm.norm_map]
      rwa [dist_zero_right] at hf
    · intro hu
      let x := (toWeakSpace ℂ E).symm u
      refine ⟨(R x).toWeakDual, ?_, ?_⟩
      · change dist (R x) 0 ≤ r
        rw [dist_zero_right, R.norm_map]
        exact hu
      · change toWeakSpace ℂ E (R.symm (R x)) = u
        rw [R.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rw [← hset]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) r).image hcont

end HilbertBalls

section OperatorBalls

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A weakly compact vector ball at every radius gives weak operator
compactness of each operator ball. -/
theorem isCompact_wot_operatorBall_of_compact_vectorBalls (R : ℝ) (hR : 0 ≤ R)
    (hballs : ∀ r : ℝ, IsCompact {u : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm u‖ ≤ r}) :
    IsCompact {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ R} := by
  let ball (x : E) : Set (WeakSpace ℂ E) := {u | ‖(toWeakSpace ℂ E).symm u‖ ≤ R * ‖x‖}
  let addEq (x y : E) : Set (E → WeakSpace ℂ E) := {u | u (x + y) = u x + u y}
  let smulEq (c : ℂ) (x : E) : Set (E → WeakSpace ℂ E) := {u | u (c • x) = c • u x}
  let equations := (⋂ x, ⋂ y, addEq x y) ∩ (⋂ c, ⋂ x, smulEq c x)
  let good := Set.pi Set.univ ball ∩ equations
  have hEq : IsClosed equations := by
    apply IsClosed.inter
    · exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
    · exact isClosed_iInter fun c ↦ isClosed_iInter fun x ↦
        isClosed_eq (continuous_apply (c • x)) ((continuous_apply x).const_smul c)
  have hcompact : IsCompact good :=
    (isCompact_univ_pi fun x ↦ hballs (R * ‖x‖)).inter_right hEq
  have hbound (u : good) (x : E) : ‖(toWeakSpace ℂ E).symm (u.val x)‖ ≤ R * ‖x‖ :=
    u.property.1 x (mem_univ x)
  let linear (u : good) : E →ₗ[ℂ] E :=
    { toFun := fun x ↦ (toWeakSpace ℂ E).symm (u.val x)
      map_add' := fun x y ↦ by
        have h : u.val (x + y) = u.val x + u.val y :=
          mem_iInter.1 (mem_iInter.1 u.property.2.1 x) y
        rw [h, map_add]
      map_smul' := fun c x ↦ by
        have h : u.val (c • x) = c • u.val x :=
          mem_iInter.1 (mem_iInter.1 u.property.2.2 c) x
        rw [h, map_smul]
        rfl }
  let operator (u : good) : E →WOT[ℂ] E :=
    ContinuousLinearMapWOT.ofCLM ((linear u).mkContinuous R (hbound u))
  have hcont : Continuous operator := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro x f
    change Continuous (fun u : good ↦ f ((toWeakSpace ℂ E).symm (u.val x)))
    exact (WeakBilin.eval_continuous (topDualPairing ℂ E).flip f).comp
      ((continuous_apply x).comp continuous_subtype_val)
  have hsurj : Set.range operator = {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨u, rfl⟩
      exact ContinuousLinearMap.opNorm_le_bound _ hR (hbound u)
    · intro hT
      have hT' : ‖T.toCLM‖ ≤ R := hT
      let u (x : E) := toWeakSpace ℂ E (T x)
      have hu : u ∈ good := by
        refine ⟨fun x _ ↦ ?_, ?_, ?_⟩
        · change ‖(toWeakSpace ℂ E).symm (toWeakSpace ℂ E (T x))‖ ≤ R * ‖x‖
          rw [LinearEquiv.symm_apply_apply]
          exact T.toCLM.le_of_opNorm_le hT' x
        · exact mem_iInter.2 fun x ↦ mem_iInter.2 fun y ↦ by
            change u (x + y) = u x + u y
            simp [u, map_add]
        · exact mem_iInter.2 fun c ↦ mem_iInter.2 fun x ↦ by
            change u (c • x) = c • u x
            simp [u, map_smul]
      refine ⟨⟨u, hu⟩, ?_⟩
      apply ContinuousLinearMapWOT.toCLM_injective
      apply ContinuousLinearMap.ext
      intro x
      exact (toWeakSpace ℂ E).symm_apply_apply (T x)
  let : CompactSpace good := isCompact_iff_compactSpace.mp hcompact
  rw [← hsurj]
  exact isCompact_range hcont

end OperatorBalls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isCompact_wot_contractions :
    IsCompact {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ 1} :=
  isCompact_wot_operatorBall_of_compact_vectorBalls 1 zero_le_one isCompact_weakHilbert_ball

theorem compact_weakOperatorClosure_hilbert_contractions {S : Type*} [Semigroup S]
    (π : S →ₙ* (E →L[ℂ] E)) (hπ : ∀ s, ‖π s‖ ≤ 1) :
    IsCompact (weakOperatorClosure π : Set (E →WOT[ℂ] E)) := by
  have hc : IsCompact {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ 1} := isCompact_wot_contractions
  change IsCompact (closure (range (weakRepresentation π)))
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal
    (by rintro _ ⟨s, rfl⟩; exact hπ s) hc.isClosed)

end JdLG
