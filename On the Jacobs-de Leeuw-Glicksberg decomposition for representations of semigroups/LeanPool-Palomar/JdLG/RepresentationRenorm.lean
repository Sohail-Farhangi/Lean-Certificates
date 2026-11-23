/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.UniformSpace.Equiv

/-! # The equivalent orbit norm of a uniformly bounded monoid representation -/

@[expose] public section

open Set

namespace JdLG

variable {S E : Type*} [Monoid S] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The supremum of the original norms along an operator orbit. -/
noncomputable def orbitNormFun (π : S →* (E →L[ℂ] E)) (x : E) : ℝ :=
  ⨆ s, ‖π s x‖

private theorem orbitNormFun_bddAbove (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) (x : E) :
    BddAbove (range fun s ↦ ‖π s x‖) :=
  ⟨C * ‖x‖, fun _ ⟨s, he⟩ ↦ he ▸ (π s).le_of_opNorm_le (hC s) x⟩

/-- The original norm is a lower bound for the orbit norm. -/
theorem norm_le_orbitNormFun (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) (x : E) : ‖x‖ ≤ orbitNormFun π x := by
  have h := le_ciSup (orbitNormFun_bddAbove π hC x) 1
  rwa [map_one, one_apply_eq_self] at h

/-- The uniform operator bound gives the other comparison of the equivalent norms. -/
theorem orbitNormFun_le (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) (x : E) : orbitNormFun π x ≤ C * ‖x‖ :=
  ciSup_le fun s ↦ (π s).le_of_opNorm_le (hC s) x

/-- The scalar-homogeneous seminorm given by the supremum along an orbit. -/
noncomputable def orbitSeminorm (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) : Seminorm ℂ E :=
  Seminorm.ofSMulLE (orbitNormFun π) (by simp [orbitNormFun])
    (fun x y ↦ ciSup_le fun s ↦ by
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (le_ciSup (orbitNormFun_bddAbove π hC x) s)
        (le_ciSup (orbitNormFun_bddAbove π hC y) s)))
    (fun c x ↦ ciSup_le fun s ↦ by
      rw [map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (le_ciSup (orbitNormFun_bddAbove π hC x) s) (norm_nonneg _))

/-- The orbit norm is an additive-group norm. It is nondegenerate because the
representation maps the monoid identity to the identity operator. -/
noncomputable def orbitNorm (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) : AddGroupNorm E where
  toAddGroupSeminorm := (orbitSeminorm π hC).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' x hx := by
    have hx' : orbitNormFun π x = 0 := hx
    exact norm_eq_zero.mp (le_antisymm ((norm_le_orbitNormFun π hC x).trans_eq hx') (norm_nonneg _))

/-- The additive-group norm evaluates to the explicit supremum. -/
@[simp] theorem orbitNorm_apply (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) (x : E) : orbitNorm π hC x = orbitNormFun π x :=
  rfl

/-- The orbit norm has complex scalar homogeneity. -/
theorem orbitNorm_smul (π : S →* (E →L[ℂ] E)) {C : ℝ} (hC : ∀ s, ‖π s‖ ≤ C)
    (c : ℂ) (x : E) : orbitNorm π hC (c • x) = ‖c‖ * orbitNorm π hC x :=
  map_smul_eq_mul (orbitSeminorm π hC) c x

/-- Every representing operator is a contraction in the orbit norm. -/
theorem orbitNorm_apply_op_le (π : S →* (E →L[ℂ] E)) {C : ℝ} (hC : ∀ s, ‖π s‖ ≤ C)
    (s : S) (x : E) : orbitNorm π hC (π s x) ≤ orbitNorm π hC x := by
  rw [orbitNorm_apply, orbitNorm_apply]
  apply ciSup_le
  intro t
  change ‖π t (π s x)‖ ≤ orbitNormFun π x
  rw [← mul_apply_eq_comp, ← map_mul]
  exact le_ciSup (orbitNormFun_bddAbove π hC x) (t * s)

/-- The norm comparison in §2.4, together with complex homogeneity and contractivity. -/
theorem exists_equivalent_contractive_norm (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) :
    ∃ n : AddGroupNorm E,
      (∀ x, n x = ⨆ s, ‖π s x‖) ∧
      (∀ x, ‖x‖ ≤ n x ∧ n x ≤ C * ‖x‖) ∧
      (∀ (c : ℂ) x, n (c • x) = ‖c‖ * n x) ∧
      ∀ s x, n (π s x) ≤ n x :=
  ⟨orbitNorm π hC, orbitNorm_apply π hC,
    fun x ↦ by
      rw [orbitNorm_apply]
      exact ⟨norm_le_orbitNormFun π hC x, orbitNormFun_le π hC x⟩,
    orbitNorm_smul π hC, orbitNorm_apply_op_le π hC⟩

end JdLG
