/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Tactic.Linarith

/-! # Normal operators and the image–kernel decomposition -/

@[expose] public section

open ContinuousLinearMap
open scoped InnerProductSpace

namespace Mixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 4, equation (1). The image is the algebraic range of a bounded operator. -/
theorem normal_range_orthogonal (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    T.rangeᗮ = T.ker :=
  hT.orthogonal_range

/-- Lemma 4, equation (2). The norm closure of the image and the kernel are complementary. -/
theorem normal_rangeClosure_isCompl_ker (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    IsCompl T.range.topologicalClosure T.ker := by
  rw [← normal_range_orthogonal T hT, ← T.range.orthogonal_orthogonal_eq_closure]
  exact T.rangeᗮ.isCompl_orthogonal.symm

/-- Lemma 5, with the span of the union of the ranges written as an indexed supremum. -/
theorem normal_iInf_ker_orthogonal {ι : Type*} (T : ι → (H →L[ℂ] H))
    (hT : ∀ i, IsStarNormal (T i)) :
    (⨅ i, (T i).ker)ᗮ = (⨆ i, (T i).range).topologicalClosure := by
  simp_rw [← normal_range_orthogonal (T _) (hT _)]
  rw [Submodule.iInf_orthogonal, Submodule.orthogonal_orthogonal_eq_closure]

/-- Lemma 5 in the closed-linear-span form stated in the paper. -/
theorem normal_iInf_ker_orthogonal_eq_span {ι : Type*} (T : ι → (H →L[ℂ] H))
    (hT : ∀ i, IsStarNormal (T i)) :
    (⨅ i, (T i).ker)ᗮ =
      (Submodule.span ℂ (⋃ i, ((T i).range : Set H))).topologicalClosure := by
  simpa only [Submodule.span_iUnion, Submodule.span_eq] using normal_iInf_ker_orthogonal T hT

/-- Operators with the same kernel have this kernel for their product if the right
factor is normal. -/
theorem ker_mul_eq_ker_of_right_normal {A B : H →L[ℂ] H}
    (hB : IsStarNormal B) (hAB : A.ker = B.ker) :
    (A * B).ker = B.ker := by
  ext x
  change A (B x) = 0 ↔ B x = 0
  constructor
  · intro h
    have h₁ : B x ∈ B.range := ⟨x, rfl⟩
    have h₂ : B x ∈ B.rangeᗮ := by
      rw [normal_range_orthogonal B hB, ← hAB]
      exact h
    exact (Submodule.disjoint_def.mp B.range.orthogonal_disjoint) (B x) h₁ h₂
  · intro h
    rw [h, map_zero]

/-- Proposition 2(ii) for positive powers. -/
theorem normal_ker_pow (T : H →L[ℂ] H) (hT : IsStarNormal T) {n : ℕ} (hn : 0 < n) :
    (T ^ n).ker = T.ker := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction k with
  | zero => exact congrArg (fun A : H →L[ℂ] H ↦ A.ker) (pow_one T)
  | succ k ih =>
    rw [pow_succ]
    exact ker_mul_eq_ker_of_right_normal hT ih

/-- Proposition 2(ii) in its adjoint–operator–power form. -/
theorem normal_ker_adjoint_ker_pow (T : H →L[ℂ] H) (hT : IsStarNormal T) {n : ℕ}
    (hn : 0 < n) :
    T.adjoint.ker = T.ker ∧ T.ker = (T ^ n).ker :=
  ⟨hT.ker_adjoint_eq_ker, (normal_ker_pow T hT hn).symm⟩

/-- Proposition 2(ii) for positive total degree in an operator and its adjoint. -/
theorem normal_ker_mul_adjoint_pow (T : H →L[ℂ] H) (hT : IsStarNormal T) {n m : ℕ}
    (h : 1 ≤ n + m) :
    (T ^ n * T.adjoint ^ m).ker = T.ker := by
  let _ : IsStarNormal T := hT
  have hAdj : IsStarNormal T.adjoint := ContinuousLinearMap.star_eq_adjoint T ▸ inferInstance
  by_cases hn : n = 0
  · subst n
    have hm : 0 < m := by omega
    rw [pow_zero, one_mul, normal_ker_pow _ hAdj hm]
    exact hT.ker_adjoint_eq_ker
  · by_cases hm : m = 0
    · subst m
      simpa only [pow_zero, mul_one] using normal_ker_pow T hT (Nat.pos_of_ne_zero hn)
    · have hRight : (T.adjoint ^ m).ker = T.ker :=
        (normal_ker_pow _ hAdj (Nat.pos_of_ne_zero hm)).trans hT.ker_adjoint_eq_ker
      let _ : IsStarNormal T.adjoint := hAdj
      rw [ker_mul_eq_ker_of_right_normal inferInstance
          ((normal_ker_pow T hT (Nat.pos_of_ne_zero hn)).trans hRight.symm), hRight]

/-- The operator fact used in Lemma 7. An idempotent contraction is self-adjoint. -/
theorem isSelfAdjoint_of_idempotent_contraction (T : H →L[ℂ] H)
    (hIdem : T * T = T) (hNorm : ‖T‖ ≤ 1) : IsSelfAdjoint T := by
  have hAdjNorm : ‖T.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hNorm
  have hApply (x : H) : T (T x) = T x :=
    congrArg (fun A : H →L[ℂ] H ↦ A x) hIdem
  have hEq (x : H) : T.adjoint (T x) = T x := by
    have hle := T.adjoint.le_of_opNorm_le hAdjNorm (T x)
    rw [one_mul] at hle
    have hInner : ⟪T.adjoint (T x), T x⟫_ℂ = ⟪T x, T x⟫_ℂ := by
      rw [T.adjoint_inner_left, hApply]
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hExp := norm_sub_sq (𝕜 := ℂ) (T.adjoint (T x)) (T x)
    rw [hInner, inner_self_eq_norm_sq] at hExp
    have hsq := pow_le_pow_left₀ (norm_nonneg (T.adjoint (T x))) hle 2
    nlinarith
  have he : T = star T * T := by
    ext x
    exact (hEq x).symm
  exact he ▸ IsSelfAdjoint.star_mul_self T

end Mixing

