/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Topology.Compactness.Compact

/-!
# Fixed points in weakly compact operator semigroups

The finite intersection argument gives the projection in Proposition 3.4 of
Barthmann, Farhangi and Kuznetsova, arXiv:2509.24003v3.
-/

@[expose] public section

namespace JdLG

open ContinuousLinearMapWOT Set

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An operator fixes `x` for each operator in the semigroup. -/
def IsFixedBy (operators : Subsemigroup (E →WOT[𝕜] E)) (x : E) : Prop :=
  ∀ A ∈ operators, A x = x

private theorem isClosed_fixed_image (operators : Subsemigroup (E →WOT[𝕜] E)) (x : E) :
    IsClosed {P : E →WOT[𝕜] E | IsFixedBy operators (P x)} := by
  have heq : {P : E →WOT[𝕜] E | IsFixedBy operators (P x)} =
      ⋂ A : operators, ⋂ f : StrongDual 𝕜 E,
        {P : E →WOT[𝕜] E | (f.comp A.1.toCLM) (P x) = f (P x)} := by
    ext P
    simp only [mem_ofPred_eq, IsFixedBy, mem_iInter]
    constructor
    · intro h A f
      exact congrArg f (h A.1 A.2)
    · intro h A hA
      exact (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).2 (h ⟨A, hA⟩)
  rw [heq]
  exact isClosed_iInter fun A ↦ isClosed_iInter fun f ↦
    isClosed_eq (continuous_dual_apply x (f.comp A.1.toCLM)) (continuous_dual_apply x f)

private theorem exists_fixed_image_on_finset (operators : Subsemigroup (E →WOT[𝕜] E))
    (hex : ∀ x : E, ∃ A ∈ operators, IsFixedBy operators (A x)) (F : Finset E) :
    ∃ P ∈ operators, ∀ x ∈ F, IsFixedBy operators (P x) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨P, hP, _⟩ := hex 0
    exact ⟨P, hP, by simp⟩
  | @insert x F _ ih =>
    obtain ⟨P, hP, hPF⟩ := ih
    obtain ⟨A, hA, hAx⟩ := hex (P x)
    refine ⟨A * P, operators.mul_mem hA hP, fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simpa only [ContinuousLinearMapWOT.mul_apply] using hAx
    · have heq : (A * P) y = P y := hPF y hy A hA
      rw [heq]
      exact hPF y hy

private theorem exists_common_fixed_projection (operators : Subsemigroup (E →WOT[𝕜] E))
    (hcompact : IsCompact (operators : Set (E →WOT[𝕜] E)))
    (hex : ∀ x : E, ∃ A ∈ operators, IsFixedBy operators (A x)) :
    ∃ P ∈ operators, ∀ x : E, IsFixedBy operators (P x) := by
  let closed := fun x : E ↦ {P : E →WOT[𝕜] E | IsFixedBy operators (P x)}
  obtain ⟨P, hP, hmem⟩ := hcompact.inter_iInter_nonempty closed
    (isClosed_fixed_image operators) (fun F ↦ by
      obtain ⟨P, hP, hPF⟩ := exists_fixed_image_on_finset operators hex F
      exact ⟨P, hP, mem_iInter.mpr fun x ↦ mem_iInter.mpr fun hx ↦ hPF x hx⟩)
  exact ⟨P, hP, mem_iInter.mp hmem⟩

/-- Proposition 3.4. If each orbit of a weak-operator compact semigroup contains
a unique fixed vector, its smallest two-sided ideal is the singleton `{P}`.
The reversible vectors are the common fixed vectors, and a vector is killed by
some operator in the semigroup exactly when it is in the kernel of `P`. -/
theorem decomposition_of_unique_fixed_point
    (operators : Subsemigroup (E →WOT[𝕜] E))
    (hcompact : IsCompact (operators : Set (E →WOT[𝕜] E)))
    (hfixed : ∀ x : E, ∃! y : E,
      (∃ A ∈ operators, A x = y) ∧ IsFixedBy operators y) :
    ∃ P ∈ operators, (∀ A ∈ operators, A * P = P ∧ P * A = P) ∧
      (∀ x : E, (∀ A ∈ operators, ∃ B ∈ operators, B (A x) = x) ↔
        IsFixedBy operators x) ∧
      ∀ x : E, (∃ A ∈ operators, A x = 0) ↔ P x = 0 := by
  have hex : ∀ x : E, ∃ A ∈ operators, IsFixedBy operators (A x) := by
    intro x
    obtain ⟨y, ⟨⟨A, hA, rfl⟩, hy⟩, _⟩ := hfixed x
    exact ⟨A, hA, hy⟩
  obtain ⟨P, hP, hfix⟩ := exists_common_fixed_projection operators hcompact hex
  have hright : ∀ A ∈ operators, P * A = P := by
    intro A hA
    ext x
    obtain ⟨_, _, hunique⟩ := hfixed x
    have h1 := hunique (P (A x)) ⟨⟨P * A, operators.mul_mem hP hA, rfl⟩, hfix (A x)⟩
    have h2 := hunique (P x) ⟨⟨P, hP, rfl⟩, hfix x⟩
    exact h1.trans h2.symm
  refine ⟨P, hP, fun A hA ↦ ⟨ContinuousLinearMapWOT.ext fun x ↦ hfix x A hA,
    hright A hA⟩, ?_, ?_⟩
  · intro x
    constructor
    · intro h
      obtain ⟨B, hB, hBP⟩ := h P hP
      have hx : P x = x := (hfix x B hB).symm.trans hBP
      rw [← hx]
      exact hfix x
    · exact fun h A hA ↦ ⟨P, hP, by rw [h A hA, h P hP]⟩
  · intro x
    constructor
    · rintro ⟨A, hA, hx⟩
      have h := congrArg (fun B : E →WOT[𝕜] E ↦ B x) (hright A hA)
      simpa only [ContinuousLinearMapWOT.mul_apply, hx, map_zero] using h.symm
    · exact fun hx ↦ ⟨P, hP, hx⟩

end JdLG
