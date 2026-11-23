/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# A two-element right zero semigroup

Example 3.5 acts by right translations on the functions on a two-element
right zero semigroup. We use the equivalent coordinates `ℂ × ℂ`.
-/

@[expose] public section

namespace JdLG.RightZeroExample

/-- The two points of the right zero semigroup in Example 3.5. -/
inductive Point where
  | first
  | second

instance : Semigroup Point where
  mul _ b := b
  mul_assoc _ _ _ := rfl

instance : Finite Point := Finite.of_injective
  (fun a ↦ match a with | .first => false | .second => true) (by
    intro a b h
    cases a <;> cases b <;> simp_all)

/-- Right translation makes a function constant at the selected coordinate. -/
noncomputable def translate : Point → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)
  | .first => (ContinuousLinearMap.fst ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)
  | .second => (ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The two right translations form a representation. -/
noncomputable def representation : Point →ₙ* ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) where
  toFun := translate
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    cases a <;> cases b <;> rfl

private theorem mem_weakOperatorClosure_iff_exists
    (A : (ℂ × ℂ) →WOT[ℂ] (ℂ × ℂ)) :
    A ∈ weakOperatorClosure representation ↔
      ∃ s : Point, weakRepresentation representation s = A := by
  change A ∈ closure (Set.range (weakRepresentation representation)) ↔ _
  simp only [(Set.finite_range (weakRepresentation representation)).isClosed.closure_eq,
    Set.mem_range]

private theorem fixed_of_equal_coordinates (x : ℂ × ℂ) (hx : x.1 = x.2)
    (A : weakOperatorClosure representation) : closureAction representation A x = x := by
  obtain ⟨s, hs⟩ := (mem_weakOperatorClosure_iff_exists A.1).1 A.2
  change A.1 x = x
  rw [← hs]
  obtain ⟨z, w⟩ := x
  change z = w at hx
  subst w
  cases s <;> rfl

/-- The reversible vectors in Example 3.5 are the constant functions. -/
theorem reversible_iff_equal_coordinates (x : ℂ × ℂ) :
    IsReversible (closureAction representation) x ↔ x.1 = x.2 := by
  let A : weakOperatorClosure representation :=
    ⟨weakRepresentation representation .first, subset_closure ⟨.first, rfl⟩⟩
  constructor
  · intro h
    obtain ⟨B, hB⟩ := h A
    change closureAction representation B (x.1, x.1) = x at hB
    rw [fixed_of_equal_coordinates (x.1, x.1) rfl B] at hB
    exact congrArg Prod.snd hB
  · exact fun h B ↦ ⟨A, by rw [fixed_of_equal_coordinates x h B,
      fixed_of_equal_coordinates x h A]⟩

/-- The almost weakly stable vectors in the weakly closed example form the
union of the two coordinate axes. -/
theorem stable_iff_coordinate_zero (x : ℂ × ℂ) :
    IsAlmostWeaklyStable (closureAction representation) x ↔ x.1 = 0 ∨ x.2 = 0 := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨s, hs⟩ := (mem_weakOperatorClosure_iff_exists A.1).1 A.2
    change A.1 x = 0 at hA
    rw [← hs] at hA
    cases s
    · exact Or.inl (congrArg Prod.fst hA)
    · exact Or.inr (congrArg Prod.fst hA)
  · rintro (h | h)
    · refine ⟨⟨weakRepresentation representation .first, subset_closure ⟨.first, rfl⟩⟩, ?_⟩
      change (x.1, x.1) = (0, 0)
      rw [h]
    · refine ⟨⟨weakRepresentation representation .second, subset_closure ⟨.second, rfl⟩⟩, ?_⟩
      change (x.2, x.2) = (0, 0)
      rw [h]

/-- Example 3.5. The two coordinate axes are individually stable, but their
sum need not be stable. -/
theorem stable_not_add_closed :
    ∃ x y : ℂ × ℂ,
      IsAlmostWeaklyStable (closureAction representation) x ∧
      IsAlmostWeaklyStable (closureAction representation) y ∧
      ¬ IsAlmostWeaklyStable (closureAction representation) (x + y) := by
  refine ⟨(1, 0), (0, 1), ?_, ?_, ?_⟩
  · exact (stable_iff_coordinate_zero _).2 (Or.inr rfl)
  · exact (stable_iff_coordinate_zero _).2 (Or.inl rfl)
  · rw [stable_iff_coordinate_zero]
    simp

/-- The two right translations are not JdLG-admissible. -/
theorem not_admissible : ¬ IsJdLGAdmissible representation := by
  intro h
  obtain ⟨P, _, _, _, _, hstable⟩ := decomposition_of_admissible h
  obtain ⟨x, y, hx, hy, hxy⟩ := stable_not_add_closed
  have hadd : x + y ∈ LinearMap.ker (closureAction representation P).toLinearMap :=
    (LinearMap.ker (closureAction representation P).toLinearMap).add_mem
      ((hstable x).1 hx) ((hstable y).1 hy)
  exact hxy ((hstable (x + y)).2 hadd)

end JdLG.RightZeroExample
