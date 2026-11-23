/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Dual
public import JdLG.RightZeroExample

/-!
# The two finite operator examples in Section 2.2

Examples 2.1 and 2.2 use the same two rank-one projections, first as
operators on `ℂ × ℂ` and then as operators on its continuous dual.
-/

@[expose] public section

namespace JdLG.PaperExamplesFinite

/-- The two-point right zero semigroup with an identity adjoined. -/
inductive Point where
  | unit
  | first
  | second

instance : Monoid Point where
  one := .unit
  mul a b := match b with
    | .unit => a
    | .first => .first
    | .second => .second
  mul_assoc a b c := by cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one _ := rfl

instance : Finite Point := Finite.of_injective
  (fun a ↦ (match a with | .unit => 0 | .first => 1 | .second => 2 : Fin 3)) (by
    intro a b h
    cases a <;> cases b <;> simp_all)

instance : Finite Pointᵐᵒᵖ :=
  Finite.of_injective MulOpposite.unop MulOpposite.unop_injective

local notation "V" => ℂ × ℂ

/-- The operators of Example 2.1 are the identity and two diagonal projections. -/
noncomputable def operator : Point → V →L[ℂ] V
  | .unit => ContinuousLinearMap.id ℂ V
  | .first => (ContinuousLinearMap.fst ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)
  | .second => (ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The monoid of Example 2.1 acting on `ℂ²`. -/
noncomputable def primal : Point →ₙ* (V →L[ℂ] V) where
  toFun := operator
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    cases a <;> cases b <;> rfl

theorem primal_unit : primal .unit = 1 := rfl

theorem primal_first_apply (x : V) : primal .first x = (x.1, x.1) := rfl

theorem primal_second_apply (x : V) : primal .second x = (x.2, x.2) := rfl

theorem primal_multiplication_table :
    primal .second * primal .first = primal .first ∧
    primal .first * primal .first = primal .first ∧
    primal .first * primal .second = primal .second ∧
    primal .second * primal .second = primal .second := by
  simp only [← map_mul]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem finite_closure_mem {S : Type*} [Semigroup S] [Finite S]
    (ρ : S →ₙ* (V →L[ℂ] V)) (A : V →WOT[ℂ] V) :
    A ∈ weakOperatorClosure ρ ↔ ∃ s : S, weakRepresentation ρ s = A := by
  change A ∈ closure (Set.range (weakRepresentation ρ)) ↔ _
  simp only [(Set.finite_range (weakRepresentation ρ)).isClosed.closure_eq, Set.mem_range]

theorem primal_weakly_compact : IsCompact (weakOperatorClosure primal : Set (V →WOT[ℂ] V)) := by
  have h : (weakOperatorClosure primal : Set (V →WOT[ℂ] V)) =
      Set.range (weakRepresentation primal) := by
    ext A
    exact finite_closure_mem primal A
  rw [h]
  exact (Set.finite_range _).isCompact

theorem primal_stable_iff_coordinate_zero (x : V) :
    IsAlmostWeaklyStable (closureAction primal) x ↔ x.1 = 0 ∨ x.2 = 0 := by
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨s, hs⟩ := (finite_closure_mem primal A.1).1 A.2
    change A.1 x = 0 at hA
    rw [← hs] at hA
    cases s
    · exact Or.inl (congrArg Prod.fst hA)
    · exact Or.inl (congrArg Prod.fst hA)
    · exact Or.inr (congrArg Prod.fst hA)
  · rintro (h | h)
    · refine ⟨closureInclusion primal .first, ?_⟩
      change (x.1, x.1) = (0, 0)
      rw [h]
    · refine ⟨closureInclusion primal .second, ?_⟩
      change (x.2, x.2) = (0, 0)
      rw [h]

theorem primal_stable_not_add_closed :
    ∃ x y : V,
      IsAlmostWeaklyStable (closureAction primal) x ∧
      IsAlmostWeaklyStable (closureAction primal) y ∧
      ¬ IsAlmostWeaklyStable (closureAction primal) (x + y) := by
  refine ⟨(1, 0), (0, 1), ?_, ?_, ?_⟩
  · exact (primal_stable_iff_coordinate_zero _).2 (Or.inr rfl)
  · exact (primal_stable_iff_coordinate_zero _).2 (Or.inl rfl)
  · rw [primal_stable_iff_coordinate_zero]
    simp

theorem primal_stable_not_invariant :
    ∃ s : Point, ∃ x : V, IsAlmostWeaklyStable (closureAction primal) x ∧
      ¬ IsAlmostWeaklyStable (closureAction primal) (primal s x) := by
  refine ⟨.first, (1, 0), (primal_stable_iff_coordinate_zero _).2 (Or.inr rfl), ?_⟩
  rw [primal_stable_iff_coordinate_zero, primal_first_apply]
  simp

/-- The diagonal line in `ℂ²`. -/
def diagonal : Submodule ℂ V :=
  LinearMap.ker (LinearMap.fst ℂ ℂ ℂ - LinearMap.snd ℂ ℂ ℂ)

theorem mem_diagonal_iff (x : V) : x ∈ diagonal ↔ x.1 = x.2 := by
  change x.1 - x.2 = 0 ↔ x.1 = x.2
  exact sub_eq_zero

theorem diagonal_eq_span : diagonal = Submodule.span ℂ ({(1, 1)} : Set V) := by
  ext x
  rw [mem_diagonal_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    exact ⟨x.1, Prod.ext (mul_one x.1) ((mul_one x.1).trans h)⟩
  · rintro ⟨z, rfl⟩
    rfl

theorem diagonal_is_invariant :
    ∀ s : Point, ∀ x ∈ diagonal, primal s x ∈ diagonal := by
  intro s x hx
  cases s
  · exact hx
  · exact (mem_diagonal_iff _).2 rfl
  · exact (mem_diagonal_iff _).2 rfl

private theorem full_of_off_diagonal {Y : Submodule ℂ V}
    (hY : ∀ s : Point, ∀ x ∈ Y, primal s x ∈ Y)
    {x : V} (hx : x ∈ Y) (hne : x.1 ≠ x.2) : Y = ⊤ := by
  have hv : (0, x.2 - x.1) ∈ Y := by
    have hh := Y.sub_mem hx (hY .first x hx)
    change (x.1 - x.1, x.2 - x.1) ∈ Y at hh
    simpa only [sub_self] using hh
  have hd : x.2 - x.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hev : ((0, 1) : V) ∈ Y := by
    simpa [Prod.smul_mk, smul_eq_mul, hd] using Y.smul_mem (x.2 - x.1)⁻¹ hv
  have hdiag : ((1, 1) : V) ∈ Y := hY .second _ hev
  have heh : ((1, 0) : V) ∈ Y := by
    simpa using Y.sub_mem hdiag hev
  apply top_unique
  intro z _
  simpa [Prod.smul_mk, smul_eq_mul] using
    Y.add_mem (Y.smul_mem z.1 heh) (Y.smul_mem z.2 hev)

/-- The only invariant subspace apart from `⊥` and `⊤` is the diagonal. -/
theorem primal_only_proper_nonzero_invariant (Y : Submodule ℂ V)
    (hY : ∀ s : Point, ∀ x ∈ Y, primal s x ∈ Y) (hne : Y ≠ ⊥) (hproper : Y ≠ ⊤) :
    Y = diagonal := by
  have hle : Y ≤ diagonal := by
    intro x hx
    exact (mem_diagonal_iff _).2 (by
      by_contra hh
      exact hproper (full_of_off_diagonal hY hx hh))
  obtain ⟨x, hx, hxne⟩ := Y.ne_bot_iff.1 hne
  have hsame := (mem_diagonal_iff _).1 (hle hx)
  have hfirst : x.1 ≠ 0 := by
    intro h
    exact hxne (Prod.ext h (hsame.symm.trans h))
  have hones : ((1, 1) : V) ∈ Y := by
    have hh := Y.smul_mem x.1⁻¹ hx
    change (x.1⁻¹ * x.1, x.1⁻¹ * x.2) ∈ Y at hh
    rw [← hsame] at hh
    simpa [hfirst] using hh
  apply le_antisymm hle
  rw [diagonal_eq_span]
  exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hones)

/-- The algebraic pairing with the dual in the standard basis of `ℂ²`. -/
noncomputable def dualCoordinate (x : V) : StrongDual ℂ V :=
  x.1 • (ContinuousLinearMap.fst ℂ ℂ ℂ) + x.2 • (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The adjoint operators in the dual coordinates of Example 2.2. -/
noncomputable def dualOperator : Point → V →L[ℂ] V
  | .unit => ContinuousLinearMap.id ℂ V
  | .first => ((ContinuousLinearMap.fst ℂ ℂ ℂ) + ContinuousLinearMap.snd ℂ ℂ ℂ).prod 0
  | .second => (0 : V →L[ℂ] ℂ).prod
      ((ContinuousLinearMap.fst ℂ ℂ ℂ) + ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The opposite monoid acts by the adjoints, in coordinates. -/
noncomputable def dual : Pointᵐᵒᵖ →ₙ* (V →L[ℂ] V) where
  toFun s := dualOperator s.unop
  map_mul' s t := by
    apply ContinuousLinearMap.ext
    intro x
    cases s using MulOpposite.rec' with
    | h s =>
      cases t using MulOpposite.rec' with
      | h t =>
        cases s <;> cases t <;> ext <;> simp [dualOperator]

theorem dual_first_apply (x : V) : dual (MulOpposite.op .first) x = (x.1 + x.2, 0) := rfl

theorem dual_second_apply (x : V) : dual (MulOpposite.op .second) x = (0, x.1 + x.2) := rfl

/-- The displayed coordinate operators are literally the Banach adjoints under
the linear coordinate pairing, which is bilinear rather than Hermitian. -/
theorem dual_is_adjoint (s : Point) (x : V) :
    dualCoordinate (dual (MulOpposite.op s) x) = banachAdjoint (primal s) (dualCoordinate x) := by
  apply ContinuousLinearMap.ext
  intro y
  cases s
  · rfl
  · change (x.1 + x.2) * y.1 + 0 * y.2 = x.1 * y.1 + x.2 * y.1
    rw [zero_mul, add_zero, add_mul]
  · change 0 * y.1 + (x.1 + x.2) * y.2 = x.1 * y.2 + x.2 * y.2
    rw [zero_mul, zero_add, add_mul]

/-- Every continuous linear functional has the displayed coordinate pairing. -/
theorem dualCoordinate_bijective : Function.Bijective dualCoordinate := by
  constructor
  · intro x y h
    apply Prod.ext
    · simpa [dualCoordinate] using congrArg (fun f : StrongDual ℂ V ↦ f (1, 0)) h
    · simpa [dualCoordinate] using congrArg (fun f : StrongDual ℂ V ↦ f (0, 1)) h
  · intro f
    refine ⟨(f (1, 0), f (0, 1)), ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    have hx : x.1 • ((1, 0) : V) + x.2 • ((0, 1) : V) = x := by
      ext <;> simp [smul_eq_mul]
    change f (1, 0) * x.1 + f (0, 1) * x.2 = f x
    conv_rhs => rw [← hx, map_add, map_smul, map_smul]
    simp only [smul_eq_mul, mul_comm]

theorem dual_weakly_compact : IsCompact (weakOperatorClosure dual : Set (V →WOT[ℂ] V)) := by
  have h : (weakOperatorClosure dual : Set (V →WOT[ℂ] V)) =
      Set.range (weakRepresentation dual) := by
    ext A
    exact finite_closure_mem dual A
  rw [h]
  exact (Set.finite_range _).isCompact

/-- Reversible vectors are invariant under any represented semigroup, even
when they fail to be a subspace as in Example 2.2. -/
theorem reversible_apply {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (ρ : S →ₙ* (E →L[𝕜] E))
    {x : E} (hx : IsReversible ρ x) (t : S) : IsReversible ρ (ρ t x) := by
  intro s
  obtain ⟨u, hu⟩ := hx (s * t)
  rw [map_mul] at hu
  refine ⟨t * u, ?_⟩
  rw [map_mul]
  exact congrArg (ρ t) hu

theorem dual_reversible_iff_coordinate_zero (x : V) :
    IsReversible (closureAction dual) x ↔ x.1 = 0 ∨ x.2 = 0 := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := h (closureInclusion dual (MulOpposite.op .first))
    obtain ⟨s, hs⟩ := (finite_closure_mem dual B.1).1 B.2
    change B.1 (x.1 + x.2, 0) = x at hB
    rw [← hs] at hB
    cases s using MulOpposite.rec' with
    | h s =>
      cases s
      · exact Or.inr (congrArg Prod.snd hB).symm
      · exact Or.inr (congrArg Prod.snd hB).symm
      · exact Or.inl (congrArg Prod.fst hB).symm
  · intro hx A
    obtain ⟨s, hs⟩ := (finite_closure_mem dual A.1).1 A.2
    change ∃ B : weakOperatorClosure dual, B.1 (A.1 x) = x
    rw [← hs]
    obtain ⟨u, v⟩ := x
    change u = 0 ∨ v = 0 at hx
    cases s using MulOpposite.rec' with
    | h s =>
      rcases hx with h | h
      · subst u
        refine ⟨closureInclusion dual (MulOpposite.op .second), ?_⟩
        cases s
        · change (0, 0 + v) = (0, v)
          rw [zero_add]
        · change (0, (0 + v) + 0) = (0, v)
          rw [zero_add, add_zero]
        · change (0, 0 + (0 + v)) = (0, v)
          rw [zero_add, zero_add]
      · subst v
        refine ⟨closureInclusion dual (MulOpposite.op .first), ?_⟩
        cases s
        · change (u + 0, 0) = (u, 0)
          rw [add_zero]
        · change ((u + 0) + 0, 0) = (u, 0)
          rw [add_zero, add_zero]
        · change (0 + (u + 0), 0) = (u, 0)
          rw [zero_add, add_zero]

theorem dual_reversible_not_add_closed :
    ∃ x y : V,
      IsReversible (closureAction dual) x ∧ IsReversible (closureAction dual) y ∧
      ¬ IsReversible (closureAction dual) (x + y) := by
  refine ⟨(1, 0), (0, 1), ?_, ?_, ?_⟩
  · exact (dual_reversible_iff_coordinate_zero _).2 (Or.inr rfl)
  · exact (dual_reversible_iff_coordinate_zero _).2 (Or.inl rfl)
  · rw [dual_reversible_iff_coordinate_zero]
    simp

/-- Example 3.5 has two distinct reversible-plus-stable decompositions of `(1,0)`. -/
theorem rightZero_nonunique_splitting :
    ∃ r₁ r₂ w₁ w₂ : V, r₁ ≠ r₂ ∧
      IsReversible (closureAction RightZeroExample.representation) r₁ ∧
      IsReversible (closureAction RightZeroExample.representation) r₂ ∧
      IsAlmostWeaklyStable (closureAction RightZeroExample.representation) w₁ ∧
      IsAlmostWeaklyStable (closureAction RightZeroExample.representation) w₂ ∧
      r₁ + w₁ = (1, 0) ∧ r₂ + w₂ = (1, 0) := by
  refine ⟨(0, 0), (1, 1), (1, 0), (0, -1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact zero_ne_one (congrArg Prod.fst h)
  · exact (RightZeroExample.reversible_iff_equal_coordinates _).2 rfl
  · exact (RightZeroExample.reversible_iff_equal_coordinates _).2 rfl
  · exact (RightZeroExample.stable_iff_coordinate_zero _).2 (Or.inr rfl)
  · exact (RightZeroExample.stable_iff_coordinate_zero _).2 (Or.inl rfl)
  · simp
  · simp

end JdLG.PaperExamplesFinite
