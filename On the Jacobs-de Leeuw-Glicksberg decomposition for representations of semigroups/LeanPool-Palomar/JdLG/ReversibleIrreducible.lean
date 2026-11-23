/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleHilbertSum

/-! # Irreducible summands for compact unitary actions -/

@[expose] public section

open Set Submodule

namespace JdLG

section FiniteDimensional

variable {G 𝕜 H : Type*} [Group G] [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (U : G →* (H ≃ₗᵢ[𝕜] H))

/-- A nonzero invariant subspace with no proper nonzero invariant subspace. -/
def UnitaryIrreducibleOn (W : Submodule 𝕜 H) : Prop :=
  W ≠ ⊥ ∧ UnitaryInvariant U W ∧
    ∀ V ≤ W, UnitaryInvariant U V → V = ⊥ ∨ V = W

/-- A nonzero finite-dimensional invariant subspace contains an irreducible
subspace, obtained by minimizing dimension among its nonzero invariant subspaces. -/
theorem exists_irreducibleOn_le {W : Submodule 𝕜 H} [FiniteDimensional 𝕜 W]
    (hW : UnitaryInvariant U W) (hWne : W ≠ ⊥) :
    ∃ A ≤ W, UnitaryIrreducibleOn U A ∧ FiniteDimensional 𝕜 A := by
  classical
  let P (n : ℕ) := ∃ A ≤ W, A ≠ ⊥ ∧ UnitaryInvariant U A ∧ Module.finrank 𝕜 A = n
  have hP : ∃ n, P n := ⟨_, W, le_rfl, hWne, hW, rfl⟩
  obtain ⟨A, hAW, hAne, hA, hdim⟩ := Nat.find_spec hP
  let : FiniteDimensional 𝕜 A :=
    FiniteDimensional.of_injective _ (Submodule.inclusion_injective hAW)
  refine ⟨A, hAW, ⟨hAne, hA, fun V hVA hV ↦ ?_⟩, inferInstance⟩
  by_cases hVne : V = ⊥
  · exact Or.inl hVne
  · right
    by_contra hneq
    have hlt : V < A := lt_of_le_of_ne hVA hneq
    have hm := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hdim] at hm
    exact Nat.find_min hP hm ⟨V, hVA.trans hAW, hVne, hV, rfl⟩

/-- A finite-dimensional invariant subspace is spanned by its irreducible
unitary subspaces. -/
theorem iSup_irreducibleOn_le_eq {W : Submodule 𝕜 H} [FiniteDimensional 𝕜 W]
    (hW : UnitaryInvariant U W) :
    (⨆ A : {A : Submodule 𝕜 H // A ≤ W ∧ UnitaryIrreducibleOn U A}, A.1) = W := by
  let I := {A : Submodule 𝕜 H | A ≤ W ∧ UnitaryIrreducibleOn U A}
  let B : Submodule 𝕜 H := ⨆ A : I, A.1
  have hBW : B ≤ W := iSup_le fun A ↦ A.2.1
  have hB : UnitaryInvariant U B := UnitaryInvariant.iSup fun A : I ↦ A.2.2.2.1
  let : FiniteDimensional 𝕜 B :=
    FiniteDimensional.of_injective _ (Submodule.inclusion_injective hBW)
  let D := Bᗮ ⊓ W
  have hD : UnitaryInvariant U D :=
    fun g x hx ↦ ⟨hB.orthogonal g x hx.1, hW g x hx.2⟩
  have hDW : D ≤ W := inf_le_right
  let : FiniteDimensional 𝕜 D :=
    FiniteDimensional.of_injective _ (Submodule.inclusion_injective hDW)
  have hDzero : D = ⊥ := by
    by_contra hDne
    obtain ⟨A, hAD, hA, _⟩ := exists_irreducibleOn_le U hD hDne
    have hAB : A ≤ B := le_iSup (fun a : I ↦ a.1) ⟨A, hAD.trans hDW, hA⟩
    have hA' : A ≤ B ⊓ Bᗮ := le_inf hAB (hAD.trans inf_le_left)
    rw [Submodule.inf_orthogonal_eq_bot] at hA'
    exact hA.1 (le_antisymm hA' bot_le)
  change B = W
  calc
    B = B ⊔ D := by rw [hDzero, sup_bot_eq]
    _ = (B ⊔ Bᗮ) ⊓ W := (sup_inf_assoc_of_le Bᗮ hBW).symm
    _ = W := by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection, top_inf_eq]

end FiniteDimensional

section CompactGroup

variable {G 𝕜 H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A strongly continuous unitary action of a compact group has dense linear
span of its irreducible finite-dimensional invariant subspaces. -/
theorem iSup_finiteDimensional_irreducible_topologicalClosure_eq_top
    (U : G →* (H ≃ₗᵢ[𝕜] H)) (hU : ∀ x, Continuous fun g ↦ U g x) :
    (⨆ W : {W : Submodule 𝕜 H // FiniteDimensional 𝕜 W ∧ UnitaryIrreducibleOn U W},
      W.1).topologicalClosure = ⊤ := by
  let J := {W : Submodule 𝕜 H | FiniteDimensional 𝕜 W ∧ UnitaryIrreducibleOn U W}
  let V : Submodule 𝕜 H := ⨆ W : J, W.1
  obtain ⟨I, hI, hsum⟩ := exists_invariant_hilbertSum_of_compact_unitary U hU
  let (i : I) : FiniteDimensional 𝕜 i.1 := (hI i.1 i.2).1
  have hle (i : I) : i.1 ≤ V := by
    rw [← iSup_irreducibleOn_le_eq U (hI i.1 i.2).2]
    refine iSup_le fun A ↦ le_iSup (fun W : J ↦ W.1) ⟨A.1, ?_, A.2.2⟩
    exact FiniteDimensional.of_injective _ (Submodule.inclusion_injective A.2.1)
  have hdense : (⨆ i : I, i.1).topologicalClosure = ⊤ := by
    have hr := hsum.OrthogonalFamily.range_linearIsometry
    rw [LinearMap.range_eq_top.2 hsum.surjective_isometry] at hr
    simpa only [Submodule.range_subtype, Submodule.subtypeₗᵢ_toLinearMap] using hr.symm
  change V.topologicalClosure = ⊤
  exact top_unique (hdense ▸ Submodule.topologicalClosure_mono (iSup_le hle))

end CompactGroup

end JdLG
