/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleUnitary
public import JdLG.ReversibleUnitaryRestriction
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Order.Zorn

/-! # Hilbert sums of finite-dimensional invariant subspaces -/

@[expose] public section

open Set Submodule
open scoped InnerProductSpace

namespace JdLG

section Decomposition

variable {G 𝕜 H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A strongly continuous unitary action of a compact group is the Hilbert direct sum
of finite-dimensional invariant subspaces. The family is produced by maximality, using
the averaging argument on its orthogonal complement. -/
theorem exists_invariant_hilbertSum_of_compact_unitary
    (U : G →* (H ≃ₗᵢ[𝕜] H)) (hU : ∀ x, Continuous fun g ↦ U g x) :
    ∃ I : Set (Submodule 𝕜 H),
      (∀ V ∈ I, FiniteDimensional 𝕜 V ∧ UnitaryInvariant U V) ∧
        IsHilbertSum 𝕜 (fun i : I ↦ i.1) (fun i ↦ i.1.subtypeₗᵢ) := by
  let admissible : Set (Set (Submodule 𝕜 H)) :=
    {s | (∀ V ∈ s, V ≠ ⊥ ∧ FiniteDimensional 𝕜 V ∧ UnitaryInvariant U V) ∧
      s.Pairwise fun V W ↦ V ⟂ W}
  obtain ⟨I, hI⟩ := zorn_subset admissible (fun c hc hchain ↦ by
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun _ ↦ subset_sUnion_of_mem⟩
    · intro V hV
      obtain ⟨s, hs, hVs⟩ := mem_sUnion.1 hV
      exact (hc hs).1 V hVs
    · intro V hV W hW hne
      obtain ⟨s, hs, hVs⟩ := mem_sUnion.1 hV
      obtain ⟨t, ht, hWt⟩ := mem_sUnion.1 hW
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 (hst hVs) hWt hne
      · exact (hc hs).2 hVs (hts hWt) hne)
  have hgood : ∀ V ∈ I, V ≠ ⊥ ∧ FiniteDimensional 𝕜 V ∧ UnitaryInvariant U V := hI.1.1
  have hortho : I.Pairwise fun V W ↦ V ⟂ W := hI.1.2
  let W : Submodule 𝕜 H := ⨆ i : I, i.1
  have hW : UnitaryInvariant U W := UnitaryInvariant.iSup fun i : I ↦ (hgood i.1 i.2).2.2
  have htotal : Wᗮ = ⊥ := by
    by_contra hbot
    rw [← Submodule.subsingleton_iff_eq_bot] at hbot
    let : Nontrivial Wᗮ := not_subsingleton_iff_nontrivial.1 hbot
    obtain ⟨x, hx⟩ : ∃ x : Wᗮ, x ≠ 0 := exists_ne 0
    let U' := unitarySubmoduleAction U Wᗮ hW.orthogonal
    have hU' (y : Wᗮ) : Continuous fun g ↦ U' g y :=
      (hU y).subtype_mk _
    obtain ⟨V', hV'ne, hV'fd, hV'inv⟩ :=
      exists_finiteDimensional_invariant_of_compact_unitary U' hU' hx
    let V := V'.map Wᗮ.subtype
    have hVle : V ≤ Wᗮ := by
      rintro z ⟨y, _, rfl⟩
      exact y.2
    have hVne : V ≠ ⊥ := by
      intro hVzero
      apply hV'ne
      apply le_antisymm _ bot_le
      intro y hy
      have hmem : (y : H) ∈ V := ⟨y, hy, rfl⟩
      rw [hVzero, Submodule.mem_bot] at hmem
      exact (Submodule.mem_bot 𝕜).2 (Subtype.ext hmem)
    have hVfd : FiniteDimensional 𝕜 V := by
      change FiniteDimensional 𝕜 (V'.map Wᗮ.subtype)
      infer_instance
    have hVi : UnitaryInvariant U V := by
      rintro g _ ⟨y, hy, rfl⟩
      exact ⟨U' g y, hV'inv g _ hy, rfl⟩
    have hVW (B : Submodule 𝕜 H) (hB : B ∈ I) : V ⟂ B :=
      Submodule.isOrtho_iff_le.2
        (hVle.trans (Submodule.orthogonal_le (le_iSup (fun i : I ↦ i.1) ⟨B, hB⟩)))
    have hnew : insert V I ∈ admissible := by
      refine ⟨?_, ?_⟩
      · intro B hB
        rcases mem_insert_iff.1 hB with rfl | hB
        · exact ⟨hVne, hVfd, hVi⟩
        · exact hgood B hB
      · intro A hA B hB hAB
        rcases mem_insert_iff.1 hA with rfl | hA
        · exact hVW B ((mem_insert_iff.1 hB).resolve_left hAB.symm)
        rcases mem_insert_iff.1 hB with rfl | hB
        · exact (hVW A hA).symm
        · exact hortho hA hB hAB
    have hVm : V ∈ I := hI.2 hnew (subset_insert _ _) (mem_insert _ _)
    exact hVne (Submodule.isOrtho_self.1 (hVW V hVm))
  refine ⟨I, fun V hV ↦ (hgood V hV).2, ?_⟩
  let (i : I) : FiniteDimensional 𝕜 i.1 := (hgood i.1 i.2).2.1
  apply IsHilbertSum.mkInternal
  · intro i j hij x y
    exact Submodule.isOrtho_iff_inner_eq.1
      (hortho i.2 j.2 (fun he ↦ hij (Subtype.ext he))) _ x.2 _ y.2
  · change ⊤ ≤ W.topologicalClosure
    rw [← Submodule.orthogonal_orthogonal_eq_closure, htotal, Submodule.bot_orthogonal_eq_top]

end Decomposition

end JdLG
