/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationQuotientSpectrum
public import Mixing.NilrotationRegularEmbedding
public import Mixing.NilrotationLebesgueBasis

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory TopologicalSpace
open scoped Nilrotation ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G]

/-- An ergodic nilrotation with nontrivial effective commutator action has
countably infinite homogeneous Lebesgue spectrum off its eigenfunctions. -/
theorem nilrotationQuotient_countableLebesgue_of_dense_lift
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a^j*d*(γ:G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hEff : ¬(⊤ : Subgroup G).lowerCentralSeries 1 ≤ L) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    HasLebesgueComplement U ℕ := by
  classical
  let series := (⊤ : Subgroup G).lowerCentralSeries
  have hExists : ∃ i : ℕ, series i ≤ L := ⟨n, by
    change (⊤ : Subgroup G).lowerCentralSeries n ≤ L
    rw [hn]
    exact bot_le⟩
  let i := Nat.find hExists
  have hi : series i ≤ L := Nat.find_spec hExists
  have hi' : 1 < i := by
    by_contra! he
    exact hEff (((⊤ : Subgroup G).lowerCentralSeries_antitone he).trans hi)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, i = j+1 := ⟨i-1, by omega⟩
  have hj' : 0 < j := by omega
  have hnon : ¬series j ≤ L := Nat.find_min hExists (show j < Nat.find hExists by
    change j < i
    omega)
  let C := series j
  have hC : ⁅C, (⊤ : Subgroup G)⁆ ≤ L := by
    change series (j+1) ≤ L
    rwa [← hj]
  let q := nilrotation_lattice_le_verticalClosure C L
  let M := nilrotationVerticalClosure C L
  let ν := μ.map (Subgroup.quotientMapOfLE q)
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    (nilrotationQuotientMap_continuous q).measurable.aemeasurable).mpr inferInstance
  let : CompactSpace (G ⧸ M) := nilrotationQuotient_compactSpace q
  have hB := nilrotationQuotient_spectralFacts_of_dense_lift M
    (Subgroup.isClosed_topologicalClosure _) n hn a d (nilrotation_dense_lifted_cosets_mono q hd)
    hgen ν (nilrotationQuotient_map_preserves q μ hμ)
  obtain ⟨hFacts,_,hOrbits⟩ := nilrotationQuotient_vertical_spectralFacts j L hL hC a d hd hgen μ hμ
    (fun _ ↦ hB)
  let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
  let : MeasureTheory.IsSeparable μ := MeasureTheory.isSeparable_of_sigmaFinite μ
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  obtain ⟨J,hJ⟩ := exists_purePointOrthogonal_hilbertSumRegularEmbedding U hFacts.haarAC
  obtain ⟨x,hHaar,hCross⟩ := hOrbits hj' hnon
  obtain ⟨I,hI⟩ := exists_regularShiftEmbedding_of_haarOrbits U x hHaar hCross
  exact hasLebesgueComplement_of_countable_shift_embeddings U (purePointPart_invariant U).orthogonal J I hJ hI

/-- Every ergodic compact homogeneous nilrotation in the generated presentation
is pure point or has countably infinite homogeneous Lebesgue complement. -/
theorem nilrotationQuotient_purePoint_or_countableLebesgue_of_dense_lift
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a^j*d*(γ:G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    purePointPart U = ⊤ ∨ HasLebesgueComplement U ℕ := by
  by_cases h : (⊤ : Subgroup G).lowerCentralSeries 1 ≤ L
  · left
    -- At the abelian stage the compact vertical representation is the time action's ambient group.
    exact (nilrotationQuotient_vertical_spectralFacts 0 L hL h a d hd hgen μ hμ
      (fun hpos ↦ (Nat.not_lt_zero _ hpos).elim)).2.1 rfl
  · exact Or.inr (nilrotationQuotient_countableLebesgue_of_dense_lift L hL n hn a d hd hgen μ hμ h)

end Mixing
