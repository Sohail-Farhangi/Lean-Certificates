/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.WeakMixing
public import Mixing.FolnerExistence
public import Mixing.SupportingJdLG.DiscreteFolnerVariation
public import Mixing.SupportingJdLG.Ultrafilters

/-! # From ultrafilter vanishing to weak mixing

Apply the prior Jacobs–de Leeuw–Glicksberg certificate's Følner criterion to
the weak operator closure of this paper's unitary representation.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped InnerProductSpace Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Corollary 4 in its singleton form. The ultrafilter itself can be arbitrary. -/
theorem isWeaklyMixing_of_ultrafilterOperator_eq_zero (U : G →* (H ≃ₗᵢ[ℂ] H))
    (p : Ultrafilter G) (hp : ultrafilterOperator U p = 0) :
    IsWeaklyMixing U := by
  classical
  let π := linearRepresentation U
  have hCompact : IsCompact (JdLGBridge.weakOperatorClosure π : Set (H →WOT[ℂ] H)) :=
    weakOperatorClosure_isCompact U
  have hComm (a b : G) : π a * π b = π b * π a := by
    rw [← map_mul, ← map_mul, mul_comm' a b]
  have hAdm := JdLGBridge.admissible_of_commutative hCompact hComm
  let _ : CompactSpace (JdLGBridge.weakOperatorClosure π) := isCompact_iff_compactSpace.mp hCompact
  let _ : MeasurableSpace (JdLGBridge.weakOperatorClosure π) := borel _
  let _ : BorelSpace (JdLGBridge.weakOperatorClosure π) := ⟨rfl⟩
  let _ : MeasurableSpace G := ⊤
  let _ : DiscreteMeasurableSpace G := ⟨fun _ => trivial⟩
  intro x F hF
  let ν (n : ℕ) := JdLGBridge.normalizedRestrictedMeasure Measure.count (F n : Set G)
  have hProb (n : ℕ) : IsProbabilityMeasure (ν n) :=
    JdLGBridge.normalizedCountingBlock_probability (F n) (hF.1 n)
  have hFolner : JdLGBridge.LeftFolnerProbabilities ν atTop := by
    apply (JdLGBridge.leftFolnerProbabilities_counting_iff_strongFolner F hF.1 atTop).mpr
    intro a
    refine (hF.2 a).congr' (.of_forall fun n => ?_)
    unfold finsetDensity
    congr 1
    apply congrArg (fun s : Finset G => (s.card : ℝ))
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter, Set.mem_ofPred_eq,
      not_exists, not_and, ne_eq]
    tauto
  have hStable : JdLGBridge.IsAlmostWeaklyStable (JdLGBridge.closureAction π) x := by
    refine ⟨Ultrafilter.extend (weakClosureInclusion U) p, ?_⟩
    change ultrafilterOperator U p x = 0
    rw [hp, zero_apply]
  have hLim :=
    (JdLGBridge.stable_iff_folnerCoefficientMoments π Measurable.of_discrete ν hProb
      hFolner hAdm x 1 zero_lt_one).mp hStable (InnerProductSpace.toDual ℂ H x)
  have hCoeff (s : G) : InnerProductSpace.toDual ℂ H x (π s x) = ⟪x, U s x⟫_ℂ := rfl
  simpa only [Real.rpow_one, ν, JdLGBridge.integral_normalizedCountingBlock, hCoeff] using hLim

/-- Corollary 4. Every nonempty ultrafilter mixing family forces weak mixing. -/
theorem isWeaklyMixing_of_isUMixing (U : G →* (H ≃ₗᵢ[ℂ] H)) {P : Set (Ultrafilter G)}
    (hP : P.Nonempty) (hU : IsUMixing U P) : IsWeaklyMixing U := by
  obtain ⟨p, hp⟩ := hP
  exact isWeaklyMixing_of_ultrafilterOperator_eq_zero U p (hU p hp)

/-- Proposition 4(ii). Every individual essential ultrafilter tests weak mixing. -/
theorem isWeaklyMixing_iff_ultrafilterOperator_eq_zero_of_essential
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (p : Ultrafilter G) (hp : p ∈ essentialUltrafilters G) :
    IsWeaklyMixing U ↔ ultrafilterOperator U p = 0 :=
  ⟨fun h => isUMixing_essential_of_isWeaklyMixing U h p hp,
    isWeaklyMixing_of_ultrafilterOperator_eq_zero U p⟩

/-- Proposition 4(iii), for a group equipped with a Følner sequence. The
smallest ideal lies in the principal two-sided ideal of any essential ultrafilter. -/
theorem isWeaklyMixing_iff_ultrafilterOperator_eq_zero_of_smallestIdeal_of_folner
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (p : Ultrafilter G) (hp : p ∈ JdLGBridge.smallestIdeal (Ultrafilter G))
    (F : ℕ → Finset G) (hF : IsFolnerSequence F) :
    IsWeaklyMixing U ↔ ultrafilterOperator U p = 0 := by
  refine ⟨fun h => ?_, isWeaklyMixing_of_ultrafilterOperator_eq_zero U p⟩
  have hPos : HasPositiveFolnerDensity (Set.univ : Set G) := by
    refine ⟨F, hF, 1, zero_lt_one, Filter.Eventually.frequently (.of_forall fun n => ?_)⟩
    have hCard : (F n).card ≠ 0 := (hF.1 n).card_ne_zero
    simp [finsetDensity, hCard]
  obtain ⟨q, hq, _⟩ := exists_essentialUltrafilter_mem_of_hasPositiveFolnerDensity hPos
  let I : Set (Ultrafilter G) := {x | ∃ a b : Ultrafilter G, x = a * q * b}
  have hI : JdLGBridge.IsTwoSidedIdeal I := by
    constructor
    · rintro a _ ⟨b, c, rfl⟩
      exact ⟨a * b, c, by simp only [mul_assoc]⟩
    · rintro _ ⟨a, b, rfl⟩ c
      exact ⟨a, b * c, mul_assoc _ _ _⟩
  have hIn : I.Nonempty := ⟨q * q * q, q, q, rfl⟩
  obtain ⟨a, b, heq⟩ := JdLGBridge.smallestIdeal_subset hIn hI hp
  rw [heq, ultrafilterOperator_mul, ultrafilterOperator_mul,
    isUMixing_essential_of_isWeaklyMixing U h q hq, mul_zero, zero_mul]

/-- Proposition 4(iii). Every member of the smallest two-sided ideal of the
Stone–Čech semigroup tests weak mixing on a countable abelian group. -/
theorem isWeaklyMixing_iff_ultrafilterOperator_eq_zero_of_smallestIdeal
    {G : Type*} [CommGroup G] [Countable G] (U : G →* (H ≃ₗᵢ[ℂ] H))
    (p : Ultrafilter G) (hp : p ∈ JdLGBridge.smallestIdeal (Ultrafilter G)) :
    IsWeaklyMixing U ↔ ultrafilterOperator U p = 0 := by
  obtain ⟨F, hF⟩ := exists_isFolnerSequence (G := G)
  exact isWeaklyMixing_iff_ultrafilterOperator_eq_zero_of_smallestIdeal_of_folner U p hp F hF

end Mixing
