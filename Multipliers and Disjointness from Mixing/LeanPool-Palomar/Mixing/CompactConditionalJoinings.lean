/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ProbabilityMeasureBorel
public import Mixing.SigmaCompactWitness
public import Mixing.System
public import Mixing.WeakProbabilityOperations

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set TopologicalSpace
open scoped NNReal

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]

/-- Joint laws with a fixed first marginal and diagonal invariance.
The second marginal is the parameter of a joining fibre. -/
def probabilityJoiningLaws (S : System G X) (T : System G Y) :
    Set (ProbabilityMeasure (X × Y)) :=
  {μ | μ.map Prod.fst = (⟨S.measure, S.probability⟩ : ProbabilityMeasure X) ∧
    ∀ g, μ.map (S.prodAct T g) = μ}

variable [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] [BorelSpace X]
variable [TopologicalSpace Y] [CompactSpace Y] [MetrizableSpace Y] [BorelSpace Y]

omit [CompactSpace X] in
theorem isClosed_probabilityJoiningLaws (S : System G X) (T : System G Y)
    (hS : ∀ g, Continuous (S.act g)) (hT : ∀ g, Continuous (T.act g)) :
    IsClosed (probabilityJoiningLaws S T) := by
  have he : probabilityJoiningLaws S T =
      {μ : ProbabilityMeasure (X × Y) | μ.map Prod.fst = ⟨S.measure, S.probability⟩} ∩
        ⋂ g, {μ : ProbabilityMeasure (X × Y) | μ.map (S.prodAct T g) = μ} := by
    ext μ
    simp only [probabilityJoiningLaws, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [he]
  exact (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
    (isClosed_iInter fun g ↦ isClosed_eq
      (ProbabilityMeasure.continuous_map ((hS g).prodMap (hT g))) continuous_id)

/-- Select a non-product law whenever the specified second marginal admits
one, and otherwise select the independent product law. -/
theorem exists_measurable_nonproduct_joining_witness (S : System G X) (T : System G Y)
    (hS : ∀ g, Continuous (S.act g)) (hT : ∀ g, Continuous (T.act g)) :
    let P := probabilityProduct (⟨S.measure, S.probability⟩ : ProbabilityMeasure X)
    ∃ k : ProbabilityMeasure Y → ProbabilityMeasure (X × Y), Measurable k ∧
      (∀ ν, (∀ g, ν.map (T.act g) = ν) →
        k ν ∈ probabilityJoiningLaws S T ∧ (k ν).map Prod.snd = ν) ∧
      ∀ ν, (∃ ξ ∈ probabilityJoiningLaws S T, ξ.map Prod.snd = ν ∧ ξ ≠ P ν) →
        k ν ≠ P ν := by
  dsimp only
  let : BorelSpace (ProbabilityMeasure Y) := probabilityMeasure_borelSpace (X := Y)
  let : BorelSpace (ProbabilityMeasure (X × Y)) := probabilityMeasure_borelSpace (X := X × Y)
  let P : ProbabilityMeasure Y → ProbabilityMeasure (X × Y) :=
    probabilityProduct ⟨S.measure, S.probability⟩
  let Q (ξ : ProbabilityMeasure (X × Y)) := ξ.map Prod.snd
  have hQ : Continuous Q := ProbabilityMeasure.continuous_map continuous_snd
  have hP : Continuous P := continuous_probabilityProduct_left_fixed _
  let D := {ξ ∈ probabilityJoiningLaws S T | ξ ≠ P (Q ξ)}
  have hD : IsSigmaCompact D :=
    isSigmaCompact_closed_and_ne (isClosed_probabilityJoiningLaws S T hS hT)
      continuous_id (hP.comp hQ)
  obtain ⟨k, hkm, hkIn, hkOut⟩ :=
    exists_measurable_witness_of_isSigmaCompact Q hQ hD P hP.measurable
  refine ⟨k, hkm, ?_, ?_⟩
  · intro ν hInv
    by_cases h : ν ∈ Q '' D
    · exact ⟨(hkIn ν h).1.1, (hkIn ν h).2⟩
    rw [hkOut ν h]
    have hInv' (g : G) : (ν : Measure Y).map (T.act g) = (ν : Measure Y) :=
      congrArg ProbabilityMeasure.toMeasure (hInv g)
    refine ⟨⟨?_, fun g ↦ ?_⟩, ?_⟩
    · apply Subtype.ext
      change (S.measure.prod (ν : Measure Y)).map Prod.fst = S.measure
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    · apply Subtype.ext
      change (S.measure.prod (ν : Measure Y)).map (Prod.map (S.act g) (T.act g)) =
        S.measure.prod (ν : Measure Y)
      rw [← Measure.map_prod_map _ _ (S.preserves g).measurable (T.preserves g).measurable,
        (S.preserves g).map_eq, hInv' g]
    · apply Subtype.ext
      change (S.measure.prod (ν : Measure Y)).map Prod.snd = (ν : Measure Y)
      rw [Measure.map_snd_prod, measure_univ, one_smul]
  · intro ν ⟨ξ, hξ, he, hne⟩
    have hIn : ν ∈ Q '' D := ⟨ξ, ⟨hξ, fun hEq ↦ hne (he ▸ hEq)⟩, he⟩
    have hh := hkIn ν hIn
    have hne' : k ν ≠ P (Q (k ν)) := hh.1.2
    rwa [hh.2] at hne'

end Mixing
