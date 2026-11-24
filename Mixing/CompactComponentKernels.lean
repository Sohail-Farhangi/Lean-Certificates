/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.JoiningEmbeddings

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {G X Y Z : Type*} [Group G] [Countable G]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty Y]
  {S : System G X} {T : System G Y} {R : System G Z}

/-- A selected family of joinings on compact name spaces pulls back to a
kernel of joinings on the original spaces. -/
theorem exists_lift_compact_componentKernel (F : FactorMap T R)
    (K : Kernel Z (CompactNames G × CompactNames G)) [IsMarkovKernel K]
    (hK : ∀ᵐ z ∂R.measure,
      ∃ hInv : ∀ g, MeasurePreserving (T.act g)
        (F.conditionalKernel z) (F.conditionalKernel z),
      IsJoining S.compactNameSystem
        (T.withInvariantMeasure (F.conditionalKernel z) hInv).compactNameSystem (K z)) :
    ∃ K' : Kernel Z (X × Y), IsMarkovKernel K' ∧
      ∀ᵐ z ∂R.measure,
        (K' z).map (Prod.map S.compactName T.compactName) = K z ∧
        (K' z).map Prod.fst = S.measure ∧ (K' z).map Prod.snd = F.conditionalKernel z ∧
        ∀ g, (K' z).map (S.prodAct T g) = K' z := by
  let e := Prod.map S.compactName T.compactName
  have he : MeasurableEmbedding e :=
    S.measurableEmbedding_compactName.prodMap T.measurableEmbedding_compactName
  have hSupport : ∀ᵐ z ∂R.measure, ∀ᵐ w ∂K z, w ∈ Set.range e := by
    filter_upwards [hK] with z hz
    obtain ⟨_, hj⟩ := hz
    exact ae_mem_range_prodMap_of_map_marginals
      S.measurableEmbedding_compactName T.measurableEmbedding_compactName
      hj.fst.map_eq hj.snd.map_eq
  obtain ⟨K', hMarkov, hLift⟩ := exists_markovKernel_lift_of_ae_mem_range he R.measure
    K (S.measure.prod T.measure) hSupport
  refine ⟨K', hMarkov, ?_⟩
  filter_upwards [hK, hLift] with z hz hL
  obtain ⟨hz, hlocal⟩ := hz
  let Tz := T.withInvariantMeasure (F.conditionalKernel z) hz
  have hJoin : IsJoining S Tz (K' z) := by
    apply S.compactNameFactor.isJoining_of_map_of_embeddings Tz.compactNameFactor
      S.measurableEmbedding_compactName T.measurableEmbedding_compactName
    change IsJoining S.compactNameSystem Tz.compactNameSystem ((K' z).map e)
    rw [hL]
    exact hlocal
  exact ⟨hL, hJoin.fst.map_eq, hJoin.snd.map_eq, fun g ↦ (hJoin.invariant g).map_eq⟩

end Mixing
