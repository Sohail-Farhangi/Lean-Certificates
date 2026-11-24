/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactConditionalJoinings
public import Mixing.CompactComponentKernels
public import Mixing.JoiningKernelIntegration

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {G X Y Z : Type*} [Group G] [Countable G]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y] [MeasurableEq Z]
  {S : System G X} {T : System G Y} {R : System G Z}

omit [MeasurableEq Z] in
/-- The conditional law over an invariant factor is an invariant probability
law for almost every factor coordinate. -/
theorem FactorMap.ae_conditionalKernel_preserving_of_identity (F : FactorMap T R)
    (hFix : ∀ g, R.act g = id) :
    ∀ᵐ z ∂R.measure, ∀ g, MeasurePreserving (T.act g)
      (F.conditionalKernel z) (F.conditionalKernel z) := by
  apply ae_all_iff.2
  intro g
  filter_upwards [F.ae_conditionalKernel_equivariant g] with z hz
  exact ⟨(T.preserves g).measurable, by simpa only [hFix g, id_eq] using hz⟩

/-- Lemma 1(iii), from global disjointness to disjointness on almost
every component. The selection takes place in the compact spaces of
probability measures on the Boolean orbit models. -/
theorem lemma1_iii_of_disjoint (F : FactorMap T R) (hFix : ∀ g, R.act g = id)
    (hd : Disjoint S T) :
    ∀ᵐ z ∂R.measure,
      ∀ hInv : ∀ g, MeasurePreserving (T.act g)
        (F.conditionalKernel z) (F.conditionalKernel z),
      Disjoint S (T.withInvariantMeasure (F.conditionalKernel z) hInv) := by
  let S' := S.compactNameSystem
  let T' := T.compactNameSystem
  let B := CompactNames G
  let η := F.conditionalKernel
  let ν := η.map T.compactName
  have : IsMarkovKernel ν := Kernel.IsMarkovKernel.map η T.measurable_compactName
  let a := probabilityOfMarkovKernel ν
  let e := Prod.map S.compactName T.compactName
  have he : MeasurableEmbedding e :=
    S.measurableEmbedding_compactName.prodMap T.measurableEmbedding_compactName
  have hν (z : Z) : (a z : Measure B) = (η z).map T.compactName :=
    Kernel.map_apply η T.measurable_compactName z
  obtain ⟨k, hkm, hkJoin, hkNonproduct⟩ := exists_measurable_nonproduct_joining_witness
    S' T' (fun g ↦ continuous_compactNameShift g) (fun g ↦ continuous_compactNameShift g)
  let K := markovKernelOfProbability (k ∘ a) (hkm.comp (measurable_probabilityOfMarkovKernel ν))
  have hK (z : Z) : K z = (k (a z) : Measure (B × B)) := rfl
  have hLocal (z : Z) (hz : ∀ g, MeasurePreserving (T.act g) (η z) (η z)) :
      IsJoining S' (T.withInvariantMeasure (η z) hz).compactNameSystem (K z) := by
    have hInv' (g : G) : (a z).map (T'.act g) = a z := by
      apply Subtype.ext
      change ((a z : Measure B).map (compactNameShift g)) = _
      have hm : Measurable (compactNameShift g) := (T'.preserves g).measurable
      simp only [hν]
      rw [Measure.map_map hm T.measurable_compactName,
        ← T.compactName_equivariant g,
        ← Measure.map_map T.measurable_compactName (T.preserves g).measurable, (hz g).map_eq]
      exact (hν z).symm
    obtain ⟨⟨hleft, hinv⟩, hright⟩ := hkJoin (a z) hInv'
    refine ⟨inferInstance, ⟨measurable_fst, congrArg ProbabilityMeasure.toMeasure hleft⟩,
      ⟨measurable_snd, (congrArg ProbabilityMeasure.toMeasure hright).trans (hν z)⟩,
      fun g ↦ ⟨(S'.preserves g).measurable.prodMap (T'.preserves g).measurable,
        congrArg ProbabilityMeasure.toMeasure (hinv g)⟩⟩
  have hInv := F.ae_conditionalKernel_preserving_of_identity hFix
  have hCompact : ∀ᵐ z ∂R.measure,
      ∃ hInv : ∀ g, MeasurePreserving (T.act g) (η z) (η z),
      IsJoining S' (T.withInvariantMeasure (η z) hInv).compactNameSystem (K z) := by
    filter_upwards [hInv] with z hz
    exact ⟨hz, hLocal z hz⟩
  obtain ⟨K', hMarkov, hLift⟩ := exists_lift_compact_componentKernel F K hCompact
  have hProduct := ae_componentKernel_eq_prod_of_disjoint F hd K' (hLift.mono fun _ h ↦ h.2)
  filter_upwards [hLift, hProduct] with z hL hP hz
  let Tz := T.withInvariantMeasure (η z) hz
  intro σ hσ
  apply he.map_injective
  have hMap := hσ.map S.compactNameFactor Tz.compactNameFactor
  let ξ : ProbabilityMeasure (B × B) := ⟨σ.map e, hMap.probability⟩
  let product := probabilityProduct ⟨S'.measure, S'.probability⟩ (a z)
  have hp : (product : Measure (B × B)) = (S.measure.prod (η z)).map e := by
    change S'.measure.prod (a z : Measure B) = _
    rw [hν]
    exact Measure.map_prod_map _ _ S.measurable_compactName T.measurable_compactName
  have hkProd : k (a z) = product := by
    apply Subtype.ext
    change K z = (product : Measure (B × B))
    rw [← hL.1, hP, hp]
  have hξ : ξ ∈ probabilityJoiningLaws S' T' :=
    ⟨Subtype.ext hMap.fst.map_eq, fun g ↦ Subtype.ext (hMap.invariant g).map_eq⟩
  have hξSnd : ξ.map Prod.snd = a z := Subtype.ext (hMap.snd.map_eq.trans (hν z).symm)
  have hEq : ξ = product := by
    by_contra h
    exact hkNonproduct (a z) ⟨ξ, hξ, hξSnd, h⟩ hkProd
  exact (congrArg ProbabilityMeasure.toMeasure hEq).trans hp

/-- Lemma 1(iii), the disjointness equivalence over the invariant factor. -/
theorem lemma1_iii (hS : S.IsErgodic) (F : FactorMap T R) (hFix : ∀ g, R.act g = id) :
    Disjoint S T ↔ ∀ᵐ z ∂R.measure,
      ∀ hInv : ∀ g, MeasurePreserving (T.act g)
        (F.conditionalKernel z) (F.conditionalKernel z),
      Disjoint S (T.withInvariantMeasure (F.conditionalKernel z) hInv) := by
  refine ⟨lemma1_iii_of_disjoint F hFix, fun h ↦ ?_⟩
  have hfix (g : G) : F.toFun ∘ T.act g = F.toFun := by
    rw [F.equivariant g, hFix g, Function.id_comp]
  apply lemma1_iii_of_componentwise_disjoint hS F.preserves.measurable hfix
  rw [F.preserves.map_eq]
  exact h

end Mixing
