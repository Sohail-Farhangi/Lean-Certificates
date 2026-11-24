/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactNames

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {G X X' Y Y' Z : Type*} [Group G]
  [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace Z]

/-- If equivariant embeddings take a measure to a joining of the image
systems, the original measure is a joining. -/
theorem FactorMap.isJoining_of_map_of_embeddings
    {S : System G X} {S' : System G X'} {T : System G Y} {T' : System G Y'}
    (F : FactorMap S S') (J : FactorMap T T')
    (hF : MeasurableEmbedding F.toFun) (hJ : MeasurableEmbedding J.toFun)
    {μ : Measure (X × Y)} (h : IsJoining S' T' (μ.map (Prod.map F.toFun J.toFun))) :
    IsJoining S T μ := by
  let e := Prod.map F.toFun J.toFun
  have he : MeasurableEmbedding e := hF.prodMap hJ
  have hp := h.probability
  have hμ : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff
    he.measurable.aemeasurable).1 hp
  have hleft : MeasurePreserving Prod.fst μ S.measure := by
    refine ⟨measurable_fst, hF.map_injective ?_⟩
    rw [F.preserves.map_eq, Measure.map_map hF.measurable measurable_fst]
    have hMap := h.fst.map_eq
    rw [Measure.map_map measurable_fst he.measurable] at hMap
    exact hMap
  have hright : MeasurePreserving Prod.snd μ T.measure := by
    refine ⟨measurable_snd, hJ.map_injective ?_⟩
    rw [J.preserves.map_eq, Measure.map_map hJ.measurable measurable_snd]
    have hMap := h.snd.map_eq
    rw [Measure.map_map measurable_snd he.measurable] at hMap
    exact hMap
  refine ⟨hμ, hleft, hright, fun g ↦ ⟨(S.preserves g).measurable.prodMap
    (T.preserves g).measurable, he.map_injective ?_⟩⟩
  have hg : Measurable (S.prodAct T g) := (S.preserves g).measurable.prodMap (T.preserves g).measurable
  have hg' : Measurable (S'.prodAct T' g) := (h.invariant g).measurable
  have hcomp : e ∘ S.prodAct T g = S'.prodAct T' g ∘ e := by
    funext w
    exact Prod.ext (congrFun (F.equivariant g) w.1) (congrFun (J.equivariant g) w.2)
  have hinv := (h.invariant g).map_eq
  rw [Measure.map_map hg' he.measurable] at hinv
  rw [Measure.map_map he.measurable hg, hcomp]
  exact hinv

/-- Marginals supported on embedded coordinate spaces force a measure to be
supported on the product of the embedded spaces. -/
theorem ae_mem_range_prodMap_of_map_marginals
    {f : X → X'} {g : Y → Y'} (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    {μ : Measure (X' × Y')} {σ : Measure X} {τ : Measure Y}
    (hfst : μ.map Prod.fst = σ.map f) (hsnd : μ.map Prod.snd = τ.map g) :
    ∀ᵐ w ∂μ, w ∈ Set.range (Prod.map f g) := by
  have hf' : ∀ᵐ x ∂σ.map f, x ∈ Set.range f :=
    (hf.ae_map_iff).mpr (ae_of_all _ fun _ ↦ mem_range_self _)
  have hg' : ∀ᵐ y ∂τ.map g, y ∈ Set.range g :=
    (hg.ae_map_iff).mpr (ae_of_all _ fun _ ↦ mem_range_self _)
  have h₁ := (ae_map_iff measurable_fst.aemeasurable hf.measurableSet_range).mp (hfst ▸ hf')
  have h₂ := (ae_map_iff measurable_snd.aemeasurable hg.measurableSet_range).mp (hsnd ▸ hg')
  filter_upwards [h₁, h₂] with w hw₁ hw₂
  exact range_prodMap.symm ▸ (show w ∈ Set.range f ×ˢ Set.range g from ⟨hw₁, hw₂⟩)

/-- Disjointness is invariant under equivariant measure-preserving embeddings. -/
theorem FactorMap.disjoint_iff_of_embeddings
    {S : System G X} {S' : System G X'} {T : System G Y} {T' : System G Y'}
    (F : FactorMap S S') (J : FactorMap T T')
    (hF : MeasurableEmbedding F.toFun) (hJ : MeasurableEmbedding J.toFun) :
    Disjoint S T ↔ Disjoint S' T' := by
  let e := Prod.map F.toFun J.toFun
  have he := hF.prodMap hJ
  have hprod : (S.measure.prod T.measure).map e = S'.measure.prod T'.measure := by
    rw [← F.preserves.map_eq, ← J.preserves.map_eq]
    exact (Measure.map_prod_map S.measure T.measure hF.measurable hJ.measurable).symm
  constructor
  · intro hd μ hμ
    have hs : ∀ᵐ w ∂μ, w ∈ Set.range e :=
      ae_mem_range_prodMap_of_map_marginals hF hJ
        (hμ.fst.map_eq.trans F.preserves.map_eq.symm) (hμ.snd.map_eq.trans J.preserves.map_eq.symm)
    have hmap : (μ.comap e).map e = μ :=
      (he.map_comap μ).trans (Measure.restrict_eq_self_of_ae_mem hs)
    have hJoin : IsJoining S T (μ.comap e) :=
      F.isJoining_of_map_of_embeddings J hF hJ (hmap.symm ▸ hμ)
    rw [← hmap, hd _ hJoin, hprod]
  · intro hd μ hμ
    apply he.map_injective
    exact (hd _ (hμ.map F J)).trans hprod.symm

/-- A kernel supported almost everywhere on an embedded set has a Markov
kernel lift, with an arbitrary probability value chosen on the exceptional set. -/
theorem exists_markovKernel_lift_of_ae_mem_range {f : X → X'} (hf : MeasurableEmbedding f)
    (ν : Measure Z) (κ : Kernel Z X') [IsMarkovKernel κ]
    (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (hκ : ∀ᵐ z ∂ν, ∀ᵐ x ∂κ z, x ∈ Set.range f) :
    ∃ η : Kernel Z X, IsMarkovKernel η ∧ ∀ᵐ z ∂ν, (η z).map f = κ z := by
  classical
  let U := {z | κ z (Set.range f) = 1}
  have hU : MeasurableSet U := (κ.measurable_coe hf.measurableSet_range)
    (measurableSet_singleton 1)
  let η := Kernel.piecewise hU (κ.comapRight hf) (Kernel.const Z μ₀)
  have hMarkov : IsMarkovKernel η := by
    refine ⟨fun z ↦ ⟨?_⟩⟩
    rw [Kernel.piecewise_apply']
    by_cases hz : z ∈ U
    · rw [ite_eq_left hz, Kernel.comapRight_apply' κ hf z .univ, image_univ]
      exact hz
    · simp [hz]
  refine ⟨η, hMarkov, ?_⟩
  filter_upwards [hκ] with z hz
  have hzU : z ∈ U := by
    change κ z (Set.range f) = 1
    have hh := congrArg (fun m : Measure X' ↦ m Set.univ)
      (Measure.restrict_eq_self_of_ae_mem hz)
    rwa [Measure.restrict_apply_univ, measure_univ] at hh
  rw [Kernel.piecewise_apply, ite_eq_left hzU, Kernel.comapRight_apply,
    hf.map_comap, Measure.restrict_eq_self_of_ae_mem hz]

end Mixing
