/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactJoiningMidpoints
public import Mixing.ComponentDisjointness
public import Mixing.ExtremeJoiningMidpoint

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {G X Y Z : Type*} [CommGroup G] [Countable G]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y] [MeasurableEq Z]
  {S : System G X} {T : System G Y} {R : System G Z}

/-- Lemma 1(ii). An extreme joining disintegrates into extreme joinings over
the invariant factor of the second system when the first system is ergodic.
A hypothetical conditional split is selected in compact probability spaces
and lifted back to the original spaces before integration. -/
theorem lemma1_ii (hS : S.IsErgodic) (F : FactorMap T R) (hFix : ∀ g, R.act g = id)
    {joining : Measure (X × Y)} [IsProbabilityMeasure joining]
    (hJoining : IsExtremeJoining S T joining) :
    let κ := (coordinateGraph joining (F.toFun ∘ Prod.snd)).condKernel
    ∀ᵐ z ∂R.measure,
      ∀ hInv : ∀ g, MeasurePreserving (T.act g)
        (F.conditionalKernel z) (F.conditionalKernel z),
      IsExtremeJoining S (T.withInvariantMeasure (F.conditionalKernel z) hInv) (κ z) := by
  dsimp only
  let η := F.conditionalKernel
  let κ := (coordinateGraph joining (F.toFun ∘ Prod.snd)).condKernel
  let S' := S.compactNameSystem
  let T' := T.compactNameSystem
  let B := CompactNames G
  let e := Prod.map S.compactName T.compactName
  have he : MeasurableEmbedding e :=
    S.measurableEmbedding_compactName.prodMap T.measurableEmbedding_compactName
  let K := κ.map e
  have : IsMarkovKernel K := Kernel.IsMarkovKernel.map κ he.measurable
  let a := probabilityOfMarkovKernel K
  have hA (z : Z) : (a z : Measure (B × B)) = (κ z).map e :=
    Kernel.map_apply κ he.measurable z
  have hfix (g : G) : F.toFun ∘ T.act g = F.toFun := by
    rw [F.equivariant g, hFix g, Function.id_comp]
  have hκ := lemma1_i hS hJoining.1 F.preserves.measurable hfix
  rw [F.preserves.map_eq] at hκ
  have hInv := F.ae_conditionalKernel_preserving_of_identity hFix
  obtain ⟨k, hkm, hkMid, hkJoin, hkNe⟩ := exists_measurable_joining_midpoint_witness
    S' T' (fun g ↦ continuous_compactNameShift g) (fun g ↦ continuous_compactNameShift g)
  let M₀ := markovKernelOfProbability (Prod.fst ∘ k ∘ a)
    (measurable_fst.comp (hkm.comp (measurable_probabilityOfMarkovKernel K)))
  let M₁ := markovKernelOfProbability (Prod.snd ∘ k ∘ a)
    (measurable_snd.comp (hkm.comp (measurable_probabilityOfMarkovKernel K)))
  have hM₀ (z : Z) : M₀ z = ((k (a z)).1 : Measure (B × B)) := rfl
  have hM₁ (z : Z) : M₁ z = ((k (a z)).2 : Measure (B × B)) := rfl
  have hLocal : ∀ᵐ z ∂R.measure,
      ∃ hI : ∀ g, MeasurePreserving (T.act g) (η z) (η z),
      IsJoining S (T.withInvariantMeasure (η z) hI) (κ z) := by
    filter_upwards [hκ, hInv] with z hC hz
    exact ⟨hz, inferInstance, hC.1, hC.2.1, hC.2.2⟩
  have hBoth : ∀ᵐ z ∂R.measure,
      ∃ hI : ∀ g, MeasurePreserving (T.act g) (η z) (η z),
      IsJoining S' (T.withInvariantMeasure (η z) hI).compactNameSystem (M₀ z) ∧
      IsJoining S' (T.withInvariantMeasure (η z) hI).compactNameSystem (M₁ z) := by
    filter_upwards [hLocal] with z hz
    obtain ⟨hI, hj⟩ := hz
    let Tz := T.withInvariantMeasure (η z) hI
    have hMapped : IsJoining S' Tz.compactNameSystem (a z : Measure (B × B)) :=
      (hA z).symm ▸ hj.map S.compactNameFactor Tz.compactNameFactor
    have hLaws : a z ∈ probabilityJoiningLaws S' T' :=
      ⟨Subtype.ext hMapped.fst.map_eq, fun g ↦ Subtype.ext (hMapped.invariant g).map_eq⟩
    obtain ⟨h₀, h₁, hSnd₀, hSnd₁⟩ := hkJoin (a z) hLaws
    have hJoiningLaw (ξ : ProbabilityMeasure (B × B)) (hLaw : ξ ∈ probabilityJoiningLaws S' T')
        (hsnd : ξ.map Prod.snd = (a z).map Prod.snd) :
        IsJoining S' Tz.compactNameSystem (ξ : Measure (B × B)) := by
      obtain ⟨hfst, hact⟩ := hLaw
      exact ⟨inferInstance, ⟨measurable_fst, congrArg ProbabilityMeasure.toMeasure hfst⟩,
        ⟨measurable_snd, (congrArg ProbabilityMeasure.toMeasure hsnd).trans hMapped.snd.map_eq⟩,
        fun g ↦ ⟨(S'.preserves g).measurable.prodMap (T'.preserves g).measurable,
          congrArg ProbabilityMeasure.toMeasure (hact g)⟩⟩
    exact ⟨hI, hJoiningLaw _ h₀ hSnd₀, hJoiningLaw _ h₁ hSnd₁⟩
  obtain ⟨L₀, hMarkov₀, hLift₀⟩ := exists_lift_compact_componentKernel F M₀
    (hBoth.mono fun _ h ↦ ⟨h.choose, h.choose_spec.1⟩)
  obtain ⟨L₁, hMarkov₁, hLift₁⟩ := exists_lift_compact_componentKernel F M₁
    (hBoth.mono fun _ h ↦ ⟨h.choose, h.choose_spec.2⟩)
  let half : ℝ≥0∞ := 1 / 2
  have hHalfLe : half ≤ 1 := by norm_num [half]
  have hHalf : 1 - half = half := by
    apply (ENNReal.add_left_inj (ne_top_of_le_ne_top ENNReal.one_ne_top hHalfLe)).1
    rw [tsub_add_cancel_of_le hHalfLe, ← two_mul, show half = (2 : ℝ≥0∞)⁻¹ from one_div _,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have mapMid (μ₀ μ₁ : Measure (X × Y)) :
      (half • μ₀ + half • μ₁).map e = half • μ₀.map e + half • μ₁.map e := by
    rw [Measure.map_add _ _ he.measurable, Measure.map_smul _ he.measurable.aemeasurable,
      Measure.map_smul _ he.measurable.aemeasurable]
  have hMid : ∀ᵐ z ∂R.measure, half • L₀ z + (1 - half) • L₁ z = κ z := by
    filter_upwards [hLift₀, hLift₁] with z h₀ h₁
    apply he.map_injective
    rw [hHalf, mapMid, h₀.1, h₁.1, hM₀, hM₁, ← probabilityMidpoint_toMeasure (k (a z)),
      hkMid, hA]
  have hEq := ae_component_decomposition_trivial_of_extreme F hJoining L₀ L₁
    (hLift₀.mono fun _ h ↦ h.2) (hLift₁.mono fun _ h ↦ h.2)
    (show 0 < half by norm_num [half]) (show half < 1 by norm_num [half]) hMid
  filter_upwards [hκ, hLift₀, hLift₁, hEq] with z hC h₀ h₁ hE hI
  let Tz := T.withInvariantMeasure (η z) hI
  apply (isExtremeJoining_iff_midpoint).2
  refine ⟨⟨inferInstance, hC.1, hC.2.1, hC.2.2⟩, ?_⟩
  intro μ₀ μ₁ hJ₀ hJ₁ hSum
  have hJ₀' := hJ₀.map S.compactNameFactor Tz.compactNameFactor
  have hJ₁' := hJ₁.map S.compactNameFactor Tz.compactNameFactor
  let ξ₀ : ProbabilityMeasure (B × B) := ⟨μ₀.map e, hJ₀'.probability⟩
  let ξ₁ : ProbabilityMeasure (B × B) := ⟨μ₁.map e, hJ₁'.probability⟩
  have hξ₀ : ξ₀ ∈ probabilityJoiningLaws S' T' :=
    ⟨Subtype.ext hJ₀'.fst.map_eq, fun g ↦ Subtype.ext (hJ₀'.invariant g).map_eq⟩
  have hξ₁ : ξ₁ ∈ probabilityJoiningLaws S' T' :=
    ⟨Subtype.ext hJ₁'.fst.map_eq, fun g ↦ Subtype.ext (hJ₁'.invariant g).map_eq⟩
  have hSnd : ξ₀.map Prod.snd = ξ₁.map Prod.snd :=
    Subtype.ext (hJ₀'.snd.map_eq.trans hJ₁'.snd.map_eq.symm)
  have hMid' : probabilityMidpoint (ξ₀, ξ₁) = a z := by
    apply Subtype.ext
    change (probabilityMidpoint (ξ₀, ξ₁)).toMeasure = (a z).toMeasure
    calc
      _ = half • μ₀.map e + half • μ₁.map e := probabilityMidpoint_toMeasure (ξ₀, ξ₁)
      _ = (κ z).map e := by rw [← mapMid, hSum]
      _ = _ := (hA z).symm
  have hkEq : (k (a z)).1 = (k (a z)).2 := by
    apply Subtype.ext
    exact (hM₀ z).symm.trans
      (h₀.1.symm.trans ((congrArg (Measure.map e) hE).trans (h₁.1.trans (hM₁ z))))
  by_contra hne
  exact hkNe (a z) ⟨ξ₀, hξ₀, ξ₁, hξ₁, hSnd,
    fun h ↦ hne (he.map_injective (congrArg ProbabilityMeasure.toMeasure h)), hMid'⟩ hkEq

end Mixing
