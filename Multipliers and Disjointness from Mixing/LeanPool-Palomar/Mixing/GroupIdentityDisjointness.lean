/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ErgodicBarycenters
public import Mixing.IdentityDisjointness

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped ENNReal

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]

/-- Ergodicity of the group action implies disjointness from every identity system. -/
theorem System.disjoint_identity_of_isErgodic {S : System G X} (hS : S.IsErgodic)
    (ν : Measure Y) [IsProbabilityMeasure ν] : Disjoint S (System.identity G ν) := by
  intro joining hj
  let := hj.probability
  apply Measure.ext_prod
  intro A B hA hB
  let η := joining.restrict (Prod.snd ⁻¹' B)
  let τ := η.map Prod.fst
  have hτ : τ ≤ S.measure := by
    rw [← hj.fst.map_eq]
    exact Measure.map_mono Measure.restrict_le_self measurable_fst
  let : IsFiniteMeasure τ := ⟨(hτ univ).trans_lt (measure_lt_top _ _)⟩
  have hτpres (g : G) : MeasurePreserving (S.act g) τ τ := by
    have hpres : MeasurePreserving (S.prodAct (System.identity G ν) g) η η :=
      (hj.invariant g).restrict_preimage (measurable_snd hB)
    refine ⟨(S.preserves g).measurable, ?_⟩
    have hcomp : S.act g ∘ Prod.fst = Prod.fst ∘ S.prodAct (System.identity G ν) g := rfl
    change (η.map Prod.fst).map (S.act g) = η.map Prod.fst
    rw [Measure.map_map (S.preserves g).measurable measurable_fst, hcomp,
      ← Measure.map_map measurable_fst hpres.measurable, hpres.map_eq]
  have hτeq := S.eq_smul_of_invariant_absolutelyContinuous hS τ hτpres hτ.absolutelyContinuous
  have hrect : τ A = joining (A ×ˢ B) := by
    change (joining.restrict (Prod.snd ⁻¹' B)).map Prod.fst A = _
    rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
    rfl
  have huniv : τ univ = ν B := by
    change (joining.restrict (Prod.snd ⁻¹' B)).map Prod.fst univ = _
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    exact hj.snd.measure_preimage hB.nullMeasurableSet
  rw [← hrect, hτeq, smul_apply, smul_eq_mul, huniv, mul_comm, Measure.prod_prod]
  rfl

/-- A measurable event invariant almost everywhere under a countable group has
an everywhere invariant measurable representative. -/
theorem System.exists_invariant_event_ae_eq [Countable G] (S : System G X)
    (A : Set X) (hA : MeasurableSet A) (hInv : ∀ g, S.act g ⁻¹' A =ᵐ[S.measure] A) :
    ∃ B : Set X, MeasurableSet B ∧ B =ᵐ[S.measure] A ∧ ∀ g, S.act g ⁻¹' B = B := by
  let B := ⋂ g : G, S.act g ⁻¹' A
  refine ⟨B, MeasurableSet.iInter (fun g => (S.preserves g).measurable hA), ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hInv] with x hx
    simp only [B, mem_iInter]
    exact ⟨fun h => (hx 1).mp (h 1), fun h g => (hx g).mpr h⟩
  · intro h
    ext x
    simp only [mem_preimage, B, mem_iInter]
    have hcomp (g : G) : S.act g (S.act h x) = S.act (g * h) x :=
      congrFun (S.act_mul g h).symm x
    simp only [hcomp]
    refine ⟨fun he g => ?_, fun he g => he (g * h)⟩
    simpa only [inv_mul_cancel_right] using he (g * h⁻¹)

/-- Theorem 1.1(i), extended to actions of arbitrary countable groups. -/
theorem theorem1_1_i_countableGroup [Countable G] (S : System G X) :
    S.IsErgodic ↔
      ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν],
        Disjoint S (System.identity G ν) := by
  constructor
  · intro h Y _ ν _
    exact System.disjoint_identity_of_isErgodic h ν
  · intro hd A hA hInv
    by_contra h
    have hm₀ : 0 < S.measure A := by
      refine pos_iff_ne_zero.mpr fun hz ↦ h ?_
      exact eventuallyEmptyOrUniv_iff.mpr (Or.inr (by simpa [ae_iff] using hz))
    have hm₁ : S.measure A < 1 := by
      refine lt_of_le_of_ne prob_le_one fun he ↦ h ?_
      have hz : S.measure Aᶜ = 0 := by rw [prob_compl_eq_one_sub hA, he, tsub_self]
      exact eventuallyEmptyOrUniv_iff.mpr (Or.inl (by rwa [ae_iff]))
    obtain ⟨B, hB, hBA, hBact⟩ := S.exists_invariant_event_ae_eq A hA hInv
    classical
    let t : X → Bool := fun x ↦ if x ∈ B then true else false
    have ht : Measurable t := measurable_const.ite hB measurable_const
    let ν := S.measure.map t
    let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff ht.aemeasurable).2
      inferInstance
    let T := System.identity G ν
    let f : FactorMap S T :=
      ⟨t, ⟨ht, rfl⟩, fun g ↦ by
        funext x
        have he : S.act g x ∈ B ↔ x ∈ B :=
          congrArg (fun E : Set X ↦ x ∈ E) (hBact g) |>.to_iff
        change t (S.act g x) = t x
        simp [t, he]⟩
    have hpre : t ⁻¹' ({true} : Set Bool) = B := by ext x; simp [t]
    have hm : T.measure ({true} : Set Bool) = S.measure A := by
      change ν {true} = _
      rw [Measure.map_apply ht (measurableSet_singleton true), hpre]
      exact measure_congr hBA
    exact f.not_disjoint_of_event (measurableSet_singleton true) (by rwa [hm]) (by rwa [hm])
      (hd Bool ν)

end Mixing
