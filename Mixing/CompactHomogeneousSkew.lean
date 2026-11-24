/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactGroupSkew
public import Mixing.FactorJoiningLift

/-! # Disjointness for homogeneous skew products -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure

namespace Mixing

variable {G X Y K F : Type*} [CommGroup G] [Group K]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K] [MeasurableMul₂ K]
variable [MeasurableSpace F]

/-- A system disjoint from an extension is disjoint from its factor. -/
theorem FactorMap.disjoint_target_of_disjoint_source {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] [MeasurableEq F]
    {A : System G E} {B : System G F} {S : System G X}
    (π : FactorMap A B) (h : Disjoint S A) : Disjoint S B := by
  apply Disjoint.symm
  intro ν hν
  obtain ⟨μ, hμ, hpush⟩ := π.exists_joining_lift hν
  have he := (Disjoint.symm h) μ hμ
  rw [← hpush, he]
  exact (π.preserves.prod (MeasurePreserving.id S.measure)).map_eq

variable (T : System G Y) (c : MeasurableSkewCocycle (K := K) T)
variable (mK : Measure K) [IsProbabilityMeasure mK] [IsMulLeftInvariant mK]
variable [MulAction K F] [MeasurableSMul₂ K F]
variable (q : K → F) (hq : Measurable q) (hEq : ∀ k l, q (k * l) = k • q l)

omit [MulAction K F] [MeasurableSMul₂ K F] in
theorem homogeneousProjection_preserving (hq : Measurable q) :
    MeasurePreserving (Prod.map id q) (compactGroupSkewSystem T c mK).measure
      (T.measure.prod (mK.map q)) :=
  (MeasurePreserving.id T.measure).prod ⟨hq, rfl⟩

/-- The skew product on a measured homogeneous quotient of the compact fibre group.
For the quotient by a closed subgroup, take `q` to be the coset map. -/
noncomputable def homogeneousSkewSystem : System G (Y × F) where
  measure := T.measure.prod (mK.map q)
  probability := by
    have : IsProbabilityMeasure (mK.map q) :=
      (Measure.isProbabilityMeasure_map_iff hq.aemeasurable).mpr inferInstance
    infer_instance
  act g w := (T.act g w.1, c.toFun g w.1 • w.2)
  act_one := by funext w; simp [T.act_one, c.one]
  act_mul g h := by funext w; simp [T.act_mul, c.mul, mul_smul]
  preserves g := by
    let E := compactGroupSkewSystem T c mK
    let π : Y × K → Y × F := Prod.map id q
    let act : Y × F → Y × F := fun w ↦ (T.act g w.1, c.toFun g w.1 • w.2)
    have hπ := homogeneousProjection_preserving T c mK q hq
    have hAct : Measurable act :=
      ((T.preserves g).measurable.comp measurable_fst).prodMk
        (((c.measurable g).comp measurable_fst).smul measurable_snd)
    have he : act ∘ π = π ∘ E.act g := by
      funext w
      exact Prod.ext rfl (hEq _ _).symm
    refine ⟨hAct, ?_⟩
    change (T.measure.prod (mK.map q)).map act = T.measure.prod (mK.map q)
    rw [← hπ.map_eq, Measure.map_map hAct hπ.measurable, he,
      ← Measure.map_map hπ.measurable (E.preserves g).measurable, (E.preserves g).map_eq]

/-- Projecting the compact group coordinate gives the homogeneous skew product as a factor. -/
noncomputable def homogeneousSkewFactor :
    FactorMap (compactGroupSkewSystem T c mK) (homogeneousSkewSystem T c mK q hq hEq) where
  toFun := Prod.map id q
  preserves := homogeneousProjection_preserving T c mK q hq
  equivariant g := by
    funext w
    exact Prod.ext rfl (hEq _ _)

/-- Theorem 2.1's disjointness conclusion for the homogeneous skew-product
representation of an isometric extension. -/
theorem disjoint_homogeneousSkew_of_weakMixing [Countable G] [IsMulRightInvariant mK]
    [StandardBorelSpace (Y × K)] [Nonempty (Y × K)] [MeasurableEq (Y × F)]
    [StandardBorelSpace (X × (Y × K))] [Nonempty (X × (Y × K))]
    (S : System G X) (hWeak : IsWeaklyMixing S.koopmanZeroRep) (hDisj : Disjoint S T) :
    Disjoint S (homogeneousSkewSystem T c mK q hq hEq) :=
  (homogeneousSkewFactor T c mK q hq hEq).disjoint_target_of_disjoint_source
    (disjoint_compactGroupSkew_of_weakMixing T c mK S hWeak hDisj)

end Mixing
