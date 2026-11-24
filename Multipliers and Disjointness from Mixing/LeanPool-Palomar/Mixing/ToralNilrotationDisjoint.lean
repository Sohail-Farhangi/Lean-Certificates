/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ToralNilrotationTopology
public import Mixing.CompactGroupSkew
public import Mixing.CompactRotations

/-! # Weak-mixing disjointness for the concrete toral nilrotation -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Topology

namespace Mixing.ToralNilrotation

abbrev MulCircle := Multiplicative UnitAddCircle

local instance : IsTopologicalGroup MulCircle where
  continuous_mul := by
    change Continuous (fun p : UnitAddCircle × UnitAddCircle => p.1 + p.2)
    exact continuous_add
  continuous_inv := by
    change Continuous (fun a : UnitAddCircle => -a)
    exact continuous_neg

local instance : T2Space MulCircle := by change T2Space UnitAddCircle; infer_instance
local instance : BorelSpace MulCircle := by change BorelSpace UnitAddCircle; infer_instance
local instance : MeasurableMul₂ MulCircle := by
  constructor
  change Measurable (fun p : UnitAddCircle × UnitAddCircle => p.1 + p.2)
  exact measurable_add
local instance : Nonempty MulCircle := ⟨1⟩

local notation "m" => (AddCircle.haarAddCircle : Measure UnitAddCircle)

/-- Normalized Haar measure in multiplicative circle notation. -/
noncomputable def mulHaar : Measure MulCircle := m

local instance : IsProbabilityMeasure mulHaar := by
  change IsProbabilityMeasure m
  infer_instance

local instance : IsMulLeftInvariant mulHaar := ⟨fun g => (measurePreserving_add_left m g.toAdd).map_eq⟩
local instance : IsMulRightInvariant mulHaar := ⟨fun g => (measurePreserving_add_right m g.toAdd).map_eq⟩

local instance : mulHaar.InnerRegularCompactLTTop := by
  change (m).InnerRegularCompactLTTop
  infer_instance

private def rotationParameter (α : UnitAddCircle) : Multiplicative ℤ →* MulCircle where
  toFun g := Multiplicative.ofAdd (g.toAdd • α)
  map_one' := zero_zsmul α
  map_mul' g h := add_zsmul α g.toAdd h.toAdd

private noncomputable def base (α : UnitAddCircle) : System (Multiplicative ℤ) MulCircle :=
  compactRotation (rotationParameter α) mulHaar

private def skewTerm (α : UnitAddCircle) (g : Multiplicative ℤ) (x : MulCircle) : MulCircle :=
  Multiplicative.ofAdd (((translatingElement α ^ g.toAdd).left.toAdd).2 + g.toAdd • x.toAdd)

private theorem shearPower_fst (α : UnitAddCircle) (g : Multiplicative ℤ) :
    (translatingElement α ^ g.toAdd).left.toAdd.1 = g.toAdd • α := by
  have he := congrArg (fun t : Multiplicative (UnitAddCircle × ℤ) => t.toAdd.1)
    (abelianProjection.map_zpow (translatingElement α) g.toAdd)
  exact he

private theorem shearPower_right (α : UnitAddCircle) (g : Multiplicative ℤ) :
    (translatingElement α ^ g.toAdd).right.toAdd = g.toAdd := by
  have he := congrArg Multiplicative.toAdd
    ((SemidirectProduct.rightHom (φ := shearAction)).map_zpow (translatingElement α) g.toAdd)
  change _ = g.toAdd • (1 : ℤ) at he
  simpa using he

private theorem system_act_as_skew (α : UnitAddCircle) (g : Multiplicative ℤ) (w : Torus) :
    (system α).act g w =
      (((base α).act g (Multiplicative.ofAdd w.1)).toAdd,
        (skewTerm α g (Multiplicative.ofAdd w.1)).toAdd + w.2) := by
  apply Prod.ext
  · change (translatingElement α ^ g.toAdd).left.toAdd.1 + w.1 = g.toAdd • α + w.1
    rw [shearPower_fst]
  · change (translatingElement α ^ g.toAdd).left.toAdd.2 +
      (w.2 + (translatingElement α ^ g.toAdd).right.toAdd • w.1) =
      (translatingElement α ^ g.toAdd).left.toAdd.2 + g.toAdd • w.1 + w.2
    rw [shearPower_right]
    abel

private noncomputable def skewCocycle (α : UnitAddCircle) :
    MeasurableSkewCocycle (K := MulCircle) (base α) where
  toFun := skewTerm α
  measurable g := measurable_ofAdd.comp (measurable_const.add ((continuous_zsmul g.toAdd).measurable.comp measurable_toAdd))
  one x := by
    have h := congrFun (system α).act_one (x.toAdd, 0)
    rw [system_act_as_skew] at h
    apply Multiplicative.ext
    change (skewTerm α 1 x).toAdd = 0
    simpa only [ofAdd_toAdd, add_zero, id_eq] using congrArg Prod.snd h
  mul g h x := by
    have he := congrFun ((system α).act_mul g h) (x.toAdd, 0)
    rw [system_act_as_skew, Function.comp_apply, system_act_as_skew α g, system_act_as_skew α h] at he
    apply Multiplicative.ext
    change (skewTerm α (g*h) x).toAdd =
      (skewTerm α g ((base α).act h x)).toAdd + (skewTerm α h x).toAdd
    simpa only [ofAdd_toAdd, add_zero] using congrArg Prod.snd he

/-- This toral nilrotation is Furstenberg disjoint from every weakly mixing
system on a standard Borel space. -/
theorem disjoint_of_weakMixing {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (R : System (Multiplicative ℤ) X) (hR : IsWeaklyMixing R.koopmanZeroRep) (α : UnitAddCircle) :
    Disjoint R (system α) := by
  let : Countable (Multiplicative ℤ) := by change Countable ℤ; infer_instance
  let : StandardBorelSpace MulCircle := by change StandardBorelSpace UnitAddCircle; infer_instance
  let E := compactGroupSkewSystem (base α) (skewCocycle α) mulHaar
  have hB : Disjoint R (base α) :=
    disjoint_compactRotation_of_weaklyMixing R hR (rotationParameter α) mulHaar
  have hE : Disjoint R E := disjoint_compactGroupSkew_of_weakMixing (base α) (skewCocycle α) mulHaar R hR hB
  intro η hη
  have hη' : IsJoining R E η := by
    refine ⟨hη.probability, hη.fst, hη.snd, fun g => ?_⟩
    have hAct : R.prodAct E g = R.prodAct (system α) g := by
      funext w
      exact Prod.ext rfl (system_act_as_skew α g w.2).symm
    rw [hAct]
    exact hη.invariant g
  exact hE η hη'

end Mixing.ToralNilrotation
