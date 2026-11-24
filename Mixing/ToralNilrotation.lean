/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CircleSkew
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # A two-step toral nilrotation -/

@[expose] public section

open MeasureTheory Topology
open scoped Topology

namespace Mixing.ToralNilrotation

abbrev Torus := UnitAddCircle × UnitAddCircle

/-- Integer shear on the two-dimensional torus. -/
def shear (n : ℤ) (x : Torus) : Torus := (x.1, x.2 + n • x.1)

theorem shear_zero (x : Torus) : shear 0 x = x := by
  apply Prod.ext
  · rfl
  · simp [shear]

theorem shear_add_int (n k : ℤ) (x : Torus) :
    shear (n + k) x = shear n (shear k x) := by
  apply Prod.ext
  · rfl
  · change x.2 + (n + k) • x.1 = x.2 + k • x.1 + n • x.1
    rw [add_zsmul]
    abel

theorem shear_add_point (n : ℤ) (x y : Torus) :
    shear n (x + y) = shear n x + shear n y := by
  apply Prod.ext
  · rfl
  · change x.2 + y.2 + n • (x.1 + y.1) = x.2 + n • x.1 + (y.2 + n • y.1)
    rw [zsmul_add]
    abel

/-- The automorphism induced by one integer shear. -/
def shearAut (n : ℤ) : MulAut (Multiplicative Torus) where
  toFun x := Multiplicative.ofAdd (shear n x.toAdd)
  invFun x := Multiplicative.ofAdd (shear (-n) x.toAdd)
  left_inv x := by
    change shear (-n) (shear n x.toAdd) = x.toAdd
    rw [← shear_add_int, neg_add_cancel, shear_zero]
  right_inv x := by
    change shear n (shear (-n) x.toAdd) = x.toAdd
    rw [← shear_add_int, add_neg_cancel, shear_zero]
  map_mul' x y := shear_add_point n x.toAdd y.toAdd

/-- The shears as a homomorphism into torus automorphisms. -/
def shearAction : Multiplicative ℤ →* MulAut (Multiplicative Torus) where
  toFun n := shearAut n.toAdd
  map_one' := by
    apply MulEquiv.ext
    intro x
    change shear 0 x.toAdd = x.toAdd
    exact shear_zero x.toAdd
  map_mul' n k := by
    apply MulEquiv.ext
    intro x
    change shear (n.toAdd + k.toAdd) x.toAdd = shear n.toAdd (shear k.toAdd x.toAdd)
    exact shear_add_int n.toAdd k.toAdd x.toAdd

@[simp] theorem shearAction_apply (n : Multiplicative ℤ) (x : Multiplicative Torus) :
    (shearAction n x).toAdd = shear n.toAdd x.toAdd := rfl

/-- The nilpotent group acting by affine shears of the torus. -/
abbrev ShearGroup := Multiplicative Torus ⋊[shearAction] Multiplicative ℤ

/-- Quotienting by the second torus coordinate gives an abelian group. -/
def abelianProjection : ShearGroup →* Multiplicative (UnitAddCircle × ℤ) where
  toFun a := Multiplicative.ofAdd (a.left.toAdd.1, a.right.toAdd)
  map_one' := rfl
  map_mul' a b := by
    change ((a*b).left.toAdd.1, (a*b).right.toAdd) =
      (a.left.toAdd.1 + b.left.toAdd.1, a.right.toAdd + b.right.toAdd)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    change (a.left.toAdd.1 + (shearAction a.right b.left).toAdd.1, _) = _
    rw [shearAction_apply]
    rfl

theorem abelianProjection_ker_le_center : abelianProjection.ker ≤ Subgroup.center ShearGroup := by
  intro a ha
  have ha' := MonoidHom.mem_ker.mp ha
  change (a.left.toAdd.1, a.right.toAdd) = (0, 0) at ha'
  apply Subgroup.mem_center_iff.mpr
  intro b
  apply SemidirectProduct.ext
  · change (b*a).left.toAdd = (a*b).left.toAdd
    simp only [SemidirectProduct.mul_left]
    change b.left.toAdd + (shearAction b.right a.left).toAdd =
      a.left.toAdd + (shearAction a.right b.left).toAdd
    rw [shearAction_apply, shearAction_apply]
    apply Prod.ext
    · change b.left.toAdd.1 + a.left.toAdd.1 = a.left.toAdd.1 + b.left.toAdd.1
      rw [add_comm]
    · change b.left.toAdd.2 + (a.left.toAdd.2 + b.right.toAdd • a.left.toAdd.1) =
        a.left.toAdd.2 + (b.left.toAdd.2 + a.right.toAdd • b.left.toAdd.1)
      have h₁ : a.left.toAdd.1 = 0 := congrArg Prod.fst ha'
      have h₂ : a.right.toAdd = 0 := congrArg Prod.snd ha'
      simp only [h₁, h₂, smul_zero, zero_smul, add_zero]
      exact add_comm _ _
  · exact mul_comm _ _

instance : Group.IsNilpotent ShearGroup :=
  Subgroup.isNilpotent_of_ker_le_center abelianProjection abelianProjection_ker_le_center

theorem shearGroup_nilpotencyClass_le_two : Group.nilpotencyClass ShearGroup ≤ 2 := by
  exact (Group.nilpotencyClass_le_of_ker_le_center abelianProjection abelianProjection_ker_le_center).trans
    (Nat.add_le_add_right CommGroup.nilpotencyClass_le_one 1)

/-- The shears give genuine nilpotency class two when the circle is nontrivial. -/
theorem shearGroup_nilpotencyClass (x : UnitAddCircle) (hx : x ≠ 0) :
    Group.nilpotencyClass ShearGroup = 2 := by
  apply le_antisymm shearGroup_nilpotencyClass_le_two
  by_contra! h
  have hm := (Group.IsNilpotent.nilpotencyClass_le_one_iff (G := ShearGroup)).1 (by omega)
  let a : ShearGroup := ⟨Multiplicative.ofAdd (0, 0), Multiplicative.ofAdd 1⟩
  let b : ShearGroup := ⟨Multiplicative.ofAdd (x, 0), Multiplicative.ofAdd 0⟩
  have he := congrArg (fun g : ShearGroup => g.left.toAdd.2) (isMulCommutative_iff.mp hm a b)
  simp only [a, b, SemidirectProduct.mul_left] at he
  change 0 + (0 + (1 : ℤ) • x) = 0 + (0 + (0 : ℤ) • (0 : UnitAddCircle)) at he
  exact hx (by simpa only [zero_add, one_zsmul, zero_zsmul] using he)

/-- The lattice generated by the integer shear coordinate. -/
def lattice : Subgroup ShearGroup :=
  (SemidirectProduct.inr (φ := shearAction)).range

theorem mem_lattice (a : ShearGroup) : a ∈ lattice ↔ a.left = 1 := by
  constructor
  · rintro ⟨_, rfl⟩
    rfl
  · intro h
    exact ⟨a.right, SemidirectProduct.ext h.symm rfl⟩

/-- A left coset is determined exactly by its torus coordinate. -/
theorem leftRel_lattice_iff (a b : ShearGroup) :
    QuotientGroup.leftRel lattice a b ↔ a.left = b.left := by
  rw [QuotientGroup.leftRel_apply, mem_lattice, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
    SemidirectProduct.inv_right, ← map_mul]
  constructor
  · intro h
    have he : shearAction a.right⁻¹ (a.left⁻¹ * b.left) = shearAction a.right⁻¹ 1 := h.trans (map_one _).symm
    exact inv_mul_eq_one.mp ((shearAction a.right⁻¹).injective he)
  · intro h
    simp [h]

/-- The homogeneous quotient is identified with the two-dimensional torus. -/
def quotientEquiv : ShearGroup ⧸ lattice ≃ Torus where
  toFun := Quotient.lift (fun a : ShearGroup => a.left.toAdd)
    (fun _ _ h => (leftRel_lattice_iff _ _).mp h)
  invFun x := QuotientGroup.mk (SemidirectProduct.inl (φ := shearAction) (Multiplicative.ofAdd x))
  left_inv q := QuotientGroup.induction_on q fun _a => QuotientGroup.eq.mpr
    (QuotientGroup.leftRel_apply.mp ((leftRel_lattice_iff _ _).mpr rfl))
  right_inv _ := rfl

/-- The product coordinates transport the topology of the torus and the discrete integers. -/
def groupEquiv : ShearGroup ≃ Torus × ℤ where
  toFun a := (a.left.toAdd, a.right.toAdd)
  invFun t := ⟨Multiplicative.ofAdd t.1, Multiplicative.ofAdd t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : TopologicalSpace ShearGroup := TopologicalSpace.induced groupEquiv inferInstance

theorem continuous_groupEquiv : Continuous groupEquiv := continuous_induced_dom

theorem continuous_groupEquiv_symm : Continuous groupEquiv.symm := by
  rw [continuous_induced_rng]
  exact continuous_id

/-- The compact torus carries the quotient topology of the nilpotent group. -/
def quotientHomeomorph : ShearGroup ⧸ lattice ≃ₜ Torus where
  toEquiv := quotientEquiv
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk lattice).continuous_iff.mpr
    exact continuous_groupEquiv.fst
  continuous_invFun := by
    exact QuotientGroup.continuous_mk.comp
      (continuous_groupEquiv_symm.comp (continuous_id.prodMk continuous_const))

theorem lattice_isDiscrete : DiscreteTopology lattice := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro a
  have h : ({a} : Set lattice) = (fun b : lattice => (groupEquiv b.1).2) ⁻¹' {a.1.right.toAdd} := by
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      rfl
    · intro hb
      apply Subtype.ext
      apply SemidirectProduct.ext
      · rw [(mem_lattice b.1).1 b.2, (mem_lattice a.1).1 a.2]
      · exact hb
  rw [h]
  exact (isOpen_discrete _).preimage (continuous_groupEquiv.snd.comp continuous_subtype_val)

/-- Left translation on the homogeneous quotient, in torus coordinates. -/
def affineAct (a : ShearGroup) (x : Torus) : Torus :=
  a.left.toAdd + shear a.right.toAdd x

theorem affineAct_of_mul (a b : ShearGroup) (x : Torus) :
    affineAct (a*b) x = affineAct a (affineAct b x) := by
  simp only [affineAct, SemidirectProduct.mul_left, SemidirectProduct.mul_right]
  change a.left.toAdd + (shearAction a.right b.left).toAdd + shear (a.right.toAdd+b.right.toAdd) x =
    a.left.toAdd + shear a.right.toAdd (b.left.toAdd + shear b.right.toAdd x)
  rw [shearAction_apply]
  rw [shear_add_int, shear_add_point, add_assoc]

theorem quotientEquiv_left_translation (a b : ShearGroup) :
    quotientEquiv (QuotientGroup.mk (a*b)) = affineAct a (quotientEquiv (QuotientGroup.mk b)) := rfl

/-- The chosen translation is the classical skew shift in torus coordinates. -/
def translatingElement (α : UnitAddCircle) : ShearGroup :=
  ⟨Multiplicative.ofAdd (α, 0), Multiplicative.ofAdd 1⟩

theorem affineAct_translatingElement (α : UnitAddCircle) (x : Torus) :
    affineAct (translatingElement α) x = (x.1+α, x.2+x.1) := by
  apply Prod.ext
  · change α + x.1 = x.1 + α
    exact add_comm _ _
  · change 0 + (x.2 + (1 : ℤ) • x.1) = x.2 + x.1
    simp

local notation "m" => (AddCircle.haarAddCircle : Measure UnitAddCircle)

theorem affineAct_preserving (a : ShearGroup) : MeasurePreserving (affineAct a) ((m).prod m) ((m).prod m) := by
  have hShear : MeasurePreserving (shear a.right.toAdd) ((m).prod m) ((m).prod m) := by
    have h : shear a.right.toAdd = (circleSkew m 1).act a.right := by
      funext x
      change (x.1, x.2 + a.right.toAdd • x.1) = (x.1, x.2 + (a.right.toAdd * 1) • x.1)
      rw [mul_one]
    rw [h]
    exact (circleSkew m 1).preserves a.right
  exact ((measurePreserving_add_left m a.left.toAdd.1).prod (measurePreserving_add_left m a.left.toAdd.2)).comp hShear

/-- The probability-preserving nilrotation associated to the toral skew shift. -/
noncomputable def system (α : UnitAddCircle) : System (Multiplicative ℤ) Torus where
  measure := (m).prod m
  probability := inferInstance
  act g := affineAct (translatingElement α ^ g.toAdd)
  act_one := by
    funext x
    change affineAct (translatingElement α ^ (0 : ℤ)) x = x
    rw [zpow_zero]
    change 0 + shear 0 x = x
    rw [shear_zero, zero_add]
  act_mul g h := by
    funext x
    change affineAct (translatingElement α ^ (g.toAdd+h.toAdd)) x =
      affineAct (translatingElement α ^ g.toAdd) (affineAct (translatingElement α ^ h.toAdd) x)
    rw [zpow_add, affineAct_of_mul]
  preserves g := affineAct_preserving _

theorem system_act_one_step (α : UnitAddCircle) (x : Torus) :
    (system α).act (Multiplicative.ofAdd 1) x = (x.1 + α, x.2 + x.1) := by
  change affineAct (translatingElement α ^ (1 : ℤ)) x = _
  rw [zpow_one, affineAct_translatingElement]

end Mixing.ToralNilrotation
