/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreFractions
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.WithOne.Basic

/-! # Existence of a group of right quotients -/

public section

open MulOpposite OreLocalization

namespace JdLG

universe u

variable {S : Type u} [Semigroup S]

private theorem withOne_opp_exists_common_left_multiple (hS : IsLeftReversible S)
    (a b : WithOne Sᵐᵒᵖ) : ∃ s t : WithOne Sᵐᵒᵖ, s * a = t * b := by
  cases a with
  | one => exact ⟨b, 1, by simp⟩
  | coe a =>
    cases b with
    | one => exact ⟨1, a, by simp⟩
    | coe b =>
      obtain ⟨s, t, h⟩ := hS (unop a) (unop b)
      exact ⟨↑(op s), ↑(op t), congrArg (fun x : S ↦ (↑(op x) : WithOne Sᵐᵒᵖ)) h⟩

private theorem withOne_opp_right_cancel_on_coe [IsCancelMul S]
    {a b : Sᵐᵒᵖ} {z : WithOne Sᵐᵒᵖ} (h : (a : WithOne Sᵐᵒᵖ) * z = b * z) : a = b := by
  cases z with
  | one => simpa using h
  | coe z => exact mul_right_cancel (WithOne.coe_inj.mp h)

private theorem withOne_opp_left_cancel_on_coe [IsCancelMul S]
    {a b : Sᵐᵒᵖ} {z : WithOne Sᵐᵒᵖ} (h : z * a = z * b) : a = b := by
  cases z with
  | one => simpa using h
  | coe z => exact mul_left_cancel (WithOne.coe_inj.mp h)

private theorem withOne_opp_weak_cancel [IsCancelMul S] (x y z : WithOne Sᵐᵒᵖ)
    (h : x * z = y * z) : ∃ t : WithOne Sᵐᵒᵖ, t * x = t * y := by
  cases z with
  | one => exact ⟨1, by simpa using h⟩
  | coe z =>
    cases x with
    | one =>
      cases y with
      | one => exact ⟨1, rfl⟩
      | coe y =>
        have hy : y * z = z :=
          WithOne.coe_inj.mp (by simpa only [one_mul, WithOne.coe_mul] using h.symm)
        have hz : z * y = z := mul_right_cancel (b := z) (by rw [mul_assoc, hy])
        exact ⟨↑z, by simpa only [mul_one, WithOne.coe_mul] using congrArg WithOne.coe hz.symm⟩
    | coe x =>
      cases y with
      | one =>
        have hx : x * z = z :=
          WithOne.coe_inj.mp (by simpa only [one_mul, WithOne.coe_mul] using h)
        have hz : z * x = z := mul_right_cancel (b := z) (by rw [mul_assoc, hx])
        exact ⟨↑z, by simpa only [mul_one, WithOne.coe_mul] using congrArg WithOne.coe hz⟩
      | coe y =>
        rw [withOne_opp_right_cancel_on_coe h]
        exact ⟨1, rfl⟩

@[instance_reducible]
private noncomputable def withOne_opp_oreSet [IsCancelMul S] (hS : IsLeftReversible S) :
    OreSet (⊤ : Submonoid (WithOne Sᵐᵒᵖ)) where
  ore_right_cancel x y z h := by
    obtain ⟨t, ht⟩ := withOne_opp_weak_cancel x y z h
    exact ⟨⟨t, Submonoid.mem_top t⟩, ht⟩
  oreNum a b := (withOne_opp_exists_common_left_multiple hS a b).choose_spec.choose
  oreDenom a b := ⟨(withOne_opp_exists_common_left_multiple hS a b).choose, Submonoid.mem_top _⟩
  ore_eq a b := (withOne_opp_exists_common_left_multiple hS a b).choose_spec.choose_spec

/-- A nonempty cancellative left reversible semigroup embeds in a group of right
quotients. We use the opposite of the unit group of the left Ore localization. -/
theorem exists_groupOfRightQuotients [IsCancelMul S] [Nonempty S] (hS : IsLeftReversible S) :
    ∃ (G : Type u) (_ : Group G) (ι : S →ₙ* G), IsGroupOfRightQuotients ι := by
  let R := WithOne Sᵐᵒᵖ
  let T : Submonoid R := ⊤
  let : OreSet T := withOne_opp_oreSet hS
  let Q := OreLocalization T R
  let j (a : R) : Qˣ := numeratorUnit (⟨a, Submonoid.mem_top a⟩ : T)
  have hj (a b : R) : j (a * b) = j a * j b :=
    Units.ext (map_mul (numeratorHom (S := T)) a b)
  let ι : S →ₙ* (Qˣ)ᵐᵒᵖ :=
    ⟨fun s ↦ op (j (↑(op s) : R)), fun s t ↦ congrArg op (hj (↑(op t)) (↑(op s)))⟩
  refine ⟨(Qˣ)ᵐᵒᵖ, inferInstance, ι, ?_, ?_⟩
  · intro a b h
    have h₁ : (op a : R) /ₒ (1 : T) = (op b : R) /ₒ (1 : T) :=
      congrArg (fun x : (Qˣ)ᵐᵒᵖ ↦ (unop x : Qˣ).val) h
    obtain ⟨u, v, huv, hden⟩ := oreDiv_eq_iff.mp h₁
    have hEq : (u : R) = v := by simpa only [Submonoid.coe_one, mul_one] using hden
    change (u : R) * (op b : R) = v * (op a : R) at huv
    rw [← hEq] at huv
    exact MulOpposite.op_injective (withOne_opp_left_cancel_on_coe huv).symm
  · intro w
    obtain ⟨c⟩ := ‹Nonempty S›
    let d : T := ⟨↑(op c), Submonoid.mem_top _⟩
    have hrepr (x : Q) : ∃ (r : R) (s : T), x = r /ₒ s :=
      OreLocalization.ind (fun r s ↦ ⟨r, s, rfl⟩) x
    obtain ⟨r, s, hrs⟩ := hrepr (unop w : Qˣ).val
    have hne (x : R) : (d : R) * x ≠ 1 := by
      cases x using WithOne.recOneCoe with
      | one => rw [mul_one]; exact WithOne.coe_ne_one
      | coe x => exact WithOne.coe_ne_one
    obtain ⟨a, ha⟩ := WithOne.ne_one_iff_exists.mp (hne r)
    obtain ⟨b, hb⟩ := WithOne.ne_one_iff_exists.mp (hne s)
    refine ⟨unop a, unop b, ?_⟩
    apply MulOpposite.unop_injective
    apply Units.ext
    change (unop w : Qˣ).val =
      (1 /ₒ (⟨(b : R), Submonoid.mem_top _⟩ : T)) * ((a : R) /ₒ (1 : T))
    rw [OreLocalization.one_div_mul, one_mul, hrs, OreLocalization.expand' r s d]
    change (d : R) * r /ₒ (d * s) = (a : R) /ₒ (⟨(b : R), Submonoid.mem_top _⟩ : T)
    congr 1
    · exact ha.symm
    · exact Subtype.ext hb.symm

end JdLG
