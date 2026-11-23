/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParity
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.GroupTheory.Solvable

/-!
# An ambient affine group for the parity semigroup

The first coordinate is allowed to be rational and the height any integer.
The resulting group is an extension of two abelian groups.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

/-- An affine point with rational position and integer height. -/
structure AffinePoint where
  first : ℚ
  height : ℤ

@[ext] theorem AffinePoint.ext {a b : AffinePoint} (hfirst : a.first = b.first)
    (hheight : a.height = b.height) : a = b := by
  cases a
  cases b
  simp_all

instance : One AffinePoint := ⟨⟨0, 0⟩⟩

instance : Mul AffinePoint :=
  ⟨fun a b ↦ ⟨2 ^ b.height * a.first + b.first, a.height + b.height⟩⟩

instance : Inv AffinePoint :=
  ⟨fun a ↦ ⟨-(2 ^ (-a.height) * a.first), -a.height⟩⟩

instance : Group AffinePoint := Group.ofLeftAxioms
  (fun a b c ↦ by
    apply AffinePoint.ext
    · change 2 ^ c.height * (2 ^ b.height * a.first + b.first) + c.first =
        2 ^ (b.height + c.height) * a.first + (2 ^ c.height * b.first + c.first)
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      ring
    · exact add_assoc _ _ _)
  (fun a ↦ by
    apply AffinePoint.ext
    · change 2 ^ a.height * (0 : ℚ) + a.first = a.first
      simp
    · exact zero_add _)
  (fun a ↦ by
    apply AffinePoint.ext
    · change 2 ^ a.height * -(2 ^ (-a.height) * a.first) + a.first = (0 : ℚ)
      have hp : (2 : ℚ) ^ a.height * 2 ^ (-a.height) = 1 := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), add_neg_cancel, zpow_zero]
      rw [mul_neg, ← mul_assoc, hp, one_mul, neg_add_cancel]
    · exact neg_add_cancel _)

/-- Horizontal translations form the kernel of the height homomorphism. -/
def horizontal : Multiplicative ℚ →* AffinePoint where
  toFun q := ⟨q.toAdd, 0⟩
  map_one' := rfl
  map_mul' a b := AffinePoint.ext (by
    change a.toAdd + b.toAdd = (2 : ℚ) ^ (0 : ℤ) * a.toAdd + b.toAdd
    rw [zpow_zero, one_mul]) rfl

def heightHom : AffinePoint →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd a.height
  map_one' := rfl
  map_mul' _ _ := rfl

theorem affinePoint_isSolvable : Group.IsSolvable AffinePoint := by
  apply Group.isSolvable_of_ker_le_range horizontal heightHom
  intro a ha
  have hzero : a.height = 0 := ha
  exact ⟨Multiplicative.ofAdd a.first, AffinePoint.ext rfl hzero.symm⟩

/-- The literal parity semigroup embeds into the affine group. -/
def affineEmbedding : Point →ₙ* AffinePoint where
  toFun s := ⟨s.first, (s.heightIndex : ℤ) + 1⟩
  map_mul' s t := by
    apply AffinePoint.ext
    · change ((2 ^ (t.heightIndex + 1) * s.first + t.first : ℕ) : ℚ) =
        2 ^ ((t.heightIndex : ℤ) + 1) * (s.first : ℚ) + (t.first : ℚ)
      have h : (t.heightIndex : ℤ) + 1 = ((t.heightIndex + 1 : ℕ) : ℤ) := by omega
      rw [h, zpow_natCast]
      norm_cast
    · change ((s.heightIndex + t.heightIndex + 1 : ℕ) : ℤ) + 1 =
        (s.heightIndex : ℤ) + 1 + ((t.heightIndex : ℤ) + 1)
      omega

theorem affineEmbedding_injective : Function.Injective affineEmbedding := by
  intro s t h
  have hf := congrArg AffinePoint.first h
  have hh := congrArg AffinePoint.height h
  change (s.first : ℚ) = (t.first : ℚ) at hf
  change (s.heightIndex : ℤ) + 1 = (t.heightIndex : ℤ) + 1 at hh
  exact Point.ext (by exact_mod_cast hf) (by omega)

end JdLG.PaperExamplesParity
