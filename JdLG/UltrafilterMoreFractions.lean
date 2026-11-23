/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Largeness
public import Mathlib.Algebra.Group.Hom.Basic

/-!
# Right fractions of a semigroup

Proposition 2.6 of Barthmann, Farhangi and Kuznetsova, arXiv:2509.24003v3.
The embedding is into a group of right quotients. Common right multiples
make the formula for the unique extension independent of the fraction.
-/

@[expose] public section

namespace JdLG

variable {S G H : Type*} [Semigroup S] [Group G] [Group H]

/-- An injective map into a group in which every element is a right fraction. -/
def IsGroupOfRightQuotients (ι : S →ₙ* G) : Prop :=
  Function.Injective ι ∧ ∀ g : G, ∃ a b : S, g = ι a * (ι b)⁻¹

theorem IsGroupOfRightQuotients.isLeftReversible {ι : S →ₙ* G}
    (h : IsGroupOfRightQuotients ι) : IsLeftReversible S := by
  intro a b
  obtain ⟨u, v, huv⟩ := h.2 ((ι a)⁻¹ * ι b)
  refine ⟨u, v, h.1 ?_⟩
  have hmul := congrArg (fun g ↦ ι a * g * ι v) huv
  simpa only [map_mul, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right,
    inv_mul_cancel, mul_one] using hmul.symm

private theorem rightFraction_extend_right {K : Type*} [Group K] (a b u : K) :
    (a * u) * (b * u)⁻¹ = a * b⁻¹ := by
  simp [mul_inv_rev, mul_assoc]

/-- Equality of right fractions in a right-quotient group can be checked after multiplying
both denominators on the right to a common denominator. -/
theorem IsGroupOfRightQuotients.map_rightFraction_eq {ι : S →ₙ* G}
    (h : IsGroupOfRightQuotients ι) (f : S →ₙ* H) {a b c d : S}
    (heq : ι a * (ι b)⁻¹ = ι c * (ι d)⁻¹) : f a * (f b)⁻¹ = f c * (f d)⁻¹ := by
  obtain ⟨u, v, hden⟩ := h.isLeftReversible b d
  have hrun (j : S →ₙ* G) (r s t : S) : j (r * t) * (j (s * t))⁻¹ = j r * (j s)⁻¹ := by
    simpa only [map_mul] using rightFraction_extend_right (j r) (j s) (j t)
  have hnum : a * u = c * v := h.1 <| by
    have h' := (hrun ι a b u).trans (heq.trans (hrun ι c d v).symm)
    rw [hden] at h'
    exact mul_right_cancel h'
  calc
    f a * (f b)⁻¹ = f (a * u) * (f (b * u))⁻¹ := by
      simpa only [map_mul] using (rightFraction_extend_right (f a) (f b) (f u)).symm
    _ = f (c * v) * (f (d * v))⁻¹ := by rw [hnum, hden]
    _ = f c * (f d)⁻¹ := by
      simpa only [map_mul] using rightFraction_extend_right (f c) (f d) (f v)

private theorem rightFraction_mul_of_common {K : Type*} [Group K]
    {a b c d u v : K} (h : b * u = c * v) :
    (a * b⁻¹) * (c * d⁻¹) = (a * u) * (d * v)⁻¹ := by
  have huv : b⁻¹ * c = u * v⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
    exact h.symm
  rw [mul_inv_rev, mul_assoc a, ← mul_assoc b⁻¹, huv]
  simp only [mul_assoc]

/-- Proposition 2.6. A multiplicative map to any group extends uniquely from a semigroup
to its group of right quotients. -/
theorem existsUnique_rightFractionLift {ι : S →ₙ* G} (h : IsGroupOfRightQuotients ι)
    (f : S →ₙ* H) : ∃! F : G →* H, ∀ s : S, F (ι s) = f s := by
  classical
  choose a b hab using h.2
  let lift : G → H := fun g ↦ f (a g) * (f (b g))⁻¹
  have hvalue (g : G) (u v : S) (hg : g = ι u * (ι v)⁻¹) :
      lift g = f u * (f v)⁻¹ := h.map_rightFraction_eq f ((hab g).symm.trans hg)
  have hmul (g k : G) : lift (g * k) = lift g * lift k := by
    obtain ⟨u, v, huv⟩ := h.isLeftReversible (b g) (a k)
    have hgk : g * k = ι (a g * u) * (ι (b k * v))⁻¹ := by
      calc
        g * k = (ι (a g) * (ι (b g))⁻¹) * (ι (a k) * (ι (b k))⁻¹) :=
          congrArg₂ (· * ·) (hab g) (hab k)
        _ = ι (a g * u) * (ι (b k * v))⁻¹ := by
          simpa only [map_mul] using rightFraction_mul_of_common
            (a := ι (a g)) (d := ι (b k))
            (by simpa only [map_mul] using congrArg ι huv)
    rw [hvalue (g * k) (a g * u) (b k * v) hgk]
    simpa only [map_mul, lift] using (rightFraction_mul_of_common
      (a := f (a g)) (d := f (b k)) (by simpa only [map_mul] using congrArg f huv)).symm
  have hone : lift 1 = 1 := by
    have h' : lift 1 * lift 1 = lift 1 * 1 := by simpa using (hmul 1 1).symm
    exact mul_left_cancel h'
  let F : G →* H := { toFun := lift, map_one' := hone, map_mul' := hmul }
  have hcomm (s : S) : F (ι s) = f s := by
    let t := a 1
    have hs : ι s = ι (s * t) * (ι t)⁻¹ := by simp [map_mul, mul_assoc]
    change lift (ι s) = f s
    rw [hvalue _ _ _ hs]
    simp [map_mul, mul_assoc]
  refine ⟨F, hcomm, ?_⟩
  intro F' hcomm'
  ext g
  rw [hab g, map_mul, map_inv, map_mul, map_inv, hcomm', hcomm', hcomm, hcomm]

end JdLG
