/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RotationSpectralType
public import Mixing.SpectralDisjointness
public import Mathlib.Algebra.Group.End

/-! # Spectral type on central-character components

This module derives the modulation identity in Parry's criterion from a
central commutator. It applies to unitary representations of any group. -/

@[expose] public section
noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace Topology

namespace Mixing

variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) {C : Subgroup Γ} (χ : C →* Circle)

/-- The joint eigenspace for a character of a subgroup. -/
def centralCharacterSubmodule : Submodule ℂ H where
  carrier := {x | ∀ u : C, ρ (u : Γ) x = ((χ u : Circle) : ℂ) • x}
  zero_mem' := fun _ => by rw [map_zero, smul_zero]
  add_mem' := fun {x y} hx hy u => by rw [map_add, hx u, hy u, smul_add]
  smul_mem' := fun a x hx u => by rw [map_smul, hx u, smul_comm]

theorem centralCharacterSubmodule_isClosed : IsClosed (centralCharacterSubmodule ρ χ : Set H) := by
  have he : (centralCharacterSubmodule ρ χ : Set H) =
      ⋂ u : C, {x : H | ρ (u : Γ) x = ((χ u : Circle) : ℂ) • x} := by
    ext x
    simp only [mem_iInter]
    rfl
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq (LinearIsometryEquiv.continuous _) (continuous_const.smul continuous_id))

theorem centralCharacterSubmodule_invariant (hC : C ≤ Subgroup.center Γ) :
    IsInvariantSubmodule ρ (centralCharacterSubmodule ρ χ) := by
  intro b x hx u
  have hComm := (Subgroup.mem_center_iff.mp (hC u.property)) b
  change ρ (u : Γ) (ρ b x) = ((χ u : Circle) : ℂ) • (ρ b x)
  calc
    _ = ρ ((u : Γ)*b) x := by rw [map_mul]; rfl
    _ = ρ (b*(u : Γ)) x := by rw [hComm]
    _ = _ := by
      rw [map_mul]
      change ρ b (ρ (u : Γ) x) = _
      have hXu : ρ (u : Γ) x = ((χ u : Circle) : ℂ) • x := hx u
      rw [hXu, map_smul]

instance [CompleteSpace H] : CompleteSpace (centralCharacterSubmodule ρ χ) :=
  (centralCharacterSubmodule_isClosed ρ χ).completeSpace_coe

/-- The integer powers of the chosen group element define the time representation. -/
def integerPowersHom (a : Γ) : Multiplicative ℤ →* Γ where
  toFun n := a ^ n.toAdd
  map_one' := zpow_zero a
  map_mul' n m := zpow_add a n.toAdd m.toAdd

/-- Time action restricted to the central-character eigenspace. -/
def centralCharacterTime (hC : C ≤ Subgroup.center Γ) (a : Γ) :
    Multiplicative ℤ →* ((centralCharacterSubmodule ρ χ) ≃ₗᵢ[ℂ] (centralCharacterSubmodule ρ χ)) :=
  (unitarySubmoduleAction ρ _ (centralCharacterSubmodule_invariant ρ χ hC)).comp (integerPowersHom a)

theorem mul_eq_mul_commuting_of_zpow {a b z : Γ} (hComm : Commute a z)
    (h : a*b = b*a*z) (n : ℤ) : a^n*b = b*a^n*z^n := by
  have hConj : MulAut.conj b⁻¹ a = a*z := by
    rw [MulAut.conj_apply, inv_inv, mul_assoc, h, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul]
  have he : MulAut.conj b⁻¹ (a^n) = a^n*z^n := by
    rw [map_zpow, hConj, hComm.mul_zpow]
  calc
    a^n*b = b * (MulAut.conj b⁻¹ (a^n)) := by
      rw [MulAut.conj_apply, inv_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = b*a^n*z^n := by rw [he, mul_assoc]

/-- On the central-character component, conjugating by `b` modulates time
by the value of the character on the central commutator. -/
theorem centralCharacterTime_modulates (hC : C ≤ Subgroup.center Γ) (a b : Γ) (u : C)
    (h : a*b = b*a*(u : Γ)) (s : UnitAddCircle) (hs : χ u = AddCircle.toCircle s) :
    ∃ B : (centralCharacterSubmodule ρ χ) ≃ₗᵢ[ℂ] (centralCharacterSubmodule ρ χ),
      ∀ (n : ℤ) (x : centralCharacterSubmodule ρ χ),
        centralCharacterTime ρ χ hC a (Multiplicative.ofAdd n) (B x) =
          fourier n s • B (centralCharacterTime ρ χ hC a (Multiplicative.ofAdd n) x) := by
  refine ⟨unitarySubmoduleAction ρ _ (centralCharacterSubmodule_invariant ρ χ hC) b, fun n x => ?_⟩
  apply Subtype.ext
  change ρ (a^n) (ρ b (x : H)) = fourier n s • ρ b (ρ (a^n) (x : H))
  have he := mul_eq_mul_commuting_of_zpow (Subgroup.mem_center_iff.mp (hC u.property) a) h n
  have hx : ρ ((u : Γ)^n) (x : H) = fourier n s • (x : H) := by
    have hh := x.property (u^n)
    change ρ ((u : Γ)^n) (x : H) = ((χ (u^n) : Circle) : ℂ) • (x : H) at hh
    rw [hh, map_zpow, hs, fourier_apply, AddCircle.toCircle_zsmul]
  calc
    _ = ρ (a^n*b) (x : H) := by rw [map_mul]; rfl
    _ = ρ (b*a^n*(u : Γ)^n) (x : H) := by rw [he]
    _ = _ := by
      rw [map_mul, map_mul]
      change ρ b (ρ (a^n) (ρ ((u : Γ)^n) (x : H))) = _
      rw [hx, map_smul, map_smul]

/-- The central-character form of Parry's criterion. Every phase must be
realizable as the character value of a central commutator with the translation. -/
theorem centralCharacterTime_lebesgue_type [CompleteSpace H]
    [SeparableSpace (centralCharacterSubmodule ρ χ)] [Nontrivial (centralCharacterSubmodule ρ χ)]
    (hC : C ≤ Subgroup.center Γ) (a : Γ)
    (hComm : ∀ s : UnitAddCircle, ∃ (b : Γ) (u : C), a*b = b*a*(u : Γ) ∧ χ u = AddCircle.toCircle s) :
    ∃ x : centralCharacterSubmodule ρ χ, IsMaximalSpectralVector (centralCharacterTime ρ χ hC a) x ∧
      integerVectorSpectralMeasure (centralCharacterTime ρ χ hC a) x ≪ AddCircle.haarAddCircle ∧
      AddCircle.haarAddCircle ≪ integerVectorSpectralMeasure (centralCharacterTime ρ χ hC a) x := by
  apply integer_maximalSpectralType_haar_of_modulations
  intro s
  obtain ⟨b, u, hab, hχ⟩ := hComm s
  exact centralCharacterTime_modulates ρ χ hC a b u hab s hχ

end Mixing
