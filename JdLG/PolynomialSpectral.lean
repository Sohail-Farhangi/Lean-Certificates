/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PolynomialFolner
public import JdLG.ReversibleUnitaryRestriction

/-! # Equation (20) on the orthogonal complement of the eigenvectors -/

@[expose] public section

open Filter Set
open scoped Topology InnerProductSpace

namespace JdLG

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The weak subspace of a unitary operator is the orthogonal complement of the
span of its eigenvectors. Taking the closed span has the same orthogonal complement. -/
noncomputable def unitaryWeakPart (U : H ≃ₗᵢ[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ {x : H | ∃ c : ℂ, U x = c • x})ᗮ

omit [CompleteSpace H] in
private theorem unitaryWeakPart_invariant (U : H ≃ₗᵢ[ℂ] H) :
    UnitaryInvariant (unitaryIntegerPowers U) (unitaryWeakPart U) := by
  let A : Set H := {x | ∃ c : ℂ, U x = c • x}
  let V := Submodule.span ℂ A
  let T := unitaryIntegerPowers U
  have hA (g : Multiplicative ℤ) : MapsTo (T g) A A := by
    rintro x ⟨c, hc⟩
    have hCom : Commute U (T g) := Commute.self_zpow U g.toAdd
    have hX := congrArg (fun W : H ≃ₗᵢ[ℂ] H ↦ W x) hCom.eq
    change U (T g x) = T g (U x) at hX
    exact ⟨c, hX.trans (by rw [hc, map_smul])⟩
  have hV (g : Multiplicative ℤ) (x : H) (hx : x ∈ V) : T g x ∈ V := by
    have hle : V.map (T g).toLinearMap ≤ V := by
      dsimp only [V]
      rw [Submodule.map_span]
      exact Submodule.span_mono (hA g).image_subset
    exact hle (Submodule.mem_map_of_mem hx)
  intro g x hx
  apply (V.mem_orthogonal _).mpr
  intro y hy
  have hz := hV g⁻¹ y hy
  have hCancel : T g (T g⁻¹ y) = y := by
    change (T g * T g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    inner ℂ y (T g x) = inner ℂ (T g (T g⁻¹ y)) (T g x) := by rw [hCancel]
    _ = inner ℂ (T g⁻¹ y) x := (T g).inner_map_map _ _
    _ = 0 := (V.mem_orthogonal _).mp hx _ hz

/-- The Hilbert-space comparison (20) in Example 5.4 for the weak subspace of
the unitary operator, using the actual orthogonal complement of its eigenvectors. -/
theorem tendsto_abs_coeff_perfect_powers_of_unitaryWeakPart (U : H ≃ₗᵢ[ℂ] H) (x y : H)
    (hx : x ∈ unitaryWeakPart U) (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (scalarCesaro fun n ↦ ‖inner ℂ ((U ^ (((n : ℤ) + 1) ^ k)) x) y‖)
      atTop (𝓝 0) := by
  let V := unitaryWeakPart U
  let : CompleteSpace V := (Submodule.isClosed_orthogonal _).completeSpace_coe
  let U' := unitarySubmoduleAction (unitaryIntegerPowers U) V (unitaryWeakPart_invariant U)
  have hNoEig (c : ℂ) (v : V) (hv : U' (Multiplicative.ofAdd 1) v = c • v) : v = 0 := by
    have hU : U (v : H) = c • (v : H) := by
      have h := congrArg Subtype.val hv
      simpa only [U', unitarySubmoduleAction_apply, unitaryIntegerPowers_ofAdd, zpow_one,
        Submodule.coe_smul] using h
    have hSpan : (v : H) ∈ Submodule.span ℂ {x : H | ∃ c : ℂ, U x = c • x} :=
      Submodule.subset_span ⟨c, hU⟩
    have hZero : inner ℂ (v : H) v = 0 :=
      Submodule.inner_right_of_mem_orthogonal hSpan v.property
    exact Subtype.ext (inner_self_eq_zero.mp hZero)
  let x' : V := ⟨x, hx⟩
  have hx' := PaperExamplesRigid.all_aws_of_no_unitary_eigenvectors U' hNoEig x'
  have hLinear := tendsto_abs_self_coeff_of_integer_action_aws U' x' hx'
  have hLinear' : Tendsto (scalarCesaro fun n : ℕ ↦ ‖inner ℂ x ((U ^ (n : ℤ)) x)‖)
      atTop (𝓝 0) := by
    simpa only [Submodule.coe_inner, U', unitarySubmoduleAction_apply,
      unitaryIntegerPowers_ofAdd, x'] using hLinear
  exact tendsto_abs_coeff_perfect_powers U x y hLinear' k hk

end JdLG
