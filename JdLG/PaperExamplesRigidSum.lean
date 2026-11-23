/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRigid
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The sum construction of Example 4.7

The assertions are conditional on the family of nonzero rigid unitary
components. Each obstruction in a component passes to the literal
Hilbert direct sum using the coordinate inclusion and projection.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter
open scoped Topology ENNReal

/-- The index set used by the paper for its family of rigid representations. -/
structure LacunarySequence where
  value : ℕ → ℕ
  strictlyIncreasing : StrictMono value
  positive : ∀ n, 0 < value n
  ratiosDiverge : Tendsto (fun n ↦ (value (n + 1) : ℝ) / (value n : ℝ)) atTop atTop

variable {H : LacunarySequence → Type*}
  [∀ r, NormedAddCommGroup (H r)] [∀ r, InnerProductSpace ℂ (H r)]

/-- Coordinatewise action on the Hilbert direct sum. -/
noncomputable def hilbertSumVector
    (U : (r : LacunarySequence) → ℤ → H r ≃ₗᵢ[ℂ] H r)
    (a : ℤ) (x : lp H 2) : lp H 2 :=
  ⟨fun r ↦ U r a (x r), memℓp_gen (by
    have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    simpa only [LinearIsometryEquiv.norm_map] using (lp.memℓp x).summable hp)⟩

@[simp] theorem hilbertSumVector_apply
    (U : (r : LacunarySequence) → ℤ → H r ≃ₗᵢ[ℂ] H r)
    (a : ℤ) (x : lp H 2) (r : LacunarySequence) :
    hilbertSumVector U a x r = U r a (x r) := rfl

/-- The coordinatewise unitary representation on the literal Hilbert sum. -/
noncomputable def hilbertSumRepresentation
    (U : (r : LacunarySequence) → Multiplicative ℤ →* (H r ≃ₗᵢ[ℂ] H r)) :
    Multiplicative ℤ →* (lp H 2 ≃ₗᵢ[ℂ] lp H 2) where
  toFun a :=
    { toFun := hilbertSumVector (fun r t ↦ U r (Multiplicative.ofAdd t)) a.toAdd
      invFun := hilbertSumVector (fun r t ↦ U r (Multiplicative.ofAdd t)) (-a.toAdd)
      left_inv x := lp.ext (funext fun r ↦ by
        change (U r a⁻¹ * U r a) (x r) = x r
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl)
      right_inv x := lp.ext (funext fun r ↦ by
        change (U r a * U r a⁻¹) (x r) = x r
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl)
      map_add' x y := lp.ext (funext fun r ↦ by
        change U r a (x r + y r) = U r a (x r) + U r a (y r)
        rw [map_add])
      map_smul' c x := lp.ext (funext fun r ↦ by
        change U r a (c • x r) = c • U r a (x r)
        rw [map_smul])
      norm_map' x := by
        change ‖hilbertSumVector (fun r t ↦ U r (Multiplicative.ofAdd t)) a.toAdd x‖ = ‖x‖
        have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
        simp only [lp.norm_eq_tsum_rpow hp, hilbertSumVector_apply, LinearIsometryEquiv.norm_map] }
  map_one' := by
    ext x r
    change U r 1 (x r) = x r
    rw [map_one]
    rfl
  map_mul' a b := by
    ext x r
    change U r (a * b) (x r) = U r a (U r b (x r))
    rw [map_mul]
    rfl

/-- If the components have no nonzero eigenvectors for their generators,
the generator on the Hilbert direct sum also has none. -/
theorem hilbertSum_no_nonzero_eigenvector
    (U : (r : LacunarySequence) → ℤ → H r ≃ₗᵢ[ℂ] H r)
    (hU : ∀ r (c : ℂ) (ξ : H r), U r 1 ξ = c • ξ → ξ = 0)
    (c : ℂ) (ξ : lp H 2) (hξ : hilbertSumVector U 1 ξ = c • ξ) : ξ = 0 := by
  apply lp.ext
  funext r
  apply hU r c (ξ r)
  exact congrArg (fun x : lp H 2 ↦ x r) hξ

/-- Every infinite set of natural times misses the claimed simultaneous
weak-limit property for the direct sum. -/
theorem no_common_weakDecayOn_of_rigidComponents
    (U : (r : LacunarySequence) → ℤ → H r ≃ₗᵢ[ℂ] H r)
    (hu : ∀ r, ∃ ξ : H r, ξ ≠ 0 ∧ Tendsto
      (fun n ↦ U r (r.value n : ℤ) ξ) atTop (𝓝 ξ))
    (A : Set ℕ) (hA : A.Infinite) :
    ∃ ξ : lp H 2, ¬ WeakDecayOn (fun a ↦ hilbertSumVector U a ξ) ((↑) '' A) := by
  classical
  obtain ⟨v, hmem, hmono, hpos, hratio⟩ := exists_lacunary_subsequence A hA
  let r : LacunarySequence := ⟨v, hmono, hpos, hratio⟩
  obtain ⟨z, hz, hzlim⟩ := hu r
  refine ⟨lp.single 2 r z, fun hweak ↦ ?_⟩
  let u (n : ℕ) : ℤ := v n
  have hinj : Function.Injective u :=
    (show Function.Injective (Nat.cast : ℕ → ℤ) from
      fun _ _ h ↦ Int.ofNat_inj.mp h).comp hmono.injective
  have hesc : Tendsto u atTop cofinite := by
    simpa only [Nat.cofinite_eq_atTop] using hinj.tendsto_cofinite
  have humem : ∀ n, u n ∈ (Nat.cast : ℕ → ℤ) '' A :=
    fun n ↦ Set.mem_image_of_mem _ (hmem n)
  have hzweak : WeakDecayOn (fun a ↦ U r a z) ((↑) '' A) := by
    intro f
    let e := lp.evalCLM ℂ H 2 r
    refine (hweak (f.comp e)).congr' (Eventually.of_forall fun a ↦ ?_)
    change f (U r a ((lp.single 2 r z : lp H 2) r)) = f (U r a z)
    rw [lp.single_apply_self]
  exact not_weakDecayOn_of_rigidity_sequence (fun a ↦ U r a z) ((↑) '' A) u hesc
    humem z hz hzlim hzweak

end JdLG.PaperExamplesRigid
