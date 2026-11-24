/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ToralNilrotationSpectrum
public import Mathlib.Data.Int.Lemmas

/-! # The bilateral-shift decomposition for the two-dimensional skew shift -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing.ToralNilrotation

variable (α : UnitAddCircle)

/-- One orbit for each nonzero vertical frequency and each possible horizontal residue. -/
abbrev VerticalOrbit := {u : ℤ × ℤ // u.2 ≠ 0 ∧ 0 ≤ u.1 ∧ u.1 < |u.2|}

instance : Infinite VerticalOrbit := Infinite.of_injective
  (fun n : ℕ => (⟨(0, Int.ofNat n + 1), by
    change (n : ℤ) + 1 ≠ 0 ∧ 0 ≤ (0 : ℤ) ∧ 0 < |(n : ℤ) + 1|
    rw [abs_of_pos (by omega)]
    omega⟩ : VerticalOrbit)) (by
    intro n k h
    have he := congrArg (fun u : VerticalOrbit => u.1.2) h
    change (n : ℤ) + 1 = (k : ℤ) + 1 at he
    omega)

private def orbitIndex (i : VerticalOrbit × Multiplicative ℤ) : ℤ × ℤ :=
  (i.1.1.1 + i.1.1.2 * i.2.toAdd, i.1.1.2)

private theorem orbitIndex_injective : Function.Injective orbitIndex := by
  intro i j he
  have hy : (orbitIndex i).2 = (orbitIndex j).2 := congrArg Prod.snd he
  change i.1.1.2 = j.1.1.2 at hy
  have hx : (orbitIndex i).1 = (orbitIndex j).1 := congrArg Prod.fst he
  have hi := (Int.ediv_emod_unique'' (a := (orbitIndex i).1) (q := i.2.toAdd) (r := i.1.1.1) i.1.2.1).2
    ⟨rfl, i.1.2.2.1, i.1.2.2.2⟩
  have hj := (Int.ediv_emod_unique'' (a := (orbitIndex j).1) (q := j.2.toAdd) (r := j.1.1.1) j.1.2.1).2
    ⟨rfl, j.1.2.2.1, j.1.2.2.2⟩
  rw [hx, hy] at hi
  exact Prod.ext (Subtype.ext (Prod.ext (hi.2.symm.trans hj.2) hy))
    (Multiplicative.ext (hi.1.symm.trans hj.1))

private theorem exists_orbitIndex_eq (u : ℤ × ℤ) (hu : u.2 ≠ 0) :
    ∃ i, orbitIndex i = u := by
  let j : VerticalOrbit := ⟨(u.1 % u.2, u.2), hu, Int.emod_nonneg _ hu, Int.emod_lt_abs _ hu⟩
  exact ⟨(j, Multiplicative.ofAdd (u.1 / u.2)), Prod.ext (Int.emod_add_mul_ediv _ _) rfl⟩

theorem vertical_mode_mem_purePointPart_orthogonal (u : ℤ × ℤ) (hu : u.2 ≠ 0) :
    mode α u ∈ (purePointPart (system α).koopmanRep)ᗮ := by
  let U := (system α).koopmanRep
  let : Infinite (Multiplicative ℤ) := by change Infinite ℤ; infer_instance
  let p := hyperfilter (Multiplicative ℤ)
  let A := ultrafilterOperator U p
  have hA : A (mode α u) = 0 := vertical_mode_killed α u hu p hyperfilter_le_cofinite
  intro y hy
  calc
    ⟪y, mode α u⟫_ℂ = ⟪A.adjoint (A y), mode α u⟫_ℂ := by
      rw [(ultrafilterOperator_purePoint_inverse U p hy).2]
    _ = 0 := by rw [A.adjoint_inner_left, hA, inner_zero_right]

private noncomputable def orbitBasisVector (i : VerticalOrbit × Multiplicative ℤ) :
    (purePointPart (system α).koopmanRep)ᗮ :=
  ⟨(system α).koopmanRep i.2 (mode α i.1.1), by
    rw [koopman_mode]
    exact Submodule.smul_mem _ _ (vertical_mode_mem_purePointPart_orthogonal α _ i.1.2.1)⟩

private theorem orbitBasisVector_val (i : VerticalOrbit × Multiplicative ℤ) :
    (orbitBasisVector α i : Lp ℂ 2 (system α).measure) =
      phase α i.2 i.1.1 • mode α (orbitIndex i) := koopman_mode α i.2 i.1.1

private theorem orbitBasisVector_orthonormal : Orthonormal ℂ (orbitBasisVector α) := by
  constructor
  · intro i
    change ‖(system α).koopmanRep i.2 (mode α i.1.1)‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (mode_orthonormal α).1 i.1.1
  · intro i j hij
    change ⟪(orbitBasisVector α i : Lp ℂ 2 (system α).measure),
      (orbitBasisVector α j : Lp ℂ 2 (system α).measure)⟫_ℂ = 0
    rw [orbitBasisVector_val, orbitBasisVector_val, inner_smul_left, inner_smul_right, inner_mode,
      ite_eq_right (fun he => hij (orbitIndex_injective he)), mul_zero, mul_zero]

private theorem orbitBasisVector_dense :
    (Submodule.span ℂ (range (orbitBasisVector α))).topologicalClosure = ⊤ := by
  let V := (Submodule.span ℂ (range (orbitBasisVector α))).topologicalClosure
  let : CompleteSpace V := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hOrth : Vᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply eq_zero_of_mode_inner α
    intro u
    by_cases hu : u.2 = 0
    · rw [show u = (u.1, 0) from Prod.ext rfl hu]
      exact x.property _ (Submodule.le_topologicalClosure _ (Submodule.subset_span (horizontal_mode_eigen α u.1)))
    · obtain ⟨i, hi⟩ := exists_orbitIndex_eq u hu
      have hmem : orbitBasisVector α i ∈ V :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))
      have he := hx _ hmem
      change ⟪(orbitBasisVector α i : Lp ℂ 2 (system α).measure), (x : Lp ℂ 2 (system α).measure)⟫_ℂ = 0 at he
      rw [orbitBasisVector_val, hi, inner_smul_left] at he
      have hphase : phase α i.2 i.1.1 ≠ 0 := by
        intro h
        have hn := norm_phase α i.2 i.1.1
        rw [h, norm_zero] at hn
        exact zero_ne_one hn
      exact (mul_eq_zero.mp he).resolve_left ((map_ne_zero (starRingEnd ℂ)).2 hphase)
  exact Submodule.orthogonal_eq_bot_iff.mp hOrth

/-- The concrete nilrotation has a countably infinite Lebesgue complement, with
the actual Hilbert basis identified by Fourier orbit residues. -/
theorem hasLebesgueComplement : HasLebesgueComplement (system α).koopmanRep VerticalOrbit := by
  let b := HilbertBasis.mk (orbitBasisVector_orthonormal α) (ge_of_eq (orbitBasisVector_dense α))
  refine ⟨b, fun g j n => ?_⟩
  change (system α).koopmanRep g (b (j, n) : Lp ℂ 2 (system α).measure) = (b (j, g*n) : Lp ℂ 2 (system α).measure)
  simp only [b, HilbertBasis.coe_mk]
  change (system α).koopmanRep g ((system α).koopmanRep n (mode α j.1)) =
    (system α).koopmanRep (g*n) (mode α j.1)
  rw [map_mul]
  rfl

end Mixing.ToralNilrotation
