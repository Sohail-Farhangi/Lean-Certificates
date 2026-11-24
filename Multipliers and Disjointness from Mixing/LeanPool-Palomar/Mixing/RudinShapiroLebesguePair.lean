/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroCyclicSpan
public import Mixing.PurePointLebesgue

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped Classical InnerProductSpace Topology

variable (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)

def rudinShapiroPairOrbit (i : Bool × Multiplicative ℤ) :
    Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure :=
  (rudinShapiroOrbitSystem p hp).koopmanRep i.2 (rudinShapiroPairLp p hp i.1)

theorem orthonormal_rudinShapiroPairOrbit : Orthonormal ℂ (rudinShapiroPairOrbit p hp) := by
  rw [orthonormal_iff_ite]
  rintro ⟨a, j⟩ ⟨b, k⟩
  let U := (rudinShapiroOrbitSystem p hp).koopmanRep
  change ⟪U j (rudinShapiroPairLp p hp a), U k (rudinShapiroPairLp p hp b)⟫_ℂ = _
  let x := rudinShapiroPairLp p hp a
  let y := rudinShapiroPairLp p hp b
  have he : ⟪U j x, U k y⟫_ℂ = ⟪x, U (j⁻¹ * k) y⟫_ℂ := by
    calc
      _ = ⟪U j⁻¹ (U j x), U j⁻¹ (U k y)⟫_ℂ := ((U j⁻¹).inner_map_map _ _).symm
      _ = _ := by
        change ⟪(U j⁻¹ * U j) x, (U j⁻¹ * U k) y⟫_ℂ = _
        rw [← map_mul, ← map_mul, inv_mul_cancel, map_one]
        rfl
  change ⟪U j x, U k y⟫_ℂ = _
  rw [he]
  have h := rudinShapiroPairLp_correlation p hp a b (j⁻¹ * k).toAdd
  change ⟪rudinShapiroPairLp p hp a, U (j⁻¹ * k) (rudinShapiroPairLp p hp b)⟫_ℂ = _ at h
  rw [h]
  have hh : (j⁻¹ * k).toAdd = 0 ↔ j = k := by
    change j⁻¹ * k = 1 ↔ j = k
    simpa [eq_comm] using (inv_mul_eq_one : j⁻¹ * k = 1 ↔ j = k)
  simp only [hh, Prod.mk.injEq]

theorem rudinShapiroPairOrbit_mem_purePoint_orthogonal (i : Bool × Multiplicative ℤ) :
    rudinShapiroPairOrbit p hp i ∈ (purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep)ᗮ := by
  let S := rudinShapiroOrbitSystem p hp
  let U := S.koopmanRep
  let v := rudinShapiroPairOrbit p hp i
  let f := rudinShapiroPairLp p hp i.1
  have hOrtho : Orthonormal ℂ (fun g : Multiplicative ℤ ↦ U g f) := by
    exact (orthonormal_rudinShapiroPairOrbit p hp).comp (fun g ↦ (i.1, g))
      (fun _ _ h ↦ congrArg Prod.snd h)
  have hEigen : unitaryEigenvectors U ⊆ (innerSL ℂ v).ker := by
    intro x hx
    obtain ⟨χ, hχ⟩ := hx
    have hEq (g : Multiplicative ℤ) : ‖⟪U g f, x⟫_ℂ‖ = ‖⟪f, x⟫_ℂ‖ := by
      have hInv : U g⁻¹ (U g f) = f := by
        change (U g⁻¹ * U g) f = f
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      rw [← (U g⁻¹).inner_map_map, hInv, hχ, inner_smul_right, norm_mul, Circle.norm_coe, one_mul]
    have hSummable := hOrtho.inner_products_summable x
    simp_rw [hEq] at hSummable
    have hZero : ‖⟪f, x⟫_ℂ‖ ^ 2 = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hSummable.tendsto_cofinite_zero
    change ⟪U i.2 f, x⟫_ℂ = 0
    exact norm_eq_zero.mp ((hEq i.2).trans (sq_eq_zero_iff.mp hZero))
  have hAll : purePointPart U ≤ (innerSL ℂ v).ker :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hEigen) (innerSL ℂ v).isClosed_ker
  intro x hx
  exact inner_eq_zero_symm.mp (hAll hx : ⟪v, x⟫_ℂ = 0)

/-- If the periodic subspace and the two actual cyclic orbits span L²,
the continuous part has exactly Lebesgue multiplicity two. -/
theorem rudinShapiro_hasLebesgueComplement_of_parent_span
    (hDense : (purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep ⊔
      rudinShapiroPairSpan p hp).topologicalClosure = ⊤) :
    HasLebesgueComplement (rudinShapiroOrbitSystem p hp).koopmanRep Bool := by
  let S := rudinShapiroOrbitSystem p hp
  let U := S.koopmanRep
  let P := purePointPart U
  let Q := rudinShapiroPairSpan p hp
  let e (i : Bool × Multiplicative ℤ) : Pᗮ :=
    ⟨rudinShapiroPairOrbit p hp i, rudinShapiroPairOrbit_mem_purePoint_orthogonal p hp i⟩
  let : CompleteSpace Pᗮ := P.isClosed_orthogonal.completeSpace_coe
  have hOrtho : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    exact orthonormal_iff_ite.mp (orthonormal_rudinShapiroPairOrbit p hp)
  let W := (Submodule.span ℂ (range e)).topologicalClosure
  let : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hW : Wᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply Subtype.ext
    let K := (innerSL ℂ (x : Lp ℂ 2 S.measure)).ker
    have hP : P ≤ K := by
      intro y hy
      exact inner_eq_zero_symm.mp (x.property y hy)
    have hQ : Q ≤ K := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hE : e i ∈ W :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self i))
      exact inner_eq_zero_symm.mp (hx (e i) hE)
    have hTop : (⊤ : Submodule ℂ (Lp ℂ 2 S.measure)) ≤ K := by
      rw [← hDense]
      exact Submodule.topologicalClosure_minimal _ (sup_le hP hQ) (innerSL ℂ _).isClosed_ker
    exact inner_self_eq_zero.mp (hTop Submodule.mem_top)
  have hDense' : W = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hW
  let b := HilbertBasis.mk hOrtho (ge_of_eq hDense')
  refine ⟨b, fun g j n ↦ ?_⟩
  simp only [b, HilbertBasis.coe_mk]
  change U g (U n (rudinShapiroPairLp p hp j)) = U (g * n) (rudinShapiroPairLp p hp j)
  rw [map_mul]
  rfl

end Mixing
