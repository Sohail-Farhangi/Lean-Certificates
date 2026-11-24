/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RangesAndFactors
public import Mixing.StrongMixing
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Pure point and Lebesgue components in Examples 1 and 3 -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Joint eigenvectors of a unitary representation, with unit-circle eigencharacters. -/
def unitaryEigenvectors (U : G →* (H ≃ₗᵢ[ℂ] H)) : Set H :=
  {x | ∃ χ : G →* Circle, ∀ g, U g x = (χ g : ℂ) • x}

/-- The closed span of the joint eigenvectors. -/
def purePointPart (U : G →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H :=
  (Submodule.span ℂ (unitaryEigenvectors U)).topologicalClosure

theorem isClosed_purePointPart (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsClosed (purePointPart U : Set H) :=
  Submodule.isClosed_topologicalClosure _

theorem eigenvectors_le_purePointPart (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    unitaryEigenvectors U ⊆ purePointPart U := fun _ hx ↦
  Submodule.le_topologicalClosure _ (Submodule.subset_span hx)

theorem purePointPart_le_of_eigenvectors_le (U : G →* (H ≃ₗᵢ[ℂ] H))
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H))
    (h : unitaryEigenvectors U ⊆ V) : purePointPart U ≤ V :=
  Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr h) hV

variable [CompleteSpace H]

private theorem ultrafilterOperator_of_eigenvector (U : G →* (H ≃ₗᵢ[ℂ] H))
    (p : Ultrafilter G) {x : H} (χ : G →* Circle)
    (hx : ∀ g, U g x = (χ g : ℂ) • x) {z : Circle}
    (hz : Tendsto χ (p : Filter G) (𝓝 z)) :
    ultrafilterOperator U p x = (z : ℂ) • x := by
  apply ext_inner_left ℂ
  intro y
  have hχ := ((continuous_subtype_val.tendsto z).comp hz).mul
    (tendsto_const_nhds (x := ⟪y, x⟫_ℂ))
  have hlim := tendsto_ultrafilterOperator_coeff U p y x
  simp_rw [hx, inner_smul_right] at hlim
  rw [inner_smul_right]
  exact tendsto_nhds_unique hlim hχ

theorem ultrafilterOperator_mem_purePointPart (U : G →* (H ≃ₗᵢ[ℂ] H))
    (p : Ultrafilter G) {x : H} (hx : x ∈ purePointPart U) :
    ultrafilterOperator U p x ∈ purePointPart U := by
  let A := ultrafilterOperator U p
  have h := purePointPart_le_of_eigenvectors_le U ((purePointPart U).comap A.toLinearMap)
    ((isClosed_purePointPart U).preimage A.continuous) (by
      intro v hv
      have hvW := eigenvectors_le_purePointPart U hv
      obtain ⟨χ, hχ⟩ := hv
      change A v ∈ purePointPart U
      rw [ultrafilterOperator_of_eigenvector U p χ hχ (tendsto_ultrafilterExtend χ p)]
      exact (purePointPart U).smul_mem _ hvW)
  exact h hx

/-- Each free or principal ultrafilter operator acts unitarily on the pure point subspace.
These are the two inverse identities for its restriction and its adjoint. -/
theorem ultrafilterOperator_purePoint_inverse (U : G →* (H ≃ₗᵢ[ℂ] H)) (p : Ultrafilter G)
    {x : H} (hx : x ∈ purePointPart U) :
    ultrafilterOperator U p ((ultrafilterOperator U p).adjoint x) = x ∧
      (ultrafilterOperator U p).adjoint (ultrafilterOperator U p x) = x := by
  let A := ultrafilterOperator U p
  have hEigen (v : H) (hv : v ∈ unitaryEigenvectors U) :
      A (A.adjoint v) = v ∧ A.adjoint (A v) = v := by
    obtain ⟨χ, hχ⟩ := hv
    let z := Ultrafilter.extend χ p
    have hz : Tendsto χ (p : Filter G) (𝓝 z) := tendsto_ultrafilterExtend χ p
    have hzi : Tendsto χ (inverseUltrafilter p : Filter G) (𝓝 z⁻¹) := by
      rw [inverseUltrafilter, Ultrafilter.coe_map, tendsto_map'_iff]
      simpa only [Function.comp_def, map_inv] using (continuous_inv.tendsto z).comp hz
    have hA : A v = (z : ℂ) • v := ultrafilterOperator_of_eigenvector U p χ hχ hz
    have hAdj : A.adjoint v = ((z⁻¹ : Circle) : ℂ) • v := by
      change (ultrafilterOperator U p).adjoint v = _
      rw [← ultrafilterOperator_inverse]
      exact ultrafilterOperator_of_eigenvector U (inverseUltrafilter p) χ hχ hzi
    have hm : ((z⁻¹ : Circle) : ℂ) * (z : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    constructor
    · rw [hAdj, map_smul, hA, smul_smul, hm, one_smul]
    · rw [hA, map_smul, hAdj, smul_smul, mul_comm, hm, one_smul]
  let D := A.comp A.adjoint - ContinuousLinearMap.id ℂ H
  let E := A.adjoint.comp A - ContinuousLinearMap.id ℂ H
  have hD := purePointPart_le_of_eigenvectors_le U D.ker D.isClosed_ker (by
    intro v hv
    exact sub_eq_zero.mpr (hEigen v hv).1)
  have hE := purePointPart_le_of_eigenvectors_le U E.ker E.isClosed_ker (by
    intro v hv
    exact sub_eq_zero.mpr (hEigen v hv).2)
  exact ⟨sub_eq_zero.mp (hD hx), sub_eq_zero.mp (hE hx)⟩

/-- The orthogonal complement admits a Hilbert basis on which time acts by bilateral
shifts. The index type is the spectral multiplicity space. -/
def HasLebesgueComplement (U : G →* (H ≃ₗᵢ[ℂ] H)) (I : Type*) : Prop :=
  ∃ b : HilbertBasis (I × G) ℂ (purePointPart U)ᗮ, ∀ (g : G) (j : I) (n : G),
    U g (b (j, n) : H) = (b (j, g * n) : H)

private theorem ultrafilterOperator_mem_purePointOrthogonal (U : G →* (H ≃ₗᵢ[ℂ] H))
    (p : Ultrafilter G) {x : H} (hx : x ∈ (purePointPart U)ᗮ) :
    ultrafilterOperator U p x ∈ (purePointPart U)ᗮ := by
  intro y hy
  rw [← (ultrafilterOperator U p).adjoint_inner_left, ← ultrafilterOperator_inverse]
  exact hx _ (ultrafilterOperator_mem_purePointPart U _ hy)

/-- On the Lebesgue complement every free-ultrafilter operator vanishes. -/
theorem ultrafilterOperator_zero_on_lebesgueComplement (U : G →* (H ≃ₗᵢ[ℂ] H))
    {I : Type*} (hL : HasLebesgueComplement U I) (p : Ultrafilter G)
    (hp : p ∈ freeUltrafilters G) {x : H} (hx : x ∈ (purePointPart U)ᗮ) :
    ultrafilterOperator U p x = 0 := by
  classical
  obtain ⟨b, hb⟩ := hL
  let W := (purePointPart U)ᗮ
  let A := ultrafilterOperator U p
  let D : W →L[ℂ] W := (A.comp W.subtypeL).codRestrict W fun v ↦
    ultrafilterOperator_mem_purePointOrthogonal U p v.property
  have hB (i : I × G) : D (b i) = 0 := by
    apply b.repr.injective
    apply lp.ext
    funext j
    rw [b.repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
    change ⟪(b j : H), A (b i : H)⟫_ℂ = 0
    have hlim := tendsto_ultrafilterOperator_coeff U p (b j : H) (b i : H)
    have hev : ∀ᶠ g in (p : Filter G), ⟪(b j : H), U g (b i : H)⟫_ℂ = 0 := by
      have hp' : (p : Filter G) ≤ cofinite := hp
      filter_upwards [hp' (Set.finite_singleton (j.2 * i.2⁻¹)).compl_mem_cofinite] with g hg
      rw [show U g (b i : H) = (b (i.1, g * i.2) : H) from hb g i.1 i.2]
      change ⟪b j, b (i.1, g * i.2)⟫_ℂ = 0
      have hne : j ≠ (i.1, g * i.2) := by
        intro he
        apply hg
        change g = j.2 * i.2⁻¹
        rw [congrArg Prod.snd he]
        simp
      exact b.orthonormal.inner_eq_zero hne
    have he : (fun _ : G ↦ (0 : ℂ)) =ᶠ[(p : Filter G)]
        fun g ↦ ⟪(b j : H), U g (b i : H)⟫_ℂ := hev.mono fun _ h ↦ h.symm
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he)
  have hker : (Submodule.span ℂ (Set.range b)).topologicalClosure ≤ D.ker :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact hB i)) D.isClosed_ker
  rw [b.dense_span] at hker
  let v : W := ⟨x, hx⟩
  have hz : D v = 0 := hker (Submodule.mem_top (x := v))
  exact congrArg Subtype.val hz

/-- A weak limit which vanishes on the pure point orthogonal complement
has range equal to the pure point part. -/
theorem ultrafilterOperator_range_eq_purePointPart_of_annihilation
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (p : Ultrafilter G)
    (hZero : ∀ x ∈ (purePointPart U)ᗮ, ultrafilterOperator U p x = 0) :
    (ultrafilterOperator U p).range = purePointPart U := by
  let W := purePointPart U
  let A := ultrafilterOperator U p
  let : CompleteSpace W := (isClosed_purePointPart U).completeSpace_coe
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hz := hZero (x - W.starProjection x)
      (Submodule.sub_starProjection_mem_orthogonal (K := W) x)
    have hAx : A x = A (W.starProjection x) := by
      change A (x - W.starProjection x) = 0 at hz
      rwa [map_sub, sub_eq_zero] at hz
    change A x ∈ W
    rw [hAx]
    exact ultrafilterOperator_mem_purePointPart U p (W.starProjection_apply_mem x)
  · intro x hx
    exact ⟨A.adjoint x, (ultrafilterOperator_purePoint_inverse U p hx).1⟩

/-- The spectral decomposition in Examples 1 and 3 determines the range of every
free-ultrafilter operator exactly. -/
theorem ultrafilterOperator_range_eq_purePointPart (U : G →* (H ≃ₗᵢ[ℂ] H))
    {I : Type*} (hL : HasLebesgueComplement U I) (p : Ultrafilter G)
    (hp : p ∈ freeUltrafilters G) : (ultrafilterOperator U p).range = purePointPart U :=
  ultrafilterOperator_range_eq_purePointPart_of_annihilation U p fun _ hx ↦
    ultrafilterOperator_zero_on_lebesgueComplement U hL p hp hx

variable {X : Type*} [MeasurableSpace X]

/-- The Kronecker σ-algebra represented by the closed span of the Koopman eigenfunctions. -/
@[instance_reducible]
noncomputable def System.kroneckerSigma (S : System (Multiplicative ℤ) X) : MeasurableSpace X :=
  S.sigmaOfSubmodule (purePointPart S.koopmanRep)

/-- The generated-factor assertion of Example 1, from the countable Lebesgue
complement of the pure point subspace. -/
theorem example1_generatedSigma_of_purePoint_lebesgue (S : System (Multiplicative ℤ) X)
    (ι : Type*) (hL : HasLebesgueComplement S.koopmanRep ι)
    (P : Set (Ultrafilter (Multiplicative ℤ))) (hP : P.Nonempty)
    (hFree : P ⊆ freeUltrafilters (Multiplicative ℤ)) :
    S.generatedSigma P = S.kroneckerSigma := by
  apply S.generatedSigma_eq_sigmaOfSubmodule P hP
  exact fun p hp ↦ ultrafilterOperator_range_eq_purePointPart S.koopmanRep hL p (hFree hp)

/-- The generated-factor assertion of Example 3, from the Lebesgue complement of
spectral multiplicity two. -/
theorem example3_generatedSigma_of_purePoint_lebesgue_two (S : System (Multiplicative ℤ) X)
    (hL : HasLebesgueComplement S.koopmanRep (Fin 2))
    (P : Set (Ultrafilter (Multiplicative ℤ))) (hP : P.Nonempty)
    (hFree : P ⊆ freeUltrafilters (Multiplicative ℤ)) :
    S.generatedSigma P = S.kroneckerSigma :=
  example1_generatedSigma_of_purePoint_lebesgue S (Fin 2) hL P hP hFree

end Mixing
