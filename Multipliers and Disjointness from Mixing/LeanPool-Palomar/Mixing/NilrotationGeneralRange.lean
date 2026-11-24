/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationGeometryComponentModel
public import Mixing.NilrotationQuotientSpectrum

/-! # The generated factor of an ergodic nilrotation -/

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set TopologicalSpace
open scoped Nilrotation InnerProductSpace

/-- The restriction of a weak ultrafilter limit to the pure point subspace is
unitary. Its inverse is the restriction of the adjoint. -/
def purePointUltrafilterUnitary {Γ V : Type*} [Group Γ] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (U : Γ →* (V ≃ₗᵢ[ℂ] V)) (p : Ultrafilter Γ) :
    purePointPart U ≃ₗᵢ[ℂ] purePointPart U := by
  let A := ultrafilterOperator U p
  let W := purePointPart U
  let D : W →L[ℂ] W := (A.comp W.subtypeL).codRestrict W fun x ↦
    ultrafilterOperator_mem_purePointPart U p x.property
  have hAdj (x : W) : A.adjoint x ∈ W := by
    rw [show A.adjoint = ultrafilterOperator U (inverseUltrafilter p) from
      (ultrafilterOperator_inverse U p).symm]
    exact ultrafilterOperator_mem_purePointPart U _ x.property
  refine {
    __ := D.toLinearMap
    norm_map' := ?_
    invFun x := ⟨A.adjoint x, hAdj x⟩
    left_inv x := Subtype.ext (ultrafilterOperator_purePoint_inverse U p x.property).2
    right_inv x := Subtype.ext (ultrafilterOperator_purePoint_inverse U p x.property).1 }
  intro x
  change ‖A (x : V)‖ = ‖(x : V)‖
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (A (x : V)), norm_eq_sqrt_re_inner (𝕜 := ℂ) (x : V),
    ← A.adjoint_inner_right, (ultrafilterOperator_purePoint_inverse U p x.property).2]

@[simp]
theorem purePointUltrafilterUnitary_apply {Γ V : Type*} [Group Γ] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (U : Γ →* (V ≃ₗᵢ[ℂ] V)) (p : Ultrafilter Γ)
    (x : purePointPart U) :
    (purePointUltrafilterUnitary U p x : V) = ultrafilterOperator U p x := rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [LocallyConnectedSpace G]

/-- Every free weak limit of an ergodic compact nilrotation has range equal to
its pure point subspace. -/
theorem nilrotationQuotient_range_eq_purePointPart
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hErg : (nilrotationQuotientSystem L a μ hμ).IsErgodic)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    (ultrafilterOperator U p).range = purePointPart U := by
  let H := nilrotationComponentSubgroup a
  let t : H := ⟨a, nilrotationComponentSubgroup_contains_time a⟩
  let : SecondCountableTopology H := Subtype.secondCountableTopology (H : Set G)
  obtain ⟨D, hD, hc, hd, ν, hνProb, hν, e, he⟩ :=
    nilrotationQuotient_exists_component_model L hL a μ hμ hErg
  let : CompactSpace (H ⧸ D) := hc
  let : IsProbabilityMeasure ν := hνProb
  apply ultrafilterOperator_range_eq_purePointPart_of_intertwining_equiv e he p
  exact nilrotationQuotient_range_eq_purePointPart_of_dense_lift D hD n
    (nilrotationComponentSubgroup_lowerCentralSeries_eq_bot a n hn) t 1
    (by simpa only [mul_one] using hd) (nilrotationComponentSubgroup_generated a)
    ν hν p hp

/-- Example 1. Every free weak limit annihilates the orthogonal complement of
the Kronecker subspace of an ergodic compact nilrotation. -/
theorem nilrotationQuotient_ultrafilter_zero_on_orthogonal
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hErg : (nilrotationQuotientSystem L a μ hμ).IsErgodic)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    ∀ x ∈ (purePointPart U)ᗮ, ultrafilterOperator U p x = 0 := by
  let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
  let A := ultrafilterOperator U p
  change ∀ x ∈ (purePointPart U)ᗮ, A x = 0
  intro x hx
  have hrange := nilrotationQuotient_range_eq_purePointPart L hL n hn a μ hμ hErg p hp
  have hy : A x ∈ purePointPart U := hrange ▸ ⟨x, rfl⟩
  have hAdj : A.adjoint (A x) ∈ purePointPart U := by
    rw [show A.adjoint = ultrafilterOperator U (inverseUltrafilter p) from
      (ultrafilterOperator_inverse U p).symm]
    exact ultrafilterOperator_mem_purePointPart U _ hy
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change ⟪A x, A x⟫_ℂ = 0
  rw [← A.adjoint_inner_left]
  exact hx _ hAdj

/-- Example 1. Every nonempty family of free ultrafilters gives the Kronecker
factor of an ergodic compact nilrotation. -/
theorem nilrotationQuotient_generatedSigma_eq_kroneckerSigma
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hErg : (nilrotationQuotientSystem L a μ hμ).IsErgodic)
    (P : Set (Ultrafilter (Multiplicative ℤ))) (hP : P.Nonempty)
    (hf : P ⊆ freeUltrafilters (Multiplicative ℤ)) :
    let S := nilrotationQuotientSystem L a μ hμ
    S.generatedSigma P = S.kroneckerSigma := by
  apply System.generatedSigma_eq_sigmaOfSubmodule _ _ hP
  exact fun p hp ↦ nilrotationQuotient_range_eq_purePointPart L hL n hn a μ hμ hErg p (hf hp)

end Mixing
