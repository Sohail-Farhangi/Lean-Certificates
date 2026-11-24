/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationGeneralRange
public import Mixing.NilrotationQuotientLebesgue

/-! # The pure point and countable Lebesgue parts of an ergodic nilrotation -/

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set TopologicalSpace
open scoped Nilrotation InnerProductSpace Topology

/-- A purely discrete representation has a zero Lebesgue complement. -/
theorem HasLebesgueComplement.empty_of_purePointPart_eq_top {Γ V : Type*} [Group Γ]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (U : Γ →* (V ≃ₗᵢ[ℂ] V)) (h : purePointPart U = ⊤) : HasLebesgueComplement U Empty := by
  classical
  let W := (purePointPart U)ᗮ
  let f : Empty × Γ → W := fun p ↦ p.1.elim
  have hf : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    exact fun j ↦ j.1.elim
  have hDense : ⊤ ≤ (Submodule.span ℂ (range f)).topologicalClosure := by
    intro x _
    have hx : (x : V) ∈ (⊥ : Submodule ℂ V) := by
      simpa only [W, h, Submodule.top_orthogonal_eq_bot] using x.property
    have hx0 : x = 0 := Subtype.ext ((Submodule.mem_bot ℂ).mp hx)
    rw [hx0]
    exact Submodule.zero_mem _
  exact ⟨HilbertBasis.mk hf hDense, fun _ i ↦ i.elim⟩

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [LocallyConnectedSpace G]

/-- The nonzero orthogonal complement of the Kronecker subspace has
Lebesgue spectrum of countably infinite multiplicity. -/
theorem nilrotationQuotient_purePoint_or_countableLebesgue
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hErg : (nilrotationQuotientSystem L a μ hμ).IsErgodic) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    purePointPart U = ⊤ ∨ HasLebesgueComplement U ℕ := by
  let H := nilrotationComponentSubgroup a
  let t : H := ⟨a, nilrotationComponentSubgroup_contains_time a⟩
  let : SecondCountableTopology H := Subtype.secondCountableTopology (H : Set G)
  obtain ⟨D, hD, hc, hd, ν, hνProb, hν, e, he⟩ :=
    nilrotationQuotient_exists_component_model L hL a μ hμ hErg
  let : CompactSpace (H ⧸ D) := hc
  let : IsProbabilityMeasure ν := hνProb
  rcases nilrotationQuotient_purePoint_or_countableLebesgue_of_dense_lift D hD n
    (nilrotationComponentSubgroup_lowerCentralSeries_eq_bot a n hn) t 1
    (by simpa only [mul_one] using hd) (nilrotationComponentSubgroup_generated a) ν hν with h | h
  · exact Or.inl (purePointPart_eq_top_of_intertwining_equiv e he h)
  · exact Or.inr (HasLebesgueComplement.of_intertwining_equiv e he h)

/-- Example 1. The orthogonal complement of the Kronecker subspace of every
ergodic nilrotation admits a bilateral-shift basis with countable multiplicity. -/
theorem nilrotationQuotient_hasCountableLebesgueComplement
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hErg : (nilrotationQuotientSystem L a μ hμ).IsErgodic) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    ∃ I : Type, Countable I ∧ HasLebesgueComplement U I := by
  rcases nilrotationQuotient_purePoint_or_countableLebesgue L hL n hn a μ hμ hErg with h | h
  · exact ⟨Empty, inferInstance, HasLebesgueComplement.empty_of_purePointPart_eq_top _ h⟩
  · exact ⟨ℕ, inferInstance, h⟩

/-- Example 1. The spectral splitting, weak limits, generated factor, distality,
and Furstenberg disjointness of ergodic compact nilrotations. -/
theorem example1_nilrotation
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hErg : (nilrotationQuotientSystem L a μ hμ).IsErgodic) :
    let S := nilrotationQuotientSystem L a μ hμ
    let U := S.koopmanRep
    (∃ I : Type, Countable I ∧ HasLebesgueComplement U I) ∧
    (∀ p ∈ freeUltrafilters (Multiplicative ℤ),
      (∃ A : purePointPart U ≃ₗᵢ[ℂ] purePointPart U,
        ∀ x : purePointPart U, (A x : Lp ℂ 2 S.measure) = ultrafilterOperator U p x) ∧
      ∀ x ∈ (purePointPart U)ᗮ, ultrafilterOperator U p x = 0) ∧
    (∀ P : Set (Ultrafilter (Multiplicative ℤ)), P.Nonempty →
      P ⊆ freeUltrafilters (Multiplicative ℤ) → S.generatedSigma P = S.kroneckerSigma) ∧
    (∀ {I : Type*} (v : I → G) {l : Filter I} [l.NeBot] {x y z : G ⧸ L},
      Tendsto (fun i ↦ v i • x) l (𝓝 z) → Tendsto (fun i ↦ v i • y) l (𝓝 z) → x = y) ∧
    (∀ (X : Type*) [MeasurableSpace X] [StandardBorelSpace X]
      (R : System (Multiplicative ℤ) X), IsWeaklyMixing R.koopmanZeroRep → Disjoint R S) := by
  refine ⟨nilrotationQuotient_hasCountableLebesgueComplement L hL n hn a μ hμ hErg,
    ?_, nilrotationQuotient_generatedSigma_eq_kroneckerSigma L hL n hn a μ hμ hErg, ?_, ?_⟩
  · intro p hp
    exact ⟨⟨purePointUltrafilterUnitary _ p, purePointUltrafilterUnitary_apply _ p⟩,
      nilrotationQuotient_ultrafilter_zero_on_orthogonal L hL n hn a μ hμ hErg p hp⟩
  · intro I v l hl x y z hx hy
    exact nilrotation_distal_quotient L hL n hn v hx hy
  · intro X _ _ R hR
    exact nilrotationQuotient_disjoint_of_weakMixing R hR L hL n hn a μ hμ

end Mixing
