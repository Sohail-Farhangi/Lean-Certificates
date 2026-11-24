/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationQuotientSpectralStep
public import Mixing.NilrotationHaarComplement
public import Mixing.NilrotationGeometryDensity

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory
open scoped Nilrotation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G]

/-- The spectral facts propagate through the closed lower-central tower.
The last layer is the original stabilizer whenever the series terminates. -/
theorem nilrotationQuotient_spectralFacts_of_dense_lift
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a^j*d*(γ:G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    NilrotationSpectralFacts U := by
  let T (H : Subgroup G) (h : L ≤ H) : System (Multiplicative ℤ) (G ⧸ H) :=
    let ν := μ.map (Subgroup.quotientMapOfLE h)
    letI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
      (nilrotationQuotientMap_continuous h).measurable.aemeasurable).mpr inferInstance
    nilrotationQuotientSystem H a ν (nilrotationQuotient_map_preserves h μ hμ)
  let P {H : Subgroup G} (S : System (Multiplicative ℤ) (G ⧸ H)) := NilrotationSpectralFacts S.koopmanRep
  have hTower (i : ℕ) : P (T (nilrotationClosedLayer L i) (nilrotationClosedLayer_lattice_le L i)) := by
    induction i with
    | zero =>
      generalize_proofs h
      revert h
      rw [nilrotationClosedLayer_zero]
      intro h
      let : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
      let U := (T ⊤ h).koopmanRep
      have hTop : purePointPart U = ⊤ := by
        apply top_unique
        intro x _
        apply eigenvectors_le_purePointPart U
        refine ⟨1, fun g ↦ ?_⟩
        simp only [MonoidHom.one_apply, Circle.coe_one, one_smul]
        change Lp.compMeasurePreserving _ ((T ⊤ h).preserves g) x = x
        apply Lp.ext
        filter_upwards [Lp.coeFn_compMeasurePreserving x ((T ⊤ h).preserves g)] with w hw
        exact hw.trans (congrArg (fun z : G ⧸ (⊤ : Subgroup G) ↦ x z) (Subsingleton.elim _ _))
      change NilrotationSpectralFacts U
      refine ⟨?_, ?_⟩
      · rw [HasHaarAbsolutelyContinuousComplement, hTop, Submodule.top_orthogonal_eq_bot]
        exact bot_le
      · intro p _
        rw [hTop]
        exact top_unique fun x _ ↦ ⟨(ultrafilterOperator U p).adjoint x,
          (ultrafilterOperator_purePoint_inverse U p (hTop.symm ▸ Submodule.mem_top)).1⟩
    | succ i ih =>
      let H := nilrotationClosedLayer L (i+1)
      let C := (⊤ : Subgroup G).lowerCentralSeries i
      let hH := nilrotationClosedLayer_lattice_le L (i+1)
      let : CompactSpace (G ⧸ H) := nilrotationQuotient_compactSpace hH
      let ν := μ.map (Subgroup.quotientMapOfLE hH)
      let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
        (nilrotationQuotientMap_continuous hH).measurable.aemeasurable).mpr inferInstance
      have hc := nilrotationClosedLayer_commutator_le L i
      apply (nilrotationQuotient_vertical_spectralFacts i H (Subgroup.isClosed_topologicalClosure _) hc a d
        (nilrotation_dense_lifted_cosets_mono hH hd) hgen ν (nilrotationQuotient_map_preserves hH μ hμ) ?_).1
      intro _
      let h := nilrotation_lattice_le_verticalClosure C H
      let V := nilrotationVerticalClosure C H
      have he : ν.map (Subgroup.quotientMapOfLE h) = μ.map (Subgroup.quotientMapOfLE (hH.trans h)) := by
        change (μ.map _).map _ = _
        rw [Measure.map_map (nilrotationQuotientMap_continuous h).measurable
          (nilrotationQuotientMap_continuous hH).measurable, nilrotationQuotientMap_comp]
      change P (nilrotationQuotientSystem V a (ν.map _) _)
      rw [nilrotationQuotientSystem_eq_of_measure a _ _ he]
      change P (T V (hH.trans h))
      have eV : V = nilrotationClosedLayer L i := nilrotationClosedLayer_vertical L i
      exact (congrArg (fun J ↦ ∀ q : L ≤ J, P (T J q)) eV).mpr (fun _ ↦ ih) (hH.trans h)
  have hend := hTower n
  generalize_proofs h at hend
  revert hend
  have eL := nilrotationClosedLayer_last L hL n hn
  revert h
  rw [eL]
  intro h hend
  have hμId : μ.map (Subgroup.quotientMapOfLE h) = μ := by
    rw [nilrotationQuotientMap_le_eq h, Measure.map_id]
  have hSystem : T L h = nilrotationQuotientSystem L a μ hμ :=
    nilrotationQuotientSystem_eq_of_measure a _ _ hμId
  exact hSystem ▸ hend

/-- Each free weak limit has range equal to the pure point subspace. -/
theorem nilrotationQuotient_range_eq_purePointPart_of_dense_lift
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a^j*d*(γ:G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    (ultrafilterOperator U p).range = purePointPart U :=
  (nilrotationQuotient_spectralFacts_of_dense_lift L hL n hn a d hd hgen μ hμ).weakRange p hp

/-- For every nonempty family of free ultrafilters the generated factor of
the nilrotation is the Kronecker factor. -/
theorem nilrotationQuotient_generatedSigma_eq_kroneckerSigma_of_dense_lift
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (n : ℕ) (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a^j*d*(γ:G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (P : Set (Ultrafilter (Multiplicative ℤ))) (hP : P.Nonempty)
    (hf : P ⊆ freeUltrafilters (Multiplicative ℤ)) :
    let S := nilrotationQuotientSystem L a μ hμ
    S.generatedSigma P = S.kroneckerSigma := by
  apply System.generatedSigma_eq_sigmaOfSubmodule _ _ hP
  exact fun p hp ↦ nilrotationQuotient_range_eq_purePointPart_of_dense_lift L hL n hn a d hd
    hgen μ hμ p (hf hp)

end Mixing
