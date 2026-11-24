module

public import Mixing.GeneratedSigma
public import Mixing.GeneratedMultiplier

@[expose] public section

namespace Mixing

open Filter MeasureTheory Set
open scoped BigOperators

variable {G X : Type*} [CommGroup G] [m : MeasurableSpace X]

/-- The finite-product density definition implies generation of the full σ-algebra. -/
theorem System.generatedSigma_eq_of_isUGenerated {S : System G X} {P : Set (Ultrafilter G)}
    (hgen : S.IsUGenerated P) : S.generatedSigma P = m := by
  let F := S.generatedFactorMap P
  let J := F.pullback.toLinearMap
  have hmem {p : Ultrafilter G} (hp : p ∈ P) (f : BoundedObservable X) :
      @Measurable X ℂ (S.generatedSigma P) _ (S.ultrafilterTranslate p f) :=
    S.generatedSigma_measurable_of_ae_eq P (S.ultrafilterTranslate p f).measurable
      (S.generatedSigma_measurable_image P hp (f.l2 S.measure))
      (S.ultrafilterTranslate_ae p f)
  have hprod : S.generatedProducts P ⊆ (J.range : Set (Lp ℂ 2 S.measure)) := by
    rintro _ ⟨n, p, f, hp, rfl⟩
    have hMeas : @Measurable X ℂ (S.generatedSigma P) _
        (S.ultrafilterProduct p f : X → ℂ) := by
      let _ : MeasurableSpace X := S.generatedSigma P
      exact Finset.measurable_prod Finset.univ (fun i _ ↦ hmem (hp i) (f i))
    exact S.mem_range_generatedFactor_pullback
      (S.generatedSigma_measurable_of_ae_eq P (Lp.stronglyMeasurable _).measurable hMeas
        ((S.ultrafilterProduct p f).coe_l2 S.measure))
  have hRangeClosed : IsClosed (J.range : Set (Lp ℂ 2 S.measure)) :=
    F.pullback.isometry.isClosedEmbedding.isClosed_range
  have hcl := closure_minimal (show _ ⊆ (J.range : Set (Lp ℂ 2 S.measure)) from
    Submodule.span_le.mpr hprod) hRangeClosed
  change Dense (Submodule.span ℂ (S.generatedProducts P) : Set (Lp ℂ 2 S.measure)) at hgen
  rw [hgen.closure_eq] at hcl
  apply le_antisymm (S.generatedSigma_le P)
  intro B hB
  let e := indicatorConstLp 2 hB (measure_ne_top S.measure B) (1 : ℂ)
  obtain ⟨w, hw⟩ := hcl (Set.mem_univ e)
  have hw' : F.pullback w = e := hw
  have hm : @Measurable X ℂ (S.generatedSigma P) _ w := (Lp.stronglyMeasurable w).measurable
  have h : (w : WithSigma (S.generatedSigma P) → ℂ) =ᵐ[S.measure]
      B.indicator (fun _ ↦ 1) := by
    have hPull := Lp.coeFn_compMeasurePreserving w F.preserves
    change F.pullback w =ᵐ[S.measure] w at hPull
    rw [hw'] at hPull
    exact hPull.symm.trans indicatorConstLp_coeFn
  have hind : @Measurable X ℂ (S.generatedSigma P) _ (B.indicator fun _ ↦ 1) :=
    S.generatedSigma_measurable_of_ae_eq P (measurable_const.indicator hB) hm h.symm
  have hpre : (B.indicator (fun _ ↦ (1 : ℂ))) ⁻¹' ({1} : Set ℂ) = B := by
    classical
    ext x
    by_cases hx : x ∈ B <;> simp [hx]
  rw [← hpre]
  exact hind (measurableSet_singleton _)

end Mixing
