module

public import Mixing.GeneratedSigma
public import Mixing.GeneratedMultiplier
public import Mixing.IdentityDisjointness

@[expose] public section

namespace Mixing

open Filter MeasureTheory Set

universe u

variable {G : Type*} {X : Type u} [CommGroup G] [MeasurableSpace X]

/-- Failure of U-mixing gives a nontrivial event in the generated factor. -/
theorem System.generatedFactor_nontrivial_of_not_isUMixing
    {S : System G X} {P : Set (Ultrafilter G)} (hmix : ¬ S.IsUMixing P) :
    ∃ B : Set (WithSigma (S.generatedSigma P)), MeasurableSet B ∧
      0 < (S.generatedFactor P).measure B ∧ (S.generatedFactor P).measure B < 1 := by
  let T := S.generatedFactor P
  let F := S.generatedFactorMap P
  change ¬ ∀ p ∈ P, ultrafilterOperator S.koopmanZeroRep p = 0 at hmix
  push Not at hmix
  obtain ⟨p, hp, hnz⟩ := hmix
  have hvec : ∃ f, ultrafilterOperator S.koopmanZeroRep p f ≠ 0 := by
    by_contra! h
    apply hnz
    exact ContinuousLinearMap.ext fun f ↦ (h f).trans (zero_apply f).symm
  obtain ⟨f, hf⟩ := hvec
  let v := ultrafilterOperator S.koopmanZeroRep p f
  have hsub : Intertwines S.koopmanZeroRep S.koopmanRep (meanZero S.measure).subtypeL :=
    fun _ _ ↦ rfl
  have hv : (v : Lp ℂ 2 S.measure) = ultrafilterOperator S.koopmanRep p f :=
    hsub.ultrafilter p f
  obtain ⟨w, hw⟩ := S.range_ultrafilterOperator_le_generatedFactor_pullback P hp ⟨f, hv.symm⟩
  by_contra h
  have hpre : PreErgodic id T.measure := by
    apply PreErgodic.of_preimage_eq_of_measurable measurable_id
      (MeasurePreserving.id T.measure).quasiMeasurePreserving
    intro B hB _
    rw [eventuallyEmptyOrUniv_iff, ae_iff, ae_iff]
    rcases eq_or_ne (T.measure B) 0 with hz | hz
    · exact Or.inr (by simpa only [not_not, ofPred_mem_eq] using hz)
    · left
      have hle : T.measure B ≤ 1 := prob_le_one
      have hge : 1 ≤ T.measure B := not_lt.mp fun hlt ↦ h ⟨B, hB, pos_iff_ne_zero.mpr hz, hlt⟩
      have he := hle.antisymm hge
      change T.measure Bᶜ = 0
      rw [prob_compl_eq_one_sub hB, he, tsub_self]
  obtain ⟨c, hc⟩ := hpre.ae_eq_const_of_ae_eq_comp (Lp.stronglyMeasurable w).measurable rfl
  have hc' : (v : Lp ℂ 2 S.measure) =ᵐ[S.measure] Function.const X c := by
    rw [← hw]
    exact (Lp.coeFn_compMeasurePreserving w F.preserves).trans
      (F.preserves.quasiMeasurePreserving.ae_eq_comp hc)
  have hcv := (mem_meanZero_iff_integral S.measure (v : Lp ℂ 2 S.measure)).mp v.property
  rw [integral_congr_ae hc'] at hcv
  change (∫ _ : X, c ∂S.measure) = 0 at hcv
  simp [integral_const, measureReal_def] at hcv
  apply hf
  apply Subtype.ext
  apply Lp.ext
  simp only [hcv] at hc'
  exact hc'.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := S.measure)).symm

/-- The implication of Theorem 1.3 from disjointness to mixing, once the generated
factor is expressed in the finite-product density formulation. -/
theorem theorem1_3_ii_iii_of_generatedFactor (S : System G X) (P : Set (Ultrafilter G))
    (hgen : (S.generatedFactor P).IsUGenerated P)
    (hd : ∀ (Y : Type u) [MeasurableSpace Y] (T : System G Y), T.IsUGenerated P → Disjoint S T) :
    S.IsUMixing P := by
  by_contra hmix
  obtain ⟨B, hB, h₀, h₁⟩ := S.generatedFactor_nontrivial_of_not_isUMixing hmix
  exact (S.generatedFactorMap P).not_disjoint_of_event hB h₀ h₁
    (hd _ (S.generatedFactor P) hgen)

/-- The nontriviality assertion of Corollary 1. A nontrivial factor of a generated
system has a nontrivial generated factor of its own. -/
theorem corollary1_nontrivial {Y : Type*} [MeasurableSpace Y]
    {S : System G X} {T : System G Y} {P : Set (Ultrafilter G)}
    (hgen : S.IsUGenerated P) (f : FactorMap S T)
    {B : Set Y} (hB : MeasurableSet B) (hB₀ : 0 < T.measure B) (hB₁ : T.measure B < 1) :
    ∃ A : Set (WithSigma (T.generatedSigma P)), MeasurableSet A ∧
      0 < (T.generatedFactor P).measure A ∧ (T.generatedFactor P).measure A < 1 := by
  apply T.generatedFactor_nontrivial_of_not_isUMixing
  intro hmix
  exact f.not_disjoint_of_event hB hB₀ hB₁
    (System.disjoint_of_isUGenerated hgen hmix)

end Mixing
