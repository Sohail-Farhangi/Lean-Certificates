/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mixing.SupportingJdLG.Stable
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Invariant means on the compact semigroup

The real positive functional of a mean is represented by its regular probability measure.
Translation invariance then identifies the measure with Haar measure on the group ideal.
This proves the compact-host form of Lemma 4.1 of Barthmann, Farhangi and Kuznetsova,
arXiv:2509.24003v3.
-/

@[expose] public section

open MeasureTheory Set
open scoped CompactlySupported

namespace Mixing.JdLGBridge

section Mean

variable {S : Type*} [Semigroup S] [TopologicalSpace S] [CompactSpace S]

/-- A continuous real function on a compact space has compact support. -/
def compactRealFunction (f : S → ℝ) (hf : Continuous f) : C_c(S, ℝ) :=
  ⟨⟨f, hf⟩, HasCompactSupport.of_compactSpace _⟩

/-- The real positive functional of a normalized left-invariant mean on a compact semigroup.
We use compactly supported continuous functions, which on this space include all continuous
functions. -/
structure LeftInvariantContinuousMean (hleft : ∀ s : S, Continuous (fun t => s * t)) where
  functional : C_c(S, ℝ) →ₚ[ℝ] ℝ
  normalized : functional (compactRealFunction (fun _ => 1) continuous_const) = 1
  translate : ∀ (s : S) (f : C_c(S, ℝ)),
    functional (compactRealFunction (fun t => f (s * t)) (f.continuous.comp (hleft s))) =
      functional f

namespace LeftInvariantContinuousMean

variable [T2Space S] [MeasurableSpace S] [BorelSpace S]
  {hleft : ∀ s : S, Continuous (fun t => s * t)} (m : LeftInvariantContinuousMean hleft)

instance rieszMeasure_probability : IsProbabilityMeasure (RealRMK.rieszMeasure m.functional) := by
  apply isProbabilityMeasure_iff_real.mpr
  have h := (RealRMK.integral_rieszMeasure m.functional
    (compactRealFunction (fun _ : S => 1) continuous_const)).trans m.normalized
  change (∫ _ : S, (1 : ℝ) ∂RealRMK.rieszMeasure m.functional) = 1 at h
  simpa only [integral_const, smul_eq_mul, mul_one] using h

instance rieszMeasure_leftInvariant :
    Measure.IsMulLeftInvariant (RealRMK.rieszMeasure m.functional) := by
  constructor
  intro s
  let μ := RealRMK.rieszMeasure m.functional
  let translation : S → S := fun t => s * t
  have htranslation : Continuous translation := hleft s
  have : IsFiniteMeasure (μ.map translation) := μ.isFiniteMeasure_map translation
  have : (μ.map translation).InnerRegular := Measure.InnerRegular.map_of_continuous htranslation
  change μ.map translation = μ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf : AEStronglyMeasurable (fun t => f t) (μ.map translation) :=
    f.continuous.aestronglyMeasurable
  rw [integral_map htranslation.measurable.aemeasurable hf]
  have h := RealRMK.integral_rieszMeasure m.functional
    (compactRealFunction (fun t => f (s * t)) (f.continuous.comp (hleft s)))
  exact h.trans ((m.translate s f).trans (RealRMK.integral_rieszMeasure m.functional f).symm)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The left-invariant mean integrates the restriction of each continuous function against
normalized Haar measure on the compact group ideal. -/
theorem apply_eq_groupIdealHaar (i : G →ₙ* S) (hi : Continuous i)
    (hinjective : Function.Injective i) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (f : C_c(S, ℝ)) :
    m.functional f = ∫ g, f (i g) ∂normalizedHaar G := by
  have hμ := leftInvariantProbability_eq_groupIdealHaar i hi hinjective hleft habsorb
    (RealRMK.rieszMeasure m.functional)
  have hf : AEStronglyMeasurable (fun t => f t) ((normalizedHaar G).map i) :=
    f.continuous.aestronglyMeasurable
  rw [← RealRMK.integral_rieszMeasure, hμ, integral_map hi.measurable.aemeasurable hf]

end LeftInvariantContinuousMean

end Mean

section Stability

variable {S G E : Type*} [Semigroup S] [TopologicalSpace S] [CompactSpace S]
  [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The functional in the compact-host version of (9) applied to a matrix coefficient. -/
noncomputable def compactCoefficientMoment
    {hleft : ∀ s : S, Continuous (fun t => s * t)} (m : LeftInvariantContinuousMean hleft)
    (ρ : S →ₙ* (E →L[ℂ] E)) (x : E) (f : StrongDual ℂ E)
    (hcontinuous : Continuous (fun s => f (ρ s x))) (p : ℝ) (hp : 0 < p) : ℝ :=
  m.functional <| compactRealFunction (fun s => ‖f (ρ s x)‖ ^ p)
    (hcontinuous.norm.rpow_const (fun _ => Or.inr hp.le))

/-- Almost weak stability is equivalent to vanishing of all coefficient moments at any
positive power, and to vanishing at some common positive power. The mean here is the mean
on the compact semigroup, as represented in (11) of the paper. -/
theorem almostWeaklyStable_iff_continuousMeanMoments
    {hleft : ∀ s : S, Continuous (fun t => s * t)} (m : LeftInvariantContinuousMean hleft)
    (i : G →ₙ* S) (hi : Continuous i) (hinjective : Function.Injective i)
    (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (ρ : S →ₙ* (E →L[ℂ] E)) (x : E)
    (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun s => f (ρ s x))) :
    ((∃ s : S, ρ s x = 0) ↔ ∀ (p : ℝ) (hp : 0 < p) (f : StrongDual ℂ E),
        compactCoefficientMoment m ρ x f (hcontinuous f) p hp = 0) ∧
      ((∃ s : S, ρ s x = 0) ↔ ∃ (p : ℝ) (hp : 0 < p), ∀ f : StrongDual ℂ E,
        compactCoefficientMoment m ρ x f (hcontinuous f) p hp = 0) := by
  have hmoment (p : ℝ) (hp : 0 < p) (f : StrongDual ℂ E) :
      compactCoefficientMoment m ρ x f (hcontinuous f) p hp =
        ∫ s, ‖f (ρ s x)‖ ^ p ∂RealRMK.rieszMeasure m.functional :=
    (RealRMK.integral_rieszMeasure m.functional _).symm
  have hcriterion := almostWeaklyStable_iff_invariantProbabilityMoments i hi hinjective
    hleft habsorb ρ x hcontinuous (RealRMK.rieszMeasure m.functional)
  refine ⟨⟨fun hx p hp f => (hmoment p hp f).trans (hcriterion.1.mp hx p hp f), ?_⟩,
    ⟨?_, ?_⟩⟩
  · intro h
    exact hcriterion.1.mpr fun p hp f => (hmoment p hp f).symm.trans (h p hp f)
  · intro hx
    obtain ⟨p, hp, hf⟩ := hcriterion.2.mp hx
    exact ⟨p, hp, fun f => (hmoment p hp f).trans (hf f)⟩
  · rintro ⟨p, hp, hf⟩
    exact hcriterion.2.mpr ⟨p, hp, fun f => (hmoment p hp f).symm.trans (hf f)⟩

end Stability

end Mixing.JdLGBridge
