/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mixing.SupportingJdLG.StableOperator
public import Mathlib.MeasureTheory.Measure.Support

/-!
# The group ideal of a bi-invariant mean

A bi-invariant mean on a compact semitopological semigroup gives a compact group ideal.
The ideal is the support of the regular probability measure representing the mean.
-/

@[expose] public section

open MeasureTheory Set
open scoped CompactlySupported

namespace Mixing.JdLGBridge

/-- For a continuous map from a compact Hausdorff space, pushing forward a regular measure
takes its support to the image of its support. -/
theorem support_map_eq_image_of_compact {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure X) [μ.Regular]
    {f : X → Y} (hf : Continuous f) : (μ.map f).support = f '' μ.support := by
  have hclosed : IsClosed (f '' μ.support) :=
    ((Measure.isClosed_support (μ := μ)).isCompact.image hf).isClosed
  apply le_antisymm
  · apply Measure.support_subset_of_isClosed hclosed
    change (μ.map f) (f '' μ.support)ᶜ = 0
    rw [Measure.map_apply hf.measurable hclosed.isOpen_compl.measurableSet]
    apply measure_mono_null _ (Measure.measure_compl_support_of_regular (μ := μ))
    exact fun x hx hxSupport => hx ⟨x, hxSupport, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Measure.support_eq_forall_isOpen] at hx ⊢
    intro U hxU hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    exact hx _ hxU (hU.preimage hf)

section Ideal

variable {S : Type*} [Semigroup S] [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [MeasurableSpace S] [BorelSpace S]

/-- The support of a regular two-sided invariant probability is a compact group ideal. -/
theorem exists_groupIdeal_of_biInvariantProbability
    (hleft : ∀ s : S, Continuous (s * ·)) (hright : ∀ s : S, Continuous (· * s))
    (μ : Measure S) [IsProbabilityMeasure μ] [μ.Regular]
    [Measure.IsMulLeftInvariant μ] [Measure.IsMulRightInvariant μ] :
    ∃ K : GroupIdeal S, K.carrier = μ.support := by
  have hL (s : S) : (s * ·) '' μ.support = μ.support := by
    rw [← support_map_eq_image_of_compact μ (hleft s),
      Measure.IsMulLeftInvariant.map_mul_left_eq_self]
  have hR (s : S) : (· * s) '' μ.support = μ.support := by
    rw [← support_map_eq_image_of_compact μ (hright s),
      Measure.IsMulRightInvariant.map_mul_right_eq_self]
  have hn : μ.support.Nonempty := by
    by_contra h
    have hEmpty := Set.not_nonempty_iff_eq_empty.mp h
    have hnull := Measure.measure_compl_support_of_regular (μ := μ)
    simp [hEmpty] at hnull
  have hclosed : IsCompact μ.support := (Measure.isClosed_support (μ := μ)).isCompact
  have hleftMem (s : S) {a : S} (ha : a ∈ μ.support) : s * a ∈ μ.support :=
    hL s ▸ ⟨a, ha, rfl⟩
  have hrightMem {a : S} (ha : a ∈ μ.support) (s : S) : a * s ∈ μ.support :=
    hR s ▸ ⟨a, ha, rfl⟩
  obtain ⟨e, he, hee⟩ := exists_idempotent_in_compact_subsemigroup hright μ.support hn hclosed
    (fun a _ _ hb => hleftMem a hb)
  have hleftId {a : S} (ha : a ∈ μ.support) : e * a = a := by
    obtain ⟨b, _, rfl⟩ := show a ∈ (e * ·) '' μ.support from (hL e).symm ▸ ha
    rw [← mul_assoc, hee]
  have hrightId {a : S} (ha : a ∈ μ.support) : a * e = a := by
    obtain ⟨b, _, rfl⟩ := show a ∈ (· * e) '' μ.support from (hR e).symm ▸ ha
    rw [mul_assoc, hee]
  refine ⟨⟨μ.support, e, he, hleftMem, @hrightMem, @hleftId, @hrightId, ?_⟩, rfl⟩
  intro a ha
  obtain ⟨b, hb, hab⟩ := show e ∈ (a * ·) '' μ.support from (hL a).symm ▸ he
  obtain ⟨c, hc, hca⟩ := show e ∈ (· * a) '' μ.support from (hR a).symm ▸ he
  change a * b = e at hab
  change c * a = e at hca
  have hcb : c = b := calc
    c = c * e := (hrightId hc).symm
    _ = c * (a * b) := by rw [hab]
    _ = (c * a) * b := (mul_assoc _ _ _).symm
    _ = e * b := by rw [hca]
    _ = b := hleftId hb
  exact ⟨b, hb, hcb ▸ hca, hab⟩

namespace LeftInvariantContinuousMean

variable {hleft : ∀ s : S, Continuous (s * ·)} (m : LeftInvariantContinuousMean hleft)

/-- Right invariance for a left-invariant positive functional. -/
def IsRightInvariant (hright : ∀ s : S, Continuous (· * s)) : Prop :=
  ∀ (s : S) (f : C_c(S, ℝ)),
    m.functional (compactRealFunction (fun t => f (t * s)) (f.continuous.comp (hright s))) =
      m.functional f

/-- Right invariance of the mean gives right invariance of the representing measure. -/
theorem rieszMeasure_rightInvariant {hright : ∀ s : S, Continuous (· * s)}
    (hm : m.IsRightInvariant hright) : Measure.IsMulRightInvariant
      (RealRMK.rieszMeasure m.functional) := by
  constructor
  intro s
  let μ := RealRMK.rieszMeasure m.functional
  let translation : S → S := fun t => t * s
  have htranslation : Continuous translation := hright s
  have : IsFiniteMeasure (μ.map translation) := μ.isFiniteMeasure_map translation
  have : (μ.map translation).InnerRegular := Measure.InnerRegular.map_of_continuous htranslation
  change μ.map translation = μ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf : AEStronglyMeasurable (fun t => f t) (μ.map translation) :=
    f.continuous.aestronglyMeasurable
  rw [integral_map htranslation.measurable.aemeasurable hf]
  have h := RealRMK.integral_rieszMeasure m.functional
    (compactRealFunction (fun t => f (t * s)) (f.continuous.comp (hright s)))
  exact h.trans ((hm s f).trans (RealRMK.integral_rieszMeasure m.functional f).symm)

/-- The forward implication in the minimal-idempotent criterion of Theorem 1.1,
from a bi-invariant mean on continuous functions to a compact group ideal. -/
theorem exists_compact_groupIdeal_of_biInvariant {hright : ∀ s : S, Continuous (· * s)}
    (hm : m.IsRightInvariant hright) : ∃ K : GroupIdeal S, IsCompact K.carrier := by
  have := m.rieszMeasure_rightInvariant hm
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_biInvariantProbability hleft hright
    (RealRMK.rieszMeasure m.functional)
  exact ⟨K, hK ▸ (Measure.isClosed_support.isCompact :
    IsCompact (RealRMK.rieszMeasure m.functional).support)⟩

/-- A normalized bi-invariant mean gives a unique minimal idempotent. -/
theorem existsUnique_minimalIdempotent_of_biInvariant {hright : ∀ s : S, Continuous (· * s)}
    (hm : m.IsRightInvariant hright) : ∃! e : S, IsMinimalIdempotent e :=
  (exists_compact_groupIdeal_iff_existsUnique_minimalIdempotent hright).mp
    (m.exists_compact_groupIdeal_of_biInvariant hm)

end LeftInvariantContinuousMean

/-- Lemma 4.1 on a compact semitopological host with a bi-invariant mean. The compact
group ideal is obtained from the mean, supplying all the assumptions of the criterion. -/
theorem almostWeaklyStable_iff_biInvariantMeanMoments
    {hleft : ∀ s : S, Continuous (s * ·)} {hright : ∀ s : S, Continuous (· * s)}
    (m : LeftInvariantContinuousMean hleft) (hm : m.IsRightInvariant hright)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : S →ₙ* (E →L[ℂ] E)) (x : E)
    (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun s => f (ρ s x))) :
    ((∃ s : S, ρ s x = 0) ↔ ∀ (p : ℝ) (hp : 0 < p) (f : StrongDual ℂ E),
        compactCoefficientMoment m ρ x f (hcontinuous f) p hp = 0) ∧
      ((∃ s : S, ρ s x = 0) ↔ ∃ (p : ℝ) (hp : 0 < p), ∀ f : StrongDual ℂ E,
        compactCoefficientMoment m ρ x f (hcontinuous f) p hp = 0) := by
  obtain ⟨K, hK⟩ := m.exists_compact_groupIdeal_of_biInvariant hm
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let i : K.carrier →ₙ* S := ⟨Subtype.val, fun _ _ => rfl⟩
  have habsorb (s : S) : ∃ g : K.carrier, i g = i 1 * s :=
    ⟨⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩, rfl⟩
  exact almostWeaklyStable_iff_continuousMeanMoments m i continuous_subtype_val
    Subtype.val_injective habsorb ρ x hcontinuous

end Ideal

end Mixing.JdLGBridge
