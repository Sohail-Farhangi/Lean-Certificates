/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar coefficients on the almost weakly stable part

Lemma 4.1 of Barthmann, Farhangi and Kuznetsova, arXiv:2509.24003v3, uses the
compact group ideal of the weakly almost periodic compactification. This file
proves the coefficient criterion on a compact group ideal using normalized Haar
measure and continuous matrix coefficients.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped BigOperators

namespace Mixing.JdLGBridge

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized to give the whole compact group mass one. -/
noncomputable def normalizedHaar : Measure G :=
  Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩

instance : (normalizedHaar G).IsHaarMeasure := by
  unfold normalizedHaar
  infer_instance

instance : IsProbabilityMeasure (normalizedHaar G) where
  measure_univ := by
    unfold normalizedHaar
    exact Measure.haarMeasure_self

end CompactGroup

section InvariantMeasure

variable {S G : Type*} [Semigroup S] [TopologicalSpace S] [T2Space S]
  [MeasurableSpace S] [BorelSpace S]
  [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The retraction onto the compact group ideal transports every left-invariant probability
to a full-support left-invariant probability on the group. Joint continuity of multiplication
is unnecessary for this transfer. -/
theorem exists_fullSupportProbability_groupIdeal (i : G →ₙ* S) (hi : Continuous i)
    (hinjective : Function.Injective i) (hleft : ∀ s : S, Continuous (fun t => s * t))
    (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s) (μ : Measure S)
    [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ Measure.IsMulLeftInvariant ν ∧
      ν.IsOpenPosMeasure ∧ μ = ν.map i := by
  have hembedding := (hi.isClosedEmbedding hinjective).isEmbedding
  let p : S → G := fun s => (habsorb s).choose
  have hpi (s : S) : i (p s) = i 1 * s := (habsorb s).choose_spec
  have hp : Continuous p := by
    apply hembedding.continuous_iff.mpr
    rw [show i ∘ p = fun s => i 1 * s from funext hpi]
    exact hleft (i 1)
  have hgleft (g : G) : Continuous (fun t : G => g * t) := by
    apply hembedding.continuous_iff.mpr
    change Continuous (fun t : G => i (g * t))
    simpa only [map_mul, Function.comp_def] using (hleft (i g)).comp hi
  let ν : Measure G := μ.map p
  have hνprobability : IsProbabilityMeasure ν := by
    unfold ν
    infer_instance
  have hνinvariant : Measure.IsMulLeftInvariant ν := ⟨fun g => by
    have heq : (g * ·) ∘ p = p ∘ (i g * ·) := by
      funext s
      apply hinjective
      change i (g * p s) = i (p (i g * s))
      rw [map_mul, hpi, hpi, ← mul_assoc, ← map_mul, mul_one, ← mul_assoc, ← map_mul, one_mul]
    unfold ν
    rw [Measure.map_map (hgleft g).measurable hp.measurable, heq,
      ← Measure.map_map hp.measurable (hleft (i g)).measurable,
      Measure.IsMulLeftInvariant.map_mul_left_eq_self]⟩
  have hνfullSupport : ν.IsOpenPosMeasure := by
    constructor
    intro U hU hnonempty hzero
    obtain ⟨u, hu⟩ := hnonempty
    let cover : G → Set G := fun g => (g * ·) ⁻¹' U
    have hcover : (univ : Set G) ⊆ ⋃ g, cover g := by
      intro t _
      apply mem_iUnion.mpr
      exact ⟨u * t⁻¹, by simpa [cover, mul_assoc] using hu⟩
    obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover cover
      (fun g => hU.preimage (hgleft g)) hcover
    have hnull (g : G) : ν (cover g) = 0 := by
      rw [show ν (cover g) = (ν.map (g * ·)) U from
        (Measure.map_apply (hgleft g).measurable hU.measurableSet).symm,
        hνinvariant.map_mul_left_eq_self g, hzero]
    have hle : ν univ ≤ 0 := calc
      ν univ ≤ ν (⋃ g ∈ F, cover g) := measure_mono hF
      _ ≤ ∑ g ∈ F, ν (cover g) := measure_biUnion_finset_le _ _
      _ = 0 := by simp only [hnull, Finset.sum_const_zero]
    simp [hνprobability.measure_univ] at hle
  refine ⟨ν, hνprobability, hνinvariant, hνfullSupport, ?_⟩
  unfold ν
  rw [Measure.map_map hi.measurable hp.measurable,
    show i ∘ p = (i 1 * ·) from funext hpi, Measure.IsMulLeftInvariant.map_mul_left_eq_self]

/-- If the compact ideal is a topological group, an invariant probability is the pushforward
of its normalized Haar measure. -/
theorem leftInvariantProbability_eq_groupIdealHaar [IsTopologicalGroup G]
    (i : G →ₙ* S) (hi : Continuous i) (hinjective : Function.Injective i)
    (hleft : ∀ s : S, Continuous (fun t => s * t)) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (μ : Measure S) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] :
    μ = (normalizedHaar G).map i := by
  obtain ⟨ν, hνprobability, hνinvariant, _, hμ⟩ :=
    exists_fullSupportProbability_groupIdeal i hi hinjective hleft habsorb μ
  have : ν.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior ν univ isCompact_univ
      (by simp) (by simp) (by simp)
  have hν : ν = normalizedHaar G := Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν _
  rwa [← hν]

end InvariantMeasure

section Annihilator

variable {S G E : Type*} [Semigroup S] [Group G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A vector killed by one semigroup element is killed by the identity of the group ideal.
The range condition is the absorption used in this implication. -/
theorem exists_annihilator_iff_group_identity (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s) (x : E) :
    (∃ s : S, ρ s x = 0) ↔ ρ (i 1) x = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨g, hg⟩ := habsorb s
    have hzero : ρ (i g) x = 0 := by
      rw [hg, map_mul]
      change ρ (i 1) (ρ s x) = 0
      rw [hs, map_zero]
    have heq : ρ (i (g⁻¹ * g)) x = ρ (i g⁻¹) (ρ (i g) x) := by
      simp only [map_mul]; rfl
    rw [inv_mul_cancel, hzero, map_zero] at heq
    exact heq
  · intro hx
    exact ⟨i 1, hx⟩

end Annihilator

section Coefficients

variable {S G E : Type*} [Semigroup S] [Group G] [TopologicalSpace G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Haar integral of a power of the norm of a scalar coefficient. -/
noncomputable def haarCoefficientMoment [IsTopologicalGroup G]
    (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (x : E) (f : StrongDual ℂ E) (p : ℝ) : ℝ :=
  ∫ g, ‖f (ρ (i g) x)‖ ^ p ∂normalizedHaar G

/-- For a weakly continuous orbit on the group ideal, the moment at any positive power for a
full-support measure vanishes exactly when the identity of the group ideal kills the vector. -/
theorem fullSupportCoefficientMoments_eq_zero_iff (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (x : E) (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun g => f (ρ (i g) x)))
    (ν : Measure G) [IsFiniteMeasure ν] [ν.IsOpenPosMeasure]
    {p : ℝ} (hp : 0 < p) :
    (∀ f : StrongDual ℂ E, (∫ g, ‖f (ρ (i g) x)‖ ^ p ∂ν) = 0) ↔ ρ (i 1) x = 0 := by
  constructor
  · intro h
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro f
    let integrand : G → ℝ := fun g => ‖f (ρ (i g) x)‖ ^ p
    have hcont : Continuous integrand := (hcontinuous f).norm.rpow_const (fun _ => Or.inr hp.le)
    have hnneg : 0 ≤ integrand := fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have haezero := (integral_eq_zero_iff_of_nonneg hnneg
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp (h f)
    have heq := (hcont.ae_eq_iff_eq ν continuous_zero).mp haezero
    have hone : ‖f (ρ (i 1) x)‖ ^ p = 0 := congrFun heq 1
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hp.ne').mp hone)
  · intro h f
    have hzero (g : G) : ρ (i g) x = 0 := by
      have heq : ρ (i (g * 1)) x = ρ (i g) (ρ (i 1) x) := by simp only [map_mul]; rfl
      rw [mul_one, h, map_zero] at heq
      exact heq
    simp [hzero, Real.zero_rpow hp.ne']

/-- The equivalence specialized to normalized Haar measure on a compact topological group. -/
theorem haarCoefficientMoments_eq_zero_iff [IsTopologicalGroup G]
    (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (x : E) (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun g => f (ρ (i g) x)))
    {p : ℝ} (hp : 0 < p) :
    (∀ f : StrongDual ℂ E, haarCoefficientMoment i ρ x f p = 0) ↔ ρ (i 1) x = 0 :=
  fullSupportCoefficientMoments_eq_zero_iff i ρ x hcontinuous (normalizedHaar G) hp

/-- The three clauses of the Haar coefficient criterion, on the compact group ideal of a
semigroup of operators. In particular, vanishing for one common positive power suffices. -/
theorem almostWeaklyStable_iff_haarCoefficientMoments [IsTopologicalGroup G] (i : G →ₙ* S)
    (ρ : S →ₙ* (E →L[ℂ] E)) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (x : E) (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun g => f (ρ (i g) x))) :
    ((∃ s : S, ρ s x = 0) ↔ ∀ p : ℝ, 0 < p → ∀ f : StrongDual ℂ E,
        haarCoefficientMoment i ρ x f p = 0) ∧
      ((∃ s : S, ρ s x = 0) ↔ ∃ p : ℝ, 0 < p ∧ ∀ f : StrongDual ℂ E,
        haarCoefficientMoment i ρ x f p = 0) := by
  have hannihilator := exists_annihilator_iff_group_identity i ρ habsorb x
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hx p hp
    exact (haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous hp).2 (hannihilator.1 hx)
  · intro h
    exact hannihilator.2 ((haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous zero_lt_one).1
      (h 1 zero_lt_one))
  · intro hx
    exact ⟨1, zero_lt_one, (haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous zero_lt_one).2
      (hannihilator.1 hx)⟩
  · rintro ⟨p, hp, h⟩
    exact hannihilator.2 ((haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous hp).1 h)

/-- The almost weak stability criterion for any left-invariant probability on the compact
semigroup, expressed through its scalar matrix coefficients. -/
theorem almostWeaklyStable_iff_invariantProbabilityMoments
    [TopologicalSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    (i : G →ₙ* S) (hi : Continuous i) (hinjective : Function.Injective i)
    (hleft : ∀ s : S, Continuous (fun t => s * t)) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (ρ : S →ₙ* (E →L[ℂ] E)) (x : E)
    (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun s => f (ρ s x)))
    (μ : Measure S) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] :
    ((∃ s : S, ρ s x = 0) ↔ ∀ p : ℝ, 0 < p → ∀ f : StrongDual ℂ E,
        (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = 0) ∧
      ((∃ s : S, ρ s x = 0) ↔ ∃ p : ℝ, 0 < p ∧ ∀ f : StrongDual ℂ E,
        (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = 0) := by
  obtain ⟨ν, hνprobability, _, hνsupport, hμ⟩ :=
    exists_fullSupportProbability_groupIdeal i hi hinjective hleft habsorb μ
  have hmoments (p : ℝ) (hp : 0 < p) (f : StrongDual ℂ E) :
      (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = ∫ g, ‖f (ρ (i g) x)‖ ^ p ∂ν := by
    have hf : Continuous (fun s => ‖f (ρ s x)‖ ^ p) :=
      (hcontinuous f).norm.rpow_const (fun _ => Or.inr hp.le)
    rw [hμ, integral_map hi.measurable.aemeasurable hf.aestronglyMeasurable]
  have hcriterion (p : ℝ) (hp : 0 < p) :
      (∀ f : StrongDual ℂ E, (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = 0) ↔ ∃ s : S, ρ s x = 0 := by
    simp_rw [hmoments p hp]
    exact (fullSupportCoefficientMoments_eq_zero_iff i ρ x (fun f =>
      (hcontinuous f).comp hi) ν hp).trans
        (exists_annihilator_iff_group_identity i ρ habsorb x).symm
  refine ⟨⟨fun hx p hp => (hcriterion p hp).2 hx, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    exact (hcriterion 1 zero_lt_one).1 (h 1 zero_lt_one)
  · intro hx
    exact ⟨1, zero_lt_one, (hcriterion 1 zero_lt_one).2 hx⟩
  · rintro ⟨p, hp, hf⟩
    exact (hcriterion p hp).1 hf

end Coefficients

end Mixing.JdLGBridge
