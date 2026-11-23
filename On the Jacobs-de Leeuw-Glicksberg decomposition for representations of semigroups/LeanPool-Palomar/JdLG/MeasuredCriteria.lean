/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MeasuredTransfer

/-!
# Stability criteria on measured semigroups

The compact-host moment characterization pulls back to the given measured
semigroup, where an arbitrary left-invariant L∞ mean and lower left Banach
density give equivalent criteria.
-/

@[expose] public section

open MeasureTheory Set
open scoped CompactlySupported ENNReal Topology

namespace JdLG

variable {S E : Type*} [Semigroup S] [MeasurableSpace S] {μ : Measure S}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : S →ₙ* (E →L[ℂ] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]
  (hπ : Measurable (closureInclusion π))

/-- The upper bound of a coefficient on the compact operator closure. -/
noncomputable def coefficientBound (x : E) (f : StrongDual ℂ E) : ℝ :=
  ‖(⟨(fun s ↦ f (closureAction π s x)), continuous_closureAction_coefficient π x f⟩ :
    C(weakOperatorClosure π, ℂ))‖

omit [MeasurableSpace S] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)] in
theorem norm_coefficient_le_coefficientBound (x : E) (f : StrongDual ℂ E) (s : S) :
    ‖f (π s x)‖ ≤ coefficientBound π x f := by
  let g : C(weakOperatorClosure π, ℂ) :=
    ⟨(fun t ↦ f (closureAction π t x)), continuous_closureAction_coefficient π x f⟩
  exact g.norm_coe_le_norm (closureInclusion π s)

include hπ

omit [CompactSpace (weakOperatorClosure π)] in
theorem measurable_coefficient (x : E) (f : StrongDual ℂ E) :
    Measurable fun s : S ↦ f (π s x) :=
  (continuous_closureAction_coefficient π x f).measurable.comp hπ

omit [CompactSpace (weakOperatorClosure π)] in
theorem measurableSet_weakReturn (x : E) {U : Set (WeakSpace ℂ E)} (hU : IsOpen U) :
    MeasurableSet ((fun s : S ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U) :=
  (hU.preimage (continuous_weakOrbit_closureAction π x)).measurableSet.preimage hπ

/-- Bi-amenability of the measured semigroup supplies admissibility for a
relatively weakly compact, measurably represented semigroup. This is the
measured-semigroup case of Corollary 1.4. -/
theorem admissible_of_measuredBiInvariantMean (b : MeasuredMean μ)
    (hbL : b.IsLeftInvariant) (hbR : b.IsRightInvariant) : IsJdLGAdmissible π := by
  let m := b.toContinuousMean (closureInclusion π) hπ
    (fun t ↦ continuous_const_mul t) (fun t ↦ continuous_mul_const t)
    (denseRange_closureInclusion π) hbL
  have hR : m.IsRightInvariant (fun t ↦ continuous_mul_const t) :=
    b.toContinuousMean_rightInvariant (closureInclusion π) hπ
      (fun t ↦ continuous_const_mul t) (fun t ↦ continuous_mul_const t)
      (denseRange_closureInclusion π) hbL hbR
  exact ⟨isCompact_iff_compactSpace.mpr inferInstance,
    m.existsUnique_minimalIdempotent_of_biInvariant hR⟩

/-- The coefficient moment in part (ii) of Theorem 4.2. -/
noncomputable def measuredCoefficientMoment (m : MeasuredMean μ)
    (x : E) (f : StrongDual ℂ E) (p : ℝ) (hp : 0 < p) : ℝ :=
  m.value (fun s ↦ ‖f (π s x)‖ ^ p)
    (MeasuredMean.memLp_norm_rpow (measurable_coefficient π hπ x f) hp
      (norm_coefficient_le_coefficientBound π x f))

/-- The equivalence between almost weak stability and all coefficient
moments in Theorem 4.2(i)–(ii), valid for any single positive exponent. -/
theorem stable_iff_measuredCoefficientMoments (hadm : IsJdLGAdmissible π) (m : MeasuredMean μ)
    (hm : m.IsLeftInvariant) (x : E) (p : ℝ) (hp : 0 < p) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ f : StrongDual ℂ E, measuredCoefficientMoment π hπ m x f p hp = 0 := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hadm
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let mT := m.toContinuousMean (closureInclusion π) hπ
    (continuous_leftTranslate_weakOperatorClosure π) (fun t ↦ continuous_mul_const t)
    (denseRange_closureInclusion π) hm
  have h := (weakOrbitClosure_iff_compactMeanMoments π K mT x).2
  rw [stable_iff_zero_mem_weakOrbitClosure hadm.1]
  refine ⟨fun hx f ↦ ?_, fun hs ↦ h.mpr ⟨p, hp, ?_⟩⟩
  · have hh := ((weakOrbitClosure_iff_compactMeanMoments π K mT x).1.mp hx) p hp f
    exact hh
  · intro f
    exact hs f

/-- Theorem 4.2(i)–(iii) stated through weakly open returns of full mean. -/
theorem stable_iff_measuredWeakReturns (hadm : IsJdLGAdmissible π) (m : MeasuredMean μ)
    (hm : m.IsLeftInvariant) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ U : Set (WeakSpace ℂ E), ∀ hU : IsOpen U, 0 ∈ U →
        m.mass ((fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U)
          (measurableSet_weakReturn π hπ x hU) = 1 := by
  refine (stable_iff_measuredCoefficientMoments π hπ hadm m hm x 1 zero_lt_one).trans ?_
  exact (m.weakReturns_iff_coefficientMoments (fun s ↦ π s x)
    (fun _ hU ↦ measurableSet_weakReturn π hπ x hU) (measurable_coefficient π hπ x)
    (coefficientBound π x) (norm_coefficient_le_coefficientBound π x) 1 zero_lt_one).symm

/-- Theorem 4.2(i)–(iv) with literal lower left Banach density, the infimum
over the masses assigned by all left-invariant means. -/
theorem stable_iff_lowerBanachDensityWeakReturns (b : MeasuredMean μ)
    (hbL : b.IsLeftInvariant) (hbR : b.IsRightInvariant) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ U : Set (WeakSpace ℂ E), ∀ hU : IsOpen U, 0 ∈ U →
        MeasuredMean.lowerBanachDensity (measure := μ)
          ((fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U)
          (measurableSet_weakReturn π hπ x hU) = 1 := by
  have hadm := admissible_of_measuredBiInvariantMean π hπ b hbL hbR
  constructor
  · intro hx U hU h0
    refine (MeasuredMean.lowerBanachDensity_eq_one_iff b hbL _ _).2 fun m hm ↦ ?_
    exact (stable_iff_measuredWeakReturns π hπ hadm m hm x).1 hx U hU h0
  · intro hh
    refine (stable_iff_measuredWeakReturns π hπ hadm b hbL x).2 fun U hU h0 ↦ ?_
    exact (MeasuredMean.lowerBanachDensity_eq_one_iff b hbL _ _).1 (hh U hU h0) b hbL

end JdLG
