/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.AverageLimits
public import JdLG.MeasuredCriteria
public import JdLG.ReversibleHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.UrysohnsLemma

/-!
# Stability from left Følner averages

A family of averaging probabilities is left Følner when the normalized
integrals are asymptotically invariant uniformly over measurable tests
bounded by one. This test formulation uses the total-variation norm.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped CompactlySupported ENNReal Topology

namespace JdLG

section Averaging

variable {S I : Type*} [Semigroup S] [MeasurableSpace S]

/-- The left Følner total-variation condition for probability averages. -/
def LeftFolnerProbabilities (ν : I → Measure S) (l : Filter I) : Prop :=
  ∀ s : S, ∀ ε > 0, ∀ᶠ n in l, ∀ g : S → ℝ, Measurable g →
    (∀ t, ‖g t‖ ≤ 1) →
    ‖(∫ t, g (s * t) ∂ν n) - ∫ t, g t ∂ν n‖ < ε

/-- Normalized restriction to a Følner block. -/
noncomputable def normalizedRestrictedMeasure (measure : Measure S) (F : Set S) : Measure S :=
  (measure F)⁻¹ • measure.restrict F

omit [Semigroup S] in
theorem normalizedRestrictedMeasure_probability (measure : Measure S) {F : Set S}
    (hF₀ : measure F ≠ 0) (hFtop : measure F ≠ ∞) :
    IsProbabilityMeasure (normalizedRestrictedMeasure measure F) := by
  constructor
  simp only [normalizedRestrictedMeasure, smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel hF₀ hFtop]

omit [Semigroup S] in
theorem normalizedRestrictedMeasure_compl (measure : Measure S) {F : Set S}
    (hF : MeasurableSet F) : normalizedRestrictedMeasure measure F Fᶜ = 0 := by
  rw [normalizedRestrictedMeasure, smul_apply, Measure.restrict_apply hF.compl, compl_inter_self,
    measure_empty, smul_zero]

omit [Semigroup S] in
/-- If the measures of the averaging blocks grow without bound, every
fixed measurable set of finite measure has asymptotic mass zero. -/
theorem normalizedRestrictedMeasure_real_tendsto_zero (measure : Measure S) (F : I → Set S)
    {l : Filter I} (hF : Tendsto (fun n ↦ measure (F n)) l (𝓝 ∞))
    {C : Set S} (hCm : MeasurableSet C) (hC : measure C ≠ ∞) :
    Tendsto (fun n ↦ (normalizedRestrictedMeasure measure (F n)).real C) l (𝓝 0) := by
  have hi : Tendsto (fun n ↦ (measure (F n))⁻¹) l (𝓝 0) := by
    simpa only [one_div, ENNReal.inv_top] using
      (ENNReal.Tendsto.const_div (a := 1) hF (Or.inr ENNReal.one_ne_top))
  have hr := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hi
  rw [ENNReal.toReal_zero] at hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_mul] using hr.mul_const (measure.real C))
    (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  exact Eventually.of_forall fun n ↦ by
    rw [Measure.real, normalizedRestrictedMeasure, smul_apply, smul_eq_mul,
      ENNReal.toReal_mul, Measure.restrict_apply hCm]
    exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hC (measure_mono inter_subset_left)) ENNReal.toReal_nonneg

variable {T : Type*} [Semigroup T] [TopologicalSpace T] [SeparatelyContinuousMul T]
  [CompactSpace T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
  (i : S →ₙ* T) (hi : Measurable i)
  (ν : I → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
  {l : Filter I}

omit [T2Space T] in
include hi in
theorem LeftFolnerProbabilities.tendsto_defect (hν : LeftFolnerProbabilities ν l)
    (s : S) (f : C_c(T, ℝ)) :
    Tendsto (fun n ↦ continuousTestIntegral (fun n ↦ (ν n).map i) n
        (compactRealFunction (f ∘ (i s * ·)) (f.continuous.comp (continuous_const_mul (i s)))) -
        continuousTestIntegral (fun n ↦ (ν n).map i) n f) l (𝓝 0) := by
  let C := ‖f.toContinuousMap‖ + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  let g : S → ℝ := fun t ↦ C⁻¹ * f (i t)
  have hgbound (t : S) : ‖g t‖ ≤ 1 := by
    change ‖C⁻¹ * f (i t)‖ ≤ 1
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hC.le), ← div_eq_inv_mul,
      div_le_one hC]
    exact (f.toContinuousMap.norm_coe_le_norm (i t)).trans (le_add_of_nonneg_right zero_le_one)
  have hgm : Measurable g := measurable_const.mul (f.continuous.measurable.comp hi)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [hν s (ε / C) (div_pos hε hC)] with n hn
  have hs := hn g hgm hgbound
  let F := compactRealFunction (f ∘ (i s * ·)) (f.continuous.comp (continuous_const_mul (i s)))
  have hpre (j : C_c(T, ℝ)) :
      continuousTestIntegral (fun n ↦ (ν n).map i) n j = ∫ t, j (i t) ∂ν n :=
    integral_map hi.aemeasurable j.continuous.aestronglyMeasurable
  have he :
      (∫ t, g (s * t) ∂ν n) - ∫ t, g t ∂ν n =
        C⁻¹ * (continuousTestIntegral (fun n ↦ (ν n).map i) n F -
          continuousTestIntegral (fun n ↦ (ν n).map i) n f) := by
    simp only [hpre]
    change ((∫ t, C⁻¹ * f (i (s * t)) ∂ν n) - ∫ t, C⁻¹ * f (i t) ∂ν n) =
      C⁻¹ * ((∫ t, f (i s * i t) ∂ν n) - ∫ t, f (i t) ∂ν n)
    simp only [map_mul i, integral_const_mul, mul_sub]
  rw [he, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr hC.le), ← div_eq_inv_mul,
    div_lt_div_iff_of_pos_right hC] at hs
  rwa [dist_zero_right]

include hi hprob in
/-- Continuous test averages of a left Følner family converge to normalized
Haar integration on the group ideal of any compact host. -/
theorem LeftFolnerProbabilities.tendsto_integral (hd : DenseRange i)
    (hν : LeftFolnerProbabilities ν l) (K : GroupIdeal T)
    [CompactSpace K.carrier] [IsTopologicalGroup K.carrier]
    [MeasurableSpace K.carrier] [BorelSpace K.carrier] (f : C_c(T, ℝ)) :
    Tendsto (fun n ↦ ∫ t, f (i t) ∂ν n) l
      (𝓝 (∫ g : K.carrier, f g ∂normalizedHaar K.carrier)) := by
  have h := tendsto_testIntegral_of_left_asymptoticInvariant (fun n ↦ (ν n).map i)
    (fun n ↦ by
      let : IsProbabilityMeasure (ν n) := hprob n
      exact (Measure.isProbabilityMeasure_map_iff hi.aemeasurable).2 inferInstance)
    l i hd K (fun s f ↦ hν.tendsto_defect i hi ν s f) f
  have hpre (n : I) :
      continuousTestIntegral (fun n ↦ (ν n).map i) n f = ∫ t, f (i t) ∂ν n :=
    integral_map hi.aemeasurable f.continuous.aestronglyMeasurable
  simpa only [hpre] using h

end Averaging

section Operator

variable {S E I : Type*} [Semigroup S] [MeasurableSpace S]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (π : S →ₙ* (E →L[ℂ] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]
  (hπ : Measurable (closureInclusion π))
  (ν : I → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
  {l : Filter I} [l.NeBot]

include hπ hprob

/-- Theorem 4.2(i) and (v), for normalized probabilities of a left
Følner family. Every fixed positive exponent gives the same criterion. -/
theorem stable_iff_folnerCoefficientMoments (hν : LeftFolnerProbabilities ν l)
    (hadm : IsJdLGAdmissible π) (x : E) (p : ℝ) (hp : 0 < p) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ f : StrongDual ℂ E, Tendsto (fun n ↦ ∫ s, ‖f (π s x)‖ ^ p ∂ν n) l (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hadm
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  obtain ⟨m, _⟩ := K.exists_biInvariantMean hK (K.isTopologicalGroup_of_isCompact hK)
    (hleft := continuous_leftTranslate_weakOperatorClosure π)
    (hright := fun t ↦ continuous_mul_const t)
  let j : K.carrier →ₙ* weakOperatorClosure π := ⟨Subtype.val, fun _ _ ↦ rfl⟩
  have habsorb (t : weakOperatorClosure π) : ∃ g : K.carrier, j g = j 1 * t :=
    ⟨⟨K.identity * t, K.mul_mem_right K.identity_mem t⟩, rfl⟩
  have hlim (f : StrongDual ℂ E) :
      Tendsto (fun n ↦ ∫ s, ‖f (π s x)‖ ^ p ∂ν n) l
        (𝓝 (compactCoefficientMoment m (closureAction π) x f
          (continuous_closureAction_coefficient π x f) p hp)) := by
    let F := compactRealFunction (fun t ↦ ‖f (closureAction π t x)‖ ^ p)
      ((continuous_closureAction_coefficient π x f).norm.rpow_const (fun _ ↦ Or.inr hp.le))
    have h := hν.tendsto_integral (closureInclusion π) hπ ν hprob
      (denseRange_closureInclusion π) K F
    have hEq := m.apply_eq_groupIdealHaar j continuous_subtype_val Subtype.val_injective habsorb F
    change Tendsto (fun n ↦ ∫ s, F (closureInclusion π s) ∂ν n) l (𝓝 (m.functional F))
    rw [hEq]
    exact h
  rw [stable_iff_zero_mem_weakOrbitClosure hadm.1]
  have hc := weakOrbitClosure_iff_compactMeanMoments π K m x
  constructor
  · intro h f
    exact (hc.1.mp h p hp f) ▸ hlim f
  · intro h
    exact hc.2.mpr ⟨p, hp, fun f ↦ tendsto_nhds_unique (hlim f) (h f)⟩

omit [l.NeBot] in
/-- Almost weak stability makes every weak neighborhood return set have
asymptotic mass one along left Følner probabilities. -/
theorem folnerWeakReturns_of_stable (hν : LeftFolnerProbabilities ν l)
    (hadm : IsJdLGAdmissible π) {x : E} (hx : IsAlmostWeaklyStable (closureAction π) x)
    (U : Set (WeakSpace ℂ E)) (hU : IsOpen U) (h0 : 0 ∈ U) :
    Tendsto (fun n ↦ (ν n).real ((fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U)) l (𝓝 1) := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hadm
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let V := (fun t ↦ toWeakSpace ℂ E (closureAction π t x)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_weakOrbit_closureAction π x)
  have hdisj : Disjoint K.carrier Vᶜ := by
    apply disjoint_left.2
    intro t ht hnot
    have ht0 : closureAction π t x = 0 := by
      have htK := K.mul_identity ht
      have hx0 := (K.stable_iff_projection_eq_zero (closureAction π) x).mp hx
      change closureAction π K.identity x = 0 at hx0
      rw [← htK, map_mul]
      change closureAction π t (closureAction π K.identity x) = 0
      rw [hx0, map_zero]
    exact hnot (show toWeakSpace ℂ E (closureAction π t x) ∈ U from by
      rw [ht0, map_zero]; exact h0)
  obtain ⟨F, hFzero, hFone, hFIcc⟩ :=
    exists_continuous_zero_one_of_isClosed hK.isClosed hV.isClosed_compl hdisj
  let f := compactRealFunction F F.continuous
  have hlim := hν.tendsto_integral (closureInclusion π) hπ ν hprob
    (denseRange_closureInclusion π) K f
  have hzero : (∫ g : K.carrier, f g ∂normalizedHaar K.carrier) = 0 :=
    integral_eq_const (ae_of_all _ fun g ↦ hFzero g.property)
  rw [hzero] at hlim
  let A := (fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U
  have hA : MeasurableSet A := measurableSet_weakReturn π hπ x hU
  have hbad : Tendsto (fun n ↦ (ν n).real Aᶜ) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
    exact Eventually.of_forall fun n ↦ by
      let : IsProbabilityMeasure (ν n) := hprob n
      rw [← integral_indicator_one hA.compl]
      apply integral_mono
      · exact (integrable_const (1 : ℝ)).indicator hA.compl
      · exact Integrable.of_bound (F.continuous.measurable.comp hπ).aestronglyMeasurable 1
          (ae_of_all _ fun s ↦ by
            change ‖F (closureInclusion π s)‖ ≤ 1
            rw [Real.norm_of_nonneg (hFIcc (closureInclusion π s)).1]
            exact (hFIcc (closureInclusion π s)).2)
      · intro s
        by_cases hs : s ∈ Aᶜ
        · rw [indicator_of_mem hs]
          exact (hFone (show closureInclusion π s ∈ Vᶜ from hs)).symm.le
        · rw [indicator_of_notMem hs]
          exact (hFIcc (closureInclusion π s)).1
  have hm (n : I) : (ν n).real A = 1 - (ν n).real Aᶜ := by
    let : IsProbabilityMeasure (ν n) := hprob n
    rw [probReal_compl_eq_one_sub hA, sub_sub_cancel]
  have h1 : Tendsto (fun _ : I ↦ (1 : ℝ)) l (𝓝 1) := tendsto_const_nhds
  have hdiff := h1.sub hbad
  simp only [sub_zero] at hdiff
  exact hdiff.congr' (Eventually.of_forall fun n ↦ (hm n).symm)

/-- Theorem 4.2(i) and (vi), using full probability on each weak return
set. The converse uses the complement of the closed weak orbit. -/
theorem stable_iff_folnerWeakReturns (hν : LeftFolnerProbabilities ν l)
    (hadm : IsJdLGAdmissible π) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ U : Set (WeakSpace ℂ E), IsOpen U → 0 ∈ U →
        Tendsto (fun n ↦ (ν n).real ((fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U)) l (𝓝 1) := by
  refine ⟨folnerWeakReturns_of_stable π hπ ν hprob hν hadm, fun h ↦ ?_⟩
  rw [stable_iff_zero_mem_weakOrbitClosure hadm.1]
  by_contra hx
  let U := (closure (range fun s ↦ toWeakSpace ℂ E (π s x)))ᶜ
  have hu : (fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U = ∅ := by
    ext s
    exact ⟨fun hNo ↦ (hNo (subset_closure ⟨s, rfl⟩)).elim, fun hs ↦ hs.elim⟩
  have hlim := h U isClosed_closure.isOpen_compl hx
  rw [hu] at hlim
  have hlim₀ : Tendsto (fun n ↦ (ν n).real (∅ : Set S)) l (𝓝 0) := by
    simp only [measureReal_empty]
    exact tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hlim₀ hlim)

end Operator

section LowerFolnerDensity

variable {S E A : Type*} {I : A → Type*} [Nonempty A]
  [Semigroup S] [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (π : S →ₙ* (E →L[ℂ] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]

/-- Theorem 4.2(i) and (vii), with lower density given by the infimum
of the liminf densities along a nonempty family of left Følner nets. The
index type and filter may vary between nets. -/
theorem stable_iff_lowerFolnerDensityWeakReturns (hπ : Measurable (closureInclusion π))
    (hadm : IsJdLGAdmissible π) (x : E) (ν : ∀ a : A, I a → Measure S)
    (l : ∀ a, Filter (I a)) (hl : ∀ a, NeBot (l a))
    (hp : ∀ a n, IsProbabilityMeasure (ν a n))
    (hf : ∀ a, LeftFolnerProbabilities (ν a) (l a)) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ U : Set (WeakSpace ℂ E), IsOpen U → 0 ∈ U →
        sInf (range fun a : A ↦ liminf
          (fun n ↦ (ν a n).real ((fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U)) (l a)) = 1 := by
  constructor
  · intro hx U hU h0
    have ht (a : A) : liminf
        (fun n ↦ (ν a n).real ((fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U)) (l a) = 1 := by
      let : NeBot (l a) := hl a
      exact (folnerWeakReturns_of_stable π hπ (ν a) (hp a) (hf a) hadm hx U hU h0).liminf_eq
    simp only [ht, range_const, csInf_singleton]
  · intro h
    rw [stable_iff_zero_mem_weakOrbitClosure hadm.1]
    by_contra hx
    let U := (closure (range fun s ↦ toWeakSpace ℂ E (π s x)))ᶜ
    have hu : (fun s ↦ toWeakSpace ℂ E (π s x)) ⁻¹' U = ∅ := by
      ext s
      exact ⟨fun hNo ↦ (hNo (subset_closure ⟨s, rfl⟩)).elim, fun hs ↦ hs.elim⟩
    have ht (a : A) : liminf (fun n ↦ (ν a n).real (∅ : Set S)) (l a) = 0 := by
      let : NeBot (l a) := hl a
      simp only [measureReal_empty, liminf_const]
    have hno := h U isClosed_closure.isOpen_compl hx
    simp only [hu, ht, range_const, csInf_singleton] at hno
    exact zero_ne_one hno

end LowerFolnerDensity

end JdLG
