/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.WeakCompactCountableChain
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Density-one weak decay without separability

The common support of the countably many Radon pushforwards is weakly
compact and satisfies the countable chain condition. We obtain the
countable neighborhood basis on this support and apply the compact
exhaustion argument to the original sampling probabilities.
-/

@[expose] public section

namespace JdLG

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "W" => WeakSpace ℂ E

/-- A countable family of compact-inner-regular probabilities concentrated
on a weakly compact set has a common weakly compact first-countable support. -/
theorem exists_firstCountable_common_weakSupport [MeasurableSpace W] [BorelSpace W]
    (m : ℕ → Measure W) (hp : ∀ n, IsProbabilityMeasure (m n))
    (hr : ∀ n, (m n).InnerRegularWRT IsCompact IsOpen)
    {K : Set W} (hK : IsCompact K) (hK₀ : ∀ n, m n Kᶜ = 0) :
    ∃ H : Set W, H ⊆ K ∧ IsCompact H ∧ FirstCountableTopology H ∧ ∀ n, m n Hᶜ = 0 := by
  let μ := Measure.sum m
  let H := μ.support
  let (n : ℕ) : IsProbabilityMeasure (m n) := hp n
  let : SFinite μ := inferInstanceAs (SFinite (Measure.sum m))
  have hKμ : K ∈ ae μ := by
    change Measure.sum m Kᶜ = 0
    rw [Measure.sum_apply _ hK.isClosed.isOpen_compl.measurableSet]
    simp only [hK₀, tsum_zero]
  have hHc : IsClosed H := Measure.isClosed_support
  have hsub : H ⊆ K := Measure.support_subset_of_isClosed hK.isClosed hKμ
  have hH : IsCompact H := hK.of_isClosed_subset hHc hsub
  have hz (n : ℕ) : m n Hᶜ = 0 := by
    by_contra hn
    obtain ⟨C, hCs, hCc, hCp⟩ := hr n hHc.isOpen_compl 0 (pos_iff_ne_zero.2 hn)
    have hzero : μ C = 0 := Measure.measure_eq_zero_of_isCompact_subset_compl_support hCc hCs
    have hl : m n C ≤ μ C := Measure.le_sum m n C
    exact (not_lt_of_ge (hzero ▸ hl)) hCp
  have hμz : μ Hᶜ = 0 := by
    change Measure.sum m Hᶜ = 0
    rw [Measure.sum_apply _ hHc.isOpen_compl.measurableSet]
    simp only [hz, tsum_zero]
  refine ⟨H, hsub, hH, firstCountableTopology_weakCompact_of_ccc hH ?_, hz⟩
  intro D hD ho
  let A (U : D) := (Subtype.val : H → W) '' U.val
  have hAV (U : D) : ∃ V : Set W, IsOpen V ∧
      (Subtype.val : H → W) ⁻¹' V = U.val ∧ A U = V ∩ H := by
    obtain ⟨V, hV, he⟩ := isOpen_induced_iff.1 (ho U.val U.property).1
    refine ⟨V, hV, he, ?_⟩
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, v.property⟩
      change v ∈ (Subtype.val : H → W) ⁻¹' V
      rwa [he]
    · rintro ⟨hv, hh⟩
      exact ⟨⟨x, hh⟩, he.symm ▸ hv, rfl⟩
  have hAm (U : D) : MeasurableSet (A U) := by
    obtain ⟨V, hV, _, hA⟩ := hAV U
    rw [hA]
    exact hV.measurableSet.inter hHc.measurableSet
  have hAp (U : D) : 0 < μ (A U) := by
    obtain ⟨V, hV, he, hA⟩ := hAV U
    obtain ⟨x, hx⟩ := (ho U.val U.property).2
    have hxV : x.val ∈ V := by
      change x ∈ (Subtype.val : H → W) ⁻¹' V
      rwa [he]
    rw [hA, measure_inter_conull hμz]
    exact (Measure.mem_support_iff_forall _).1 x.property V (hV.mem_nhds hxV)
  have hd : Pairwise (Disjoint on A) := by
    intro U V hUV
    exact disjoint_image_of_injective Subtype.val_injective
      (hD U.property V.property (fun h ↦ hUV (Subtype.ext h)))
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hAm hd
  have he : {U : D | 0 < μ (A U)} = univ := eq_univ_of_forall hAp
  rw [he] at hc
  exact countable_univ_iff.1 hc

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]

/-- If all weak neighborhoods of a limit point have asymptotically full
sampling mass, compact-inner-regular probabilities give a single measurable
set of full density on which the weak limit holds along the cocompact filter. -/
theorem exists_density_one_weak_tendsto_of_innerRegular
    (ν : ℕ → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    (hreg : ∀ n, (ν n).InnerRegularWRT IsCompact IsOpen)
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFm : ∀ n, MeasurableSet (F n))
    (hsupp : ∀ n, ν n (F n)ᶜ = 0) (φ : S → W) (hφ : Continuous φ)
    [OpensMeasurableSpace S]
    {K : Set W} (hK : IsCompact K) (hφK : range φ ⊆ K) (y : W)
    (hret : ∀ U : Set W, IsOpen U → y ∈ U →
      Tendsto (fun n ↦ (ν n).real (φ ⁻¹' U)) atTop (𝓝 1)) :
    ∃ A : Set S, MeasurableSet A ∧ Tendsto (fun n ↦ (ν n).real A) atTop (𝓝 1) ∧
      Tendsto φ (cocompact S ⊓ 𝓟 A) (𝓝 y) := by
  classical
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let m (n : ℕ) := Measure.map φ (ν n)
  have hm (n : ℕ) : IsProbabilityMeasure (m n) := by
    let : IsProbabilityMeasure (ν n) := hprob n
    exact (Measure.isProbabilityMeasure_map_iff hφ.measurable.aemeasurable).2 (hprob n)
  have hr (n : ℕ) : (m n).InnerRegularWRT IsCompact IsOpen :=
    (hreg n).map hφ.measurable.aemeasurable (fun _ hU ↦ hU.preimage hφ)
      (fun _ hC ↦ hC.image hφ) (fun _ hU ↦ hU.measurableSet)
  have hK₀ (n : ℕ) : m n Kᶜ = 0 := by
    rw [Measure.map_apply hφ.measurable hK.isClosed.isOpen_compl.measurableSet]
    have hpre : φ ⁻¹' Kᶜ = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro s hs
      exact hs (hφK (mem_range_self s))
    rw [hpre, measure_empty]
  obtain ⟨H, _, hH, hHfc, hz⟩ := exists_firstCountable_common_weakSupport m hm hr hK hK₀
  let : FirstCountableTopology H := hHfc
  have hz' (n : ℕ) : ν n (φ ⁻¹' H)ᶜ = 0 := by
    have hn := hz n
    rwa [Measure.map_apply hφ.measurable hH.isClosed.isOpen_compl.measurableSet] at hn
  have hy : y ∈ H := by
    by_contra hyn
    have ht := hret Hᶜ hH.isClosed.isOpen_compl hyn
    have hzero : (fun n ↦ (ν n).real (φ ⁻¹' Hᶜ)) = fun _ ↦ (0 : ℝ) := by
      funext n
      rw [Measure.real, preimage_compl, hz' n, ENNReal.toReal_zero]
    rw [hzero] at ht
    exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds ht)
  let yH : H := ⟨y, hy⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let φ₀ (s : S) : W := if φ s ∈ H then φ s else y
  let ψ (s : S) : H := ⟨φ₀ s, by
    by_cases hs : φ s ∈ H <;> simp [φ₀, hs, hy]⟩
  have hψ : Measurable ψ := by
    have hu : Measurable φ₀ := Measurable.ite (hφ.measurable hH.isClosed.measurableSet)
      hφ.measurable measurable_const
    let : MeasurableSpace H := MeasurableSpace.comap Subtype.val inferInstance
    have haux : @Measurable S H _ (MeasurableSpace.comap Subtype.val inferInstance) ψ :=
      hu.subtype_mk
    rwa [← borel_comap] at haux
  have hψret (U : Set H) (hU : IsOpen U) (hyU : yH ∈ U) :
      Tendsto (fun n ↦ (ν n).real (ψ ⁻¹' U)) atTop (𝓝 1) := by
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
    have he (n : ℕ) : ψ ⁻¹' ((Subtype.val : H → W) ⁻¹' V) =ᵐ[ν n] φ ⁻¹' V := by
      filter_upwards [show φ ⁻¹' H ∈ ae (ν n) from hz' n] with s hs
      change (φ₀ s ∈ V) ↔ (φ s ∈ V)
      change φ s ∈ H at hs
      simp [φ₀, hs]
    simpa only [Measure.real, measure_congr (he _)] using hret V hV hyU
  obtain ⟨A, hA, hAd, hAt⟩ := exists_density_one_tendsto_cocompact_of_countableBasis
    ν hprob F hF hFm hsupp ψ hψ yH hψret
  refine ⟨A ∩ φ ⁻¹' H, hA.inter (hφ.measurable hH.isClosed.measurableSet), ?_, ?_⟩
  · simpa only [Measure.real, measure_inter_conull (hz' _)] using hAd
  · have hsub : cocompact S ⊓ 𝓟 (A ∩ φ ⁻¹' H) ≤ cocompact S ⊓ 𝓟 A :=
      inf_le_inf_left _ (principal_mono.2 inter_subset_left)
    refine ((continuous_subtype_val.continuousAt.tendsto.comp hAt).mono_left hsub).congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self (A ∩ φ ⁻¹' H))] with s hs
    exact ite_eq_left hs.2

variable [T2Space S] [BorelSpace S]

/-- The equivalence (vi)–(ix) in Theorem 4.2 for normalized compact
sampling blocks of increasing mass and a continuous, weakly compact orbit. -/
theorem density_one_weak_tendsto_iff_measuredBlocks
    (μ : Measure S) [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFpos : ∀ n, μ (F n) ≠ 0)
    (hGrow : Tendsto (fun n ↦ μ (F n)) atTop (𝓝 ⊤))
    (φ : S → W) (hφ : Continuous φ) {K : Set W} (hK : IsCompact K)
    (hφK : range φ ⊆ K) (y : W) :
    (∀ U : Set W, IsOpen U → y ∈ U →
      Tendsto (fun n ↦ (normalizedRestrictedMeasure μ (F n)).real (φ ⁻¹' U)) atTop (𝓝 1)) ↔
    ∃ A : Set S, MeasurableSet A ∧
      Tendsto (fun n ↦ (normalizedRestrictedMeasure μ (F n)).real A) atTop (𝓝 1) ∧
      Tendsto φ (cocompact S ⊓ 𝓟 A) (𝓝 y) := by
  let ν (n : ℕ) := normalizedRestrictedMeasure μ (F n)
  have hp (n : ℕ) : IsProbabilityMeasure (ν n) :=
    normalizedRestrictedMeasure_probability μ (hFpos n) (hF n).measure_ne_top
  constructor
  · intro hret
    have hreg (n : ℕ) : (ν n).InnerRegularWRT IsCompact IsOpen := by
      let : IsProbabilityMeasure (ν n) := hp n
      let : (ν n).InnerRegularCompactLTTop := by
        change ((μ (F n))⁻¹ • μ.restrict (F n)).InnerRegularCompactLTTop
        infer_instance
      exact fun _ hU ↦ Measure.InnerRegular.innerRegular hU.measurableSet
    exact exists_density_one_weak_tendsto_of_innerRegular ν hp hreg F hF
      (fun n ↦ (hF n).isClosed.measurableSet)
      (fun n ↦ normalizedRestrictedMeasure_compl μ (hF n).isClosed.measurableSet)
      φ hφ hK hφK y hret
  · rintro ⟨A, _, hd, ht⟩ U hU hyU
    exact density_one_returns_of_tendsto_cocompact ν hp
      (fun _ hC ↦ normalizedRestrictedMeasure_real_tendsto_zero μ F hGrow
        hC.isClosed.measurableSet hC.measure_ne_top) φ hd ht U (hU.mem_nhds hyU)

variable [Semigroup S] [CompleteSpace E]

/-- Almost weak stability is equivalent to weak decay on a set of density
one along a left Følner sequence of compact blocks of increasing Radon mass.
The Banach space may be nonseparable. -/
theorem stable_iff_folner_density_one_weakDecay_of_radon
    (π : S →ₙ* (E →L[ℂ] E)) [CompactSpace (weakOperatorClosure π)]
    [MeasurableSpace (weakOperatorClosure π)] [BorelSpace (weakOperatorClosure π)]
    (hπ : Continuous (closureInclusion π)) (μ : Measure S)
    [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFpos : ∀ n, μ (F n) ≠ 0)
    (hGrow : Tendsto (fun n ↦ μ (F n)) atTop (𝓝 ⊤))
    (hν : LeftFolnerProbabilities (fun n ↦ normalizedRestrictedMeasure μ (F n)) atTop)
    (hadm : IsJdLGAdmissible π) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
    ∃ A : Set S, MeasurableSet A ∧
      Tendsto (fun n ↦ (normalizedRestrictedMeasure μ (F n)).real A) atTop (𝓝 1) ∧
      Tendsto (fun s ↦ toWeakSpace ℂ E (π s x)) (cocompact S ⊓ 𝓟 A) (𝓝 0) := by
  let ν (n : ℕ) := normalizedRestrictedMeasure μ (F n)
  have hp (n : ℕ) : IsProbabilityMeasure (ν n) :=
    normalizedRestrictedMeasure_probability μ (hFpos n) (hF n).measure_ne_top
  let eval (t : weakOperatorClosure π) := toWeakSpace ℂ E (closureAction π t x)
  let φ (s : S) := eval (closureInclusion π s)
  have hE : Continuous eval := continuous_weakOrbit_closureAction π x
  have hsub : range φ ⊆ range eval := by
    rintro _ ⟨s, rfl⟩
    exact mem_range_self _
  exact (stable_iff_folnerWeakReturns π hπ.measurable ν hp hν hadm x).trans
    (density_one_weak_tendsto_iff_measuredBlocks μ F hF hFpos hGrow φ (hE.comp hπ)
      (isCompact_range hE) hsub 0)

end JdLG
