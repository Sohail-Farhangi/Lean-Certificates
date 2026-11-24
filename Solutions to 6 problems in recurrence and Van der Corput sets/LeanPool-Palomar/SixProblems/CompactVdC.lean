/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CompactVdCReverse
public import SixProblems.HaarRecognition
public import Mixing.SupportingJdLG.Stable

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Mixing
open scoped InnerProductSpace

theorem integral_eq_zero_of_isVdC_vector {G X E : Type} [Group G] [MeasurableSpace X]
    [StandardBorelSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {R : Set G} (hR : IsVdC R) (S : System G X) (V : X → E) (hV : StronglyMeasurable V)
    (hB : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (hZero : ∀ r ∈ R, ∫ x, ⟪V x,V (S.act r x)⟫_ℂ ∂S.measure = 0) :
    (∫ x, V x ∂S.measure) = 0 := by
  let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
  let e := (stdOrthonormalBasis ℂ E).repr
  have hZ := lemma4_2 hR S (fun x ↦ e (V x)) (e.continuous.comp_stronglyMeasurable hV).measurable
    (by obtain ⟨C,hC⟩ := hB; exact ⟨C,fun x ↦ (e.norm_map _).trans_le (hC x)⟩)
    (by intro r hr; simp_rw [e.inner_map_map]; exact hZero r hr)
  obtain ⟨C,hC⟩ := hB
  have hi := Integrable.of_bound (μ := S.measure) hV.aestronglyMeasurable C (ae_of_all _ hC)
  change ∫ x, e.toLinearIsometry.toContinuousLinearMap (V x) ∂S.measure = _ at hZ
  rw [e.toLinearIsometry.toContinuousLinearMap.integral_comp_comm hi] at hZ
  change e (∫ x, V x ∂S.measure) = 0 at hZ
  apply e.injective
  simpa only [map_zero] using hZ

variable {G K : Type} [Group G] [Group K] [TopologicalSpace K] [T2Space K]
  [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

/-- The forward implication of Theorem 4.6, using the Hilbert-space observable
obtained by applying a unitary representation to the inverse value. -/
theorem measureTheoreticVdC_of_isVdC {R : Set G} (hR : IsVdC R) (m : Measure K)
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure] [IsInvInvariant m] :
    IsMeasureTheoreticVdC R m := by
  intro X _ _ S F hF hDiff
  let F' (x : X) := (F x)⁻¹
  have hF' : Measurable F' := hF.inv
  let ν := S.measure.map F'
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hF'.aemeasurable).mpr inferInstance
  have hν : ν = m := (proposition4_5 m ν).2 (by
    intro E _ _ _ ρ hρ hI hN ξ η
    let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
    let V (x : X) := ρ (F' x) η
    have hV : StronglyMeasurable V := (hρ η).stronglyMeasurable.comp_measurable hF'
    have hB (x : X) : ‖V x‖ ≤ ‖η‖ := (LinearIsometryEquiv.norm_map _ _).le
    have hW : ∫ x, V x ∂S.measure = 0 := by
      apply integral_eq_zero_of_isVdC_vector hR S V hV ⟨_,hB⟩
      intro g hg
      let d (x : X) := F (S.act g x) * (F x)⁻¹
      have hd : Measurable d := (hF.comp (S.preserves g).measurable).mul hF.inv
      let c (k : K) := ⟪η,ρ k η⟫_ℂ
      have hc : Continuous c := continuous_const.inner (hρ η)
      have he (x : X) : ⟪V x,V (S.act g x)⟫_ℂ = c (d x)⁻¹ := by
        rw [← (ρ (F x)).inner_map_map]
        change ⟪(ρ (F x) * ρ (F x)⁻¹) η,(ρ (F x) * ρ (F (S.act g x))⁻¹) η⟫_ℂ = _
        rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
        simp [c, d, mul_inv_rev]
      have hInv := measurePreserving_inv m
      have hm : S.measure.map (Inv.inv ∘ d) = m := by
        rw [← Measure.map_map measurable_inv hd, hDiff g hg, hInv.map_eq]
      simp_rw [he]
      change (∫ x, c ((Inv.inv ∘ d) x) ∂S.measure) = 0
      rw [← integral_map (measurable_inv.comp hd).aemeasurable hc.aestronglyMeasurable, hm]
      exact integral_coefficient_haar_eq_zero m ρ hρ hI hN η η
    change ∫ k, ⟪ξ,ρ k η⟫_ℂ ∂ν = 0
    rw [integral_map hF'.aemeasurable (continuous_const.inner (hρ η)).aestronglyMeasurable]
    have hi := Integrable.of_bound (μ := S.measure) hV.aestronglyMeasurable ‖η‖ (ae_of_all _ hB)
    change ∫ x, innerSL ℂ ξ (V x) ∂S.measure = 0
    rw [(innerSL ℂ ξ).integral_comp_comm hi, hW, map_zero])
  have he : Inv.inv ∘ F' = F := by funext x; exact inv_inv _
  rw [← he, ← Measure.map_map measurable_inv hF', show S.measure.map F' = ν from rfl,
    hν, (measurePreserving_inv m).map_eq]

/-- Theorem 4.6 at the normalized Haar measure of a nontrivial compact
metrizable group. -/
theorem theorem4_6 [Countable G] [StandardBorelSpace K] [Nontrivial K] (R : Set G)
    (m : Measure K) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    IsVdC R ↔ IsMeasureTheoreticVdC R m := by
  let : IsMulRightInvariant m := ⟨fun k ↦ by
    let : IsProbabilityMeasure (m.map (· * k)) :=
      (Measure.isProbabilityMeasure_map_iff (continuous_mul_const k).measurable.aemeasurable).mpr inferInstance
    exact isHaarMeasure_eq_of_isProbabilityMeasure (m.map (· * k)) m⟩
  let : IsInvInvariant m := ⟨by
    let : IsProbabilityMeasure m.inv :=
      (Measure.isProbabilityMeasure_map_iff continuous_inv.measurable.aemeasurable).mpr inferInstance
    let : m.inv.IsHaarMeasure := isHaarMeasure_of_isCompact_nonempty_interior m.inv
      Set.univ isCompact_univ (by simp) (by simp) (by simp)
    exact isHaarMeasure_eq_of_isProbabilityMeasure m.inv m⟩
  constructor
  · intro h
    exact measureTheoreticVdC_of_isVdC h m
  · intro h
    exact isVdC_of_measureTheoreticVdC m h

end SixProblems
