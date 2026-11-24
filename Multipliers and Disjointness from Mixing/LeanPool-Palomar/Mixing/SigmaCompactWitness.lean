/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactMeasurableSection

@[expose] public section
noncomputable section

namespace Mixing

open Function Set TopologicalSpace

variable {A B D : Type*}
  [TopologicalSpace A] [CompactSpace A] [MetrizableSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [T2Space B] [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace D] [MetrizableSpace D]

omit [MetrizableSpace A] [MeasurableSpace A] [BorelSpace A] in
/-- The subset of a compact space defined by a closed constraint and an
inequality of two continuous values is σ-compact. -/
theorem isSigmaCompact_closed_and_ne {s : Set A} (hs : IsClosed s)
    {u v : A → D} (hu : Continuous u) (hv : Continuous v) :
    IsSigmaCompact {x ∈ s | u x ≠ v x} := by
  let : MetricSpace D := metrizableSpaceMetric D
  let K (n : ℕ) := s ∩ {x | 1 / (n + 1 : ℝ) ≤ dist (u x) (v x)}
  refine ⟨K, fun n ↦ (hs.inter (isClosed_le continuous_const (hu.dist hv))).isCompact, ?_⟩
  ext x
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, K]
  constructor
  · rintro ⟨n, hS, hD⟩
    exact ⟨hS, dist_pos.mp ((one_div_pos.mpr (by positivity : 0 < (n + 1 : ℝ))).trans_le hD)⟩
  · rintro ⟨hS, hD⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hD)
    exact ⟨n, hS, hn.le⟩

private theorem measurableSet_of_isSigmaCompact {s : Set B} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet

omit [CompactSpace A] in
/-- Select a witness from each nonempty fibre of a σ-compact set, and use
a prescribed measurable default at the other parameter points. -/
theorem exists_measurable_witness_of_isSigmaCompact (f : A → B) (hf : Continuous f)
    {s : Set A} (hs : IsSigmaCompact s) (d : B → A) (hd : Measurable d) :
    ∃ t : B → A, Measurable t ∧
      (∀ y ∈ f '' s, t y ∈ s ∧ f (t y) = y) ∧
      ∀ y ∉ f '' s, t y = d y := by
  classical
  let : MetricSpace A := metrizableSpaceMetric A
  let : SigmaCompactSpace s := isSigmaCompact_iff_sigmaCompactSpace.mp hs
  let U := f '' s
  have hU : MeasurableSet U := measurableSet_of_isSigmaCompact (hs.image hf)
  let F (x : s) : U := ⟨f x, x, x.property, rfl⟩
  have hF : Continuous F := (hf.comp continuous_subtype_val).subtype_mk _
  have hsurj : Surjective F := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨g, hgm, hg⟩ := exists_measurable_section_of_continuous_sigmaCompact F hF hsurj
  let t (y : B) : A := if hy : y ∈ U then (g ⟨y, hy⟩ : A) else d y
  refine ⟨t, ?_, ?_, fun y hy ↦ dite_eq_right hy⟩
  · intro V hV
    have hpre : t ⁻¹' V =
        (Subtype.val '' ((fun y : U ↦ (g y : A)) ⁻¹' V)) ∪ (Uᶜ ∩ d ⁻¹' V) := by
      ext y
      by_cases hy : y ∈ U
      · simp only [mem_preimage, t, mem_union, mem_inter_iff, mem_compl_iff, hy, dite_true,
          not_true_eq_false, false_and, or_false]
        refine ⟨fun h ↦ ⟨⟨y, hy⟩, h, rfl⟩, ?_⟩
        rintro ⟨z, hz, hzy⟩
        have he : z = (⟨y, hy⟩ : U) := Subtype.ext hzy
        subst z
        exact hz
      · simp only [mem_preimage, t, mem_union, mem_inter_iff, mem_compl_iff, hy, dite_false,
          not_false_eq_true, true_and]
        refine ⟨Or.inr, fun h ↦ h.elim ?_ id⟩
        rintro ⟨z, _, hz⟩
        exact (hy (hz ▸ z.property)).elim
    rw [hpre]
    exact ((MeasurableEmbedding.subtype_coe hU).measurableSet_image.mpr
      ((measurable_subtype_coe.comp hgm) hV)).union (hU.compl.inter (hd hV))
  · intro y hy
    change y ∈ U at hy
    simpa only [t, dite_eq_left hy] using
      And.intro (g ⟨y, hy⟩).property (congrArg Subtype.val (hg ⟨y, hy⟩))

end Mixing
