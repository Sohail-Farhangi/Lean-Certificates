module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mixing.PartialRigidity

@[expose] public section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The fibre-mass argument in Theorem 5.2.

The input from the partially rigid Markov operator is `hmajorize`: each
indicator admits a factor-measurable image with the same integral and with
pointwise lower bound `a` on that event. -/
theorem ae_measure_gap_of_fibre_majorization
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y X) [IsMarkovKernel κ] (π : X → Y) (hπ : Measurable π)
    (hfibre : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, π x = y)
    (a : ℝ≥0∞)
    (hmajorize : ∀ A : Set X, MeasurableSet A →
      ∃ h : Y → ℝ≥0∞, Measurable h ∧
        (∀ᵐ x ∂(κ ∘ₘ ν), x ∈ A → a ≤ h (π x)) ∧
        (∫⁻ y, h y ∂ν) = (κ ∘ₘ ν) A)
    {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ y ∂ν, κ y A = 0 ∨ a ≤ κ y A := by
  classical
  let E : Set Y := {y | 0 < κ y A ∧ κ y A < a}
  have hm := κ.measurable_coe hA
  have hE : MeasurableSet E := (measurableSet_lt measurable_const hm).inter
    (measurableSet_lt hm measurable_const)
  have hνE : ν E = 0 := by
    by_contra hpos
    let A' := A ∩ π ⁻¹' E
    have hA' : MeasurableSet A' := hA.inter (hπ hE)
    obtain ⟨h, _, hlo, hμ⟩ := hmajorize A' hA'
    have hcomp : (κ ∘ₘ ν) A' = ∫⁻ y in E, κ y A ∂ν := by
      rw [Measure.bind_apply hA' κ.aemeasurable, ← lintegral_indicator hE]
      apply lintegral_congr_ae
      filter_upwards [hfibre] with y hy
      by_cases hyE : y ∈ E
      · rw [indicator_of_mem hyE]
        apply measure_congr
        filter_upwards [hy] with x hx
        exact ⟨fun he ↦ he.1, fun he ↦ ⟨he, by simpa only [mem_preimage, hx] using hyE⟩⟩
      · rw [indicator_of_notMem hyE]
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hy] with x hx hxA
        exact hyE (by simpa only [mem_preimage, hx] using hxA.2)
    have haE : ∀ᵐ y ∂ν, y ∈ E → a ≤ h y := by
      filter_upwards [hfibre, Measure.ae_ae_of_ae_comp hlo] with y hy hAy hyE
      have hmem : ¬ ∀ᵐ x ∂κ y, x ∉ A := by
        rw [← measure_eq_zero_iff_ae_notMem]
        exact (show 0 < κ y A from hyE.1).ne'
      have hex : ∃ x, x ∈ A ∧ π x = y ∧ (x ∈ A' → a ≤ h (π x)) := by
        by_contra! hn
        apply hmem
        filter_upwards [hy, hAy] with x hx hx' hxA
        obtain ⟨hxA', hlt⟩ := hn x hxA hx
        exact (not_lt_of_ge (hx' hxA')) hlt
      obtain ⟨x, hxA, hxy, hAx⟩ := hex
      specialize hAx ⟨hxA, by simpa only [mem_preimage, hxy] using hyE⟩
      simpa only [hxy] using hAx
    have hbound : a * ν E ≤ ∫⁻ y, h y ∂ν := by
      rw [← lintegral_indicator_const hE]
      apply lintegral_mono_ae
      filter_upwards [haE] with y hy
      by_cases hyE : y ∈ E
      · simpa only [indicator_of_mem hyE] using hy hyE
      · simp only [indicator_of_notMem hyE, zero_le]
    have hstrict : (∫⁻ y in E, κ y A ∂ν) < a * ν E := by
      rw [← setLIntegral_const E a]
      apply lintegral_strict_mono
      · intro hz
        exact hpos (by simpa using congrArg (fun μ : Measure Y ↦ μ univ) hz)
      · exact measurable_const.aemeasurable
      · rw [← hcomp]
        exact measure_ne_top _ _
      · rw [ae_restrict_iff' hE]
        exact ae_of_all _ fun y hy ↦ hy.2
    rw [hμ, hcomp] at hbound
    exact (not_lt_of_ge hbound) hstrict
  rw [ae_iff]
  have hcompl : {y | ¬ (κ y A = 0 ∨ a ≤ κ y A)} = E := by
    ext y
    simp only [E, mem_ofPred_eq, not_or, not_le, pos_iff_ne_zero]
  rw [hcompl]
  exact hνE

private theorem ae_ball_mass_of_fibre_majorization
    [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y X) [IsMarkovKernel κ] (π : X → Y) (hπ : Measurable π)
    (hfibre : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, π x = y)
    (a : ℝ≥0∞)
    (hmajorize : ∀ A : Set X, MeasurableSet A →
      ∃ h : Y → ℝ≥0∞, Measurable h ∧
        (∀ᵐ x ∂(κ ∘ₘ ν), x ∈ A → a ≤ h (π x)) ∧
        (∫⁻ y, h y ∂ν) = (κ ∘ₘ ν) A) :
    ∀ᵐ y ∂ν, ∀ x ∈ (κ y).support, ∀ r : ℝ, 0 < r → a ≤ κ y (Metric.ball x r) := by
  let basis := TopologicalSpace.countableBasis X
  have hgap (A : basis) : ∀ᵐ y ∂ν, κ y A = 0 ∨ a ≤ κ y A :=
    ae_measure_gap_of_fibre_majorization ν κ π hπ hfibre a hmajorize
      (TopologicalSpace.isOpen_of_mem_countableBasis A.property).measurableSet
  filter_upwards [ae_all_iff.2 hgap] with y hy
  intro x hx r hr
  have hnhds := Metric.ball_mem_nhds x hr
  obtain ⟨A, hA, hxA, hsub⟩ :=
    (TopologicalSpace.isBasis_countableBasis X).mem_nhds_iff.mp hnhds
  have hpos := (Measure.mem_support_iff_forall x).mp hx A
    ((TopologicalSpace.isOpen_of_mem_countableBasis hA).mem_nhds hxA)
  exact ((hy ⟨A, hA⟩).resolve_left hpos.ne').trans (measure_mono hsub)

/-- The finite-support conclusion of the fibre-mass argument, with a simultaneous
almost-everywhere assertion over a countable open basis. -/
theorem ae_finite_fibre_support_of_majorization
    [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y X) [IsMarkovKernel κ] (π : X → Y) (hπ : Measurable π)
    (hfibre : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, π x = y)
    (a : ℝ≥0∞) (ha : 0 < a) (ha₁ : a ≤ 1)
    (hmajorize : ∀ A : Set X, MeasurableSet A →
      ∃ h : Y → ℝ≥0∞, Measurable h ∧
        (∀ᵐ x ∂(κ ∘ₘ ν), x ∈ A → a ≤ h (π x)) ∧
        (∫⁻ y, h y ∂ν) = (κ ∘ₘ ν) A) :
    ∀ᵐ y ∂ν, ∃ s : Finset X, (s : Set X) = (κ y).support ∧ (κ y) (s : Set X)ᶜ = 0 ∧
      (s.card : ℝ≥0∞) * a ≤ 1 := by
  filter_upwards [ae_ball_mass_of_fibre_majorization ν κ π hπ hfibre a hmajorize] with y hy
  exact finite_support_of_support_ball_lower_bound _ ha ha₁ hy

/-- Fibre majorization bounds the mass of the conditional atom at almost every original point. -/
theorem ae_atom_mass_of_fibre_majorization
    [MetricSpace X] [SecondCountableTopology X] [BorelSpace X] [MeasurableEq Y]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y X) [IsMarkovKernel κ] (π : X → Y) (hπ : Measurable π)
    (hfibre : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, π x = y)
    (a : ℝ≥0∞)
    (hmajorize : ∀ A : Set X, MeasurableSet A →
      ∃ h : Y → ℝ≥0∞, Measurable h ∧
        (∀ᵐ x ∂(κ ∘ₘ ν), x ∈ A → a ≤ h (π x)) ∧
        (∫⁻ y, h y ∂ν) = (κ ∘ₘ ν) A) :
    ∀ᵐ x ∂(κ ∘ₘ ν), a ≤ κ (π x) {x} := by
  have hm : Measurable (fun x : X => κ (π x) {x}) := by
    have he : MeasurableSet {w : X × X | w.2 = w.1} :=
      measurableSet_eq_fun measurable_snd measurable_fst
    have hh : Measurable (fun x : X => (Kernel.id ×ₖ κ.comap π hπ) x {w : X × X | w.2 = w.1}) :=
      (Kernel.id ×ₖ κ.comap π hπ).measurable_coe he
    convert hh using 1
    funext x
    rw [Kernel.prod_apply, Kernel.id_apply, Kernel.comap_apply, Measure.dirac_prod,
      Measure.map_apply measurable_prodMk_left he]
    congr 1
  apply Measure.ae_comp_of_ae_ae (measurableSet_le measurable_const hm)
  filter_upwards [hfibre, ae_ball_mass_of_fibre_majorization ν κ π hπ hfibre a hmajorize]
    with y hfy hy
  filter_upwards [hfy, (κ y).support_mem_ae] with x hxy hx
  rw [hxy]
  exact measure_singleton_ge_of_ball_lower_bound _ (hy x hx)

end Mixing
