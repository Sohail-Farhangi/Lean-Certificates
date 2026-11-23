/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MeasuredMeans
public import JdLG.UltrafilterMoreMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.LocallyConstant.Algebra

/-! # Discrete invariant means on sets and on L-infinity -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace JdLG

attribute [local instance] stoneCechClopenMeasurableSpace

variable {S : Type*}

private theorem exists_count_bound [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {f : S → ℝ} (hf : MemLp f ∞ (Measure.count : Measure S)) :
    ∃ C : ℝ, ∀ s, ‖f s‖ ≤ C := by
  refine ⟨(eLpNorm f ∞ Measure.count).toReal, fun s ↦ ?_⟩
  simpa using ENNReal.toReal_mono hf.eLpNorm_ne_top (eNorm_le_eLpNorm_count f s (by simp))

private noncomputable def extendScalar (f : S → ℝ) (p : Ultrafilter S) : ℝ :=
  limUnder (p : Filter S) f

private theorem extendScalar_pure (f : S → ℝ) (s : S) :
    extendScalar f (pure s) = f s :=
  (tendsto_pure_nhds f s).limUnder_eq

private theorem continuous_extendScalar {f : S → ℝ} (hf : ∃ C : ℝ, ∀ s, ‖f s‖ ≤ C) :
    Continuous (extendScalar f) := by
  obtain ⟨C, hC⟩ := hf
  let K := Metric.closedBall (0 : ℝ) C
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 C)
  let g : S → K := fun s ↦ ⟨f s, mem_closedBall_zero_iff.mpr (hC s)⟩
  have h : Continuous (fun p : Ultrafilter S ↦ ((Ultrafilter.extend g p : K) : ℝ)) :=
    continuous_subtype_val.comp (continuous_ultrafilter_extend g)
  apply h.congr
  intro p
  have hT := (continuous_subtype_val.tendsto _).comp (tendsto_ultrafilterExtend g p)
  exact hT.limUnder_eq.symm

private theorem extendScalar_integrable [Semigroup S] (m : LeftInvariantSetMean S) {f : S → ℝ}
    (hf : ∃ C : ℝ, ∀ s, ‖f s‖ ≤ C) : Integrable (extendScalar f) m.stoneCechMeasure := by
  have hc := continuous_extendScalar hf
  obtain ⟨C, hC⟩ := hf
  have h : ∀ p, ‖extendScalar f p‖ ≤ C := by
    intro p
    apply closure_minimal (s := range (pure : S → Ultrafilter S))
      (t := {q | ‖extendScalar f q‖ ≤ C}) _ (isClosed_le hc.norm continuous_const)
        (denseRange_pure p)
    rintro _ ⟨s, rfl⟩
    change ‖extendScalar f (pure s)‖ ≤ C
    simpa only [extendScalar_pure] using hC s
  exact ⟨(stoneCechClopenMeasurable_of_continuous hc).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (ae_of_all _ h)⟩

private theorem extendScalar_mono {f g : S → ℝ} (hf : ∃ C : ℝ, ∀ s, ‖f s‖ ≤ C)
    (hg : ∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) (h : ∀ s, f s ≤ g s) :
    ∀ p, extendScalar f p ≤ extendScalar g p := by
  intro p
  apply closure_minimal (s := range (pure : S → Ultrafilter S))
    (t := {q | extendScalar f q ≤ extendScalar g q}) _
    (isClosed_le (continuous_extendScalar hf) (continuous_extendScalar hg)) (denseRange_pure p)
  rintro _ ⟨s, rfl⟩
  change extendScalar f (pure s) ≤ extendScalar g (pure s)
  simpa only [extendScalar_pure] using h s

variable [Semigroup S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- A left invariant set mean determines a normalized mean on real L∞ for counting measure. -/
noncomputable def LeftInvariantSetMean.toDiscreteMeasuredMean (m : LeftInvariantSetMean S) :
    MeasuredMean (Measure.count : Measure S) where
  functional :=
    { toFun := fun a ↦ ∫ p, extendScalar a p ∂m.stoneCechMeasure
      map_add' := by
        intro a b
        have h₁ := exists_count_bound (Lp.memLp a)
        have h₂ := exists_count_bound (Lp.memLp b)
        have h₃ := exists_count_bound (Lp.memLp (a + b))
        have hExt : extendScalar (⇑(a + b)) = extendScalar a + extendScalar b := by
          apply (continuous_extendScalar h₃).ext_on denseRange_pure
            ((continuous_extendScalar h₁).add (continuous_extendScalar h₂))
          rintro _ ⟨s, rfl⟩
          simp only [Pi.add_apply, extendScalar_pure]
          exact Measure.ae_count_iff.mp (Lp.coeFn_add a b) s
        rw [hExt]
        exact integral_add (extendScalar_integrable m h₁) (extendScalar_integrable m h₂)
      map_smul' := by
        intro c a
        have h₁ := exists_count_bound (Lp.memLp a)
        have h₂ := exists_count_bound (Lp.memLp (c • a))
        have hExt : extendScalar (⇑(c • a)) = c • extendScalar a := by
          apply (continuous_extendScalar h₂).ext_on denseRange_pure
            ((continuous_extendScalar h₁).const_smul c)
          rintro _ ⟨s, rfl⟩
          simp only [Pi.smul_apply, extendScalar_pure]
          exact Measure.ae_count_iff.mp (Lp.coeFn_smul c a) s
        rw [hExt]
        exact integral_smul c (extendScalar a) }
  monotone' := by
    intro a b hab
    have h₁ := exists_count_bound (Lp.memLp a)
    have h₂ := exists_count_bound (Lp.memLp b)
    exact integral_mono (extendScalar_integrable m h₁) (extendScalar_integrable m h₂)
      (extendScalar_mono h₁ h₂ (Measure.ae_count_iff.mp hab))
  unit' := by
    let f : S → ℝ := fun _ ↦ 1
    let hf : MemLp f ∞ (Measure.count : Measure S) := memLp_top_constant 1
    have h : (⇑(hf.toLp f)) = f := funext (Measure.ae_count_iff.mp hf.coeFn_toLp)
    have hExt : extendScalar f = fun _ ↦ 1 := by
      apply (continuous_extendScalar (exists_count_bound hf)).ext_on denseRange_pure
        continuous_const
      rintro _ ⟨s, rfl⟩
      exact extendScalar_pure f s
    change (∫ p, extendScalar (⇑(hf.toLp f)) p ∂m.stoneCechMeasure) = 1
    rw [h, hExt]
    simp

private theorem toDiscreteMeasuredMean_value (m : LeftInvariantSetMean S) {f : S → ℝ}
    (hf : MemLp f ∞ (Measure.count : Measure S)) :
    m.toDiscreteMeasuredMean.value f hf = ∫ p, extendScalar f p ∂m.stoneCechMeasure := by
  have h : (⇑(hf.toLp f)) = f := funext (Measure.ae_count_iff.mp hf.coeFn_toLp)
  change (∫ p, extendScalar (⇑(hf.toLp f)) p ∂m.stoneCechMeasure) = _
  rw [h]

theorem LeftInvariantSetMean.toDiscreteMeasuredMean_leftInvariant (m : LeftInvariantSetMean S) :
    m.toDiscreteMeasuredMean.IsLeftInvariant := by
  intro s f hf ht
  let L : Ultrafilter S → Ultrafilter S := ((pure s : Ultrafilter S) * ·)
  have hL : Continuous L := by
    simpa only [L, pure_mul_as_map] using continuous_ultrafilter_map (s * ·)
  have hLm := stoneCechClopenMeasurable_of_continuous_selfmap L hL
  have hExt : extendScalar (f ∘ (s * ·)) = extendScalar f ∘ L := by
    apply (continuous_extendScalar (exists_count_bound ht)).ext_on denseRange_pure
      ((continuous_extendScalar (exists_count_bound hf)).comp hL)
    rintro _ ⟨t, rfl⟩
    simp only [Function.comp_apply, extendScalar_pure, L, pure_mul_as_map, Ultrafilter.map_pure]
  rw [toDiscreteMeasuredMean_value, toDiscreteMeasuredMean_value, hExt]
  simp only [Function.comp_apply]
  rw [← integral_map (μ := m.stoneCechMeasure) hLm.aemeasurable
      (stoneCechClopenMeasurable_of_continuous
        (continuous_extendScalar (exists_count_bound hf))).aestronglyMeasurable,
    m.stoneCechMeasure_map_principal_left]

theorem LeftInvariantSetMean.toDiscreteMeasuredMean_mass (m : LeftInvariantSetMean S) (A : Set S) :
    m.toDiscreteMeasuredMean.mass A MeasurableSet.of_discrete = m.mass A := by
  let C : Set (Ultrafilter S) := {p | A ∈ p}
  have hC : IsClopen C := ⟨ultrafilter_isClosed_basic A, ultrafilter_isOpen_basic A⟩
  have hmC : MeasurableSet C := MeasurableSpace.measurableSet_generateFrom hC
  let hA : MeasurableSet A := MeasurableSet.of_discrete
  let f := A.indicator (fun _ ↦ (1 : ℝ))
  let hf : MemLp f ∞ (Measure.count : Measure S) := MeasuredMean.memLp_indicator_one hA
  have hExt : extendScalar f = C.indicator (fun _ ↦ 1) := by
    have hContinuous : Continuous (C.indicator (fun _ ↦ (1 : ℝ))) := by
      rw [← show (1 : Ultrafilter S → ℝ) = (fun _ ↦ 1) from rfl, ← LocallyConstant.coe_charFn ℝ hC]
      exact (LocallyConstant.charFn ℝ hC).continuous
    apply (continuous_extendScalar (exists_count_bound hf)).ext_on denseRange_pure
      hContinuous
    rintro _ ⟨s, rfl⟩
    rw [extendScalar_pure]
    by_cases h : s ∈ A
    · have hs : (pure s : Ultrafilter S) ∈ C := Ultrafilter.mem_pure.mpr h
      simp [f, h, hs]
    · have hs : (pure s : Ultrafilter S) ∉ C := fun h' ↦ h (Ultrafilter.mem_pure.mp h')
      simp [f, h, hs]
  have hpre : (pure ⁻¹' C : Set S) = A := Set.ext fun _ ↦ Ultrafilter.mem_pure
  change m.toDiscreteMeasuredMean.value f hf = _
  rw [toDiscreteMeasuredMean_value, hExt, integral_indicator hmC, setIntegral_const,
    smul_eq_mul, mul_one, measureReal_def, m.stoneCechMeasure_clopen hC, hpre,
    ENNReal.toReal_ofReal (m.nonneg A)]

/-- A positive value on a set in the finitely additive presentation is witnessed by
a genuine left invariant linear mean on real L∞ for counting measure. -/
theorem exists_discreteMeasuredMean_of_hasPositiveBanachDensity {A : Set S}
    (h : HasPositiveBanachDensity A) :
    ∃ m : MeasuredMean (Measure.count : Measure S), m.IsLeftInvariant ∧
      0 < m.mass A MeasurableSet.of_discrete := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m.toDiscreteMeasuredMean, m.toDiscreteMeasuredMean_leftInvariant,
    m.toDiscreteMeasuredMean_mass A ▸ hm⟩

/-- Restrict a discrete invariant mean to indicator functions to obtain its set mean. -/
noncomputable def MeasuredMean.toLeftInvariantSetMean
    (m : MeasuredMean (Measure.count : Measure S)) (hm : m.IsLeftInvariant) :
    LeftInvariantSetMean S where
  mass A := m.mass A MeasurableSet.of_discrete
  nonneg A := m.mass_nonneg (A := A) MeasurableSet.of_discrete
  empty := by
    change m.value ((∅ : Set S).indicator (fun _ ↦ (1 : ℝ))) _ = 0
    refine (m.value_congr_ae (hg := memLp_top_constant 0)
      (ae_of_all _ (fun s ↦ by simp))).trans (m.value_constant 0)
  univ := m.mass_univ
  add_disjoint := by
    intro A B hAB
    simp only [MeasuredMean.mass, ← m.value_add]
    apply m.value_congr_ae
    apply ae_of_all
    intro s
    by_cases hA : s ∈ A
    · have hB : s ∉ B := fun hB ↦ Set.disjoint_left.mp hAB hA hB
      simp [hA, hB]
    · by_cases hB : s ∈ B <;> simp [hA, hB]
  invariant := by
    intro s A
    let f := A.indicator (fun _ ↦ (1 : ℝ))
    let hA : MeasurableSet A := MeasurableSet.of_discrete
    let hB : MeasurableSet ((s * ·) ⁻¹' A) := MeasurableSet.of_discrete
    let hf : MemLp f ∞ (Measure.count : Measure S) := MeasuredMean.memLp_indicator_one hA
    have ht : MemLp (f ∘ (s * ·)) ∞ (Measure.count : Measure S) :=
      MeasuredMean.memLp_indicator_one hB
    exact (m.value_congr_ae (hg := ht) (ae_of_all _ (fun _ ↦ rfl))).trans (hm s f hf ht)

/-- Upper Banach density positivity as used by essential ultrafilters agrees
with positivity for an invariant functional on the discrete L∞ space. -/
theorem hasPositiveBanachDensity_iff_exists_discreteMeasuredMean {A : Set S} :
    HasPositiveBanachDensity A ↔
      ∃ m : MeasuredMean (Measure.count : Measure S), m.IsLeftInvariant ∧
        0 < m.mass A MeasurableSet.of_discrete := by
  exact ⟨exists_discreteMeasuredMean_of_hasPositiveBanachDensity,
    fun ⟨m, hm, hA⟩ ↦ ⟨m.toLeftInvariantSetMean hm, hA⟩⟩

end JdLG
