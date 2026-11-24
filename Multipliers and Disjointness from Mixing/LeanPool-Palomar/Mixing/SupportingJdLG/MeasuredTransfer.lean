/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mixing.SupportingJdLG.MeasuredReturns
public import Mixing.SupportingJdLG.SeparateAveraging
public import Mixing.SupportingJdLG.StableBiMean

/-!
# Transfer of measured means to the compact operator closure

Pull a continuous test back to the measured semigroup and apply the
given mean on L∞. The Riesz measure of the resulting functional permits
the invariance identity to extend from represented elements to their
closure. This is the bridge in Lemma 4.1 and Theorem 4.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped CompactlySupported ENNReal Topology

namespace Mixing.JdLGBridge.MeasuredMean

variable {S : Type*} [MeasurableSpace S] {measure : Measure S}

/-- Right invariance on essentially bounded measurable representatives. -/
def IsRightInvariant [Mul S] (m : MeasuredMean measure) : Prop :=
  ∀ (s : S) (f : S → ℝ) (hf : MemLp f ∞ measure) (ht : MemLp (f ∘ (· * s)) ∞ measure),
    m.value (f ∘ (· * s)) ht = m.value f hf

section Transfer

variable {T : Type*} [Semigroup S] [Semigroup T] [TopologicalSpace T] [CompactSpace T]
  [T2Space T] [MeasurableSpace T] [BorelSpace T]
  (m : MeasuredMean measure) (i : S →ₙ* T) (hi : Measurable i)
  (hleft : ∀ t : T, Continuous (t * ·)) (hright : ∀ t : T, Continuous (· * t))

include hi

omit [T2Space T] in
theorem memLp_comp (f : C_c(T, ℝ)) : MemLp (f ∘ i) ∞ measure :=
  memLp_top_of_bound (f.continuous.measurable.comp hi).aestronglyMeasurable
    ‖f.toContinuousMap‖ (ae_of_all _ fun s ↦ f.toContinuousMap.norm_coe_le_norm (i s))

/-- Restrict a measured mean to pullbacks of continuous functions. -/
noncomputable def continuousFunctional : C_c(T, ℝ) →ₚ[ℝ] ℝ where
  toFun f := m.value (f ∘ i) (memLp_comp i hi f)
  map_add' f g := (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
    (m.value_add (memLp_comp i hi f) (memLp_comp i hi g))
  map_smul' c f := (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
    (m.value_smul c (memLp_comp i hi f))
  monotone' _ _ h := m.value_mono (ae_of_all _ fun s ↦ h (i s))

omit [T2Space T] in
theorem continuousFunctional_one :
    m.continuousFunctional i hi (compactRealFunction (fun _ ↦ 1) continuous_const) = 1 :=
  (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans m.value_one

omit [Semigroup S] [Semigroup T] hi in
/-- Invariance of a normalized positive functional extends from a dense set
of translations to the whole compact semitopological host. -/
theorem continuousFunctional_translate_of_dense {X : Type*} (j : X → T)
    (Φ : C_c(T, ℝ) →ₚ[ℝ] ℝ)
    (hunit : Φ (compactRealFunction (fun _ ↦ 1) continuous_const) = 1)
    (L : T → T → T) (hL₁ : ∀ t, Continuous fun s ↦ L s t)
    (hL₂ : ∀ s, Continuous (L s)) (hd : DenseRange j)
    (hinv : ∀ s : X, ∀ f : C_c(T, ℝ),
      Φ (compactRealFunction (f ∘ L (j s)) (f.continuous.comp (hL₂ (j s)))) = Φ f)
    (t : T) (f : C_c(T, ℝ)) :
    Φ (compactRealFunction (f ∘ L t) (f.continuous.comp (hL₂ t))) = Φ f := by
  let μ := RealRMK.rieszMeasure Φ
  have hμ : IsProbabilityMeasure μ := by
    apply isProbabilityMeasure_iff_real.mpr
    have h := (RealRMK.integral_rieszMeasure Φ
      (compactRealFunction (fun _ : T ↦ 1) continuous_const)).trans
        hunit
    change (∫ _ : T, (1 : ℝ) ∂μ) = 1 at h
    simpa only [integral_const, smul_eq_mul, mul_one] using h
  have hcont : Continuous fun s ↦ ∫ z, f (L s z) ∂μ :=
    continuous_integral_of_separatelyContinuous μ (fun s z ↦ f (L s z))
      (fun z ↦ f.continuous.comp (hL₁ z)) (fun s ↦ f.continuous.comp (hL₂ s))
      ‖f.toContinuousMap‖ (fun s z ↦ f.toContinuousMap.norm_coe_le_norm (L s z))
  have hr (s : T) : (∫ z, f (L s z) ∂μ) =
      Φ (compactRealFunction (f ∘ L s) (f.continuous.comp (hL₂ s))) :=
    RealRMK.integral_rieszMeasure Φ
      (compactRealFunction (f ∘ L s) (f.continuous.comp (hL₂ s)))
  have he := hd.equalizer hcont (continuous_const (y := Φ f))
    (funext fun s ↦ (hr (j s)).trans (hinv s f))
  exact (hr t).symm.trans (congrFun he t)

/-- A left-invariant mean transfers to the compact host of a dense measurable
representation. Measurability is the only regularity required of the map. -/
noncomputable def toContinuousMean (hd : DenseRange i) (hm : m.IsLeftInvariant) :
    LeftInvariantContinuousMean hleft where
  functional := m.continuousFunctional i hi
  normalized := m.continuousFunctional_one i hi
  translate t f := by
    apply continuousFunctional_translate_of_dense i (m.continuousFunctional i hi)
      (m.continuousFunctional_one i hi) (· * ·) hright hleft hd _ t f
    intro s g
    have hEq (a : S) : g (i s * i a) = g (i (s * a)) := by rw [map_mul i]
    have htr : MemLp ((g ∘ i) ∘ (s * ·)) ∞ measure := (memLp_comp i hi
      (compactRealFunction (g ∘ (i s * ·)) (g.continuous.comp (hleft (i s))))).ae_eq
        (ae_of_all _ hEq)
    exact (m.value_congr_ae (ae_of_all _ hEq)).trans (hm s _ (memLp_comp i hi g) htr)

theorem toContinuousMean_rightInvariant (hd : DenseRange i) (hm : m.IsLeftInvariant)
    (hmr : m.IsRightInvariant) :
    (m.toContinuousMean i hi hleft hright hd hm).IsRightInvariant hright := by
  intro t f
  apply continuousFunctional_translate_of_dense i (m.continuousFunctional i hi)
    (m.continuousFunctional_one i hi) (fun s z ↦ z * s) hleft hright hd _ t f
  intro s g
  have hEq (a : S) : g (i a * i s) = g (i (a * s)) := by rw [map_mul i]
  have htr : MemLp ((g ∘ i) ∘ (· * s)) ∞ measure := (memLp_comp i hi
    (compactRealFunction (g ∘ (· * i s)) (g.continuous.comp (hright (i s))))).ae_eq
      (ae_of_all _ hEq)
  exact (m.value_congr_ae (ae_of_all _ hEq)).trans (hmr s _ (memLp_comp i hi g) htr)

end Transfer

open Filter

/-- Lower left Banach density of a measurable set, defined using all
left-invariant means on the given measure space. -/
noncomputable def lowerBanachDensity [Semigroup S] (A : Set S) (hA : MeasurableSet A) : ℝ :=
  sInf {r : ℝ | ∃ m : MeasuredMean measure, m.IsLeftInvariant ∧ m.mass A hA = r}

theorem lowerBanachDensity_eq_one_iff [Semigroup S] (m : MeasuredMean measure)
    (hm : m.IsLeftInvariant) (A : Set S) (hA : MeasurableSet A) :
    lowerBanachDensity (measure := measure) A hA = 1 ↔
      ∀ m : MeasuredMean measure, m.IsLeftInvariant → m.mass A hA = 1 := by
  unfold lowerBanachDensity
  constructor
  · intro h n hn
    have hbounded : BddBelow {r : ℝ | ∃ m : MeasuredMean measure, m.IsLeftInvariant ∧
        m.mass A hA = r} := ⟨0, fun _ ⟨q, _, hq⟩ ↦ hq ▸ q.mass_nonneg hA⟩
    exact le_antisymm (n.mass_le_one hA)
      (h ▸ csInf_le hbounded ⟨n, hn, rfl⟩)
  · intro h
    have heq : {r : ℝ | ∃ m : MeasuredMean measure, m.IsLeftInvariant ∧ m.mass A hA = r} = {1} := by
      ext r
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact mem_singleton_iff.2 (h q hq)
      · rintro hr
        exact ⟨m, hm, (h m hm).trans (mem_singleton_iff.1 hr).symm⟩
    rw [heq, csInf_singleton]

end Mixing.JdLGBridge.MeasuredMean
