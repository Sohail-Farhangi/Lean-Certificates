/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.BoundedPET
public import VdC.Cube
public import VdC.Applications
public import VdC.CompactClosure
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Order.OrderIsoNat

/-! # Ergodic Examples -/

@[expose] public section

open Filter Finset Function MeasureTheory Set TopologicalSpace
open scoped Topology BigOperators ComplexConjugate

namespace VdC

section Observable

variable {X : Type*} [MeasurableSpace X]

def orbitSequence (T : X → X) (x : X) (n : ℕ) : X := T^[n] x

def BoundedObservable (f : X → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C

noncomputable def koopmanCorrelation (μ : Measure X) (T : X → X) (f : X → ℂ) (h : ℕ) : ℂ :=
  ∫ y, f (T^[h] y) * star (f y) ∂μ

def KoopmanWeakMixing (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f → (∫ y, f y ∂μ) = 0 →
    Tendsto (realCesaro (fun h => ‖koopmanCorrelation μ T f (h+1)‖)) atTop (𝓝 0)

def KoopmanLebesgueSpectrum (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f → (∫ y, f y ∂μ) = 0 →
    ∃ ν : FiniteMeasure UnitAddCircle, HasSpectrum (koopmanCorrelation μ T f) ν ∧
      (ν : Measure UnitAddCircle) ≪ circleHaar

def KoopmanSingularSpectrum (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f →
    ∃ ν : FiniteMeasure UnitAddCircle, HasSpectrum (koopmanCorrelation μ T f) ν ∧
      (ν : Measure UnitAddCircle).MutuallySingular circleHaar

theorem BoundedObservable.orbit_bounded {f : X → ℂ} (hf : BoundedObservable f) (T : X → X) (x : X) :
    BoundedSeq (fun n => f (orbitSequence T x n)) := by
  obtain ⟨C, hC, hbound⟩ := hf.2
  exact ⟨C, hC, fun _ => hbound _⟩

/-- `EquationForExamples` for one bounded measurable observable, concurrently at all lags. -/
theorem ae_orbit_correlation {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {f : X → ℂ} (hf : BoundedObservable f) :
    ∀ᵐ x ∂μ, CorrLimits (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) id
      (koopmanCorrelation μ T f) := by
  apply ae_all_iff.mpr
  intro h
  let g (x : X) := f (T^[h] x) * star (f x)
  have hmeas : Measurable g := (hf.1.comp (hT.measurable.iterate h)).mul
    (Complex.continuous_conj.measurable.comp hf.1)
  obtain ⟨C, hC, hb⟩ := hf.2
  have hbound (x : X) : ‖g x‖ ≤ C*C := by
    change ‖f (T^[h] x) * star (f x)‖ ≤ C*C
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb _) (hb _) (norm_nonneg _) hC
  filter_upwards [ae_tendsto_orbitCesaro hT hmeas (mul_nonneg hC hC) hbound] with x hx
  have he (n : ℕ) : T^[n + h] x = T^[h] (T^[n] x) := by rw [Nat.add_comm n h, iterate_add_apply]
  simpa only [orbitSequence, corr, he, id_eq, koopmanCorrelation, g] using hx

private theorem sub_limit_eq {x : ℕ → ℂ} {r u : ℕ → ℂ} (h : CorrLimits x x id r)
    {M : ℕ → ℕ} (hM : StrictMono M) (hu : CorrLimits x x M u) : u = r := by
  funext k
  exact tendsto_nhds_unique (hu k) ((h k).comp hM.tendsto_atTop)

theorem nearlyWeakMixing_of_full_self_corr {x : ℕ → ℂ} (hx : BoundedSeq x) {r : ℕ → ℂ}
    (hr : CorrLimits x x id r) (ht : Tendsto (realCesaro (fun h => ‖r (h+1)‖)) atTop (𝓝 0)) :
    NearlyWeakMixing x := by
  apply nearlyWeakMixing_of_self_mean hx
  intro M u hM hu
  rwa [sub_limit_eq hr hM hu]

theorem spectrallyLebesgue_of_full_self_corr {x : ℕ → ℂ} (hx : BoundedSeq x) {r : ℕ → ℂ}
    (hr : CorrLimits x x id r) {ν : FiniteMeasure UnitAddCircle} (hν : HasSpectrum r ν)
    (ha : (ν : Measure UnitAddCircle) ≪ circleHaar) : SpectrallyLebesgue x := by
  exact ⟨hx, fun M u hM hu => ⟨ν, (sub_limit_eq hr hM hu).symm ▸ hν, ha⟩⟩

theorem spectrallySingular_of_full_self_corr {x : ℕ → ℂ} (hx : BoundedSeq x) {r : ℕ → ℂ}
    (hr : CorrLimits x x id r) {ν : FiniteMeasure UnitAddCircle} (hν : HasSpectrum r ν)
    (hs : (ν : Measure UnitAddCircle).MutuallySingular circleHaar) : SpectrallySingular x := by
  exact ⟨hx, fun M u hM hu => ⟨ν, (sub_limit_eq hr hM hu).symm ▸ hν, hs⟩⟩

end Observable

section ContinuousTests

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem boundedObservable_of_continuous (f : C(X, ℂ)) : BoundedObservable f :=
  ⟨f.continuous.measurable, ‖f‖, norm_nonneg _, ContinuousMap.norm_coe_le_norm f⟩

omit [MeasurableSpace X] [BorelSpace X] in
private theorem norm_corr_pair_sub_le (f g : C(X, ℂ)) (a b : X) :
    ‖f a * star (f b) - g a * star (g b)‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  rw [show f a * star (f b) - g a * star (g b) =
      (f a-g a) * star (f b) + g a * star (f b-g b) by rw [star_sub]; ring]
  calc
    _ ≤ ‖(f a-g a)*star (f b)‖ + ‖g a * star (f b-g b)‖ := norm_add_le _ _
    _ ≤ ‖f-g‖*‖f‖ + ‖g‖*‖f-g‖ := by
      simp only [norm_mul, norm_star]
      exact add_le_add
        (mul_le_mul (ContinuousMap.norm_coe_le_norm (f-g) a) (ContinuousMap.norm_coe_le_norm f b)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (ContinuousMap.norm_coe_le_norm g a) (ContinuousMap.norm_coe_le_norm (f-g) b)
          (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

private theorem norm_koopmanCorrelation_sub_le (μ : Measure X) [IsProbabilityMeasure μ]
    {T : X → X} (hT : Measurable T) (f g : C(X, ℂ)) (h : ℕ) :
    ‖koopmanCorrelation μ T f h - koopmanCorrelation μ T g h‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  have hint (w : C(X, ℂ)) : Integrable (fun y => w (T^[h] y) * star (w y)) μ := by
    apply Integrable.of_bound (((w.continuous.measurable.comp (hT.iterate h)).mul
      (Complex.continuous_conj.measurable.comp w.continuous.measurable)).aestronglyMeasurable) (‖w‖*‖w‖)
    exact Eventually.of_forall fun y => by
      change ‖w (T^[h] y) * star (w y)‖ ≤ _
      rw [norm_mul, norm_star]
      exact mul_le_mul (ContinuousMap.norm_coe_le_norm w _) (ContinuousMap.norm_coe_le_norm w _)
        (norm_nonneg _) (norm_nonneg _)
  rw [koopmanCorrelation, koopmanCorrelation, ← integral_sub (hint f) (hint g)]
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Eventually.of_forall fun y => norm_corr_pair_sub_le f g (T^[h] y) y)

omit [MeasurableSpace X] [BorelSpace X] in
private theorem norm_orbit_corr_sub_le (T : X → X) (x : X) (f g : C(X, ℂ)) (h N : ℕ) :
    ‖corr (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) h N -
      corr (fun n => g (orbitSequence T x n)) (fun n => g (orbitSequence T x n)) h N‖ ≤
      ‖f-g‖*(‖f‖+‖g‖) := by
  rw [corr, corr, ← cesaro_sub]
  exact norm_cesaro_le _ (by positivity) (fun n => norm_corr_pair_sub_le f g _ _) N

/-- A single full-measure set works for all continuous tests and all lags. -/
theorem ae_continuous_orbit_correlation [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) : ∀ᵐ x ∂μ, ∀ f : C(X, ℂ),
      CorrLimits (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) id
        (koopmanCorrelation μ T f) := by
  classical
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense C(X, ℂ)
  have : Countable S := hSc.to_subtype
  have hS : ∀ᵐ x ∂μ, ∀ g : S,
      CorrLimits (fun n => g.1 (orbitSequence T x n)) (fun n => g.1 (orbitSequence T x n)) id
        (koopmanCorrelation μ T g.1) :=
    ae_all_iff.mpr fun g => ae_orbit_correlation hT (boundedObservable_of_continuous g.1)
  filter_upwards [hS] with x hx
  intro f h
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := min 1 (ε / (12 * (‖f‖ + 1)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hSd f) δ hδ
  rw [dist_eq_norm] at hfg
  have hgB : ‖g‖ ≤ ‖f‖+1 := by
    have hh := hfg.le.trans (min_le_left _ _ : δ ≤ 1)
    have ht := norm_add_le (g-f) f
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith only [hh, ht]
  have hE : ‖f-g‖*(‖f‖+‖g‖) ≤ ε/4 := by
    have hh := hfg.le.trans (min_le_right _ _ : δ ≤ ε/(12*(‖f‖+1)))
    refine (mul_le_mul hh (show ‖f‖+‖g‖ ≤ 2*‖f‖+1 by linarith only [hgB])
      (by positivity) (by positivity)).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 12*(‖f‖+1))]
    nlinarith only [hε, mul_nonneg hε.le (norm_nonneg f)]
  filter_upwards [Metric.tendsto_nhds.mp (hx ⟨g, hg⟩ h) (ε/3) (by positivity)] with N hN
  let a := corr (fun n => f (orbitSequence T x n)) (fun n => f (orbitSequence T x n)) h N
  let b := corr (fun n => g (orbitSequence T x n)) (fun n => g (orbitSequence T x n)) h N
  let u := koopmanCorrelation μ T g h
  let v := koopmanCorrelation μ T f h
  rw [dist_eq_norm] at hN ⊢
  have hab : ‖a-b‖ ≤ ε/4 := (norm_orbit_corr_sub_le T x f g h N).trans hE
  have huv : ‖u-v‖ ≤ ε/4 := by
    rw [norm_sub_rev]
    exact (norm_koopmanCorrelation_sub_le μ hT.measurable f g h).trans hE
  have hh : ‖a-v‖ ≤ ‖a-b‖ + ‖b-u‖ + ‖u-v‖ := by
    rw [show a-v = (a-b+(b-u))+(u-v) by ring]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  change ‖a-v‖ < ε
  change ‖b-u‖ < ε/3 at hN
  linarith only [hab, huv, hN, hh, hε]

/-- `LemmaConstructingSequences` (i), in the correlation formulation of weak mixing. -/
theorem ae_orbit_weaklyMixing [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hm : KoopmanWeakMixing μ T) :
    ∀ᵐ x ∂μ, WeaklyMixingDistribution μ (orbitSequence T x) := by
  filter_upwards [ae_continuous_orbit_correlation hT] with x hx
  intro f hf
  exact nearlyWeakMixing_of_full_self_corr (bounded_test f _) (hx f) (hm f (boundedObservable_of_continuous f) hf)

/-- `LemmaConstructingSequences` (ii). -/
theorem ae_orbit_spectrallyLebesgue [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hm : KoopmanLebesgueSpectrum μ T) :
    ∀ᵐ x ∂μ, SpectrallyLebesgueDistribution μ (orbitSequence T x) := by
  filter_upwards [ae_continuous_orbit_correlation hT] with x hx
  intro f hf
  obtain ⟨ν, hν, ha⟩ := hm f (boundedObservable_of_continuous f) hf
  exact spectrallyLebesgue_of_full_self_corr (bounded_test f _) (hx f) hν ha

/-- `LemmaConstructingSequences` (v). -/
theorem ae_orbit_spectrallySingular [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hm : KoopmanSingularSpectrum μ T) :
    ∀ᵐ x ∂μ, SpectrallySingularDistribution (orbitSequence T x) := by
  filter_upwards [ae_continuous_orbit_correlation hT] with x hx
  intro f
  obtain ⟨ν, hν, ha⟩ := hm f (boundedObservable_of_continuous f)
  exact spectrallySingular_of_full_self_corr (bounded_test f _) (hx f) hν ha

end ContinuousTests

section Visits

variable {X : Type*} [MeasurableSpace X]

def visitTimes (T : X → X) (A : Set X) (x : X) : Set ℕ := {n | orbitSequence T x n ∈ A}

noncomputable def visitObservable (A : Set X) (x : X) : ℂ := A.indicator (fun _ => 1) x

theorem boundedObservable_visit (A : Set X) (hA : MeasurableSet A) :
    BoundedObservable (visitObservable A) := by
  refine ⟨measurable_const.indicator hA, 1, zero_le_one, ?_⟩
  intro x
  unfold visitObservable
  by_cases hx : x ∈ A <;> simp [hx, zero_le_one]

omit [MeasurableSpace X] in
theorem visitObservable_orbit (T : X → X) (A : Set X) (x : X) (n : ℕ) :
    visitObservable A (orbitSequence T x n) = selectionWeight (visitTimes T A x) n := by
  by_cases h : orbitSequence T x n ∈ A <;> simp [visitObservable, selectionWeight, visitTimes, h]

theorem realCesaro_selectionWeight (A : Set ℕ) (N : ℕ) :
    realCesaro (fun n => (selectionWeight A n).re) N = (initialCount A N : ℝ) / N := by
  classical
  unfold realCesaro initialCount
  congr 1
  have hpt (n : ℕ) : (selectionWeight A n).re = if n ∈ A then 1 else 0 := by
    by_cases h : n ∈ A <;> simp [selectionWeight, h]
  simp only [hpt, ← Finset.sum_filter]
  simp

theorem ae_visit_density {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, Tendsto (fun N => (initialCount (visitTimes T A x) N : ℝ) / (N : ℝ)) atTop (𝓝 (μ.real A)) := by
  have hB := boundedObservable_visit A hA
  obtain ⟨C, hC, hb⟩ := hB.2
  filter_upwards [ae_tendsto_orbitCesaro hT hB.1 hC hb] with x hx
  have hCpx := Complex.continuous_re.continuousAt.tendsto.comp hx
  have hint : (∫ y, visitObservable A y ∂μ) = (μ.real A : ℂ) := by
    change (∫ y, A.indicator (fun _ => (1 : ℂ)) y ∂μ) = _
    rw [integral_indicator_const 1 hA, Complex.real_smul, mul_one]
  change Tendsto (fun N => (cesaro (fun n => visitObservable A (orbitSequence T x n)) N).re)
    atTop (𝓝 (∫ y, visitObservable A y ∂μ).re) at hCpx
  simpa only [← realCesaro_re, visitObservable_orbit,
    realCesaro_selectionWeight, hint, Complex.ofReal_re] using hCpx

theorem positiveLowerDensity_of_density_limit {A : Set ℕ} {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun N => (initialCount A N : ℝ) / (N : ℝ)) atTop (𝓝 a)) : HasPositiveLowerDensity A := by
  refine ⟨a/2, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ), h.eventually (lt_mem_nhds (show a/2 < a by linarith))] with N hn hu
  have hN : 0 < (N : ℝ) := by exact_mod_cast hn
  exact (le_div_iff₀ hN).mp hu.le

theorem exists_enumeration_of_positiveLowerDensity {A : Set ℕ} (h : HasPositiveLowerDensity A) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = A := by
  classical
  have hi : A.Infinite := by
    by_contra H
    have hf : A.Finite := Set.not_infinite.mp H
    obtain ⟨δ, hδ, hev⟩ := h
    obtain ⟨N, hN⟩ := exists_nat_gt ((hf.toFinset.card : ℝ)/δ)
    obtain ⟨n, hn, hn'⟩ := ((eventually_ge_atTop N).and hev).exists
    have hh : initialCount A n ≤ hf.toFinset.card := by
      unfold initialCount
      apply Finset.card_le_card
      intro i hi
      exact hf.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
    have hh' : (initialCount A n : ℝ) ≤ hf.toFinset.card := by exact_mod_cast hh
    have hlt : ((hf.toFinset.card : ℝ)/δ) < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
    have hc := (div_lt_iff₀ hδ).mp hlt
    nlinarith only [hn', hh', hc]
  have : Infinite A := hi.to_subtype
  let v := Nat.Subtype.orderIsoOfNat A
  refine ⟨fun n => (v n : ℕ), fun a b hab => v.strictMono hab, ?_⟩
  ext n
  constructor
  · rintro ⟨j, rfl⟩
    exact (v j).property
  · intro hn
    obtain ⟨j, hj⟩ := v.surjective ⟨n, hn⟩
    exact ⟨j, congrArg Subtype.val hj⟩

/-- `LemmaConstructingSequences` (vi), including the positive-density visit enumeration. -/
theorem ae_visits_spectrallySingular {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hs : KoopmanSingularSpectrum μ T) {A : Set X}
    (hA : MeasurableSet A) (hpos : 0 < μ A) :
    ∀ᵐ x ∂μ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
      HasPositiveLowerDensity (Set.range σ) ∧ SpectrallySingular (selectionWeight (Set.range σ)) := by
  have hp : 0 < μ.real A := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  have hB := boundedObservable_visit A hA
  obtain ⟨ν, hν, hS⟩ := hs (visitObservable A) hB
  filter_upwards [ae_visit_density hT hA, ae_orbit_correlation hT hB] with x hx hr
  have hd := positiveLowerDensity_of_density_limit hp hx
  obtain ⟨σ, hσ, hR⟩ := exists_enumeration_of_positiveLowerDensity hd
  refine ⟨σ, hσ, hR, ?_, ?_⟩
  · rwa [hR]
  · rw [hR]
    have hh := spectrallySingular_of_full_self_corr (hB.orbit_bounded T x) hr hν hS
    simpa only [visitObservable_orbit] using hh

end Visits

section Discrete

variable {X : Type*} [MeasurableSpace X]

/-- A bounded measurable Koopman eigenfunction with a unit-modulus eigenvalue. -/
structure BoundedKoopmanEigenfunction (μ : Measure X) (T : X → X) where
  value : X → ℂ
  bounded : BoundedObservable value
  eigenvalue : ℂ
  norm_eigenvalue : ‖eigenvalue‖ = 1
  eigen : ∀ᵐ x ∂μ, value (T x) = eigenvalue * value x

/-- The pure-point assumption in its L² approximation form. Coefficients can be
absorbed into the eigenfunctions, so it suffices to use finite sums. -/
def KoopmanDiscreteSpectrum (μ : Measure X) (T : X → X) : Prop :=
  ∀ f : X → ℂ, BoundedObservable f → ∀ ε : ℝ, 0 < ε →
    ∃ (k : ℕ) (e : Fin k → BoundedKoopmanEigenfunction μ T),
      (∫ x, ‖f x - ∑ i, (e i).value x‖ ^ 2 ∂μ) < ε

theorem ae_eigenfunction_orbit_pow {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    (e : BoundedKoopmanEigenfunction μ T) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, e.value (orbitSequence T x n) = e.value x * e.eigenvalue^n := by
  have hh : ∀ᵐ x ∂μ, ∀ n : ℕ,
      e.value (T (T^[n] x)) = e.eigenvalue * e.value (T^[n] x) :=
    ae_all_iff.mpr fun n => (hT.iterate n).quasiMeasurePreserving.ae e.eigen
  filter_upwards [hh] with x hx
  intro n
  induction n with
  | zero => simp [orbitSequence]
  | succ n ih =>
    simp only [orbitSequence, iterate_succ_apply', hx n] at ih ⊢
    rw [ih, pow_succ]
    ring

theorem compactAlong_exponential (a lam : ℂ) (hlam : ‖lam‖ = 1) {M : ℕ → ℕ} (hM : StrictMono M) :
    CompactAlong (fun n => a * lam^n) M := by
  classical
  refine ⟨⟨‖a‖, norm_nonneg _, fun n => by simp [norm_pow, hlam]⟩, hM, ?_⟩
  intro σ r hσ hr ε hε
  let u (m : ℕ) := a * lam^(m+1)
  have hclosed : closure (Set.range u) ⊆ Metric.closedBall (0 : ℂ) ‖a‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    rintro _ ⟨n, rfl⟩
    simp [u, Metric.mem_closedBall, norm_pow, hlam]
  have hcomp : IsCompact (closure (Set.range u)) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hclosed
  obtain ⟨s, hs, hfinite, hcover⟩ := exists_finite_cover_balls_of_isCompact_closure hcomp
    (Real.sqrt_pos.mpr hε)
  let j (z : ℂ) := if h : z ∈ Set.range u then Classical.choose h else 0
  have hj {z : ℂ} (hz : z ∈ s) : u (j z) = z := by
    unfold j
    rw [dite_eq_left (hs hz)]
    exact Classical.choose_spec (hs hz)
  obtain ⟨K, hK⟩ := (hfinite.image j).bddAbove
  refine ⟨K, fun m => ?_⟩
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self m))
  obtain ⟨hzs, hball⟩ := Set.mem_iUnion.mp hz
  let k := j z
  have hk : k ≤ K := hK ⟨z, hzs, rfl⟩
  have hnorm : ‖u m - u k‖ < Real.sqrt ε := by
    rw [hj hzs]
    simpa only [dist_eq_norm] using Metric.mem_ball.mp hball
  have hsq : ‖u m - u k‖^2 < ε := by
    rw [← Real.sq_sqrt hε.le]
    exact pow_lt_pow_left₀ hnorm (norm_nonneg _) (by decide)
  refine ⟨k, hk, ‖u m - u k‖^2, hsq, ?_⟩
  have hpoint (n : ℕ) : ‖a * lam^(n+(m+1)) - a * lam^(n+(k+1))‖^2 = ‖u m-u k‖^2 := by
    rw [pow_add lam n (m+1), pow_add lam n (k+1)]
    rw [show a * (lam^n * lam^(m+1)) - a * (lam^n * lam^(k+1)) = lam^n * (u m - u k) by dsimp [u]; ring]
    simp [norm_pow, hlam]
  simp only [hpoint]
  exact (realCesaro_const_tendsto (‖u m-u k‖^2)).comp (hM.comp hσ).tendsto_atTop

private theorem boundedObservable_finset_sum {ι : Type*} (s : Finset ι) (g : ι → X → ℂ)
    (hg : ∀ i, BoundedObservable (g i)) : BoundedObservable (fun x => ∑ i ∈ s, g i x) := by
  classical
  choose C hC hb using fun i => (hg i).2
  refine ⟨Finset.measurable_sum _ (fun i _ => (hg i).1), ∑ i ∈ s, C i,
    sum_nonneg (fun i _ => hC i), fun x => (norm_sum_le _ _).trans (sum_le_sum fun i _ => hb i x)⟩

theorem ae_orbit_test_compact_of_discrete {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hd : KoopmanDiscreteSpectrum μ T) {f : X → ℂ} (hf : BoundedObservable f) :
    ∀ᵐ x ∂μ, CompactSeq (fun n => f (orbitSequence T x n)) := by
  classical
  choose D e hE using fun k : ℕ => hd f hf (1/((k : ℝ)+1)) (by positivity)
  let g (k : ℕ) (x : X) := ∑ i : Fin (D k), (e k i).value x
  have hG (k : ℕ) : BoundedObservable (g k) :=
    boundedObservable_finset_sum univ (fun i => (e k i).value) (fun i => (e k i).bounded)
  have hComp (k : ℕ) : ∀ᵐ x ∂μ, CompactSeq (fun n => g k (orbitSequence T x n)) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin (D k) => ae_eigenfunction_orbit_pow hT.toMeasurePreserving (e k i))] with x hx
    unfold g
    apply compactAlong_finset_sum strictMono_id
    intro i _
    have hfun : (fun n => (e k i).value (orbitSequence T x n)) = fun n => (e k i).value x * (e k i).eigenvalue^n := funext (hx i)
    rw [hfun]
    exact compactAlong_exponential _ _ (e k i).norm_eigenvalue strictMono_id
  have hMean (k : ℕ) : ∀ᵐ x ∂μ,
      Tendsto (realCesaro (fun n => ‖f (orbitSequence T x n)-g k (orbitSequence T x n)‖^2)) atTop
        (𝓝 (∫ y, ‖f y-g k y‖^2 ∂μ)) := by
    obtain ⟨C, hC, hb⟩ := hf.2
    obtain ⟨B, hB, hc⟩ := (hG k).2
    let U (y : X) := ‖f y-g k y‖^2
    have hU : Measurable U := (hf.1.sub (hG k).1).norm.pow_const _
    have hBound (y : X) : |U y| ≤ (C+B)^2 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hb y) (hc y))) 2
    exact ae_tendsto_orbitCesaro_real hT hU (sq_nonneg _) hBound
  filter_upwards [ae_all_iff.mpr hComp, ae_all_iff.mpr hMean] with x hx hx'
  apply compactAlong_of_meanSquare_approximation (hf.orbit_bounded T x) strictMono_id
  intro ε hε
  have ht : Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨fun n => g k (orbitSequence T x n), hx k, ?_⟩
  have hu : (∫ y, ‖f y-g k y‖^2 ∂μ) < ε := (hE k).trans hk
  exact ((hx' k).eventually (gt_mem_nhds hu)).mono (fun _ h => h.le)

/-- `LemmaConstructingSequences` (iv), including the positive-density visit enumeration. -/
theorem ae_visits_compact {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ) (hs : KoopmanDiscreteSpectrum μ T) {A : Set X}
    (hA : MeasurableSet A) (hpos : 0 < μ A) :
    ∀ᵐ x ∂μ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Set.range σ = visitTimes T A x ∧
      HasPositiveLowerDensity (Set.range σ) ∧ CompactSeq (selectionWeight (Set.range σ)) := by
  have hp : 0 < μ.real A := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  filter_upwards [ae_visit_density hT hA, ae_orbit_test_compact_of_discrete hT hs (boundedObservable_visit A hA)] with x hx hc
  have hd := positiveLowerDensity_of_density_limit hp hx
  obtain ⟨σ, hσ, hR⟩ := exists_enumeration_of_positiveLowerDensity hd
  refine ⟨σ, hσ, hR, ?_, ?_⟩
  · rwa [hR]
  · rw [hR]
    simpa only [visitObservable_orbit] using hc

end Discrete

/-- `LemmaConstructingSequences` (iii). Deduce one full-measure set for all
continuous tests from the countable dense family and compact L² closure. -/
theorem ae_orbit_compact {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SeparableSpace C(X, ℂ)] {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) (hd : KoopmanDiscreteSpectrum μ T) :
    ∀ᵐ x ∂μ, CompactDistribution (orbitSequence T x) := by
  classical
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense C(X, ℂ)
  have : Countable S := hSc.to_subtype
  have hS : ∀ᵐ x ∂μ, ∀ g : S, CompactSeq (fun n => g.1 (orbitSequence T x n)) :=
    ae_all_iff.mpr fun g => ae_orbit_test_compact_of_discrete hT hd (boundedObservable_of_continuous g.1)
  filter_upwards [hS] with x hx
  intro f
  apply compactAlong_of_meanSquare_approximation (bounded_test f _) strictMono_id
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hSd f) (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  rw [dist_eq_norm] at hfg
  refine ⟨fun n => g (orbitSequence T x n), hx ⟨g, hg⟩, Eventually.of_forall fun N => ?_⟩
  have hh (n : ℕ) : ‖f (orbitSequence T x n)-g (orbitSequence T x n)‖^2 ≤ ε := by
    rw [← Real.sq_sqrt hε.le]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((ContinuousMap.norm_coe_le_norm (f-g) _).trans hfg.le) 2
  by_cases hN : 0 < N
  · exact (realCesaro_mono hh N).trans_eq (realCesaro_const_pos ε hN)
  · simp [realCesaro, Nat.eq_zero_of_not_pos hN, hε.le]

end VdC
