/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralDual
public import Mixing.MildMixing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Hilbert-space spectral criteria in the measure class -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- Vanishing of the weak ultrafilter coefficient persists after multiplying
the spectral Fourier integrand by an arbitrary integrable scalar weight. -/
theorem tendsto_weighted_spectralCoefficient_zero (x : H) (p : Ultrafilter G)
    (hx : ultrafilterOperator U p x = 0)
    (w : RepresentationSpectrum U → ℂ) (hw : Measurable w)
    (hInt : Integrable w (vectorSpectralMeasure U x)) :
    Tendsto (fun g => ∫ z, w z * spectralCoefficient U g z ∂vectorSpectralMeasure U x)
      (p : Filter G) (𝓝 0) := by
  let μ := vectorSpectralMeasure U x
  let A (n : ℕ) : Set (RepresentationSpectrum U) := {z | ‖w z‖ ≤ n}
  let wN (n : ℕ) := (A n).indicator w
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le hw.norm measurable_const
  have hm (n : ℕ) : Measurable (wN n) := hw.indicator (hA n)
  have hBound (n : ℕ) (z : RepresentationSpectrum U) : ‖wN n z‖ ≤ n := by
    by_cases hz : z ∈ A n
    · change ‖(A n).indicator w z‖ ≤ n
      rw [Set.indicator_of_mem hz]
      exact hz
    · simp [wN, Set.indicator_of_notMem hz]
  have hiN (n : ℕ) : Integrable (wN n) μ :=
    Integrable.of_bound (hm n).aestronglyMeasurable n (.of_forall (hBound n))
  have hIntMul (g : G) (f : RepresentationSpectrum U → ℂ) (hf : Measurable f)
      (hi : Integrable f μ) : Integrable (fun z => f z * spectralCoefficient U g z) μ := by
    apply hi.norm.mono' (hf.mul (spectralCoefficient U g).continuous.measurable).aestronglyMeasurable
    exact .of_forall fun z => by
      rw [Pi.mul_apply, norm_mul, spectralCoefficient_apply, Circle.norm_coe, mul_one]
  have hCutLim (n : ℕ) : Tendsto (fun g => ∫ z, wN n z * spectralCoefficient U g z ∂μ)
      (p : Filter G) (𝓝 0) := by
    have hLp : MemLp (fun z => conj (wN n z)) 2 μ :=
      MemLp.of_bound (Complex.continuous_conj.measurable.comp (hm n)).aestronglyMeasurable n
        (.of_forall fun z => by simpa only [Complex.norm_conj] using hBound n z)
    let y := cyclicSpectralIsometry U x (hLp.toLp _)
    have hCoeff (g : G) : (∫ z, wN n z * spectralCoefficient U g z ∂μ) = ⟪y, U g x⟫_ℂ := by
      change _ = ⟪y, linearRepresentation U g x⟫_ℂ
      rw [← spectralCalculus_spectralCoefficient U g]
      change _ = ⟪cyclicSpectralIsometry U x (hLp.toLp _), spectralCalculus U (spectralCoefficient U g) x⟫_ℂ
      rw [inner_cyclicSpectralIsometry_spectralCalculus, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hLp.coeFn_toLp, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ
        (spectralCoefficient U g)] with z hz hz'
      rw [hz, hz', RCLike.inner_apply', starRingEnd_self_apply]
    have ht := tendsto_ultrafilterOperator_coeff U p y x
    rw [hx, inner_zero_right] at ht
    simpa only [hCoeff] using ht
  have hTail (n : ℕ) (z : RepresentationSpectrum U) : ‖w z - wN n z‖ ≤ ‖w z‖ := by
    by_cases hz : z ∈ A n
    · simp [wN, Set.indicator_of_mem hz]
    · simp [wN, Set.indicator_of_notMem hz]
  have hTailLim (z : RepresentationSpectrum U) : Tendsto (fun n => ‖w z - wN n z‖) atTop (𝓝 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖w z‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hz : z ∈ A n := hN.trans (by exact_mod_cast hn)
    simp [wN, Set.indicator_of_mem hz]
  have hL1 : Tendsto (fun n => ∫ z, ‖w z - wN n z‖ ∂μ) atTop (𝓝 0) := by
    simpa only [Pi.sub_apply, integral_zero] using
      tendsto_integral_of_dominated_convergence (μ := μ) (fun z => ‖w z‖)
        (fun n => ((hw.sub (hm n)).norm).aestronglyMeasurable) hInt.norm
        (fun n => .of_forall fun z => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          exact hTail n z) (.of_forall hTailLim)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (hL1.eventually_lt_const (half_pos hε)).exists
  filter_upwards [(hCutLim n).norm.eventually_lt_const (show ‖(0 : ℂ)‖ < ε / 2 by simpa using half_pos hε)]
    with g hg
  rw [dist_zero_right]
  have hErr : ‖(∫ z, w z * spectralCoefficient U g z ∂μ) -
      ∫ z, wN n z * spectralCoefficient U g z ∂μ‖ ≤ ∫ z, ‖w z - wN n z‖ ∂μ := by
    rw [← integral_sub' (hIntMul g w hw hInt) (hIntMul g (wN n) (hm n) (hiN n))]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    exact .of_forall fun z => by
      simp only [Pi.sub_apply]
      rw [← sub_mul, norm_mul, spectralCoefficient_apply, Circle.norm_coe, mul_one]
  let a := ∫ z, w z * spectralCoefficient U g z ∂μ
  let b := ∫ z, wN n z * spectralCoefficient U g z ∂μ
  have hTri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a - b) b
  have hTri' : ‖a‖ ≤ (∫ z, ‖w z - wN n z‖ ∂μ) + ‖b‖ :=
    hTri.trans (add_le_add hErr le_rfl)
  exact hTri'.trans_lt (by linarith [add_lt_add hn hg])

/-- Every finite positive measure absolutely continuous with respect to the
spectral measure of a vector in the ultrafilter kernel has a vanishing
Fourier transform along that ultrafilter. -/
theorem tendsto_spectralFourier_zero_of_ac (x : H) (p : Ultrafilter G)
    (hx : ultrafilterOperator U p x = 0) (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν]
    (hν : ν ≪ dualVectorSpectralMeasure U x) :
    Tendsto (spectralFourier ν) (p : Filter G) (𝓝 0) := by
  let σ := dualVectorSpectralMeasure U x
  let w (χ : DiscreteDual G) : ℂ := ((ν.rnDeriv σ χ).toReal : ℂ)
  have hw : Measurable w :=
    Complex.continuous_ofReal.measurable.comp ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
  have hwi : Integrable w σ :=
    (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := σ)).ofReal
  let f := spectralPointDual U
  have hf : Measurable f := (spectralPointDual_continuous U).measurable
  have hlim := tendsto_weighted_spectralCoefficient_zero U x p hx (w ∘ f) (hw.comp hf)
    (hwi.comp_measurable hf)
  refine hlim.congr' (.of_forall fun g => ?_)
  change (∫ z, w (f z) * spectralCoefficient U g z ∂vectorSpectralMeasure U x) =
    ∫ χ, (dualEvaluation g χ : ℂ) ∂ν
  have hIntegrand (z : RepresentationSpectrum U) :
      w (f z) * spectralCoefficient U g z = w (f z) * (dualEvaluation g (f z) : ℂ) := rfl
  simp_rw [hIntegrand]
  have hMeas : Measurable fun χ => w χ * (dualEvaluation g χ : ℂ) :=
    hw.mul (continuous_subtype_val.comp (dualEvaluation g).continuous).measurable
  calc
    _ = ∫ χ, w χ * (dualEvaluation g χ : ℂ) ∂σ :=
      (integral_map hf.aemeasurable hMeas.aestronglyMeasurable).symm
    _ = _ := integral_rnDeriv_smul hν

/-- A vector whose spectral measure dominates all vector spectral measures
represents the maximal spectral type. -/
def IsMaximalSpectralVector (x : H) : Prop :=
  ∀ y : H, dualVectorSpectralMeasure U y ≪ dualVectorSpectralMeasure U x

/-- The measure-class form of Theorem 6.1(ii) for finite positive measures.
The right side allows every measure dominated by the maximal spectral type,
which is stronger than testing only equivalent measures. -/
theorem theorem6_1_ii_positiveMeasureClass (P : Set (Ultrafilter G))
    (x : H) (hx : IsMaximalSpectralVector U x) :
    IsUMixing U P ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν], ν ≪ dualVectorSpectralMeasure U x →
        ∀ p ∈ P, ∀ q : Ultrafilter G,
          Tendsto (spectralFourier ν) ((q * p : Ultrafilter G) : Filter G) (𝓝 0) := by
  constructor
  · intro h ν _ hν p hp q
    apply tendsto_spectralFourier_zero_of_ac U x (q * p) _ ν hν
    rw [ultrafilterOperator_mul, h p hp, mul_zero, zero_apply]
  · intro h
    apply (isUMixing_iff_all_vector_fourier_vanish U P).mpr
    intro y p hp q
    exact @h (dualVectorSpectralMeasure U y) _ (hx y) p hp q

/-- Theorem 6.1(ii) phrased using exactly the mutually absolutely continuous
finite positive representatives of the maximal spectral type. -/
theorem theorem6_1_ii_equivalent_positiveMeasureClass (P : Set (Ultrafilter G))
    (x : H) (hx : IsMaximalSpectralVector U x) :
    IsUMixing U P ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν],
        ν ≪ dualVectorSpectralMeasure U x → dualVectorSpectralMeasure U x ≪ ν →
        ∀ p ∈ P, ∀ q : Ultrafilter G,
          Tendsto (spectralFourier ν) ((q * p : Ultrafilter G) : Filter G) (𝓝 0) := by
  constructor
  · intro h ν _ hν _
    have hm := (theorem6_1_ii_positiveMeasureClass U P x hx).mp h
    exact @hm ν _ hν
  · intro h
    apply (isUMixing_iff_all_vector_fourier_vanish U P).mpr
    intro y p hp q
    have hZero : ultrafilterOperator U p x = 0 := by
      let r := inverseUltrafilter p * p
      have hRefl := Measure.AbsolutelyContinuous.refl (dualVectorSpectralMeasure U x)
      have hFourier := @h (dualVectorSpectralMeasure U x) _ hRefl hRefl p hp (inverseUltrafilter p)
      rw [funext (spectralFourier_dualVectorSpectralMeasure U x)] at hFourier
      have he := tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U r x x) hFourier
      rw [show r = inverseUltrafilter p * p from rfl, ultrafilterOperator_mul,
        ultrafilterOperator_inverse] at he
      change ⟪x, (ultrafilterOperator U p).adjoint (ultrafilterOperator U p x)⟫_ℂ = 0 at he
      rw [ContinuousLinearMap.adjoint_inner_right] at he
      exact inner_self_eq_zero.mp he
    have hZero' : ultrafilterOperator U (q * p) x = 0 := by
      rw [ultrafilterOperator_mul]
      change ultrafilterOperator U q (ultrafilterOperator U p x) = _
      rw [hZero, map_zero]
    exact tendsto_spectralFourier_zero_of_ac U x (q * p) hZero' (dualVectorSpectralMeasure U y) (hx y)

/-- Theorem 6.1(iii). Every finite positive representative of the maximal
spectral type is Rajchman exactly when the representation is strongly mixing. -/
theorem theorem6_1_iii_equivalent_positiveMeasureClass
    (x : H) (hx : IsMaximalSpectralVector U x) :
    IsStronglyMixing U ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν],
        ν ≪ dualVectorSpectralMeasure U x → dualVectorSpectralMeasure U x ≪ ν →
        Tendsto (spectralFourier ν) cofinite (𝓝 0) := by
  rw [isStronglyMixing_iff_isUMixing_free U, theorem6_1_ii_equivalent_positiveMeasureClass U _ x hx]
  constructor
  · intro h ν _ hν hν'
    apply (Filter.tendsto_iff_ultrafilter _ _ _).mpr
    intro p hp
    have hlim := @h ν _ hν hν' p hp (pure 1)
    have heq : (pure 1 : Ultrafilter G) * p = p := by
      apply Ultrafilter.coe_inj.mp
      ext S
      change (∀ᶠ a in ((pure 1 * p : Ultrafilter G) : Filter G), a ∈ S) ↔
        ∀ᶠ a in (p : Filter G), a ∈ S
      simp [Ultrafilter.eventually_mul]
    rwa [heq] at hlim
  · intro h ν _ hν hν' p hp q
    exact (@h ν _ hν hν').mono_left (mul_mem_freeUltrafilters (p := q) hp)

/-- Theorem 6.1(iv). Set the reference measure to Haar measure to obtain the
absolutely continuous spectral criterion. -/
theorem theorem6_1_iv_equivalent_positiveMeasureClass (reference : Measure (DiscreteDual G))
    (x : H) (hx : IsMaximalSpectralVector U x) :
    (∀ y : H, dualVectorSpectralMeasure U y ≪ reference) ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν],
        ν ≪ dualVectorSpectralMeasure U x → dualVectorSpectralMeasure U x ≪ ν → ν ≪ reference := by
  constructor
  · intro h ν _ hν _
    exact hν.trans (h x)
  · intro h y
    let σ := dualVectorSpectralMeasure U x
    have hσ := @h σ _ (Measure.AbsolutelyContinuous.refl σ) (Measure.AbsolutelyContinuous.refl σ)
    exact (hx y).trans hσ

end Mixing
