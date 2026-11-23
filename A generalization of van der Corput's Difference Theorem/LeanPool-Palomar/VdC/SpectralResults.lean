/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Orthogonal
public import VdC.Realization
public import VdC.SpectralAC
public import VdC.SpectralOrthogonality
public import VdC.SpectralScalars

/-! # Spectral consequences for permissible autocorrelation limits -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal ComplexConjugate

namespace VdC

noncomputable section

/-- Lemma `CreatingSpectrallyLebesgue/NWMSequences` (i). -/
theorem spectrallyLebesgue_of_limsup_square_summable {x : ℕ → ℂ} (hx : BoundedSeq x)
    (h : Summable (fun j : ℕ => limsup (fun N => ‖corr x x (j+1) N‖ ^ 2) atTop)) :
    SpectrallyLebesgue x := by
  refine ⟨hx, ?_⟩
  intro N r hN hr
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hx hN hr
  refine ⟨μ, hμ, fourier_positive_l2_absolutelyContinuous μ ?_⟩
  obtain ⟨C, hC, hbound⟩ := hx
  simp_rw [show ∀ a : ℕ, measureFourier μ (a : ℤ) = r a from hμ]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ h
  intro j
  have ht := (hr (j+1)).norm.pow 2
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => ‖corr x x (j+1) n‖ ^ 2) := by
    refine ⟨(C*C)^2, eventually_map.2 (Eventually.of_forall fun n => ?_)⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_corr_le hC hC hbound hbound (j+1) n) 2
  exact le_limsup_of_le hb fun _ he => le_of_tendsto ht (hN.tendsto_atTop.eventually he)

def pairSequences (x y : ℕ → ℂ) : Fin 2 → ℕ → ℂ :=
  fun i => if i = 0 then x else y

theorem exists_pair_spectra {x y : ℕ → ℂ} {N : ℕ → ℕ} (hp : PermissibleTriple x y N) :
    ∃ (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle),
      (∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j)) ∧
      ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n := by
  obtain ⟨xx, hxx⟩ := hp.xx
  obtain ⟨xy, hxy⟩ := hp.xy
  obtain ⟨yx, hyx⟩ := hp.yx
  obtain ⟨yy, hyy⟩ := hp.yy
  let r : Fin 2 → Fin 2 → ℕ → ℂ := fun i j =>
    if i = 0 then (if j = 0 then xx else xy) else (if j = 0 then yx else yy)
  have hr (i j : Fin 2) : CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j) := by
    fin_cases i <;> fin_cases j
    · exact hxx
    · exact hxy
    · exact hyx
    · exact hyy
  have hb (i : Fin 2) : BoundedSeq (pairSequences x y i) := by
    fin_cases i
    · exact hp.boundedX
    · exact hp.boundedY
  obtain ⟨M, hM⟩ := exists_joint_corr_spectrum (pairSequences x y) N r hb hp.strictMono hr
  exact ⟨r, M, hr, hM⟩

def baseVector (i : Fin 2) : Fin 2 → ℂ := Pi.single i 1

private theorem pairSpectrum_basis (r : Fin 2 → Fin 2 → ℕ → ℂ)
    (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (i : Fin 2) :
    HasSpectrum (r i i) (M (baseVector i)) := by
  intro n
  rw [hM]
  fin_cases i <;> simp [spectralQuadratic, baseVector, Pi.single_apply,
    integerCorrelation]

theorem pairSpectrum_ac {x y : ℕ → ℂ} {N : ℕ → ℕ} (hN : StrictMono N)
    (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hr : ∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j))
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (i : Fin 2) (h : SpectrallyLebesgue (pairSequences x y i)) :
    (M (baseVector i) : Measure UnitAddCircle) ≪ circleHaar := by
  obtain ⟨μ, hμ, hac⟩ := h.2 N (r i i) hN (hr i i)
  have he : (M (baseVector i) : Measure UnitAddCircle) = μ :=
    measure_eq_of_fourier_nat (fun n => (pairSpectrum_basis r M hM i n).trans (hμ n).symm)
  rwa [he]

private theorem pairSpectrum_singular {x y : ℕ → ℂ} {N : ℕ → ℕ} (hN : StrictMono N)
    (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hr : ∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j))
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (i : Fin 2) (h : SpectrallySingular (pairSequences x y i)) :
    (M (baseVector i) : Measure UnitAddCircle).MutuallySingular circleHaar := by
  obtain ⟨μ, hμ, hsing⟩ := h.2 N (r i i) hN (hr i i)
  have he : (M (baseVector i) : Measure UnitAddCircle) = μ :=
    measure_eq_of_fourier_nat (fun n => (pairSpectrum_basis r M hM i n).trans (hμ n).symm)
  rwa [he]

/-- The Lebesgue/singular dichotomy on a fixed permissible subsequence. -/
theorem cross_zero_of_ac_singular {x y : ℕ → ℂ} {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hx : SpectrallyLebesgue x) (hy : SpectrallySingular y)
    (hp : PermissibleTriple x y N) (hr : CorrLimits x y N r) :
    r 0 = 0 := by
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hxa := pairSpectrum_ac hp.strictMono c M hc hM 0 hx
  have hys := pairSpectrum_singular hp.strictMono c M hc hM 1 hy
  have hperp := hys.symm.mono_ac hxa Measure.AbsolutelyContinuous.rfl
  have herm := corrLimits_hermitian_zero (pairSequences x y) N c hc 0 1
  have hz := correlation_measures_orthogonal M (integerCorrelation c) hM hperp herm
  exact (tendsto_nhds_unique (hr 0) (hc 0 1 0)).trans hz

/-- Cesàro averages of x times the conjugate of y vanish. -/
theorem corr_tendsto_zero_of_ac_singular {x y : ℕ → ℂ}
    (hx : SpectrallyLebesgue x) (hy : SpectrallySingular y) :
    Tendsto (corr x y 0) atTop (𝓝 0) := by
  apply tendsto_atTop_of_permissible_refinement hx.1 hy.1 (M := id) strictMono_id
  intro φ _ hp
  obtain ⟨r, hr⟩ := hp.xy
  have hz := cross_zero_of_ac_singular hx hy hp hr
  simpa only [hz, Function.comp_def, id_eq] using hr 0

/-- Lemma `ErgodicDichotomyForSequences` (i), written as the ordinary
product in the paper. -/
theorem cesaro_product_tendsto_zero_of_ac_singular {x y : ℕ → ℂ}
    (hx : SpectrallyLebesgue x) (hy : SpectrallySingular y) :
    Tendsto (cesaro (fun n => x n * y n)) atTop (𝓝 0) := by
  convert corr_tendsto_zero_of_ac_singular hx hy.conj using 1
  ext N
  simp only [corr, Nat.add_zero, Complex.star_def, starRingEnd_self_apply]

private theorem pairSequences_combo_add (x y : ℕ → ℂ) :
    sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1) =
      fun n => x n + y n := by
  funext n
  simp [sequenceCombination, Fin.sum_univ_two, pairSequences, baseVector, Pi.single_apply]

private theorem pairSequences_combo_sub (x y : ℕ → ℂ) :
    sequenceCombination (pairSequences x y) (baseVector 0 - baseVector 1) =
      fun n => x n - y n := by
  funext n
  simp [sequenceCombination, Fin.sum_univ_two, pairSequences, baseVector, Pi.single_apply,
    sub_eq_add_neg]

private theorem pairSpectrum_combination {x y : ℕ → ℂ} {N : ℕ → ℕ}
    (r : Fin 2 → Fin 2 → ℕ → ℂ) (M : (Fin 2 → ℂ) → FiniteMeasure UnitAddCircle)
    (hr : ∀ i j, CorrLimits (pairSequences x y i) (pairSequences x y j) N (r i j))
    (hM : ∀ z n, measureFourier (M z) n = spectralQuadratic (integerCorrelation r) z n)
    (z : Fin 2 → ℂ) :
    CorrLimits (sequenceCombination (pairSequences x y) z)
      (sequenceCombination (pairSequences x y) z) N (fun h => measureFourier (M z) (h : ℤ)) := by
  simp_rw [hM, spectralQuadratic]
  exact corrLimits_sequenceCombination (pairSequences x y) z N r hr

/-- Closure of spectral Lebesgue sequences under addition. -/
theorem SpectrallyLebesgue.add {x y : ℕ → ℂ} (hx : SpectrallyLebesgue x)
    (hy : SpectrallyLebesgue y) : SpectrallyLebesgue (fun n => x n + y n) := by
  let z := baseVector 0 + baseVector 1
  have hb (i : Fin 2) : BoundedSeq (pairSequences x y i) := by
    fin_cases i
    · exact hx.1
    · exact hy.1
  refine ⟨pairSequences_combo_add x y ▸ bounded_sequenceCombination (pairSequences x y) z hb,
    ?_⟩
  intro N r hN hr
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hx.1 hy.1 hN
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hs := pairSpectrum_combination c M hc hM z
  change CorrLimits (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1))
    (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1)) (N ∘ φ) _ at hs
  rw [pairSequences_combo_add] at hs
  refine ⟨M z, fun n => tendsto_nhds_unique (hs n) ((hr n).comp hφ.tendsto_atTop), ?_⟩
  exact combinationMeasure_add_absolutelyContinuous M (integerCorrelation c) hM
    (baseVector 0) (baseVector 1) circleHaar
    (pairSpectrum_ac hp.strictMono c M hc hM 0 hx)
    (pairSpectrum_ac hp.strictMono c M hc hM 1 hy)

/-- Closure of spectrally singular sequences under addition. -/
theorem SpectrallySingular.add {x y : ℕ → ℂ} (hx : SpectrallySingular x)
    (hy : SpectrallySingular y) : SpectrallySingular (fun n => x n + y n) := by
  let v := baseVector 0
  let w := baseVector 1
  have hb (i : Fin 2) : BoundedSeq (pairSequences x y i) := by
    fin_cases i
    · exact hx.1
    · exact hy.1
  refine ⟨pairSequences_combo_add x y ▸ bounded_sequenceCombination (pairSequences x y) (v+w) hb,
    ?_⟩
  intro N r hN hr
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hx.1 hy.1 hN
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  have hs := pairSpectrum_combination c M hc hM (v+w)
  change CorrLimits (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1))
    (sequenceCombination (pairSequences x y) (baseVector 0 + baseVector 1)) (N ∘ φ) _ at hs
  rw [pairSequences_combo_add] at hs
  refine ⟨M (v+w), fun n => tendsto_nhds_unique (hs n) ((hr n).comp hφ.tendsto_atTop), ?_⟩
  let ν := (M v : Measure UnitAddCircle) + (M w : Measure UnitAddCircle)
  have hvs : (M v : Measure UnitAddCircle).MutuallySingular circleHaar :=
    pairSpectrum_singular hp.strictMono c M hc hM 0 hx
  have hws : (M w : Measure UnitAddCircle).MutuallySingular circleHaar :=
    pairSpectrum_singular hp.strictMono c M hc hM 1 hy
  have hvd : (M v : Measure UnitAddCircle) ≪ ν := by
    intro A hA
    change ((M v : Measure UnitAddCircle) + (M w : Measure UnitAddCircle)) A = 0 at hA
    rw [add_apply] at hA
    exact (add_eq_zero.mp hA).1
  have hwd : (M w : Measure UnitAddCircle) ≪ ν := by
    intro A hA
    change ((M v : Measure UnitAddCircle) + (M w : Measure UnitAddCircle)) A = 0 at hA
    rw [add_apply] at hA
    exact (add_eq_zero.mp hA).2
  exact (hvs.add_left hws).mono_ac (combinationMeasure_add_absolutelyContinuous M
    (integerCorrelation c) hM v w ν hvd hwd) Measure.AbsolutelyContinuous.rfl

/-- Any measurable mass of the original spectrum lying outside the
approximant's spectrum is bounded by the upper Cesàro mean-square error. -/
private theorem coupled_spectrum_error {x y : ℕ → ℂ} {N : ℕ → ℕ} {r : ℕ → ℂ}
    (hx : BoundedSeq x) (hy : BoundedSeq y) (hN : StrictMono N) (hr : CorrLimits x x N r)
    (μ : FiniteMeasure UnitAddCircle) (hμ : HasSpectrum r μ) {ε : ℝ}
    (hdist : ∀ᶠ N in atTop, realCesaro (fun n => ‖x n - y n‖ ^ 2) N ≤ ε) :
    ∃ (φ : ℕ → ℕ) (ry : ℕ → ℂ) (ν : FiniteMeasure UnitAddCircle),
      StrictMono φ ∧ CorrLimits y y (N ∘ φ) ry ∧ HasSpectrum ry ν ∧
        ∀ A : Set UnitAddCircle, (ν : Measure UnitAddCircle) A = 0 →
          (μ : Measure UnitAddCircle).real A ≤ ε := by
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hx hy hN
  obtain ⟨c, M, hc, hM⟩ := exists_pair_spectra hp
  let v := baseVector 0
  let w := baseVector 1
  have heq : (μ : Measure UnitAddCircle) = M v := by
    apply measure_eq_of_fourier_nat
    intro n
    rw [hμ, pairSpectrum_basis c M hM 0 n]
    exact tendsto_nhds_unique ((hr n).comp hφ.tendsto_atTop) (hc 0 0 n)
  refine ⟨φ, c 1 1, M w, hφ, hc 1 1, pairSpectrum_basis c M hM 1, ?_⟩
  intro A hA
  have heqA := combinationMeasure_apply_of_null M (integerCorrelation c) hM (v-w) w A hA
  rw [sub_add_cancel] at heqA
  have hcorr := pairSpectrum_combination c M hc hM (v-w)
  change CorrLimits (sequenceCombination (pairSequences x y) (baseVector 0 - baseVector 1))
    (sequenceCombination (pairSequences x y) (baseVector 0 - baseVector 1)) (N ∘ φ) _ at hcorr
  rw [pairSequences_combo_sub] at hcorr
  have hRe := (Complex.continuous_re.tendsto _).comp (hcorr 0)
  simp only [Function.comp_def, re_corr_zero, Int.natCast_zero, measureFourier_zero,
    Complex.ofReal_re] at hRe
  rw [heq, Measure.real, heqA]
  have hbound : (M (v-w) : Measure UnitAddCircle).real Set.univ ≤ ε :=
    le_of_tendsto hRe (hp.strictMono.tendsto_atTop.eventually hdist)
  exact (measureReal_mono (Set.subset_univ A)).trans hbound

/-- Closure under limits in upper Cesàro mean square. The stated eventual
bound follows by taking any smaller approximation error in a limsup version. -/
theorem spectrallyLebesgue_of_meanSquare_approximation {x : ℕ → ℂ} (hx : BoundedSeq x)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ y : ℕ → ℂ, SpectrallyLebesgue y ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖x n - y n‖ ^ 2) N ≤ ε) :
    SpectrallyLebesgue x := by
  refine ⟨hx, ?_⟩
  intro N r hN hr
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hx hN hr
  refine ⟨μ, hμ, ?_⟩
  intro A hA
  have hsmall (ε : ℝ) (hε : 0 < ε) : (μ : Measure UnitAddCircle).real A ≤ ε := by
    obtain ⟨y, hy, hdist⟩ := happrox ε hε
    obtain ⟨φ, ry, ν, hφ, hry, hν, hcomp⟩ :=
      coupled_spectrum_error hx hy.1 hN hr μ hμ hdist
    obtain ⟨ν', hν', hac⟩ := hy.2 (N ∘ φ) ry (hN.comp hφ) hry
    have hEq : (ν : Measure UnitAddCircle) = ν' :=
      measure_eq_of_fourier_nat fun n => (hν n).trans (hν' n).symm
    apply hcomp A
    rw [hEq]
    exact hac hA
  have hz : (μ : Measure UnitAddCircle).real A = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra! hh
    have hp : 0 < (μ : Measure UnitAddCircle).real A := hh
    have hbound := hsmall ((μ : Measure UnitAddCircle).real A / 2) (div_pos hp (by norm_num))
    linarith only [hp, hbound]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz

/-- Closure of spectrally singular sequences under upper Cesàro
mean-square approximation, using the union of the approximants'
null-Haar supporting sets. -/
theorem spectrallySingular_of_meanSquare_approximation {x : ℕ → ℂ} (hx : BoundedSeq x)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ y : ℕ → ℂ, SpectrallySingular y ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖x n - y n‖ ^ 2) N ≤ ε) :
    SpectrallySingular x := by
  refine ⟨hx, ?_⟩
  intro N r hN hr
  obtain ⟨μ, hμ⟩ := exists_corr_spectrum hx hN hr
  refine ⟨μ, hμ, ?_⟩
  let δ (k : ℕ) : ℝ := (((k + 1 : ℕ) : ℝ))⁻¹
  have hs (k : ℕ) : ∃ A : Set UnitAddCircle, MeasurableSet A ∧ circleHaar A = 0 ∧
      (μ : Measure UnitAddCircle).real Aᶜ ≤ δ k := by
    obtain ⟨y, hy, hdist⟩ := happrox (δ k) (by dsimp [δ]; positivity)
    obtain ⟨φ, ry, ν, hφ, hry, hν, hcomp⟩ :=
      coupled_spectrum_error hx hy.1 hN hr μ hμ hdist
    obtain ⟨ν', hν', hsing⟩ := hy.2 (N ∘ φ) ry (hN.comp hφ) hry
    have hEq : (ν : Measure UnitAddCircle) = ν' :=
      measure_eq_of_fourier_nat fun n => (hν n).trans (hν' n).symm
    obtain ⟨A, hA, hνA, hHA⟩ := hsing
    refine ⟨Aᶜ, hA.compl, hHA, ?_⟩
    rw [compl_compl]
    exact hcomp A (hEq.symm ▸ hνA)
  choose A hA hH hmass using hs
  let U := ⋃ k, A k
  have hbound (k : ℕ) : (μ : Measure UnitAddCircle).real Uᶜ ≤ δ k :=
    (measureReal_mono (Set.compl_subset_compl.mpr (Set.subset_iUnion A k))).trans (hmass k)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have hcast := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [δ, Function.comp_def] using tendsto_inv_atTop_zero.comp hcast
  have hzero : (μ : Measure UnitAddCircle).real Uᶜ = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto tendsto_const_nhds hδ (Eventually.of_forall hbound))
      ENNReal.toReal_nonneg
  refine ⟨Uᶜ, (MeasurableSet.iUnion hA).compl,
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hzero, ?_⟩
  simpa only [compl_compl] using measure_iUnion_null hH

end

end VdC
