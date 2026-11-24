/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralDual
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! # Orthogonality from mutually singular spectral measures -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

theorem spectralCalculus_complexify_adjoint (f : C(RepresentationSpectrum U, ℝ)) :
    (spectralCalculus U (complexify f)).adjoint = spectralCalculus U (complexify f) := by
  change star (spectralCalculus U (complexify f)) = _
  rw [← map_star, complexify_star]

theorem norm_spectralCalculus_complexify_sq (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    ‖spectralCalculus U (complexify f) x‖ ^ 2 =
      ∫ z, (f z) ^ 2 ∂vectorSpectralMeasure U x := by
  have hMul : complexify (f ^ 2) = complexify f * complexify f := by
    ext z
    simp only [complexify_apply, ContinuousMap.mul_apply, pow_two, Complex.ofReal_mul]
  have h := integral_vectorSpectralMeasure_real U x (f ^ 2)
  rw [hMul, map_mul] at h
  change (∫ z, (f z) ^ 2 ∂vectorSpectralMeasure U x) =
    (⟪x, spectralCalculus U (complexify f) (spectralCalculus U (complexify f) x)⟫_ℂ).re at h
  let A := spectralCalculus U (complexify f)
  have hInner := A.adjoint_inner_right x (A x)
  rw [show A.adjoint = A from spectralCalculus_complexify_adjoint U f] at hInner
  have hNorm : (⟪A x, A x⟫_ℂ).re = ‖A x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  exact (h.trans ((congrArg Complex.re hInner).trans hNorm)).symm

theorem norm_spectralCalculus_complexify_lt_of_zero_on (x : H)
    (f : C(RepresentationSpectrum U, ℝ)) {K : Set (RepresentationSpectrum U)}
    (hK : MeasurableSet K) (hf : ∀ z, f z ∈ Icc (0 : ℝ) 1) (hfK : Set.EqOn f 0 K)
    {ε : ℝ} (hε : 0 < ε) (hMass : vectorSpectralMeasure U x Kᶜ < ENNReal.ofReal (ε ^ 2)) :
    ‖spectralCalculus U (complexify f) x‖ < ε := by
  let μ := vectorSpectralMeasure U x
  have hi : Integrable (fun z => (f z) ^ 2) μ :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (Kᶜ.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const _).indicator hK.compl
  have hBound : (∫ z, (f z) ^ 2 ∂μ) ≤ μ.real Kᶜ := by
    calc
      _ ≤ ∫ z, Kᶜ.indicator (fun _ => (1 : ℝ)) z ∂μ := by
        apply integral_mono hi hi'
        intro z
        by_cases hz : z ∈ K
        · have h0 : f z = 0 := hfK hz
          simp [h0, hz]
        · rw [Set.indicator_of_mem (show z ∈ Kᶜ from hz)]
          nlinarith [(hf z).1, (hf z).2, mul_nonneg (hf z).1 (sub_nonneg.mpr (hf z).2)]
      _ = _ := by rw [integral_indicator hK.compl, setIntegral_const, smul_eq_mul, mul_one]
  have hlt : μ.real Kᶜ < ε ^ 2 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ Kᶜ) ENNReal.ofReal_ne_top).mpr hMass
    rwa [ENNReal.toReal_ofReal (sq_nonneg ε)] at hh
  have hsq : ‖spectralCalculus U (complexify f) x‖ ^ 2 < ε ^ 2 :=
    (norm_spectralCalculus_complexify_sq U x f).trans_lt (hBound.trans_lt hlt)
  by_contra! h
  exact hsq.not_ge (pow_le_pow_left₀ hε.le h 2)

/-- The spectral orthogonality used in Theorem 6.2. The two vectors live in
the same representation, and singularity is tested on the common dual. -/
theorem inner_eq_zero_of_dualVectorSpectralMeasure_mutuallySingular (x y : H)
    (h : dualVectorSpectralMeasure U x ⟂ₘ dualVectorSpectralMeasure U y) : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨A, hA, hAx, hAy⟩ := h
  let z := spectralPointDual U
  let B := z ⁻¹' A
  let μ := vectorSpectralMeasure U x
  let ν := vectorSpectralMeasure U y
  have hz : Measurable z := (spectralPointDual_continuous U).measurable
  have hB : MeasurableSet B := hz hA
  have hBx : μ B = 0 := by
    rw [dualVectorSpectralMeasure, Measure.map_apply hz hA] at hAx
    exact hAx
  have hBy : ν Bᶜ = 0 := by
    rw [dualVectorSpectralMeasure, Measure.map_apply hz hA.compl] at hAy
    exact hAy
  by_contra hNonzero
  let ε := ‖⟪x, y⟫_ℂ‖ / (2 * (‖x‖ + ‖y‖ + 1))
  have hε : 0 < ε := div_pos (norm_pos_iff.mpr hNonzero) (by positivity)
  let δ := ENNReal.ofReal (ε ^ 2)
  have hδ : δ ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)).ne'
  obtain ⟨K, hK, hKc, hμK⟩ := hB.compl.exists_isCompact_sdiff_lt (measure_ne_top μ Bᶜ) hδ
  obtain ⟨L, hL, hLc, hνL⟩ := hB.exists_isCompact_sdiff_lt (measure_ne_top ν B) hδ
  have hμ : μ Kᶜ < δ := by
    have hs : Kᶜ ⊆ (Bᶜ \ K) ∪ B := fun t ht => by
      by_cases hb : t ∈ B
      · exact Or.inr hb
      · exact Or.inl ⟨hb, ht⟩
    exact (measure_mono hs).trans_lt ((measure_union_le _ _).trans_lt (by rwa [hBx, add_zero]))
  have hν : ν Lᶜ < δ := by
    have hs : Lᶜ ⊆ (B \ L) ∪ Bᶜ := fun t ht => by
      by_cases hb : t ∈ B
      · exact Or.inl ⟨hb, ht⟩
      · exact Or.inr hb
    exact (measure_mono hs).trans_lt ((measure_union_le _ _).trans_lt (by rwa [hBy, add_zero]))
  have hSep : _root_.Disjoint L K := Set.disjoint_left.mpr fun t ht hk => hK hk (hL ht)
  obtain ⟨f, hfL, hfK, hf⟩ :=
    exists_continuous_zero_one_of_isClosed hLc.isClosed hKc.isClosed hSep
  let P := spectralCalculus U (complexify f)
  have hX : ‖x - P x‖ < ε := by
    have hf' (z : RepresentationSpectrum U) : (1 - f) z ∈ Icc (0 : ℝ) 1 := by
      change 0 ≤ 1 - f z ∧ 1 - f z ≤ 1
      exact ⟨sub_nonneg.mpr (hf z).2, by linarith [(hf z).1]⟩
    have hfK' : Set.EqOn ((1 : C(RepresentationSpectrum U, ℝ)) - f)
        (0 : C(RepresentationSpectrum U, ℝ)) K := by
      intro z hz
      change 1 - f z = 0
      rw [hfK hz]
      exact sub_self 1
    have hlt := norm_spectralCalculus_complexify_lt_of_zero_on U x (1 - f)
      hKc.isClosed.measurableSet hf' hfK' hε hμ
    have hComp : complexify (1 - f) = 1 - complexify f := by
      ext z
      change Complex.ofReal (1 - f z) = 1 - Complex.ofReal (f z)
      simp
    rw [hComp, map_sub, map_one, sub_apply, one_apply_eq_self] at hlt
    exact hlt
  have hY : ‖P y‖ < ε :=
    norm_spectralCalculus_complexify_lt_of_zero_on U y f hLc.isClosed.measurableSet hf hfL hε hν
  have hInner : ⟪x, y⟫_ℂ = ⟪x - P x, y⟫_ℂ + ⟪x, P y⟫_ℂ := by
    have hAdj : ⟪x, P y⟫_ℂ = ⟪P x, y⟫_ℂ := by
      have hi := P.adjoint_inner_right x y
      rw [show P.adjoint = P from spectralCalculus_complexify_adjoint U f] at hi
      exact hi
    rw [hAdj, inner_sub_left, sub_add_cancel]
  have hEstimate : ‖⟪x, y⟫_ℂ‖ ≤ ε * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ ‖⟪x - P x, y⟫_ℂ‖ + ‖⟪x, P y⟫_ℂ‖ := hInner ▸ norm_add_le _ _
      _ ≤ ‖x - P x‖ * ‖y‖ + ‖x‖ * ‖P y‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ε * (‖x‖ + ‖y‖) := by
        nlinarith [mul_le_mul_of_nonneg_right hX.le (norm_nonneg y),
          mul_le_mul_of_nonneg_left hY.le (norm_nonneg x)]
  have hεEq : ε * (2 * (‖x‖ + ‖y‖ + 1)) = ‖⟪x, y⟫_ℂ‖ :=
    div_mul_cancel₀ _ (by positivity)
  have hProd : 0 ≤ ε * (‖x‖ + ‖y‖) := by positivity
  nlinarith only [hEstimate, hεEq, hε, hProd]

end Mixing
