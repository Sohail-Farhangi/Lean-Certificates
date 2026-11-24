/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.FourierUniqueness
public import Mixing.SpectralMeasureClass
public import Mixing.WeakMixingBridge

/-! # Wiener's criterion along Følner sequences -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {G : Type*} [Group G]

/-- The average of a dual character over a finite block. -/
noncomputable def dualCharacterAverage (F : Finset G) (χ : DiscreteDual G) : ℂ :=
  (∑ g ∈ F, dualCharacters g χ) / (F.card : ℂ)

theorem norm_dualCharacterAverage_le_one (F : Finset G) (χ : DiscreteDual G) :
    ‖dualCharacterAverage F χ‖ ≤ 1 := by
  have hBound : ‖∑ g ∈ F, dualCharacters g χ‖ ≤ (F.card : ℝ) :=
    (norm_sum_le _ _).trans_eq (by
      change (∑ g ∈ F, ‖(dualEvaluation g χ : ℂ)‖) = _
      simp)
  unfold dualCharacterAverage
  rw [norm_div, Complex.norm_natCast]
  exact div_le_one_of_le₀ hBound (Nat.cast_nonneg _)

theorem folner_leftFolnerProbabilities {F : ℕ → Finset G} (hF : IsFolnerSequence F)
    [MeasurableSpace G] [DiscreteMeasurableSpace G] :
    JdLGBridge.LeftFolnerProbabilities
      (fun n => JdLGBridge.normalizedRestrictedMeasure Measure.count (F n : Set G)) atTop := by
  classical
  apply (JdLGBridge.leftFolnerProbabilities_counting_iff_strongFolner F hF.1 atTop).mpr
  intro a
  refine (hF.2 a).congr' (.of_forall fun n => ?_)
  unfold finsetDensity
  congr 1
  apply congrArg (fun s : Finset G => (s.card : ℝ))
  ext t
  simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter, Set.mem_ofPred_eq,
    not_exists, not_and, ne_eq]
  tauto

/-- A nontrivial character has zero mean along every Følner sequence. -/
theorem tendsto_dualCharacterAverage_zero {F : ℕ → Finset G} (hF : IsFolnerSequence F)
    (χ : DiscreteDual G) (hχ : χ ≠ 1) :
    Tendsto (fun n => dualCharacterAverage (F n) χ) atTop (𝓝 0) := by
  classical
  let _ : TopologicalSpace G := ⊥
  let _ : MeasurableSpace G := ⊤
  let _ : DiscreteMeasurableSpace G := ⟨fun _ => trivial⟩
  let c (g : G) : ℂ := (χ g : Circle)
  have hne : ∃ a : G, c a ≠ 1 := by
    by_contra! hh
    apply hχ
    apply PontryaginDual.ext
    intro g
    apply Subtype.ext
    exact hh g
  obtain ⟨a, ha⟩ := hne
  let D (n : ℕ) : ℂ := ((∑ g ∈ F n, c (a * g)) / ((F n).card : ℂ)) - dualCharacterAverage (F n) χ
  have hD (n : ℕ) : D n = (c a - 1) * dualCharacterAverage (F n) χ := by
    have hMul (g : G) : c (a * g) = c a * c g := by
      change ((χ (a * g) : Circle) : ℂ) = _
      rw [map_mul, Circle.coe_mul]
    change ((∑ g ∈ F n, c (a * g)) / ((F n).card : ℂ)) - dualCharacterAverage (F n) χ = _
    rw [sub_mul, one_mul]
    congr 1
    change (∑ g ∈ F n, c (a * g)) / ((F n).card : ℂ) =
      c a * ((∑ g ∈ F n, c g) / ((F n).card : ℂ))
    simp only [hMul]
    rw [← Finset.mul_sum, mul_div_assoc]
  have hFol := folner_leftFolnerProbabilities hF
  have hBoundRe (g : G) : ‖(c g).re‖ ≤ 1 :=
    (Complex.abs_re_le_norm (c g)).trans_eq (Circle.norm_coe (χ g))
  have hBoundIm (g : G) : ‖(c g).im‖ ≤ 1 :=
    (Complex.abs_im_le_norm (c g)).trans_eq (Circle.norm_coe (χ g))
  have hre (n : ℕ) : (D n).re =
      (∑ g ∈ F n, (c (a * g)).re) / (F n).card - (∑ g ∈ F n, (c g).re) / (F n).card := by
    simp only [D, dualCharacterAverage, Complex.sub_re, ← Complex.ofReal_natCast, Complex.div_ofReal_re]
    exact congrArg₂ (· - ·)
      (congrArg (fun r : ℝ => r / (F n).card) (map_sum Complex.reCLM _ _))
      (congrArg (fun r : ℝ => r / (F n).card) (map_sum Complex.reCLM _ _))
  have him (n : ℕ) : (D n).im =
      (∑ g ∈ F n, (c (a * g)).im) / (F n).card - (∑ g ∈ F n, (c g).im) / (F n).card := by
    simp only [D, dualCharacterAverage, Complex.sub_im, ← Complex.ofReal_natCast, Complex.div_ofReal_im]
    exact congrArg₂ (· - ·)
      (congrArg (fun r : ℝ => r / (F n).card) (map_sum Complex.imCLM _ _))
      (congrArg (fun r : ℝ => r / (F n).card) (map_sum Complex.imCLM _ _))
  have hLim : Tendsto D atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hFol a (ε / 2) (half_pos hε)] with n hn
    have hr := hn (fun g => (c g).re) Measurable.of_discrete hBoundRe
    have hi := hn (fun g => (c g).im) Measurable.of_discrete hBoundIm
    simp only [JdLGBridge.integral_normalizedCountingBlock] at hr hi
    rw [dist_zero_right]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans_lt
    rw [hre, him]
    exact (add_lt_add hr hi).trans_eq (add_halves ε)
  have hc : c a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have h := (tendsto_const_nhds (x := (c a - 1)⁻¹)).mul hLim
  rw [mul_zero] at h
  simpa only [hD, ← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h


section MeanSquares

variable [Countable G]

theorem integral_dualCharProduct_eq_norm_sq (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ]
    (g : G) :
    (∫ z : DiscreteDual G × DiscreteDual G, dualCharacters g (z.1 * z.2⁻¹) ∂μ.prod μ) =
      Complex.ofReal (‖spectralFourier μ g‖ ^ 2) := by
  let _ : TopologicalSpace G := ⊥
  calc
    _ = ∫ z : DiscreteDual G × DiscreteDual G,
      (dualCharacters g z.1) * conj (dualCharacters g z.2) ∂μ.prod μ := by
      apply integral_congr_ae
      exact .of_forall fun z => by
        change ((z.1 g * (z.2 g)⁻¹ : Circle) : ℂ) = ((z.1 g : Circle) : ℂ) * conj ((z.2 g : Circle) : ℂ)
        rw [Circle.coe_mul, Circle.coe_inv_eq_conj]
    _ = (∫ χ, dualCharacters g χ ∂μ) * ∫ χ, conj (dualCharacters g χ) ∂μ :=
      integral_prod_mul (μ := μ) (ν := μ) (fun χ => dualCharacters g χ)
        (fun χ => conj (dualCharacters g χ))
    _ = _ := by
      rw [integral_conj]
      change spectralFourier μ g * conj (spectralFourier μ g) = _
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Wiener's atomless direction: squared Fourier coefficients have zero
average along every Følner sequence. -/
theorem tendsto_mean_square_spectralFourier_zero {F : ℕ → Finset G} (hF : IsFolnerSequence F)
    (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto (fun n => (∑ g ∈ F n, ‖spectralFourier μ g‖ ^ 2) / (F n).card) atTop (𝓝 0) := by
  let _ : TopologicalSpace G := ⊥
  let f (n : ℕ) (z : DiscreteDual G × DiscreteDual G) :=
    dualCharacterAverage (F n) (z.1 * z.2⁻¹)
  have hCont (n : ℕ) : Continuous (f n) := by
    apply Continuous.div_const
    apply continuous_finsetSum
    intro g _
    exact (dualCharacters g).continuous.comp (continuous_fst.mul continuous_snd.inv)
  have hDiag : (μ.prod μ) {z : DiscreteDual G × DiscreteDual G | z.1 = z.2} = 0 := by
    rw [Measure.prod_apply (isClosed_eq continuous_fst continuous_snd).measurableSet]
    have he (χ : DiscreteDual G) :
        Prod.mk χ ⁻¹' {z : DiscreteDual G × DiscreteDual G | z.1 = z.2} = {χ} := by
      ext ψ
      exact eq_comm
    simp only [he, measure_singleton, lintegral_zero]
  have hAe : ∀ᵐ z ∂μ.prod μ, z.1 ≠ z.2 := by
    simpa only [ae_iff, Ne, not_not] using hDiag
  have ht : Tendsto (fun n => ∫ z, f n z ∂μ.prod μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (μ := μ.prod μ) (fun _ => (1 : ℝ))
        (fun n => (hCont n).aestronglyMeasurable) (integrable_const _)
        (fun n => .of_forall fun z => norm_dualCharacterAverage_le_one _ _)
        (hAe.mono fun z hz => tendsto_dualCharacterAverage_zero hF _
          (fun h => hz (mul_inv_eq_one.mp h)))
  have hInt (g : G) : Integrable (fun z : DiscreteDual G × DiscreteDual G =>
      dualCharacters g (z.1 * z.2⁻¹)) (μ.prod μ) := by
    exact ((dualCharacters g).continuous.comp (continuous_fst.mul continuous_snd.inv)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRe (n : ℕ) : (∫ z, f n z ∂μ.prod μ).re =
      (∑ g ∈ F n, ‖spectralFourier μ g‖ ^ 2) / (F n).card := by
    have hIntSum := integral_finsetSum (μ := μ.prod μ) (s := F n) (fun g _ => hInt g)
    have he : (∫ z, f n z ∂μ.prod μ) =
        (∑ g ∈ F n, (Complex.ofReal (‖spectralFourier μ g‖ ^ 2))) / ((F n).card : ℂ) := by
      unfold f dualCharacterAverage
      simp only [div_eq_inv_mul]
      rw [integral_const_mul]
      rw [hIntSum]
      simp only [integral_dualCharProduct_eq_norm_sq]
    rw [he, ← Complex.ofReal_natCast, Complex.div_ofReal_re]
    congr 1
    exact (map_sum Complex.reCLM _ _).trans (Finset.sum_congr rfl fun _ _ => Complex.ofReal_re _)
  have h' := (Complex.continuous_re.tendsto (0 : ℂ)).comp ht
  simpa only [Function.comp_def, hRe, Complex.zero_re] using h'

end MeanSquares

section WeakMixing

variable [Countable G] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isWeaklyMixing_of_all_vector_measures_atomless [IsMulCommutative G]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (h : ∀ x : H, NullSingletonClass (dualVectorSpectralMeasure U x)) :
    IsWeaklyMixing U := by
  intro x F hF
  let _ := h x
  let μ := dualVectorSpectralMeasure U x
  have hSq (E : ℕ → Finset G) (hE : IsFolnerSequence E) :
      Tendsto (fun n => (∑ g ∈ E n, ‖⟪x, U g x⟫_ℂ‖ ^ 2) / (E n).card) atTop (𝓝 0) := by
    simpa only [μ, spectralFourier_dualVectorSpectralMeasure] using
      tendsto_mean_square_spectralFourier_zero hE μ
  have hbound (g : G) : ‖⟪x, U g x⟫_ℂ‖ ≤ ‖x‖ * ‖x‖ := by
    simpa only [(U g).norm_map] using norm_inner_le_norm x (U g x)
  apply tendsto_zero_average_of_finsetDensity_threshold_zero (fun _ => norm_nonneg _) hbound hF.1
  intro δ hδ
  by_contra hn
  have hPos : HasPositiveFolnerDensity {g | δ ≤ ‖⟪x, U g x⟫_ℂ‖} :=
    ⟨F, hF, not_tendsto_finsetDensity_zero_iff.mp hn⟩
  have hSet : {g | δ ^ 2 ≤ ‖⟪x, U g x⟫_ℂ‖ ^ 2} = {g | δ ≤ ‖⟪x, U g x⟫_ℂ‖} := by
    ext g
    exact sq_le_sq₀ hδ.le (norm_nonneg _)
  rw [← hSet] at hPos
  obtain ⟨E, hE, hFail⟩ := not_tendsto_zero_of_hasPositiveFolnerDensity
    (fun _ => sq_nonneg _) (sq_pos_of_pos hδ) hPos
  exact hFail (hSq E hE)

theorem isWeaklyMixing_iff_all_vector_measures_atomless
    {G : Type*} [CommGroup G] [Countable G] (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsWeaklyMixing U ↔ ∀ x : H, NullSingletonClass (dualVectorSpectralMeasure U x) := by
  refine ⟨fun h x => ?_, isWeaklyMixing_of_all_vector_measures_atomless U⟩
  obtain ⟨F, hF⟩ := exists_isFolnerSequence (G := G)
  have hPos : HasPositiveFolnerDensity (Set.univ : Set G) := by
    refine ⟨F, hF, 1, zero_lt_one, Filter.Eventually.frequently (.of_forall fun n => ?_)⟩
    have hCard : (F n).card ≠ 0 := (hF.1 n).card_ne_zero
    simp [finsetDensity, hCard]
  obtain ⟨p, hp, _⟩ := exists_essentialUltrafilter_mem_of_hasPositiveFolnerDensity hPos
  have hz := isUMixing_essential_of_isWeaklyMixing U h p hp
  let _ := vectorSpectralMeasure_noAtoms_of_ultrafilterOperator_apply_eq_zero U x p
    (show ultrafilterOperator U p x = 0 by rw [hz, zero_apply])
  constructor
  intro χ
  rw [dualVectorSpectralMeasure, Measure.map_apply (spectralPointDual_continuous U).measurable
    (measurableSet_singleton _)]
  exact (Set.subsingleton_singleton.preimage (spectralPointDual_injective U)).measure_zero _

/-- Theorem 6.1(i) in the positive maximal spectral measure class. -/
theorem theorem6_1_i_equivalent_positiveMeasureClass
    {G : Type*} [CommGroup G] [Countable G] (U : G →* (H ≃ₗᵢ[ℂ] H))
    (x : H) (hx : IsMaximalSpectralVector U x) :
    IsWeaklyMixing U ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν],
        ν ≪ dualVectorSpectralMeasure U x → dualVectorSpectralMeasure U x ≪ ν → NullSingletonClass ν := by
  rw [isWeaklyMixing_iff_all_vector_measures_atomless U]
  constructor
  · intro h ν _ hν _
    let _ := h x
    exact ⟨fun _ => hν (measure_singleton _)⟩
  · intro h y
    let σ := dualVectorSpectralMeasure U x
    let _ := @h σ _ (Measure.AbsolutelyContinuous.refl σ) (Measure.AbsolutelyContinuous.refl σ)
    exact ⟨fun _ => hx y (measure_singleton _)⟩

end WeakMixing

end Mixing
