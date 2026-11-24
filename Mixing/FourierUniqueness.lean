/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralDual
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Metrizable.Basic

/-! # Fourier uniqueness on the compact dual -/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ComplexConjugate ENNReal Pointwise Topology

namespace Mixing

variable {G : Type*} [Group G]

noncomputable section

/-- The dual evaluation functions are a multiplicative family of complex continuous functions. -/
def dualCharacters : G →* C(DiscreteDual G, ℂ) where
  toFun g := ⟨fun χ => (dualEvaluation g χ : ℂ), continuous_subtype_val.comp (dualEvaluation g).continuous⟩
  map_one' := by
    let _ : TopologicalSpace G := ⊥
    ext χ
    change ((χ 1 : Circle) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  map_mul' a b := by
    let _ : TopologicalSpace G := ⊥
    ext χ
    change ((χ (a * b) : Circle) : ℂ) = ((χ a : Circle) : ℂ) * ((χ b : Circle) : ℂ)
    rw [map_mul, Circle.coe_mul]

theorem dualCharacters_star (g : G) : star (dualCharacters g) = dualCharacters g⁻¹ := by
  let _ : TopologicalSpace G := ⊥
  ext χ
  change star ((χ g : Circle) : ℂ) = ((χ g⁻¹ : Circle) : ℂ)
  rw [map_inv, Circle.coe_inv_eq_conj, Complex.star_def]

/-- Trigonometric polynomials are dense in the continuous functions on the
compact dual. -/
theorem denseRange_dualCharacterSpan :
    Dense (((Submodule.span ℂ (Set.range (dualCharacters (G := G)))) : Submodule ℂ
      C(DiscreteDual G, ℂ)) : Set C(DiscreteDual G, ℂ)) := by
  let S : StarSubalgebra ℂ C(DiscreteDual G, ℂ) :=
    StarAlgebra.adjoin ℂ (Set.range (dualCharacters (G := G)))
  have hspan : S.toSubalgebra.toSubmodule = Submodule.span ℂ (Set.range (dualCharacters (G := G))) := by
    unfold S
    rw [StarAlgebra.adjoin_eq_span]
    have hStar : star (Set.range (dualCharacters (G := G))) ⊆
        Set.range (dualCharacters (G := G)) := by
      intro f hf
      obtain ⟨g, hg⟩ := Set.mem_star.mp hf
      exact ⟨g⁻¹, by rw [← dualCharacters_star, hg, star_star]⟩
    rw [union_eq_left.mpr hStar]
    let M : Submonoid C(DiscreteDual G, ℂ) := MonoidHom.mrange (dualCharacters (G := G))
    change Submodule.span ℂ
      (↑(Submonoid.closure (M : Set C(DiscreteDual G, ℂ))) : Set C(DiscreteDual G, ℂ)) = _
    rw [Submonoid.closure_eq]
    rfl
  have hSep : S.SeparatesPoints := by
    let _ : TopologicalSpace G := ⊥
    intro χ ψ hne
    have h : ∃ g : G, dualEvaluation g χ ≠ dualEvaluation g ψ := by
      by_contra! hh
      exact hne (PontryaginDual.ext hh)
    obtain ⟨g, hg⟩ := h
    have hMem : dualCharacters g ∈ S := StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g)
    refine ⟨dualCharacters g, ⟨dualCharacters g, hMem, rfl⟩, ?_⟩
    exact fun h => hg (Subtype.ext h)
  have hDense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hSep
  rw [← hspan, dense_iff_closure_eq]
  exact congrArg (fun A : StarSubalgebra ℂ C(DiscreteDual G, ℂ) => (A : Set C(DiscreteDual G, ℂ))) hDense

/-- Integration against a finite measure as a bounded functional on continuous tests. -/
def integralContinuousDual (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ] :
    C(DiscreteDual G, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

theorem integralContinuousDual_apply (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ]
    (f : C(DiscreteDual G, ℂ)) :
    integralContinuousDual μ f = ∫ χ, f χ ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ f) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) μ f)

/-- Finite regular measures on the dual are determined by their Fourier coefficients. -/
theorem eq_of_spectralFourier_eq (μ ν : Measure (DiscreteDual G))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular]
    (h : ∀ g : G, spectralFourier μ g = spectralFourier ν g) : μ = ν := by
  let I := integralContinuousDual μ - integralContinuousDual ν
  have hLin : ∀ f : C(DiscreteDual G, ℂ), integralContinuousDual μ f = integralContinuousDual ν f := by
    intro f
    have hSub : Submodule.span ℂ (Set.range (dualCharacters (G := G))) ≤ I.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      change integralContinuousDual μ (dualCharacters g) - integralContinuousDual ν (dualCharacters g) = 0
      rw [sub_eq_zero, integralContinuousDual_apply, integralContinuousDual_apply]
      exact h g
    have hs : ((Submodule.span ℂ (Set.range (dualCharacters (G := G))) : Submodule ℂ
      C(DiscreteDual G, ℂ)) : Set C(DiscreteDual G, ℂ)) ⊆ (I.ker : Set C(DiscreteDual G, ℂ)) := hSub
    have hClosure := closure_minimal hs I.isClosed_ker
    have hMem : f ∈ I.ker :=
      hClosure ((denseRange_dualCharacterSpan (G := G)) f)
    exact sub_eq_zero.mp hMem
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have h' := hLin (complexify f.toContinuousMap)
  rw [integralContinuousDual_apply, integralContinuousDual_apply] at h'
  change (∫ χ, (f χ : ℂ) ∂μ) = (∫ χ, (f χ : ℂ) ∂ν) at h'
  have hμ := integral_ofReal (𝕜 := ℂ) (μ := μ) (f := ⇑f)
  have hν := integral_ofReal (𝕜 := ℂ) (μ := ν) (f := ⇑f)
  exact Complex.ofReal_injective (hμ.symm.trans (h'.trans hν))

instance discreteDual_metrizableSpace [Countable G] : MetrizableSpace (DiscreteDual G) := by
  let e (χ : DiscreteDual G) (g : G) := dualEvaluation g χ
  have hc : Continuous e := continuous_pi fun g => (dualEvaluation g).continuous
  have hi : Function.Injective e := by
    let _ : TopologicalSpace G := ⊥
    intro χ ψ h
    exact PontryaginDual.ext (congr_fun h)
  exact (hc.isClosedEmbedding hi).isEmbedding.metrizableSpace

/-- Convolution multiplies Fourier coefficients on the compact dual. -/
theorem spectralFourier_mconv [Countable G] (μ ν : Measure (DiscreteDual G))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (g : G) :
    spectralFourier (μ ∗ₘ ν) g = spectralFourier μ g * spectralFourier ν g := by
  let _ : TopologicalSpace G := ⊥
  have h_eval : Measurable (fun χ : DiscreteDual G => (dualEvaluation g χ : ℂ)) :=
    (continuous_subtype_val.comp (dualEvaluation g).continuous).measurable
  unfold spectralFourier Measure.mconv
  rw [integral_map (continuous_mul.measurable.aemeasurable) h_eval.aestronglyMeasurable]
  change (∫ z : DiscreteDual G × DiscreteDual G, (dualEvaluation g (z.1 * z.2) : ℂ) ∂μ.prod ν) = _
  calc
    _ = ∫ z : DiscreteDual G × DiscreteDual G,
      (dualEvaluation g z.1 : ℂ) * (dualEvaluation g z.2 : ℂ) ∂μ.prod ν := by
      apply integral_congr_ae
      exact .of_forall fun z => by
        change ((z.1 g * z.2 g : Circle) : ℂ) = ((z.1 g : Circle) : ℂ) * ((z.2 g : Circle) : ℂ)
        exact Circle.coe_mul _ _
    _ = _ := integral_prod_mul (μ := μ) (ν := ν)
      (fun χ => (dualEvaluation g χ : ℂ)) (fun χ => (dualEvaluation g χ : ℂ))

/-- Equality (18)'s spectral consequence. If the diagonal matrix coefficient
of a vector is the product of two other diagonal coefficients, its spectral
measure is the convolution of the two spectral measures. -/
theorem dualVectorSpectralMeasure_eq_mconv_of_coefficients [Countable G] [IsMulCommutative G]
    {H₁ H₂ H₃ : Type*} [NormedAddCommGroup H₁] [NormedAddCommGroup H₂] [NormedAddCommGroup H₃]
    [InnerProductSpace ℂ H₁] [InnerProductSpace ℂ H₂] [InnerProductSpace ℂ H₃]
    [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace H₃]
    (U₁ : G →* (H₁ ≃ₗᵢ[ℂ] H₁)) (U₂ : G →* (H₂ ≃ₗᵢ[ℂ] H₂)) (U₃ : G →* (H₃ ≃ₗᵢ[ℂ] H₃))
    (x₁ : H₁) (x₂ : H₂) (x₃ : H₃)
    (h : ∀ g : G, inner ℂ x₃ (U₃ g x₃) = inner ℂ x₁ (U₁ g x₁) * inner ℂ x₂ (U₂ g x₂)) :
    dualVectorSpectralMeasure U₃ x₃ = dualVectorSpectralMeasure U₁ x₁ ∗ₘ dualVectorSpectralMeasure U₂ x₂ := by
  let μ := dualVectorSpectralMeasure U₁ x₁
  let ν := dualVectorSpectralMeasure U₂ x₂
  have : IsFiniteMeasure (μ ∗ₘ ν) := Measure.isFiniteMeasure_map _ _
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_mconv, spectralFourier_dualVectorSpectralMeasure,
    spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure]
  exact h g

/-- An isometric intertwiner preserves vector spectral measures. -/
theorem dualVectorSpectralMeasure_eq_of_isometric_intertwiner [IsMulCommutative G]
    {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K))
    (J : H →ₗᵢ[ℂ] K) (hJ : ∀ g x, J (U g x) = V g (J x)) (x : H) :
    dualVectorSpectralMeasure V (J x) = dualVectorSpectralMeasure U x := by
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure, ← hJ]
  exact J.inner_map_map _ _

end

end Mixing
