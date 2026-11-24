/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CyclicL2
public import Mixing.StrongMixing

/-! # Spectral measures on the Pontryagin dual -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Mixing Topology

namespace Mixing

variable {G : Type*} [Group G]

noncomputable section

/-- The Pontryagin dual endowed with its compact-open topology for discrete G. -/
abbrev DiscreteDual (G : Type*) [Group G] := @PontryaginDual G _ ⊥

instance : MeasurableSpace (DiscreteDual G) := borel _
instance : BorelSpace (DiscreteDual G) := ⟨rfl⟩

instance discreteDual_compactSpace : CompactSpace (DiscreteDual G) := by
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  change CompactSpace (G →ₜ* Circle)
  infer_instance

/-- Evaluation of a character at a fixed group element, as a circle-valued continuous map. -/
def dualEvaluation (g : G) : C(DiscreteDual G, Circle) := by
  let _ : TopologicalSpace G := ⊥
  exact (⟨fun χ : G →ₜ* Circle => χ g, continuous_eval_const g⟩ : C(G →ₜ* Circle, Circle))

variable {H : Type*} [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- A spectrum point gives a continuous character of discrete G. -/
def spectralPointDual (z : RepresentationSpectrum U) : DiscreteDual G := by
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  exact ⟨spectralPointCharacter U z, continuous_of_discreteTopology⟩

theorem spectralPointDual_continuous : Continuous (spectralPointDual U) := by
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  change Continuous (fun z : RepresentationSpectrum U => (spectralPointDual U z : G →ₜ* Circle))
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  rw [continuous_iff_continuousAt]
  rintro ⟨z, g⟩
  have hg : ∀ᶠ t : RepresentationSpectrum U × G in 𝓝 (z, g), t.2 = g := by
    have h : ∀ᶠ g' in 𝓝 g, g' = g := (isOpen_discrete _).mem_nhds (Set.mem_singleton g)
    exact (continuous_snd.tendsto (z, g)).eventually h
  have hc : Continuous (fun z' : RepresentationSpectrum U => dualEvaluation g (spectralPointDual U z')) := by
    exact (spectralCoefficient U g).continuous.subtype_mk _
  have ht := (hc.comp continuous_fst).tendsto (z, g)
  apply ht.congr'
  filter_upwards [hg] with t ht
  change spectralPointCharacter U t.1 g = spectralPointCharacter U t.1 t.2
  rw [ht]

theorem spectralPointDual_injective : Function.Injective (spectralPointDual U) := by
  intro z w h
  apply spectralPointCharacter_injective U
  ext g
  exact congrArg (fun χ => (dualEvaluation g χ : ℂ)) h

/-- The spectral measure of the vector on the paper's common frequency space. -/
def dualVectorSpectralMeasure (x : H) : Measure (DiscreteDual G) :=
  (vectorSpectralMeasure U x).map (spectralPointDual U)

instance dualVectorSpectralMeasure_isFinite (x : H) : IsFiniteMeasure (dualVectorSpectralMeasure U x) :=
  Measure.isFiniteMeasure_map _ _

instance dualVectorSpectralMeasure_regular (x : H) : (dualVectorSpectralMeasure U x).Regular := by
  have : (dualVectorSpectralMeasure U x).InnerRegular :=
    Measure.InnerRegular.map_of_continuous (spectralPointDual_continuous U)
  infer_instance

/-- The Fourier coefficient at a group element, with the convention linear
in the acted-on vector. -/
def spectralFourier (μ : Measure (DiscreteDual G)) (g : G) : ℂ :=
  ∫ χ, (dualEvaluation g χ : ℂ) ∂μ

theorem spectralFourier_dualVectorSpectralMeasure (x : H) (g : G) :
    spectralFourier (dualVectorSpectralMeasure U x) g = ⟪x, U g x⟫_ℂ := by
  unfold spectralFourier dualVectorSpectralMeasure
  rw [integral_map (spectralPointDual_continuous U).measurable.aemeasurable]
  · calc
      _ = ∫ z, spectralCoefficient U g z ∂vectorSpectralMeasure U x :=
        integral_congr_ae (.of_forall fun _ => rfl)
      _ = _ := by
        rw [integral_vectorSpectralMeasure, spectralCalculus_spectralCoefficient]
        rfl
  · exact (continuous_subtype_val.comp (dualEvaluation g).continuous).aestronglyMeasurable

/-- The spectral Fourier formulation of ultrafilter mixing before passing to
a maximal spectral type. The tested family is `βG+P`. -/
theorem isUMixing_iff_all_vector_fourier_vanish (P : Set (Ultrafilter G)) :
    IsUMixing U P ↔ ∀ x : H, ∀ p ∈ P, ∀ q : Ultrafilter G,
      Tendsto (spectralFourier (dualVectorSpectralMeasure U x))
        ((q * p : Ultrafilter G) : Filter G) (𝓝 0) := by
  constructor
  · intro hU x p hp q
    have hzero : ultrafilterOperator U (q * p) = 0 := by
      rw [ultrafilterOperator_mul, hU p hp, mul_zero]
    rw [funext (spectralFourier_dualVectorSpectralMeasure U x)]
    simpa only [hzero, zero_apply, inner_zero_right] using
      tendsto_ultrafilterOperator_coeff U (q * p) x x
  · intro hU p hp
    apply ContinuousLinearMap.coe_injective
    rw [ContinuousLinearMap.toLinearMap_zero, ← inner_map_self_eq_zero]
    intro x
    have hlim := tendsto_ultrafilterOperator_coeff U (pure 1 * p) x x
    have heq : (pure 1 : Ultrafilter G) * p = p := by
      apply Ultrafilter.coe_inj.mp
      ext S
      change (∀ᶠ a in ((pure 1 * p : Ultrafilter G) : Filter G), a ∈ S) ↔
        ∀ᶠ a in (p : Filter G), a ∈ S
      simp [Ultrafilter.eventually_mul]
    have hlim' := hU x p hp (pure 1)
    rw [heq] at hlim
    rw [heq, funext (spectralFourier_dualVectorSpectralMeasure U x)] at hlim'
    have hzero := tendsto_nhds_unique hlim hlim'
    rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm, hzero, map_zero]

end

end Mixing
