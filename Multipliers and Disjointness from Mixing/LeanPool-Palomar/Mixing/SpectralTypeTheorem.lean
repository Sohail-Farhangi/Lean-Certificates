/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.MaximalSpectralVector
public import Mixing.SpectralWeakMixing

/-! # The spectral characterization of mixing -/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Mixing Topology

namespace Mixing

variable {G H : Type*} [CommGroup G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The finite positive representatives of the maximal spectral type. -/
def maximalSpectralType : Set (Measure (DiscreteDual G)) :=
  {ν | IsFiniteMeasure ν ∧ ∃ x : H, IsMaximalSpectralVector U x ∧
    ν ≪ dualVectorSpectralMeasure U x ∧ dualVectorSpectralMeasure U x ≪ ν}

theorem maximalSpectralType_nonempty : (maximalSpectralType U).Nonempty := by
  obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector U
  let σ := dualVectorSpectralMeasure U x
  exact ⟨σ, inferInstance, x, hx, Measure.AbsolutelyContinuous.refl σ, Measure.AbsolutelyContinuous.refl σ⟩

/-- Theorem 6.1(i). Weak mixing is equivalent to continuity of the maximal spectral type. -/
theorem theorem6_1_i [Countable G] :
    IsWeaklyMixing U ↔ ∀ ν ∈ maximalSpectralType U, NullSingletonClass ν := by
  constructor
  · rintro h ν ⟨hFinite, x, hx, hν, hν'⟩
    have hClass := (theorem6_1_i_equivalent_positiveMeasureClass U x hx).mp h
    exact @hClass ν hFinite hν hν'
  · intro h
    obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector U
    apply (theorem6_1_i_equivalent_positiveMeasureClass U x hx).mpr
    intro ν hFinite hν hν'
    exact h ν ⟨hFinite, x, hx, hν, hν'⟩

/-- Theorem 6.1(ii). An ultrafilter mixing representation has ultrafilter
mixing Fourier transforms on the whole maximal spectral type. -/
theorem theorem6_1_ii (P : Set (Ultrafilter G)) :
    IsUMixing U P ↔ ∀ ν ∈ maximalSpectralType U, ∀ p ∈ P, ∀ q : Ultrafilter G,
      Tendsto (spectralFourier ν) ((q * p : Ultrafilter G) : Filter G) (𝓝 0) := by
  constructor
  · rintro h ν ⟨hFinite, x, hx, hν, hν'⟩
    have hClass := (theorem6_1_ii_equivalent_positiveMeasureClass U P x hx).mp h
    exact @hClass ν hFinite hν hν'
  · intro h
    obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector U
    apply (theorem6_1_ii_equivalent_positiveMeasureClass U P x hx).mpr
    intro ν hFinite hν hν'
    exact h ν ⟨hFinite, x, hx, hν, hν'⟩

/-- Theorem 6.1(iii). Strong mixing is equivalent to the Rajchman condition
on the maximal spectral type. -/
theorem theorem6_1_iii :
    IsStronglyMixing U ↔ ∀ ν ∈ maximalSpectralType U, Tendsto (spectralFourier ν) cofinite (𝓝 0) := by
  constructor
  · rintro h ν ⟨hFinite, x, hx, hν, hν'⟩
    have hClass := (theorem6_1_iii_equivalent_positiveMeasureClass U x hx).mp h
    exact @hClass ν hFinite hν hν'
  · intro h
    obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector U
    apply (theorem6_1_iii_equivalent_positiveMeasureClass U x hx).mpr
    intro ν hFinite hν hν'
    exact h ν ⟨hFinite, x, hx, hν, hν'⟩

/-- Theorem 6.1(iv), taking the reference measure to be Haar measure. -/
theorem theorem6_1_iv (reference : Measure (DiscreteDual G)) :
    (∀ y : H, dualVectorSpectralMeasure U y ≪ reference) ↔
      ∀ ν ∈ maximalSpectralType U, ν ≪ reference := by
  constructor
  · rintro h ν ⟨hFinite, x, hx, hν, hν'⟩
    have hClass := (theorem6_1_iv_equivalent_positiveMeasureClass U reference x hx).mp h
    exact @hClass ν hFinite hν hν'
  · intro h
    obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector U
    apply (theorem6_1_iv_equivalent_positiveMeasureClass U reference x hx).mpr
    intro ν hFinite hν hν'
    exact h ν ⟨hFinite, x, hx, hν, hν'⟩

end Mixing
