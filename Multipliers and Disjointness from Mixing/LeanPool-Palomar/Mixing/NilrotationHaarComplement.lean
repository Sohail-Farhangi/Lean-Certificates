/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationSpectralGluing

@[expose] public section
noncomputable section
namespace Mixing

open MeasureTheory Set

variable {K B H : Type*} [Group K]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every vector orthogonal to the eigenfunctions has spectral measure
absolutely continuous with respect to Haar measure on the dual of the integers. -/
def HasHaarAbsolutelyContinuousComplement
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  (purePointPart U)ᗮ ≤ spectralAbsoluteContinuousSubmodule U integerDualHaar

omit [CompleteSpace H] in
theorem purePointPart_invariant {G : Type*} [Group G] (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsInvariantSubmodule U (purePointPart U) := by
  intro g x hx
  have h := purePointPart_le_of_eigenvectors_le U ((purePointPart U).comap (U g).toLinearMap)
    ((isClosed_purePointPart U).preimage (U g).continuous) (by
      rintro v ⟨χ,hχ⟩
      change U g v ∈ purePointPart U
      rw [hχ]
      exact (purePointPart U).smul_mem _ (eigenvectors_le_purePointPart U ⟨χ,hχ⟩))
  exact h hx

/-- The orthogonal projection off the eigenfunctions has Haar-absolutely-continuous
spectral measures if the nontrivial vertical modes and the base complement do. -/
theorem hasHaarAbsolutelyContinuousComplement_of_vertical
    (V : Multiplicative ℤ →* (B ≃ₗᵢ[ℂ] B)) (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))
    (R : K →* (H ≃ₗᵢ[ℂ] H)) (J : B →ₗᵢ[ℂ] H)
    (hJ : Intertwines V U J.toContinuousLinearMap) (hSpan : purePointPart R = ⊤)
    (hFixed : ∀ x : H, (∀ k, R k x = x) → ∃ v, J v = x)
    (hBase : HasHaarAbsolutelyContinuousComplement V)
    (hModes : ∀ (χ : K →* Circle) (x : H), χ ≠ 1 →
      (∀ k, R k x = (χ k : ℂ) • x) → dualVectorSpectralMeasure U x ≪ integerDualHaar) :
    HasHaarAbsolutelyContinuousComplement U := by
  let P := purePointPart U
  let D : ClosedSubmodule ℂ H := ⟨Pᗮ, Submodule.isClosed_orthogonal P⟩
  let A := spectralAbsoluteContinuousSubmodule U integerDualHaar
  let T := D.toSubmodule.starProjection
  have hT_P (x : H) (hx : x ∈ P) : T x = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr (Submodule.le_orthogonal_orthogonal _ hx)
  have hT_A (x : H) (hx : x ∈ A) : T x ∈ A :=
    (Measure.absolutelyContinuous_of_le
      (dualVectorSpectralMeasure_starProjection_le U D (purePointPart_invariant U).orthogonal x)).trans hx
  have hT : (⊤ : Submodule ℂ H) ≤ A.comap T.toLinearMap := by
    rw [← hSpan]
    apply purePointPart_le_of_eigenvectors_le _ _
      ((spectralAbsoluteContinuousSubmodule_isClosed U _).preimage T.continuous)
    rintro x ⟨χ,hχ⟩
    change T x ∈ A
    by_cases hχ' : χ = 1
    · subst χ
      obtain ⟨v, rfl⟩ := hFixed x (fun k ↦ by simpa using hχ k)
      let P₀ := purePointPart V
      let : CompleteSpace P₀ := (isClosed_purePointPart V).completeSpace_coe
      let v₀ := P₀.starProjection v
      have hv₀ : J v₀ ∈ P := hJ.mapsTo_purePointPart (P₀.starProjection_apply_mem v)
      have hv : J (v-v₀) ∈ A := by
        change dualVectorSpectralMeasure U (J (v-v₀)) ≪ integerDualHaar
        rw [dualVectorSpectralMeasure_eq_of_isometric_intertwiner V U J hJ]
        exact hBase (Submodule.sub_starProjection_mem_orthogonal v)
      rw [show v = v₀ + (v-v₀) from (add_sub_cancel v₀ v).symm, map_add, map_add,
        hT_P _ hv₀, zero_add]
      exact hT_A _ hv
    · exact hT_A x (hModes χ x hχ' hχ)
  intro x hx
  have ht := hT (Submodule.mem_top (x := x))
  change T x ∈ A at ht
  rwa [Submodule.starProjection_eq_self_iff.mpr hx] at ht

end Mixing
