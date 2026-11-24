/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.PurePointLebesgue
public import Mixing.RotationSpectralDecay

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory Set

variable {G K B H : Type*} [Group G] [Group K]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace B] [CompleteSpace H] in
/-- An intertwiner sends the pure point subspace into the pure point subspace. -/
theorem Intertwines.mapsTo_purePointPart
    {V : G →* (B ≃ₗᵢ[ℂ] B)} {U : G →* (H ≃ₗᵢ[ℂ] H)} {J : B →L[ℂ] H}
    (hJ : Intertwines V U J) : MapsTo J (purePointPart V) (purePointPart U) := by
  have he : purePointPart V ≤ (purePointPart U).comap J.toLinearMap := by
    apply purePointPart_le_of_eigenvectors_le V _ ((isClosed_purePointPart U).preimage J.continuous)
    rintro x ⟨χ,hχ⟩
    change J x ∈ purePointPart U
    apply eigenvectors_le_purePointPart U
    exact ⟨χ, fun g ↦ by rw [← hJ g x, hχ g, map_smul]⟩
  exact fun _ hx ↦ he hx

/-- If the compact vertical action is spanned by its characters, weak decay
on the nontrivial characters and the range theorem on the base imply the
range theorem on the extension. -/
theorem ultrafilterOperator_range_eq_purePointPart_of_vertical
    (V : G →* (B ≃ₗᵢ[ℂ] B)) (U : G →* (H ≃ₗᵢ[ℂ] H))
    (R : K →* (H ≃ₗᵢ[ℂ] H)) (J : B →L[ℂ] H) (hJ : Intertwines V U J)
    (hSpan : purePointPart R = ⊤)
    (hFixed : ∀ x : H, (∀ k, R k x = x) → x ∈ J.range)
    (p : Ultrafilter G) (hBase : (ultrafilterOperator V p).range = purePointPart V)
    (hDecay : ∀ (χ : K →* Circle) (x : H), χ ≠ 1 →
      (∀ k, R k x = (χ k : ℂ) • x) → ultrafilterOperator U p x = 0) :
    (ultrafilterOperator U p).range = purePointPart U := by
  let A := ultrafilterOperator U p
  apply le_antisymm
  · have hle : purePointPart R ≤ (purePointPart U).comap A.toLinearMap := by
      apply purePointPart_le_of_eigenvectors_le R _
        ((isClosed_purePointPart U).preimage A.continuous)
      rintro x ⟨χ, hχ⟩
      change A x ∈ purePointPart U
      by_cases hχ' : χ = 1
      · subst χ
        obtain ⟨v, rfl⟩ := hFixed x (fun k ↦ by simpa using hχ k)
        change ultrafilterOperator U p (J v) ∈ purePointPart U
        rw [← hJ.ultrafilter p]
        apply hJ.mapsTo_purePointPart
        rw [← hBase]
        exact ⟨v, rfl⟩
      · change ultrafilterOperator U p x ∈ purePointPart U
        rw [hDecay χ x hχ' hχ]
        exact Submodule.zero_mem _
    rintro _ ⟨x, rfl⟩
    exact hle (hSpan.symm ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H)))
  · exact fun x hx ↦ ⟨A.adjoint x, (ultrafilterOperator_purePoint_inverse U p hx).1⟩

end Mixing
