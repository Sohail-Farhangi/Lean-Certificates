/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RotationSpectralDecay
public import Mixing.PurePointLebesgue

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

variable {Γ I : Type*} [Group Γ] {C : Subgroup Γ}

/-- If full-phase central characters span the pure point orthogonal
complement, the corresponding time map has free-ultrafilter range
equal to its pure point subspace. -/
theorem range_eq_purePointPart_of_centralCharacters
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (χ : I → C →* Circle)
    (hSep : ∀ i, SeparableSpace (centralCharacterSubmodule ρ (χ i)))
    (hNontriv : ∀ i, Nontrivial (centralCharacterSubmodule ρ (χ i)))
    (hC : C ≤ Subgroup.center Γ) (a : Γ)
    (hSpan : (purePointPart (ρ.comp (integerPowersHom a)))ᗮ ≤
      (Submodule.span ℂ (⋃ i : I, (centralCharacterSubmodule ρ (χ i) : Set H))).topologicalClosure)
    (hComm : ∀ i (s : UnitAddCircle), ∃ (b : Γ) (u : C),
      a * b = b * a * (u : Γ) ∧ χ i u = AddCircle.toCircle s)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    (ultrafilterOperator (ρ.comp (integerPowersHom a)) p).range =
      purePointPart (ρ.comp (integerPowersHom a)) := by
  let U := ρ.comp (integerPowersHom a)
  let A := ultrafilterOperator U p
  apply ultrafilterOperator_range_eq_purePointPart_of_annihilation
  have hSub (i : I) : centralCharacterSubmodule ρ (χ i) ≤ A.ker := by
    let W := centralCharacterSubmodule ρ (χ i)
    let V := centralCharacterTime ρ (χ i) hC a
    let : CompleteSpace W := (centralCharacterSubmodule_isClosed ρ (χ i)).completeSpace_coe
    let : SeparableSpace W := hSep i
    let : Nontrivial W := hNontriv i
    have hV : ultrafilterOperator V p = 0 :=
      (isStronglyMixing_iff_isUMixing_free V).mp
        (centralCharacterTime_stronglyMixing ρ (χ i) hC a (hComm i)) p hp
    have hIn : Intertwines V U W.subtypeL := by intro g x; rfl
    intro x hx
    have he := hIn.ultrafilter p ⟨x, hx⟩
    rw [hV, zero_apply, map_zero] at he
    exact he.symm
  have hAll : (Submodule.span ℂ (⋃ i : I, (centralCharacterSubmodule ρ (χ i) : Set H))).topologicalClosure
      ≤ A.ker := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr (by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact hSub i hi)) A.isClosed_ker
  intro x hx
  exact hAll (hSpan hx)

/-- The generated-factor conclusion for a system with a central-character
spectral description of its time map. -/
theorem generatedSigma_eq_kroneckerSigma_of_centralCharacters
    {X : Type*} [MeasurableSpace X] (S : System (Multiplicative ℤ) X)
    (ρ : Γ →* (Lp ℂ 2 S.measure ≃ₗᵢ[ℂ] Lp ℂ 2 S.measure))
    (χ : I → C →* Circle)
    (hSep : ∀ i, SeparableSpace (centralCharacterSubmodule ρ (χ i)))
    (hNontriv : ∀ i, Nontrivial (centralCharacterSubmodule ρ (χ i)))
    (hC : C ≤ Subgroup.center Γ) (a : Γ) (hTime : S.koopmanRep = ρ.comp (integerPowersHom a))
    (hSpan : (purePointPart (ρ.comp (integerPowersHom a)))ᗮ ≤
      (Submodule.span ℂ (⋃ i : I, (centralCharacterSubmodule ρ (χ i) : Set (Lp ℂ 2 S.measure)))).topologicalClosure)
    (hComm : ∀ i (s : UnitAddCircle), ∃ (b : Γ) (u : C),
      a * b = b * a * (u : Γ) ∧ χ i u = AddCircle.toCircle s)
    (P : Set (Ultrafilter (Multiplicative ℤ))) (hP : P.Nonempty)
    (hFree : P ⊆ freeUltrafilters (Multiplicative ℤ)) :
    S.generatedSigma P = S.kroneckerSigma := by
  apply S.generatedSigma_eq_sigmaOfSubmodule P hP
  intro p hp
  rw [hTime]
  exact range_eq_purePointPart_of_centralCharacters ρ χ hSep hNontriv hC a hSpan hComm p (hFree hp)

end Mixing
