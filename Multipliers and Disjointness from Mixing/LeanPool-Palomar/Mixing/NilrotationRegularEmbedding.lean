/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CyclicHilbertSum
public import Mixing.IntegerRegularEmbedding
public import Mixing.NilrotationHaarComplement

@[expose] public section
noncomputable section
namespace Mixing

open MeasureTheory TopologicalSpace
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A separable representation with Haar-absolutely-continuous spectral
measures embeds into a countable Hilbert sum of regular bilateral shifts. -/
theorem exists_hilbertSumRegularEmbedding_of_haarAC [SeparableSpace H]
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))
    (hU : ∀ x, dualVectorSpectralMeasure U x ≪ integerDualHaar) :
    let V := regularShiftRep Unit (Multiplicative ℤ)
    ∃ J : H →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ RegularShiftSpace Unit (Multiplicative ℤ)) 2,
      Intertwines U (hilbertSumUnitaryRep (fun _ : ℕ ↦ V)) J.toContinuousLinearMap := by
  let V := regularShiftRep Unit (Multiplicative ℤ)
  let e := regularShiftBasis Unit (Multiplicative ℤ) ((),1)
  let : Countable (Multiplicative ℤ) := by change Countable ℤ; infer_instance
  have hE : dualVectorSpectralMeasure V e = integerDualHaar := dualVectorSpectralMeasure_regularShift Unit ()
  obtain ⟨J,hJ⟩ := exists_hilbertSumIntertwiningIsometry U V (by
    intro x
    obtain ⟨y, hy⟩ := exists_dualVectorSpectralMeasure_eq_of_ac V e (dualVectorSpectralMeasure U x)
      (hE.symm ▸ hU x)
    obtain ⟨J,hJ,_⟩ := exists_cyclicIntertwiningIsometry_of_equal_diagonal_coefficients V U y x (by
      intro g
      rw [← spectralFourier_dualVectorSpectralMeasure, ← spectralFourier_dualVectorSpectralMeasure, hy])
    exact ⟨J,hJ⟩)
  exact ⟨J, fun g x ↦ by
    apply lp.ext
    funext i
    rw [hilbertSumUnitaryRep_apply]
    exact hJ g x i⟩

/-- The Haar-absolutely-continuous complement supplies the upper bound on
spectral multiplicity by embedding into countably many bilateral shifts. -/
theorem exists_purePointOrthogonal_hilbertSumRegularEmbedding [SecondCountableTopology H]
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) (hU : HasHaarAbsolutelyContinuousComplement U) :
    let V := regularShiftRep Unit (Multiplicative ℤ)
    ∃ J : (purePointPart U)ᗮ →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ RegularShiftSpace Unit (Multiplicative ℤ)) 2,
      Intertwines (purePointOrthogonalRep U) (hilbertSumUnitaryRep (fun _ : ℕ ↦ V)) J.toContinuousLinearMap := by
  let W := (purePointPart U)ᗮ
  let : CompleteSpace W := (Submodule.isClosed_orthogonal _).completeSpace_coe
  apply exists_hilbertSumRegularEmbedding_of_haarAC
  intro x
  have he := dualVectorSpectralMeasure_eq_of_isometric_intertwiner (purePointOrthogonalRep U) U
    W.subtypeₗᵢ (fun _ _ ↦ rfl) x
  rw [← he]
  exact hU x.property

end Mixing
