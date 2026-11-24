module

public import Mixing.GeneratedSigma

@[expose] public section

namespace Mixing

open MeasureTheory Set

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- The σ-algebra generated modulo null sets by a subspace of L². -/
@[instance_reducible]
def System.sigmaOfSubmodule (S : System G X) (W : Submodule ℂ (Lp ℂ 2 S.measure)) :
    MeasurableSpace X :=
  MeasurableSpace.generateFrom {A | MeasurableSet A ∧ S.measure A = 0 ∨
    ∃ f : Lp ℂ 2 S.measure, f ∈ W ∧ ∃ B : Set ℂ, MeasurableSet B ∧ A = f ⁻¹' B}

/-- The factor-identification step in Examples 1 and 3. If all the ultrafilter
operators have the same range, that range generates exactly the displayed
factor. The spectral calculations that identify those ranges enter separately. -/
theorem System.generatedSigma_eq_sigmaOfSubmodule (S : System G X)
    (P : Set (Ultrafilter G)) (hP : P.Nonempty) (W : Submodule ℂ (Lp ℂ 2 S.measure))
    (hW : ∀ p ∈ P, (ultrafilterOperator S.koopmanRep p).range = W) :
    S.generatedSigma P = S.sigmaOfSubmodule W := by
  unfold System.generatedSigma System.sigmaOfSubmodule
  congr 1
  ext A
  constructor
  · rintro (⟨hA, hz⟩ | ⟨p, hp, f, B, hB, rfl⟩)
    · exact Or.inl ⟨hA, hz⟩
    · refine Or.inr ⟨ultrafilterOperator S.koopmanRep p f, ?_, B, hB, rfl⟩
      rw [← hW p hp]
      exact ⟨f, rfl⟩
  · rintro (⟨hA, hz⟩ | ⟨f, hf, B, hB, rfl⟩)
    · exact Or.inl ⟨hA, hz⟩
    · obtain ⟨p, hp⟩ := hP
      rw [← hW p hp] at hf
      obtain ⟨v, rfl⟩ := hf
      exact Or.inr ⟨p, hp, v, B, hB, rfl⟩

/-- A convenient criterion for the range equality in the factor-identification
step. The ultrafilter operator maps into the subspace and is surjective on it. -/
theorem System.generatedSigma_eq_of_range_surjective (S : System G X)
    (P : Set (Ultrafilter G)) (hP : P.Nonempty) (W : Submodule ℂ (Lp ℂ 2 S.measure))
    (hInto : ∀ p ∈ P, ∀ f, ultrafilterOperator S.koopmanRep p f ∈ W)
    (hOnto : ∀ p ∈ P, ∀ f ∈ W, ∃ v ∈ W, ultrafilterOperator S.koopmanRep p v = f) :
    S.generatedSigma P = S.sigmaOfSubmodule W := by
  apply S.generatedSigma_eq_sigmaOfSubmodule P hP W
  intro p hp
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact hInto p hp f
  · intro f hf
    obtain ⟨v, _, hv⟩ := hOnto p hp f hf
    exact ⟨v, hv⟩

end Mixing
