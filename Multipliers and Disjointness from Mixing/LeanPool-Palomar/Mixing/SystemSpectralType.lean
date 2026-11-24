/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralTypeTheorem
public import Mixing.SpectralMultiplier
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # The spectral type of a measure-preserving system -/

@[expose] public section

open Filter MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped Mixing Topology

namespace Mixing

universe u

variable {G : Type*} [CommGroup G]
variable {X Y Z : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The maximal spectral type `[X]` consists of the finite positive
representatives on the dual of the mean-zero Koopman representation. -/
noncomputable def System.maximalSpectralType (S : System G X) : Set (Measure (DiscreteDual G)) :=
  Mixing.maximalSpectralType S.koopmanZeroRep

/-- Haar probability measure on the compact dual of the discrete group. -/
noncomputable def dualHaarProbability (G : Type*) [CommGroup G] : Measure (DiscreteDual G) :=
  Measure.haarMeasure ⊤

instance dualHaarProbability_isMulLeftInvariant : IsMulLeftInvariant (dualHaarProbability G) := by
  unfold dualHaarProbability
  infer_instance

instance dualHaarProbability_isProbabilityMeasure : IsProbabilityMeasure (dualHaarProbability G) where
  measure_univ := by
    rw [dualHaarProbability, ← PositiveCompacts.coe_top]
    exact Measure.haarMeasure_self

/-- Theorem 6.1(i) for systems. -/
theorem System.theorem6_1_i [Countable G] (S : System G X) [SeparableSpace (meanZero S.measure)] :
    IsWeaklyMixing S.koopmanZeroRep ↔ ∀ ν ∈ S.maximalSpectralType, NullSingletonClass ν :=
  Mixing.theorem6_1_i S.koopmanZeroRep

/-- Theorem 6.1(ii) for systems. -/
theorem System.theorem6_1_ii (S : System G X) [SeparableSpace (meanZero S.measure)]
    (P : Set (Ultrafilter G)) :
    S.IsUMixing P ↔ ∀ ν ∈ S.maximalSpectralType, ∀ p ∈ P, ∀ q : Ultrafilter G,
      Tendsto (spectralFourier ν) ((q * p : Ultrafilter G) : Filter G) (𝓝 0) :=
  Mixing.theorem6_1_ii S.koopmanZeroRep P

/-- Theorem 6.1(iii) for systems. -/
theorem System.theorem6_1_iii (S : System G X) [SeparableSpace (meanZero S.measure)] :
    IsStronglyMixing S.koopmanZeroRep ↔
      ∀ ν ∈ S.maximalSpectralType, Tendsto (spectralFourier ν) cofinite (𝓝 0) :=
  Mixing.theorem6_1_iii S.koopmanZeroRep

/-- Theorem 6.1(iv) for systems. -/
theorem System.theorem6_1_iv (S : System G X) [SeparableSpace (meanZero S.measure)] :
    (∀ f : meanZero S.measure, dualVectorSpectralMeasure S.koopmanZeroRep f ≪ dualHaarProbability G) ↔
      ∀ ν ∈ S.maximalSpectralType, ν ≪ dualHaarProbability G :=
  Mixing.theorem6_1_iv S.koopmanZeroRep (dualHaarProbability G)

/-- Membership in the class `F_I` is witnessed by a positive finite representative. -/
def System.HasSpectralTypeIn (S : System G X) (I : Set (Measure (DiscreteDual G))) : Prop :=
  ∃ ν ∈ S.maximalSpectralType, ν ∈ I

/-- The multiplier conclusion against an individual system. -/
def System.IsMultiplierAgainst (S : System G X) (R : System G Z) : Prop :=
  ∀ (Y : Type u) [MeasurableSpace Y] (T : System G Y), Disjoint T R →
    ∀ (σ : Measure (X × Y)) (hσ : IsJoining S T σ), Disjoint hσ.system R

/-- Theorem 6.2, in the maximal-spectral-type formulation. The two closure
conditions are the properties of the positive part of the L-ideal used here. -/
theorem theorem6_2 [Countable G]
    (S : System G X) [SeparableSpace (meanZero S.measure)]
    (I : Set (Measure (DiscreteDual G)))
    (hI : ∀ {μ ν : Measure (DiscreteDual G)} [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ν ∈ I → μ ∗ₘ ν ∈ I)
    (hAc : ∀ {μ ν : Measure (DiscreteDual G)} [IsFiniteMeasure μ], ν ∈ I → μ ≪ ν → μ ∈ I)
    (hS : ∀ ν ∈ S.maximalSpectralType, ∀ μ ∈ I, ν ⟂ₘ μ)
    (R : System G Z) (hR : R.HasSpectralTypeIn I) : S.IsMultiplierAgainst R := by
  obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector S.koopmanZeroRep
  have hmem : dualVectorSpectralMeasure S.koopmanZeroRep x ∈ S.maximalSpectralType :=
    ⟨inferInstance, x, hx, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
  obtain ⟨_, ⟨_, z, hz, _, hd⟩, hzI⟩ := hR
  intro Y _ T hTR σ hσ
  exact theorem6_2_of_maximalSpectralVectors (hσ := hσ) I hI hAc x z hx hz (hS _ hmem)
    (hAc hzI hd) hTR

/-- Corollary 6. A singular spectral type is a multiplier against any system
with absolutely continuous spectrum. -/
theorem corollary6 [Countable G]
    (S : System G X) [SeparableSpace (meanZero S.measure)]
    (hS : ∀ ν ∈ S.maximalSpectralType, ν ⟂ₘ dualHaarProbability G)
    (R : System G Z) [SeparableSpace (meanZero R.measure)]
    (hR : ∀ f : meanZero R.measure,
      dualVectorSpectralMeasure R.koopmanZeroRep f ≪ dualHaarProbability G) : S.IsMultiplierAgainst R := by
  obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector S.koopmanZeroRep
  have hmem : dualVectorSpectralMeasure S.koopmanZeroRep x ∈ S.maximalSpectralType :=
    ⟨inferInstance, x, hx, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
  obtain ⟨z, hz⟩ := exists_isMaximalSpectralVector R.koopmanZeroRep
  intro Y _ T hTR σ hσ
  exact corollary6_of_maximalSpectralVectors (hσ := hσ) (dualHaarProbability G) x z hx hz
    (hS _ hmem) (hR z) hTR

end Mixing
