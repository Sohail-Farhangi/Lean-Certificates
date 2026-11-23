/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleTopology
public import JdLG.StableBiMean

/-! # The invariant mean from the compact group ideal -/

@[expose] public section

open MeasureTheory Set
open scoped CompactlySupported

namespace JdLG

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Normalized Haar measure on a compact group is right invariant as well. -/
instance normalizedHaar_rightInvariant : (normalizedHaar G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    let ν := (normalizedHaar G).map (· * g)
    have : IsProbabilityMeasure ν :=
      show IsProbabilityMeasure ((normalizedHaar G).map (· * g)) from inferInstance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν (normalizedHaar G)

end Haar

section Mean

variable {U : Type*} [Semigroup U] [TopologicalSpace U] [CompactSpace U]
  {hleft : ∀ s : U, Continuous (s * ·)} {hright : ∀ s : U, Continuous (· * s)}

/-- Normalized Haar integration over a compact topological group ideal gives a
normalized positive functional invariant under every left and right translation. -/
theorem GroupIdeal.exists_biInvariantMean (K : GroupIdeal U) (hK : IsCompact K.carrier)
    (htop : IsTopologicalGroup K.carrier) :
    ∃ m : LeftInvariantContinuousMean hleft, m.IsRightInvariant hright := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K.carrier := htop
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let μ := normalizedHaar K.carrier
  have hintegrable (f : C_c(U, ℝ)) : Integrable (fun a : K.carrier ↦ f a.1) μ :=
    (f.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let integrate : C_c(U, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ ∫ a : K.carrier, f a.1 ∂μ
      map_add' := fun f g ↦ integral_add (hintegrable f) (hintegrable g)
      map_smul' := fun r f ↦ integral_smul r (fun a : K.carrier ↦ f a.1)
      monotone' := fun f g h ↦ integral_mono (hintegrable f) (hintegrable g) (fun a ↦ h a.1) }
  have hleftIntegral (s : U) (f : C_c(U, ℝ)) :
      (∫ a : K.carrier, f (s * a.1) ∂μ) = ∫ a : K.carrier, f a.1 ∂μ := by
    let b : K.carrier := ⟨s * K.identity, K.mul_mem_left s K.identity_mem⟩
    have h (a : K.carrier) : s * a.1 = (b * a).1 := by
      change s * a.1 = (s * K.identity) * a.1
      rw [mul_assoc, K.identity_mul a.2]
    simp_rw [h]
    exact integral_mul_left_eq_self (μ := μ) (fun a : K.carrier ↦ f a.1) b
  have hrightIntegral (s : U) (f : C_c(U, ℝ)) :
      (∫ a : K.carrier, f (a.1 * s) ∂μ) = ∫ a : K.carrier, f a.1 ∂μ := by
    let b : K.carrier := ⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩
    have h (a : K.carrier) : a.1 * s = (a * b).1 := by
      change a.1 * s = a.1 * (K.identity * s)
      rw [← mul_assoc, K.mul_identity a.2]
    simp_rw [h]
    exact integral_mul_right_eq_self (μ := μ) (fun a : K.carrier ↦ f a.1) b
  refine ⟨⟨integrate, ?_, hleftIntegral⟩, hrightIntegral⟩
  change (∫ _ : K.carrier, (1 : ℝ) ∂μ) = 1
  simp

end Mean

section OperatorClosure

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (π : S →ₙ* (E →L[𝕜] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]

/-- Theorem 1.1. A weakly compact operator semigroup has a unique minimal idempotent
if and only if its continuous functions admit a bi-invariant mean. The mean is
represented by its real positive functional. -/
theorem existsUnique_minimalIdempotent_iff_exists_biInvariantMean :
    (∃! e : weakOperatorClosure π, IsMinimalIdempotent e) ↔
    (∃ m : LeftInvariantContinuousMean
        (fun s : weakOperatorClosure π ↦ continuous_const_mul s),
      m.IsRightInvariant (fun s ↦ continuous_mul_const s)) := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := exists_compact_groupIdeal_of_existsUnique_minimalIdempotent
      continuous_mul_const h
    exact K.exists_biInvariantMean hK (K.isTopologicalGroup_of_isCompact hK)
  · rintro ⟨m, hm⟩
    exact m.existsUnique_minimalIdempotent_of_biInvariant hm

end OperatorClosure

end JdLG
