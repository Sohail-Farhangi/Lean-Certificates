/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParityAmenability
public import JdLG.PaperExamplesParityAmbient
public import JdLG.UltrafilterMoreDiscreteMean
public import JdLG.WapSubspace

/-!
# An invariant WAP mean on the integers

The height map of the parity semigroup extends to its amenable group of
right quotients and surjects onto the integers. Pushing the mean along
that map gives the left and right invariant WAP mean used for the
integer translation space.
-/

@[expose] public section

namespace JdLG

open Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal

/-- Push a finitely additive left invariant probability along a surjective
semigroup homomorphism. -/
def LeftInvariantSetMean.map_surjective {S T : Type*} [Semigroup S] [Semigroup T]
    (m : LeftInvariantSetMean S) (f : S →ₙ* T) (hf : Function.Surjective f) :
    LeftInvariantSetMean T where
  mass A := m.mass (f ⁻¹' A)
  nonneg A := m.nonneg _
  empty := m.empty
  univ := m.univ
  add_disjoint h := m.add_disjoint (h.preimage f)
  invariant t A := by
    obtain ⟨s, rfl⟩ := hf t
    have h : f ⁻¹' ((f s * ·) ⁻¹' A) = (s * ·) ⁻¹' (f ⁻¹' A) := by
      ext x
      simp only [Set.mem_preimage, map_mul]
    rw [h, m.invariant]

namespace PaperExamplesPowers

open PaperExamplesParity

/-- The additive group of integers has a finitely additive left invariant
probability. -/
theorem integer_leftInvariantSetMean_exists :
    Nonempty (LeftInvariantSetMean (Multiplicative ℤ)) := by
  obtain ⟨G, hG, ι, hι, ⟨m⟩⟩ := parity_embeds_in_amenable_group
  let ht := heightHom.toMulHom.comp affineEmbedding
  obtain ⟨F, hF⟩ := (existsUnique_rightFractionLift hι ht).exists
  have hsurj : Function.Surjective F := by
    intro z
    let a : Point := ⟨0, z.toAdd.toNat⟩
    let b : Point := ⟨0, (-z.toAdd).toNat⟩
    refine ⟨ι a * (ι b)⁻¹, ?_⟩
    rw [map_mul, map_inv, hF a, hF b]
    change ((z.toAdd.toNat : ℤ) + 1) + -(((-z.toAdd).toNat : ℤ) + 1) = z.toAdd
    omega
  exact ⟨m.map_surjective F.toMulHom hsurj⟩

end PaperExamplesPowers

section Commutative

variable {S : Type*} [CommSemigroup S] [TopologicalSpace S] [SeparatelyContinuousMul S]
  [MeasurableSpace S] [BorelSpace S] [DiscreteMeasurableSpace S]

local notation "BC" => S →ᵇ ℝ
local notation "WAP" => weaklyAlmostPeriodicSubmodule (S := S)

omit [CommSemigroup S] [SeparatelyContinuousMul S] [DiscreteMeasurableSpace S] in
/-- A bounded continuous function is in L∞ for counting measure. -/
theorem boundedContinuous_memLp_count (f : BC) : MemLp f ∞ (Measure.count : Measure S) :=
  memLp_top_of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)

/-- On a commutative discrete semigroup, a left invariant set mean induces
a positive normalized bi-invariant mean on real WAP functions. -/
noncomputable def LeftInvariantSetMean.toWapBiInvariantMean (m : LeftInvariantSetMean S) :
    WapBiInvariantMean (S := S) where
  functional :=
    { toFun := fun f ↦ m.toDiscreteMeasuredMean.value f.val (boundedContinuous_memLp_count f.val)
      map_add' := fun f g ↦
        (m.toDiscreteMeasuredMean.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
          (m.toDiscreteMeasuredMean.value_add (boundedContinuous_memLp_count f.val)
            (boundedContinuous_memLp_count g.val))
      map_smul' := fun c f ↦
        (m.toDiscreteMeasuredMean.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
          (m.toDiscreteMeasuredMean.value_smul c (boundedContinuous_memLp_count f.val)) }
  monotone' _ _ h := m.toDiscreteMeasuredMean.value_mono (Eventually.of_forall h)
  one' := (m.toDiscreteMeasuredMean.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
    m.toDiscreteMeasuredMean.value_one
  left' s f g h := by
    have hg := MemLp.ae_eq (Eventually.of_forall h) (boundedContinuous_memLp_count g.val)
    exact (m.toDiscreteMeasuredMean.value_congr_ae (Eventually.of_forall h)).trans
      (m.toDiscreteMeasuredMean_leftInvariant s f.val (boundedContinuous_memLp_count f.val) hg)
  right' s f g h := by
    have hl (t : S) : g.val t = f.val (s * t) := by rw [mul_comm s t, h]
    have hg := MemLp.ae_eq (Eventually.of_forall hl) (boundedContinuous_memLp_count g.val)
    exact (m.toDiscreteMeasuredMean.value_congr_ae (Eventually.of_forall hl)).trans
      (m.toDiscreteMeasuredMean_leftInvariant s f.val (boundedContinuous_memLp_count f.val) hg)

end Commutative

end JdLG
