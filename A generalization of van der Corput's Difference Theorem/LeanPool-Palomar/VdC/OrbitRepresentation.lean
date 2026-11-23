/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Metrizable.Basic

/-! The topological shift representation of a bounded sequence. -/

@[expose] public section

open Function Set TopologicalSpace

namespace VdC

/-- A bounded sequence is a continuous observation of a dense forward orbit in a
compact metrizable space, as in the first assertion of `RepresentationLemma`. -/
theorem bounded_sequence_orbit_representation {u : ℕ → ℂ} (hu : BoundedSeq u) :
    ∃ (X : Type) (_top : TopologicalSpace X),
      CompactSpace X ∧ MetrizableSpace X ∧
      ∃ (S : C(X, X)) (F : C(X, ℂ)) (x : X),
        DenseRange (fun n : ℕ ↦ S^[n] x) ∧ ∀ n : ℕ, F (S^[n] x) = u n := by
  obtain ⟨C, _, hC⟩ := hu
  let B : Type := Metric.closedBall (0 : ℂ) C
  have hB : IsCompact (Metric.closedBall (0 : ℂ) C) := isCompact_closedBall _ _
  have : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let Ω : Type := ℕ → B
  let shift : Ω → Ω := fun z n ↦ z (n + 1)
  have hshift : Continuous shift := continuous_pi fun n ↦ continuous_apply (n + 1)
  let x : Ω := fun n ↦ ⟨u n, by simpa [Metric.mem_closedBall, dist_zero_right] using hC n⟩
  let orbit : Set Ω := range fun n : ℕ ↦ shift^[n] x
  let X := closure orbit
  have hinv : MapsTo shift X X := by
    have hsub : shift '' orbit ⊆ orbit := by
      rintro y ⟨z, ⟨n, rfl⟩, rfl⟩
      exact ⟨n + 1, Function.iterate_succ_apply' shift n x⟩
    intro y hy
    exact (closure_mono hsub) (image_closure_subset_closure_image hshift ⟨y, hy, rfl⟩)
  have hcompact : CompactSpace X := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let S : C(X, X) := ⟨fun z ↦ ⟨shift z, hinv z.property⟩,
    (hshift.comp continuous_subtype_val).subtype_mk _⟩
  let F : C(X, ℂ) := ⟨fun z ↦ ((z.val 0).val : ℂ),
    continuous_subtype_val.comp ((continuous_apply 0).comp continuous_subtype_val)⟩
  let y : X := ⟨x, subset_closure ⟨0, rfl⟩⟩
  have hiter (n : ℕ) : (S^[n] y : Ω) = shift^[n] x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change shift (S^[n] y : Ω) = shift (shift^[n] x)
      rw [ih]
  have horbit : Subtype.val '' (range fun n : ℕ ↦ S^[n] y) = orbit := by
    rw [← Set.range_comp]
    change (range fun n : ℕ ↦ (S^[n] y : Ω)) = orbit
    simp only [hiter, orbit]
  have hdense : DenseRange (fun n : ℕ ↦ S^[n] y) := by
    intro z
    rw [closure_subtype, horbit]
    exact z.property
  have happly (n k : ℕ) : (shift^[n] x) k = x (k + n) := by
    induction n generalizing k with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change (shift^[n] x) (k + 1) = _
      rw [ih]
      congr 1
      omega
  refine ⟨X, inferInstance, hcompact, inferInstance, S, F, y, hdense, fun n ↦ ?_⟩
  change (((S^[n] y : Ω) 0).val : ℂ) = u n
  rw [hiter, happly, zero_add]

end VdC
