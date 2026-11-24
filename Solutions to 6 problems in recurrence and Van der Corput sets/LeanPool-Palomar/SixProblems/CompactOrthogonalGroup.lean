/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ErgodicBarycenters
public import Mixing.SupportingJdLG.Stable
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Dynamics.Ergodic.Action.OfMinimal
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Set Mixing Mixing.JdLGBridge

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Regard an orthogonal representation as a homomorphism into the unitary
group of the real algebra of bounded operators. -/
def orthogonalUnitaryHom (U : G →* (E ≃ₗᵢ[ℝ] E)) : G →* unitary (E →L[ℝ] E) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp U

/-- For a finite-dimensional space this subgroup carries a compact metrizable topology. -/
def orthogonalClosure (U : G →* (E ≃ₗᵢ[ℝ] E)) : Subgroup (unitary (E →L[ℝ] E)) :=
  (orthogonalUnitaryHom U).range.topologicalClosure

private theorem unitary_compactSpace [FiniteDimensional ℝ E] :
    CompactSpace (unitary (E →L[ℝ] E)) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset isClosed_unitary
  intro T hT
  rw [Metric.mem_closedBall, dist_zero_right]
  apply ContinuousLinearMap.opNorm_le_bound T zero_le_one
  intro x
  simpa only [one_mul] using (Unitary.norm_map ⟨T,hT⟩ x).le

instance [FiniteDimensional ℝ E] (U : G →* (E ≃ₗᵢ[ℝ] E)) : CompactSpace (orthogonalClosure U) := by
  let : CompactSpace (unitary (E →L[ℝ] E)) := unitary_compactSpace
  exact isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact

/-- The original group maps densely into the compact closure. -/
def orthogonalClosureHom (U : G →* (E ≃ₗᵢ[ℝ] E)) : G →* orthogonalClosure U :=
  (orthogonalUnitaryHom U).codRestrict (orthogonalClosure U) fun g ↦
    Subgroup.le_topologicalClosure _ ⟨g,rfl⟩

theorem denseRange_orthogonalClosureHom (U : G →* (E ≃ₗᵢ[ℝ] E)) :
    DenseRange (orthogonalClosureHom U) := by
  intro x
  apply closure_subtype.mpr
  rw [← range_comp]
  exact x.property

/-- The tautological orthogonal representation of the closure on the same space. -/
def orthogonalClosureRep (U : G →* (E ≃ₗᵢ[ℝ] E)) : orthogonalClosure U →* (E ≃ₗᵢ[ℝ] E) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp (orthogonalClosure U).subtype

theorem orthogonalClosureRep_apply_hom (U : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) :
    orthogonalClosureRep U (orthogonalClosureHom U g) = U g :=
  Unitary.linearIsometryEquiv.apply_symm_apply (U g)

theorem continuous_orthogonalClosureRep_apply (U : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    Continuous (fun k ↦ orthogonalClosureRep U k x) := by
  change Continuous (fun k : orthogonalClosure U ↦ (k.val.val : E →L[ℝ] E) x)
  exact (continuous_subtype_val.comp continuous_subtype_val).clm_apply continuous_const

section HaarRotation

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- Left multiplication through a homomorphism into a compact group, with
normalized Haar measure. -/
def haarRotation (α : G →* K) : System G K where
  measure := normalizedHaar K
  probability := inferInstance
  act g k := α g * k
  act_one := by ext k; rw [map_one, one_mul]; rfl
  act_mul g h := by ext k; simp [map_mul, mul_assoc]
  preserves g := measurePreserving_mul_left _ (α g)

/-- A dense subgroup of a compact metrizable group acts ergodically on Haar measure. -/
theorem haarRotation_isErgodic [T2Space K] (α : G →* K) (hα : DenseRange α) :
    (haarRotation α).IsErgodic := by
  intro A hA hInv
  change Filter.EventuallyEmptyOrUniv A (ae (normalizedHaar K))
  apply aeconst_of_dense_setOfPred_preimage_smul_ae (M := K) hA.nullMeasurableSet
  apply hα.mono
  rintro _ ⟨g,rfl⟩
  exact hInv g

end HaarRotation

end SixProblems
