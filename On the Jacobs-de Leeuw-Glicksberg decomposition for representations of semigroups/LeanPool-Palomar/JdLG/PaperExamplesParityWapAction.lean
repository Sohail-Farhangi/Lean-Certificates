/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesParityWap
public import JdLG.PaperExamplesWapClosed

/-!
# Right translation on the full complex WAP space of the parity semigroup

The indicator and its coefficient average are realized on all bounded
weakly almost periodic functions, with the relatively weakly compact
right translation representation from the example.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

open Filter
open scoped Topology ENNReal

/-- All complex bounded weakly almost periodic functions on the parity
semigroup, with the sup norm. -/
noncomputable abbrev ComplexParityWap := wapVectorSubmodule rightTranslation

/-- Right translation restricted to the full WAP subspace. -/
noncomputable def parityWapRepresentation :
    Point →ₙ* (ComplexParityWap →L[ℂ] ComplexParityWap) :=
  wapVectorRepresentation rightTranslation

theorem parity_rightTranslation_opNorm_le (s : Point) : ‖rightTranslation s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply lp.norm_le_of_forall_le (norm_nonneg f)
  intro t
  change ‖f (t * s)‖ ≤ ‖f‖
  exact lp.norm_apply_le_norm (by simp) f _

instance : CompleteSpace ComplexParityWap :=
  (isClosed_wapVectorSubmodule rightTranslation parity_rightTranslation_opNorm_le).completeSpace_coe

theorem parityWapRepresentation_weakly_compact :
    IsCompact (weakOperatorClosure parityWapRepresentation :
      Set (ComplexParityWap →WOT[ℂ] ComplexParityWap)) :=
  compact_weakOperatorClosure_wapVectorRepresentation rightTranslation
    parity_rightTranslation_opNorm_le

/-- The even principal left ideal indicator, as a vector in the full WAP
subspace of the parity semigroup. -/
noncomputable def parityWapVector : ComplexParityWap :=
  ⟨indicator, indicator_weakly_almost_periodic⟩

theorem parityWapVector_almost_weakly_stable :
    IsAlmostWeaklyStable (closureAction parityWapRepresentation) parityWapVector := by
  refine ⟨closureInclusion parityWapRepresentation oddPoint, ?_⟩
  apply Subtype.ext
  exact rightTranslation_indicator_oddPoint

/-- The average in Eq. (15), for the literal WAP right translation
representation and point evaluation, converges to one. -/
theorem parityWapVector_coefficient_average (s₀ : Point) :
    Tendsto (fun n ↦
      (∑ s ∈ positiveGrid n, ‖(parityWapRepresentation s parityWapVector).val s₀‖) /
      ((positiveGrid n).card : ℝ)) atTop (𝓝 1) :=
  parity_coefficient_average_tendsto_one s₀

end JdLG.PaperExamplesParity
