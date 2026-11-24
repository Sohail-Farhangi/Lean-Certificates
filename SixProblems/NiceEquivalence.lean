/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.ErgodicPDApproximation
public import SixProblems.NiceOperatorial
public import SixProblems.NiceSpectral

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing

variable {G : Type} [Group G] [Countable G] [Infinite G]

theorem niceVdC_iff_nonnegativePD {R : Set G} : NiceVdC R ↔ NonnegativeOnPositiveDefinite R :=
  ⟨fun h ↦ nonnegativePD_of_ergodicNiceRecurrence hasBoundedErgodicPDApproximation
    (ergodicNiceRecurrence_of_niceRecurrence (niceRecurrence_of_niceVdC h)),
    fun h ↦ niceVdC_of_niceOperatorialRecurrence (niceOperatorialRecurrence_of_nonnegativePD h)⟩

/-- The five equivalent conditions of Theorem 2.2 for a countably infinite
group. Each condition is linked to condition (a). -/
theorem theorem2_2 (R : Set G) (hR : R.Nonempty) :
    (NiceRecurrence R ↔ ErgodicNiceRecurrence R) ∧
    (NiceRecurrence R ↔ NiceOperatorialRecurrence R) ∧
    (NiceRecurrence R ↔ ∀ φ : G → ℝ, RealPositiveDefinite φ → 0 ≤ sSup (φ '' R)) ∧
    (NiceRecurrence R ↔ NiceVdC R) := by
  have hab := ergodicNiceRecurrence_of_niceRecurrence (R := R)
  have hbd := nonnegativePD_of_ergodicNiceRecurrence hasBoundedErgodicPDApproximation (R := R)
  have hdc := niceOperatorialRecurrence_of_nonnegativePD (R := R)
  have hce := niceVdC_of_niceOperatorialRecurrence (R := R)
  have hea := niceRecurrence_of_niceVdC (R := R)
  exact ⟨⟨hab,fun h ↦ hea (hce (hdc (hbd h)))⟩,
    ⟨fun h ↦ hdc (hbd (hab h)),fun h ↦ hea (hce h)⟩,
    (show NiceRecurrence R ↔ NonnegativeOnPositiveDefinite R from
      ⟨fun h ↦ hbd (hab h),fun h ↦ hea (hce (hdc h))⟩).trans
        (nonnegativeOnPositiveDefinite_iff_sSup hR),
    ⟨fun h ↦ hce (hdc (hbd (hab h))),hea⟩⟩

/-- For an abelian acting group, the five conditions are also equivalent to
condition (f), the Fourier coefficient lower bound by the trivial atom. -/
theorem theorem2_2_abelian [IsMulCommutative G] (R : Set G) (hR : R.Nonempty) :
    NiceRecurrence R ↔ ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ],
      τ.real {1} ≤ sSup ((fun r ↦ ‖spectralFourier τ r‖) '' R) :=
  (theorem2_2 R hR).2.2.1.trans (theorem2_2_d_iff_f hR)

end SixProblems
