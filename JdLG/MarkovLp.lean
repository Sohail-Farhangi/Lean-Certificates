/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MarkovTransfer
public import JdLG.ContractiveCriterion
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! # The inclusion of probability L² into L¹ -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace JdLG

section Inclusion

variable {X 𝕜 E : Type*} [MeasurableSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (μ : Measure X) [IsProbabilityMeasure μ]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The norm-one bound for the inclusion of probability Lᵠ into Lᵖ, for p ≤ q. -/
noncomputable def probabilityLpInclusion (hpq : p ≤ q) : Lp E q μ →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ⟨f.1, Lp.antitone hpq f.2⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
    1 (fun f ↦ by
      rw [one_mul]
      change (eLpNorm (⇑f : X → E) p μ).toReal ≤ (eLpNorm (⇑f : X → E) q μ).toReal
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_le_eLpNorm_of_exponent_le hpq))

@[simp]
theorem probabilityLpInclusion_coeFn (hpq : p ≤ q) (f : Lp E q μ) :
    (probabilityLpInclusion (𝕜 := 𝕜) μ hpq f : X → E) = f := rfl

theorem probabilityLpInclusion_injective (hpq : p ≤ q) :
    Function.Injective (probabilityLpInclusion (E := E) (𝕜 := 𝕜) μ hpq) :=
  fun _ _ h ↦ Subtype.ext (congrArg (fun f : Lp E p μ ↦ f.1) h)

theorem norm_probabilityLpInclusion_le (hpq : p ≤ q) :
    ‖probabilityLpInclusion (E := E) (𝕜 := 𝕜) μ hpq‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  change (eLpNorm (⇑f : X → E) p μ).toReal ≤ (eLpNorm (⇑f : X → E) q μ).toReal
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_le_eLpNorm_of_exponent_le hpq)

/-- Simple functions belong to both spaces, so the inclusion has dense range
when the target exponent is finite. -/
theorem probabilityLpInclusion_denseRange (hpq : p ≤ q) (hp : p ≠ ∞) :
    DenseRange (probabilityLpInclusion (E := E) (𝕜 := 𝕜) μ hpq) := by
  apply (Lp.simpleFunc.dense (E := E) (μ := μ) hp).mono
  intro f hf
  let fs : Lp.simpleFunc E p μ := ⟨f, hf⟩
  let g := Lp.simpleFunc.toSimpleFunc fs
  let h := g.memLp_of_isFiniteMeasure q μ
  refine ⟨h.toLp g, ?_⟩
  apply Lp.ext
  rw [probabilityLpInclusion_coeFn]
  exact h.coeFn_toLp.trans (Lp.simpleFunc.toSimpleFunc_eq_toFun fs)

end Inclusion

section Transfer

variable {X S : Type*} [MeasurableSpace X] [Semigroup S] [Nonempty S]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- A uniformly bounded action on probability L¹ is JdLG-admissible if its
restriction through L² acts by Hilbert contractions. -/
theorem admissible_probabilityLpOne_of_lpTwo_contractions
    (π : S →ₙ* (Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ))
    (σ : S →ₙ* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
    (hinter : ∀ s x, π s (probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) x) =
      probabilityLpInclusion (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (σ s x))
    {C : ℝ} (hC : 0 ≤ C) (hπ : ∀ s, ‖π s‖ ≤ C) (hσ : ∀ s, ‖σ s‖ ≤ 1) :
    IsJdLGAdmissible π := by
  let j := probabilityLpInclusion (E := ℂ) (𝕜 := ℂ) μ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact admissible_denseIntertwiner j
    (probabilityLpInclusion_denseRange μ (by norm_num) (by simp)) hinter hC hπ
    (admissible_of_hilbert_contractions σ hσ)

end Transfer

end JdLG
