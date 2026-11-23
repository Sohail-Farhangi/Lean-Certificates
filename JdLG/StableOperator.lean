/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import JdLG.StableMeans
public import JdLG.StableReturns

/-!
# The Haar and mean criteria on the weak operator closure

For the operator closure itself, the abstract annihilator condition is exactly
membership of zero in the weak closure of the original vector orbit.
-/

@[expose] public section

open MeasureTheory Set

namespace JdLG

variable {S E : Type*} [Semigroup S] [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : S →ₙ* (E →L[ℂ] E))

/-- Left translations of the weak operator closure are continuous. -/
theorem continuous_leftTranslate_weakOperatorClosure (s : weakOperatorClosure π) :
    Continuous (fun t : weakOperatorClosure π => s * t) :=
  continuous_const_mul s

/-- The orbit map of the weak operator closure is continuous into the weak space. -/
theorem continuous_weakOrbit_closureAction (x : E) :
    Continuous (fun s : weakOperatorClosure π => toWeakSpace ℂ E (closureAction π s x)) :=
  WeakBilin.continuous_of_continuous_eval _ fun f =>
    (ContinuousLinearMapWOT.continuous_dual_apply x f).comp continuous_subtype_val

/-- A scalar coefficient of the action of the weak operator closure is continuous. -/
theorem continuous_closureAction_coefficient (x : E) (f : StrongDual ℂ E) :
    Continuous (fun s : weakOperatorClosure π => f (closureAction π s x)) :=
  (ContinuousLinearMapWOT.continuous_dual_apply x f).comp continuous_subtype_val

variable [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]

/-- The compact-host mean version of Lemma 4.1 for an actual operator representation.
The mean acts on the continuous functions of the weak operator closure. -/
theorem weakOrbitClosure_iff_compactMeanMoments
    (K : GroupIdeal (weakOperatorClosure π)) [CompactSpace K.carrier]
    [MeasurableSpace K.carrier] [BorelSpace K.carrier]
    (m : LeftInvariantContinuousMean (continuous_leftTranslate_weakOperatorClosure π)) (x : E) :
    ((0 : WeakSpace ℂ E) ∈ closure (range fun s : S => toWeakSpace ℂ E (π s x)) ↔
      ∀ (p : ℝ) (hp : 0 < p) (f : StrongDual ℂ E),
        compactCoefficientMoment m (closureAction π) x f
          (continuous_closureAction_coefficient π x f) p hp = 0) ∧
    ((0 : WeakSpace ℂ E) ∈ closure (range fun s : S => toWeakSpace ℂ E (π s x)) ↔
      ∃ (p : ℝ) (hp : 0 < p), ∀ f : StrongDual ℂ E,
        compactCoefficientMoment m (closureAction π) x f
          (continuous_closureAction_coefficient π x f) p hp = 0) := by
  let i : K.carrier →ₙ* weakOperatorClosure π := ⟨Subtype.val, fun _ _ => rfl⟩
  have habsorb (s : weakOperatorClosure π) : ∃ g : K.carrier, i g = i 1 * s :=
    ⟨⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩, rfl⟩
  have hmean := almostWeaklyStable_iff_continuousMeanMoments m i continuous_subtype_val
    Subtype.val_injective habsorb (closureAction π) x (continuous_closureAction_coefficient π x)
  have hstable := stable_iff_zero_mem_weakOrbitClosure (π := π)
    (isCompact_iff_compactSpace.mpr inferInstance) x
  exact ⟨hstable.symm.trans hmean.1, hstable.symm.trans hmean.2⟩

/-- The compact-host weak-return form of Theorem 4.2(iii) for the actual operator
representation and an invariant Borel probability on the weak operator closure. -/
theorem weakOrbitClosure_iff_compactWeakReturnFullMeasure
    (K : GroupIdeal (weakOperatorClosure π)) [CompactSpace K.carrier]
    [MeasurableSpace K.carrier] [BorelSpace K.carrier] (x : E)
    (μ : Measure (weakOperatorClosure π)) [IsProbabilityMeasure μ]
    [Measure.IsMulLeftInvariant μ] :
    (0 : WeakSpace ℂ E) ∈ closure (range fun s : S => toWeakSpace ℂ E (π s x)) ↔
      ∀ U : Set (WeakSpace ℂ E), IsOpen U → 0 ∈ U →
        μ ((fun s => toWeakSpace ℂ E (closureAction π s x)) ⁻¹' U) = 1 := by
  let i : K.carrier →ₙ* weakOperatorClosure π := ⟨Subtype.val, fun _ _ => rfl⟩
  have habsorb (s : weakOperatorClosure π) : ∃ g : K.carrier, i g = i 1 * s :=
    ⟨⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩, rfl⟩
  have hret := almostWeaklyStable_iff_weakReturnFullMeasure i continuous_subtype_val
    Subtype.val_injective (continuous_leftTranslate_weakOperatorClosure π) habsorb
    (closureAction π) x (continuous_weakOrbit_closureAction π x) μ
  have hstable := stable_iff_zero_mem_weakOrbitClosure (π := π)
    (isCompact_iff_compactSpace.mpr inferInstance) x
  exact hstable.symm.trans hret

end JdLG
