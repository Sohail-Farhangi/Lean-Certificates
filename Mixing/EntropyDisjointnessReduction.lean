/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ConditionalEventFactor
public import Mixing.EntropyFactorDirection

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {G : Type} {X Y : Type*} [CommGroup G] [Countable G]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
  [Nonempty X] [Nonempty Y]

/-- The forward direction of the entropy duality once zero entropy is known
to pass to countable self-joinings of the second system. The proof obtains
the candidate zero-entropy factor directly from conditional probabilities. -/
theorem disjoint_of_completelyPositiveEntropy_of_zeroEntropyCopies
    {S : System G X} {T : System G Y} (hCPE : S.HasCompletelyPositiveEntropy)
    (hCopies : ∀ μ : Measure (X × Y), ∀ h : IsJoining S T μ,
      h.independentCopiesSystem.HasZeroEntropy) :
    Disjoint S T := by
  intro μ h
  let := h.probability
  apply Measure.ext_prod
  intro A B hA hB
  let Q := h.conditionalEventSystem hB
  let F := h.conditionalEventFactor hB
  let κ := h.conditionalSecond
  have hQ : Q.HasZeroEntropy :=
    (h.independentCopiesEventFactor hB).hasZeroEntropy_target (hCopies μ h)
  have h01 : IsZeroOneMeasure Q.measure := ⟨hCPE (G × ℕ → ℂ) Q F hQ⟩
  obtain ⟨w, hw⟩ := MeasureTheory.IsZeroOneMeasure.exists_eq_dirac (μ := Q.measure)
  have hW : ∀ᵐ x ∂S.measure, F.toFun x = w := by
    apply (ae_map_iff F.preserves.aemeasurable
      (measurableSet_eq_fun measurable_id measurable_const)).mp
    rw [F.preserves.map_eq, hw]
    exact (ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const)).mpr rfl
  let b := h.conditionalEventObservable hB
  let d := b.l2 S.measure
  let c := ENNReal.ofReal (w (1, 0)).re
  have hAe : (fun x ↦ κ x B) =ᵐ[S.measure] fun _ ↦ c := by
    filter_upwards [hW, b.coe_l2 S.measure] with x hx hdx
    have he := congrFun hx (1, 0)
    change d (S.act 1 x) = w (1, 0) at he
    rw [S.act_one, id_eq, hdx] at he
    have hr := congrArg Complex.re he
    change (κ x B).toReal = (w (1, 0)).re at hr
    change κ x B = ENNReal.ofReal (w (1, 0)).re
    rw [← hr, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hc : c = T.measure B := by
    calc
      c = ∫⁻ _ : X, c ∂S.measure := by simp
      _ = ∫⁻ x, κ x B ∂S.measure := lintegral_congr_ae hAe.symm
      _ = (κ ∘ₘ S.measure) B := (Measure.bind_apply hB κ.aemeasurable).symm
      _ = T.measure B := by rw [h.conditionalSecond_barycenter]
  rw [← h.compProd_conditionalSecond, Measure.compProd_apply_prod hA hB, Measure.prod_prod]
  rw [lintegral_congr_ae (ae_restrict_of_ae hAe), lintegral_const, Measure.restrict_apply_univ, hc, mul_comm]

end Mixing
