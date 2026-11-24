/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.KernelIndependentCopies

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  {S : System G X} {T : System G Y} {μ : Measure (X × Y)}

namespace IsJoining

/-- Conditional distribution of the second coordinate given the first. -/
def conditionalSecond (h : IsJoining S T μ) : Kernel X Y :=
  h.fstFactor.conditionalKernel.map Prod.snd

instance (h : IsJoining S T μ) : IsMarkovKernel h.conditionalSecond :=
  Kernel.IsMarkovKernel.map _ measurable_snd

theorem conditionalSecond_barycenter (h : IsJoining S T μ) :
    h.conditionalSecond ∘ₘ S.measure = T.measure := by
  rw [conditionalSecond, ← Measure.map_comp _ _ measurable_snd,
    h.fstFactor.comp_conditionalKernel]
  exact h.snd.map_eq

theorem conditionalSecond_equivariant (h : IsJoining S T μ) (g : G) :
    ∀ᵐ x ∂S.measure, (h.conditionalSecond x).map (T.act g) =
      h.conditionalSecond (S.act g x) := by
  filter_upwards [h.fstFactor.ae_conditionalKernel_equivariant g] with x hx
  let η := h.fstFactor.conditionalKernel
  change (η x).map (S.prodAct T g) = η (S.act g x) at hx
  have hcomp : T.act g ∘ (Prod.snd : X × Y → Y) = Prod.snd ∘ S.prodAct T g := rfl
  simp only [conditionalSecond, Kernel.map_apply _ measurable_snd]
  change ((η x).map Prod.snd).map (T.act g) = (η (S.act g x)).map Prod.snd
  rw [Measure.map_map (T.preserves g).measurable measurable_snd, hcomp,
    ← Measure.map_map measurable_snd (h.invariant g).measurable, hx]

/-- Recover the joining by integrating its conditional second marginals. -/
theorem compProd_conditionalSecond (h : IsJoining S T μ) :
    S.measure ⊗ₘ h.conditionalSecond = μ := by
  let η := h.fstFactor.conditionalKernel
  have hGraph : S.measure ⊗ₘ η = coordinateGraph μ Prod.fst :=
    h.fstFactor.compProd_conditionalKernel
  apply Measure.ext_prod
  intro A B hA hB
  have hm : Measurable (fun w : X × Y ↦ (w.1, w)) := measurable_fst.prodMk measurable_id
  rw [Measure.compProd_apply_prod hA hB]
  simp only [conditionalSecond, Kernel.map_apply' _ measurable_snd _ hB]
  rw [← Measure.compProd_apply_prod hA (measurable_snd hB), hGraph,
    coordinateGraph, Measure.map_apply hm (hA.prod (measurable_snd hB))]
  rfl

/-- Countable relatively independent samples of the second coordinate over
the first coordinate. The base coordinate is integrated out. -/
def independentCopiesSystem (h : IsJoining S T μ) : System G (ℕ → Y) where
  measure := independentCopies h.conditionalSecond ∘ₘ S.measure
  probability := inferInstance
  act g w i := T.act g (w i)
  act_one := by funext w i; rw [T.act_one]; rfl
  act_mul g k := by funext w i; exact congrFun (T.act_mul g k) (w i)
  preserves g := by
    let K := independentCopies h.conditionalSecond
    let t (w : ℕ → Y) (i : ℕ) := T.act g (w i)
    have ht : Measurable t := Measurable.of_eval fun i ↦
      (T.preserves g).measurable.comp (measurable_pi_apply i)
    refine ⟨ht, ?_⟩
    change (K ∘ₘ S.measure).map t = K ∘ₘ S.measure
    rw [Measure.map_comp _ _ ht]
    calc
      _ = K.comap (S.act g) (S.preserves g).measurable ∘ₘ S.measure := by
        apply Measure.bind_congr_right
        filter_upwards [h.conditionalSecond_equivariant g] with x hx
        rw [Kernel.map_apply K ht, Kernel.comap_apply, independentCopies_map_pi _ (T.preserves g).measurable,
          hx]
        rfl
      _ = K ∘ₘ S.measure.map (S.act g) := by
        rw [Measure.bind_map (S.preserves g).aemeasurable K.aemeasurable]
        rfl
      _ = K ∘ₘ S.measure := by rw [(S.preserves g).map_eq]

/-- Each coordinate is a factor onto the original second system. -/
def independentCopiesFactor (h : IsJoining S T μ) (i : ℕ) :
    FactorMap h.independentCopiesSystem T where
  toFun w := w i
  equivariant _ := rfl
  preserves := by
    refine ⟨measurable_pi_apply i, ?_⟩
    change (independentCopies h.conditionalSecond ∘ₘ S.measure).map (fun w ↦ w i) = T.measure
    rw [Measure.map_comp _ _ (measurable_pi_apply i), ← h.conditionalSecond_barycenter]
    apply Measure.bind_congr_right
    exact ae_of_all _ fun x ↦ (Kernel.map_apply _ (measurable_pi_apply i) x).trans
      (independentCopies_map_eval h.conditionalSecond x i)

end IsJoining

end Mixing
