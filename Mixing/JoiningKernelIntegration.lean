/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.FactorJoiningLift
public import Mixing.JoiningExtreme

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {G X Y Z : Type*} [Group G]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- A kernel carried by the fibres of a measurable coordinate is the
disintegration of its barycenter over that coordinate. -/
theorem coordinateGraph_bind_eq_compProd [MeasurableEq Z] {W : Type*} [MeasurableSpace W]
    {π : W → Z} (hπ : Measurable π) (ν : Measure Z) [IsFiniteMeasure ν]
    (κ : Kernel Z W) [IsMarkovKernel κ]
    (hκ : ∀ᵐ z ∂ν, ∀ᵐ w ∂κ z, π w = z) :
    coordinateGraph (κ ∘ₘ ν) π = ν ⊗ₘ κ := by
  have he : (fun w : Z × W ↦ (π w.2, w.2)) =ᵐ[ν ⊗ₘ κ] id := by
    apply Measure.ae_compProd_of_ae_ae
    · have heq : {w : Z × W | (π w.2, w.2) = w} = {w | π w.2 = w.1} := by
        ext w
        exact ⟨congrArg Prod.fst, fun h ↦ Prod.ext h rfl⟩
      change MeasurableSet {w : Z × W | (π w.2, w.2) = w}
      rw [heq]
      exact measurableSet_eq_fun (hπ.comp measurable_snd) measurable_fst
    · filter_upwards [hκ] with z hz
      filter_upwards [hz] with w hw
      exact Prod.ext hw rfl
  have hg : Measurable (fun w : W ↦ (π w, w)) := hπ.prodMk measurable_id
  rw [← Measure.snd_compProd, coordinateGraph, Measure.snd, Measure.map_map hg measurable_snd]
  change (ν ⊗ₘ κ).map (fun w : Z × W ↦ (π w.2, w.2)) = _
  rw [Measure.map_congr he, Measure.map_id]

/-- Integrate a measurable family of component joinings. Its total measure
has the prescribed marginals and is invariant under the diagonal action. -/
theorem isJoining_integrated_component_kernel [StandardBorelSpace Y] [Nonempty Y]
    {S : System G X} {T : System G Y} {R : System G Z}
    (F : FactorMap T R) (κ : Kernel Z (X × Y)) [IsMarkovKernel κ]
    (hκ : ∀ᵐ z ∂R.measure,
      (κ z).map Prod.fst = S.measure ∧ (κ z).map Prod.snd = F.conditionalKernel z ∧
      ∀ g, (κ z).map (S.prodAct T g) = κ z) :
    IsJoining S T (κ ∘ₘ R.measure) := by
  have hleft : (κ ∘ₘ R.measure).map Prod.fst = S.measure := by
    rw [Measure.map_comp _ _ measurable_fst]
    calc
      κ.map Prod.fst ∘ₘ R.measure = Kernel.const Z S.measure ∘ₘ R.measure := by
        apply Measure.bind_congr_right
        filter_upwards [hκ] with z hz
        simpa [Kernel.map_apply, measurable_fst] using hz.1
      _ = S.measure := by simp
  have hright : (κ ∘ₘ R.measure).map Prod.snd = T.measure := by
    rw [Measure.map_comp _ _ measurable_snd, ← F.comp_conditionalKernel]
    apply Measure.bind_congr_right
    filter_upwards [hκ] with z hz
    simpa [Kernel.map_apply, measurable_snd] using hz.2.1
  refine ⟨inferInstance, ⟨measurable_fst, hleft⟩, ⟨measurable_snd, hright⟩, ?_⟩
  intro g
  have hg : Measurable (S.prodAct T g) :=
    (S.preserves g).measurable.prodMap (T.preserves g).measurable
  refine ⟨hg, ?_⟩
  rw [Measure.map_comp _ _ hg]
  apply Measure.bind_congr_right
  filter_upwards [hκ] with z hz
  simpa [Kernel.map_apply, hg] using hz.2.2 g

/-- Fibre support follows from the second marginal of a component joining.
This also lets uniqueness of disintegration recover the component kernels. -/
theorem coordinateGraph_integrated_component_kernel
    [StandardBorelSpace Y] [Nonempty Y] [MeasurableEq Z]
    {T : System G Y} {R : System G Z}
    (F : FactorMap T R) (κ : Kernel Z (X × Y)) [IsMarkovKernel κ]
    (hκ : ∀ᵐ z ∂R.measure, (κ z).map Prod.snd = F.conditionalKernel z) :
    coordinateGraph (κ ∘ₘ R.measure) (F.toFun ∘ Prod.snd) = R.measure ⊗ₘ κ := by
  apply coordinateGraph_bind_eq_compProd (F.preserves.measurable.comp measurable_snd)
  filter_upwards [F.ae_conditionalKernel_fibre, hκ] with z hz heq
  rw [← heq] at hz
  exact (ae_map_iff measurable_snd.aemeasurable
    (measurableSet_eq_fun F.preserves.measurable measurable_const)).mp hz

/-- The converse direction of Lemma 1(iii) for a measurable witness. Whenever
the component joinings form a kernel, disjointness forces that kernel to be
the product on almost every fibre. -/
theorem ae_componentKernel_eq_prod_of_disjoint
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y] [MeasurableEq Z]
    {S : System G X} {T : System G Y} {R : System G Z}
    (F : FactorMap T R) (hd : Disjoint S T)
    (κ : Kernel Z (X × Y)) [IsMarkovKernel κ]
    (hκ : ∀ᵐ z ∂R.measure,
      (κ z).map Prod.fst = S.measure ∧ (κ z).map Prod.snd = F.conditionalKernel z ∧
      ∀ g, (κ z).map (S.prodAct T g) = κ z) :
    ∀ᵐ z ∂R.measure, κ z = S.measure.prod (F.conditionalKernel z) := by
  let J : Kernel Z (X × Y) := (Kernel.const Z S.measure) ×ₖ F.conditionalKernel
  have hJ (z : Z) : J z = S.measure.prod (F.conditionalKernel z) := by
    rw [Kernel.prod_apply, Kernel.const_apply]
  have hmargJ : ∀ᵐ z ∂R.measure, (J z).map Prod.snd = F.conditionalKernel z :=
    ae_of_all _ fun z ↦ by rw [hJ, Measure.map_snd_prod, measure_univ, one_smul]
  have hIntJ : J ∘ₘ R.measure = S.measure.prod T.measure := by
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.prod_prod, ← F.comp_conditionalKernel]
    change R.measure.bind J (A ×ˢ B) = S.measure A * R.measure.bind F.conditionalKernel B
    rw [Measure.bind_apply (hA.prod hB) J.aemeasurable,
      Measure.bind_apply hB F.conditionalKernel.aemeasurable,
      ← lintegral_const_mul _ (F.conditionalKernel.measurable_coe hB)]
    apply lintegral_congr
    intro z
    rw [hJ, Measure.prod_prod]
  have hIntκ := hd _ (isJoining_integrated_component_kernel F κ hκ)
  have he : R.measure ⊗ₘ κ = R.measure ⊗ₘ J := by
    rw [← coordinateGraph_integrated_component_kernel F κ (hκ.mono fun _ hz ↦ hz.2.1),
      ← coordinateGraph_integrated_component_kernel F J hmargJ, hIntκ, hIntJ]
  exact (Kernel.ae_eq_of_compProd_eq he).mono fun z hz ↦ hz.trans (hJ z)

/-- An extreme joining rules out any nonconstant measurable convex
decomposition of its conditional measures into component joinings.
This is the integration step in Lemma 1(ii). -/
theorem ae_component_decomposition_trivial_of_extreme {H : Type*} [CommGroup H]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y] [MeasurableEq Z]
    {S : System H X} {T : System H Y} {R : System H Z} (F : FactorMap T R)
    {joining : Measure (X × Y)} [IsProbabilityMeasure joining]
    (hjoining : IsExtremeJoining S T joining)
    (κ₀ κ₁ : Kernel Z (X × Y)) [IsMarkovKernel κ₀] [IsMarkovKernel κ₁]
    (h₀ : ∀ᵐ z ∂R.measure,
      (κ₀ z).map Prod.fst = S.measure ∧ (κ₀ z).map Prod.snd = F.conditionalKernel z ∧
      ∀ g, (κ₀ z).map (S.prodAct T g) = κ₀ z)
    (h₁ : ∀ᵐ z ∂R.measure,
      (κ₁ z).map Prod.fst = S.measure ∧ (κ₁ z).map Prod.snd = F.conditionalKernel z ∧
      ∀ g, (κ₁ z).map (S.prodAct T g) = κ₁ z)
    {a : ℝ≥0∞} (ha : 0 < a) (ha' : a < 1)
    (he : ∀ᵐ z ∂R.measure,
      a • κ₀ z + (1 - a) • κ₁ z = (coordinateGraph joining (F.toFun ∘ Prod.snd)).condKernel z) :
    ∀ᵐ z ∂R.measure, κ₀ z = κ₁ z := by
  let ρ := coordinateGraph joining (F.toFun ∘ Prod.snd)
  have hq : Measurable (F.toFun ∘ (Prod.snd : X × Y → Y)) :=
    F.preserves.measurable.comp measurable_snd
  have hfst : ρ.fst = R.measure := by
    rw [coordinateGraph_fst joining hq, ← Measure.map_map F.preserves.measurable measurable_snd,
      hjoining.1.snd.map_eq, F.preserves.map_eq]
  have hInt : ρ.condKernel ∘ₘ R.measure = joining := by
    rw [← hfst, ← Measure.snd_compProd, ρ.disintegrate ρ.condKernel, coordinateGraph_snd joining hq]
  have hsum : a • (κ₀ ∘ₘ R.measure) + (1 - a) • (κ₁ ∘ₘ R.measure) = joining := by
    rw [← hInt]
    ext A hA
    simp only [add_apply, smul_apply, smul_eq_mul, Measure.bind_apply hA
      (Kernel.aemeasurable _)]
    have hm : Measurable (fun z ↦ a * κ₀ z A) := measurable_const.mul (κ₀.measurable_coe hA)
    calc
      _ = ∫⁻ z, a * κ₀ z A + (1 - a) * κ₁ z A ∂R.measure := by
        rw [lintegral_add_left hm, lintegral_const_mul _ (κ₀.measurable_coe hA),
          lintegral_const_mul _ (κ₁.measurable_coe hA)]
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [he] with z hz
        change _ = (coordinateGraph joining (F.toFun ∘ Prod.snd)).condKernel z A
        rw [← hz, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  obtain ⟨hInt₀, hInt₁⟩ := hjoining.2 _ _
    (isJoining_integrated_component_kernel F κ₀ h₀)
    (isJoining_integrated_component_kernel F κ₁ h₁) a ha ha' hsum
  apply Kernel.ae_eq_of_compProd_eq
  rw [← coordinateGraph_integrated_component_kernel F κ₀ (h₀.mono fun _ h ↦ h.2.1),
    ← coordinateGraph_integrated_component_kernel F κ₁ (h₁.mono fun _ h ↦ h.2.1),
    hInt₀, hInt₁]

end Mixing
