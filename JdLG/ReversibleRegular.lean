/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleHaar
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Right translations on the Hilbert space of Haar square-integrable functions -/

@[expose] public section

open Filter MeasureTheory Set

namespace JdLG

section RegularAction

variable {G 𝕜 F : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The square-integrable functions with respect to normalized Haar measure. -/
noncomputable abbrev HaarL2 (G F : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F] :=
  Lp F 2 (normalizedHaar G)

/-- Right translation by one group element, as a linear isometry. -/
noncomputable def rightTranslationIsometry (g : G) :
    HaarL2 G F →ₗᵢ[𝕜] HaarL2 G F := by
  exact Lp.compMeasurePreservingₗᵢ 𝕜 (· * g) (measurePreserving_mul_right (normalizedHaar G) g)

private theorem rightTranslationIsometry_one (v : HaarL2 G F) :
    (rightTranslationIsometry (𝕜 := 𝕜) 1) v = v := by
  change Lp.compMeasurePreserving (· * (1 : G)) _ v = v
  apply Lp.ext
  simpa only [Function.comp_def, mul_one] using Lp.coeFn_compMeasurePreserving v
    (measurePreserving_mul_right (normalizedHaar G) (1 : G))

private theorem rightTranslationIsometry_mul (g h : G) (v : HaarL2 G F) :
    rightTranslationIsometry (𝕜 := 𝕜) (g * h) v =
      rightTranslationIsometry (𝕜 := 𝕜) g (rightTranslationIsometry (𝕜 := 𝕜) h v) := by
  let μ := normalizedHaar G
  change Lp.compMeasurePreserving (· * (g * h)) _ v =
    Lp.compMeasurePreserving (· * g) _ (Lp.compMeasurePreserving (· * h) _ v)
  simpa only [Function.comp_def, mul_assoc] using
    Lp.compMeasurePreserving_comp_apply v (measurePreserving_mul_right μ h)
      (measurePreserving_mul_right μ g)

/-- The right regular action by surjective linear isometries. -/
noncomputable def haarRightTranslation : G →* (HaarL2 G F ≃ₗᵢ[𝕜] HaarL2 G F) where
  toFun g := LinearIsometryEquiv.ofSurjective (rightTranslationIsometry g) fun v ↦
    ⟨rightTranslationIsometry (𝕜 := 𝕜) g⁻¹ v, by
      rw [← rightTranslationIsometry_mul, mul_inv_cancel, rightTranslationIsometry_one]⟩
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro v
    exact rightTranslationIsometry_one (𝕜 := 𝕜) v
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro v
    exact rightTranslationIsometry_mul (𝕜 := 𝕜) g h v

theorem haarRightTranslation_coeFn (g : G) (v : HaarL2 G F) :
    (haarRightTranslation (𝕜 := 𝕜) g v : G → F) =ᵐ[normalizedHaar G] fun t ↦ v (t * g) :=
  Lp.coeFn_compMeasurePreserving v (measurePreserving_mul_right (normalizedHaar G) g)

/-- Right translation of a continuous function, as a continuous function. -/
def rightTranslate (g : G) (f : C(G, F)) : C(G, F) :=
  ⟨fun t ↦ f (t * g), f.continuous.comp (continuous_mul_const g)⟩

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_rightTranslate (f : C(G, F)) : Continuous fun g ↦ rightTranslate g f := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_snd.mul continuous_fst)

/-- Every continuous function from a compact group is Haar square-integrable.
Compactness gives a separable image even when the codomain is nonseparable. -/
theorem memLp_continuous_normalizedHaar (f : C(G, F)) : MemLp f 2 (normalizedHaar G) :=
  MemLp.of_bound f.continuous.aestronglyMeasurable_of_compactSpace ‖f‖
    (Eventually.of_forall f.norm_coe_le_norm)

/-- The bounded linear inclusion of continuous functions into Haar L². -/
noncomputable def continuousToHaarL2 : C(G, F) →L[𝕜] HaarL2 G F :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (memLp_continuous_normalizedHaar f).toLp f
      map_add' := fun f g ↦ MemLp.toLp_add
        (memLp_continuous_normalizedHaar f) (memLp_continuous_normalizedHaar g)
      map_smul' := fun c f ↦ MemLp.toLp_const_smul c (memLp_continuous_normalizedHaar f) }
    1 (fun f ↦ by
      rw [one_mul]
      change ‖(memLp_continuous_normalizedHaar f).toLp f‖ ≤ ‖f‖
      rw [Lp.norm_toLp]
      have h : eLpNorm f 2 (normalizedHaar G) ≤ ENNReal.ofReal ‖f‖ := by
        simpa using eLpNorm_le_of_ae_bound (p := 2) (μ := normalizedHaar G)
          f.continuous.aestronglyMeasurable_of_compactSpace
          (Eventually.of_forall f.norm_coe_le_norm)
      simpa using ENNReal.toReal_mono ENNReal.ofReal_ne_top h)

/-- The Haar L² representative of a continuous function agrees a.e. with the function. -/
theorem continuousToHaarL2_coeFn (f : C(G, F)) :
    (continuousToHaarL2 (𝕜 := 𝕜) f : G → F) =ᵐ[normalizedHaar G] f :=
  (memLp_continuous_normalizedHaar f).coeFn_toLp

/-- The inclusion of continuous functions into Haar L² intertwines translations. -/
theorem haarRightTranslation_toLp (g : G) (f : C(G, F)) :
    haarRightTranslation (𝕜 := 𝕜) g (continuousToHaarL2 (𝕜 := 𝕜) f) =
      continuousToHaarL2 (𝕜 := 𝕜) (rightTranslate g f) := by
  apply Lp.ext
  have h := haarRightTranslation_coeFn (𝕜 := 𝕜) g
    (continuousToHaarL2 (𝕜 := 𝕜) f)
  refine h.trans ?_
  have hf := continuousToHaarL2_coeFn f (𝕜 := 𝕜)
  have hgg := measurePreserving_mul_right (normalizedHaar G) g
  exact (hgg.quasiMeasurePreserving.ae_eq_comp hf).trans
    (continuousToHaarL2_coeFn (rightTranslate g f) (𝕜 := 𝕜)).symm

end RegularAction

end JdLG
