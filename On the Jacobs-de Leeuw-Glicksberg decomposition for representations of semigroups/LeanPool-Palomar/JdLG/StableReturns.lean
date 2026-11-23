/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Stable
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Weak return sets of full invariant measure

The weak-neighborhood criterion of Theorem 4.2 on the compact semigroup host,
for an invariant Borel probability measure.
-/

@[expose] public section

open MeasureTheory Set

namespace JdLG

/-- A continuous function on a space with a full-support probability measure is constantly
`y` when the preimage of each open neighborhood of `y` has full measure. -/
theorem continuous_eq_const_of_measure_preimage_eq_one {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {μ : Measure X} [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {f : X → Y} {y : Y} (hf : Continuous f)
    (hfull : ∀ U : Set Y, IsOpen U → y ∈ U → μ (f ⁻¹' U) = 1) :
    ∀ x : X, f x = y := by
  intro x
  by_contra hxy
  obtain ⟨U, V, hU, hV, hyU, hxV, hUV⟩ := t2_separation (Ne.symm hxy)
  have hnull : μ (f ⁻¹' U)ᶜ = 0 := by
    rw [measure_compl (hU.preimage hf).measurableSet (measure_ne_top μ _),
      measure_univ, hfull U hU hyU, tsub_self]
  have hsubset : f ⁻¹' V ⊆ (f ⁻¹' U)ᶜ := fun _ hV' hU' =>
    Set.disjoint_left.mp hUV hU' hV'
  exact ((hV.preimage hf).measure_ne_zero μ ⟨x, hxV⟩) (measure_mono_null hsubset hnull)

variable {S G E : Type*} [Semigroup S] [TopologicalSpace S] [T2Space S]
  [MeasurableSpace S] [BorelSpace S] [Group G] [TopologicalSpace G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The compact-host form of the weak-neighborhood return criterion in Theorem 4.2(iii).
Almost weak stability is equivalent to assigning measure one to every weak return set. -/
theorem almostWeaklyStable_iff_weakReturnFullMeasure
    (i : G →ₙ* S) (hi : Continuous i) (hinjective : Function.Injective i)
    (hleft : ∀ s : S, Continuous (fun t => s * t)) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (ρ : S →ₙ* (E →L[ℂ] E)) (x : E)
    (hcontinuous : Continuous (fun s => toWeakSpace ℂ E (ρ s x)))
    (μ : Measure S) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] :
    (∃ s : S, ρ s x = 0) ↔ ∀ U : Set (WeakSpace ℂ E), IsOpen U → 0 ∈ U →
      μ ((fun s => toWeakSpace ℂ E (ρ s x)) ⁻¹' U) = 1 := by
  let φ : G → WeakSpace ℂ E := fun g => toWeakSpace ℂ E (ρ (i g) x)
  have hφ : Continuous φ := hcontinuous.comp hi
  obtain ⟨ν, hνprobability, _, hνsupport, hμ⟩ :=
    exists_fullSupportProbability_groupIdeal i hi hinjective hleft habsorb μ
  have hreturn (U : Set (WeakSpace ℂ E)) (hU : IsOpen U) :
      μ ((fun s => toWeakSpace ℂ E (ρ s x)) ⁻¹' U) = ν (φ ⁻¹' U) := by
    rw [hμ, Measure.map_apply hi.measurable (hU.preimage hcontinuous).measurableSet]
    rfl
  have hidentity := exists_annihilator_iff_group_identity i ρ habsorb x
  constructor
  · intro hx U hU hUzero
    have hpoint (g : G) : ρ (i g) x = 0 := by
      calc
        ρ (i g) x = ρ (i (g * 1)) x := by rw [mul_one]
        _ = ρ (i g) (ρ (i 1) x) := by simp only [map_mul]; rfl
        _ = 0 := by rw [hidentity.mp hx, map_zero]
    have hpreimage : φ ⁻¹' U = univ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      simpa only [φ, hpoint, map_zero] using hUzero
    rw [hreturn U hU, hpreimage, measure_univ]
  · intro h
    have hpoint := continuous_eq_const_of_measure_preimage_eq_one hφ
      (fun U hU hUzero => (hreturn U hU).symm.trans (h U hU hUzero)) (1 : G)
    apply hidentity.mpr
    apply (toWeakSpace ℂ E).injective
    simpa only [φ, map_zero] using hpoint

end JdLG
