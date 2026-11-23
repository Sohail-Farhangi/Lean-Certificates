/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MeasuredTransfer
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Limits of Følner test averages

Bounded continuous tests have limits along each ultrafilter refining the
averaging filter. These limits define a positive normalized functional.
Asymptotic left invariance makes it left invariant on the dense image,
and its restriction to the compact group ideal is normalized Haar.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped CompactlySupported Topology

namespace JdLG

section Limit

variable {T I : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
  [MeasurableSpace T] [BorelSpace T]
  (ν : I → Measure T) (hprob : ∀ n, IsProbabilityMeasure (ν n))

/-- The normalized average of a continuous test at one stage. -/
noncomputable def continuousTestIntegral (n : I) (f : C_c(T, ℝ)) : ℝ :=
  ∫ t, f t ∂ν n

include hprob

omit [T2Space T] [BorelSpace T] in
private theorem exists_ultrafilter_test_limit (u : Ultrafilter I) (f : C_c(T, ℝ)) :
    ∃ a : ℝ, Tendsto (fun n ↦ continuousTestIntegral ν n f) u (𝓝 a) := by
  let g := fun n ↦ continuousTestIntegral ν n f
  have hb (n : I) : ‖g n‖ ≤ ‖f.toContinuousMap‖ := by
    let : IsProbabilityMeasure (ν n) := hprob n
    have h := norm_integral_le_of_norm_le_const (μ := ν n) (f := fun t ↦ f t)
      (ae_of_all _ fun t ↦ f.toContinuousMap.norm_coe_le_norm t)
    simpa only [g, continuousTestIntegral, probReal_univ, mul_one] using h
  have hmem : Metric.closedBall (0 : ℝ) ‖f.toContinuousMap‖ ∈ u.map g := by
    change g ⁻¹' Metric.closedBall 0 ‖f.toContinuousMap‖ ∈ u
    have hset : g ⁻¹' Metric.closedBall 0 ‖f.toContinuousMap‖ = univ := by
      ext n
      simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, mem_univ, iff_true]
      exact hb n
    rw [hset]
    exact univ_mem
  obtain ⟨a, _, ha⟩ :=
    (isCompact_closedBall (0 : ℝ) ‖f.toContinuousMap‖).ultrafilter_le_nhds' (u.map g) hmem
  exact ⟨a, ha⟩

variable {S : Type*} [Semigroup S] [Semigroup T] [SeparatelyContinuousMul T]

/-- Convergence of the average of each continuous test on a compact host
with a group ideal, from the left translation condition on the dense
represented semigroup. This test condition follows from total variation
Følner convergence of the probabilities. -/
theorem tendsto_testIntegral_of_left_asymptoticInvariant
    (l : Filter I) (i : S →ₙ* T) (hi : DenseRange i)
    (K : GroupIdeal T) [CompactSpace K.carrier] [IsTopologicalGroup K.carrier]
    [MeasurableSpace K.carrier] [BorelSpace K.carrier]
    (hFolner : ∀ (s : S) (f : C_c(T, ℝ)),
      Tendsto (fun n ↦ continuousTestIntegral ν n
        (compactRealFunction (f ∘ (i s * ·)) (f.continuous.comp (continuous_const_mul (i s)))) -
        continuousTestIntegral ν n f) l (𝓝 0))
    (f : C_c(T, ℝ)) :
    Tendsto (fun n ↦ continuousTestIntegral ν n f) l
      (𝓝 (∫ g : K.carrier, f g ∂normalizedHaar K.carrier)) := by
  apply (tendsto_iff_ultrafilter _ _ _).2
  intro u hu
  let a := fun g ↦ (exists_ultrafilter_test_limit ν hprob u g).choose
  have ha (g : C_c(T, ℝ)) :
      Tendsto (fun n ↦ continuousTestIntegral ν n g) u (𝓝 (a g)) :=
    (exists_ultrafilter_test_limit ν hprob u g).choose_spec
  have hint (g : C_c(T, ℝ)) (n : I) : Integrable (fun t ↦ g t) (ν n) :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  let Φ : C_c(T, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := a
      map_add' := fun g h ↦ by
        apply tendsto_nhds_unique (ha (g + h))
        have he (n : I) : continuousTestIntegral ν n (g + h) =
            continuousTestIntegral ν n g + continuousTestIntegral ν n h :=
          integral_add (hint g n) (hint h n)
        simpa only [he] using (ha g).add (ha h)
      map_smul' := fun r g ↦ by
        change a (r • g) = r * a g
        apply tendsto_nhds_unique (ha (r • g))
        have he (n : I) : continuousTestIntegral ν n (r • g) =
            r * continuousTestIntegral ν n g :=
          integral_smul r (fun t ↦ g t)
        simpa only [he] using (ha g).const_mul r
      monotone' := fun g h hgh ↦
        le_of_tendsto_of_tendsto' (ha g) (ha h) fun n ↦
          integral_mono (hint g n) (hint h n) fun t ↦ hgh t }
  have hunit : Φ (compactRealFunction (fun _ ↦ 1) continuous_const) = 1 := by
    apply tendsto_nhds_unique (ha _)
    have he (n : I) : continuousTestIntegral ν n
        (compactRealFunction (fun _ ↦ 1) continuous_const) = 1 := by
      let : IsProbabilityMeasure (ν n) := hprob n
      unfold continuousTestIntegral
      exact integral_eq_const (ae_of_all _ fun _ ↦ rfl)
    simpa only [he] using (tendsto_const_nhds (x := (1 : ℝ)) (f := (u : Filter I)))
  have hL (t : T) : Continuous (t * ·) := continuous_const_mul t
  have hInv (s : S) (g : C_c(T, ℝ)) :
      Φ (compactRealFunction (g ∘ (i s * ·)) (g.continuous.comp (hL (i s)))) = Φ g := by
    let gs := compactRealFunction (g ∘ (i s * ·)) (g.continuous.comp (hL (i s)))
    have hv := tendsto_nhds_unique ((ha gs).sub (ha g)) ((hFolner s g).mono_left hu)
    exact sub_eq_zero.mp hv
  let m : LeftInvariantContinuousMean hL := ⟨Φ, hunit,
    MeasuredMean.continuousFunctional_translate_of_dense i Φ hunit (· * ·)
      (fun t ↦ continuous_mul_const t) hL hi hInv⟩
  let j : K.carrier →ₙ* T := ⟨Subtype.val, fun _ _ ↦ rfl⟩
  have habsorb (t : T) : ∃ g : K.carrier, j g = j 1 * t :=
    ⟨⟨K.identity * t, K.mul_mem_right K.identity_mem t⟩, rfl⟩
  have hvalue := m.apply_eq_groupIdealHaar j continuous_subtype_val Subtype.val_injective habsorb f
  exact hvalue ▸ ha f

end Limit

end JdLG
