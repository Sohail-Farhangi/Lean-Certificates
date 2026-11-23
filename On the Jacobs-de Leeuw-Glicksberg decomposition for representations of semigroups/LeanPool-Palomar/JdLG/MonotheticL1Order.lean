/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MonotheticL1
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Restriction and pointwise norm on finite-measure L¹ -/

@[expose] public section

namespace JdLG

open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {X 𝕜 E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Multiplication by a measurable-set indicator on L¹. -/
noncomputable def lpOneRestrict {A : Set X} (hA : MeasurableSet A) :
    Lp E 1 μ →L[𝕜] Lp E 1 μ :=
  let hm (f : Lp E 1 μ) := (Lp.memLp f).indicator hA.nullMeasurableSet
  LinearMap.mkContinuous
    { toFun := fun f ↦ (hm f).toLp (A.indicator (⇑f))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(hm (f + g)).coeFn_toLp, (hm f).coeFn_toLp, (hm g).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add ((hm f).toLp _) ((hm g).toLp _)] with x ha hf hg hfg hs
        change (f + g) x = f x + g x at hfg
        change _ = (hm f).toLp _ x + (hm g).toLp _ x at hs
        rw [ha, hs, hf, hg]
        by_cases hx : x ∈ A
        · simp only [indicator_of_mem hx]
          exact hfg
        · simp [hx]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(hm (c • f)).coeFn_toLp, (hm f).coeFn_toLp,
          Lp.coeFn_smul c f, Lp.coeFn_smul c ((hm f).toLp _)] with x ha hf hcf hs
        simp only [RingHom.id_apply]
        change (c • f) x = c • f x at hcf
        change _ = c • (hm f).toLp _ x at hs
        rw [ha, hs, hf]
        by_cases hx : x ∈ A <;> simp [hx, hcf] }
    1 (fun f ↦ by
      rw [one_mul]
      change ‖(hm f).toLp _‖ ≤ ‖f‖
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(hm f).coeFn_toLp] with x hx
      rw [hx]
      by_cases h : x ∈ A <;> simp [h])

theorem lpOneRestrict_ae {A : Set X} (hA : MeasurableSet A) (f : Lp E 1 μ) :
    ⇑(lpOneRestrict (𝕜 := 𝕜) hA f) =ᵐ[μ] A.indicator (⇑f) :=
  ((Lp.memLp f).indicator hA.nullMeasurableSet).coeFn_toLp

theorem norm_lpOneRestrict_le {A : Set X} (hA : MeasurableSet A) (f : Lp E 1 μ) :
    ‖lpOneRestrict (𝕜 := 𝕜) hA f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lpOneRestrict_ae (𝕜 := 𝕜) hA f] with x hx
  rw [hx]
  by_cases h : x ∈ A <;> simp [h]

theorem lpOneRestrict_add_compl {A : Set X} (hA : MeasurableSet A) (f : Lp E 1 μ) :
    lpOneRestrict (𝕜 := 𝕜) hA f + lpOneRestrict (𝕜 := 𝕜) hA.compl f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (lpOneRestrict (𝕜 := 𝕜) hA f)
    (lpOneRestrict (𝕜 := 𝕜) hA.compl f), lpOneRestrict_ae (𝕜 := 𝕜) hA f,
    lpOneRestrict_ae (𝕜 := 𝕜) hA.compl f] with x hs ha hc
  change _ = lpOneRestrict (𝕜 := 𝕜) hA f x + lpOneRestrict (𝕜 := 𝕜) hA.compl f x at hs
  rw [hs, ha, hc]
  by_cases hx : x ∈ A <;> simp [hx]

/-- The pointwise norm of a vector-valued L¹ function, viewed in real L¹. -/
noncomputable def lpOneModulus (f : Lp E 1 μ) : Lp ℝ 1 μ :=
  (Lp.memLp f).norm.toLp (fun x ↦ ‖f x‖)

theorem lpOneModulus_ae (f : Lp E 1 μ) :
    ⇑(lpOneModulus f) =ᵐ[μ] fun x ↦ ‖f x‖ :=
  (Lp.memLp f).norm.coeFn_toLp

theorem lpOneModulus_nonneg (f : Lp E 1 μ) : 0 ≤ lpOneModulus f := by
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [lpOneModulus_ae f] with x hx
  exact hx ▸ norm_nonneg _

theorem lpOne_norm_eq_integral_norm (f : Lp E 1 μ) : ‖f‖ = ∫ x, ‖f x‖ ∂μ := by
  rw [L1.norm_def, integral_norm_eq_lintegral_eNorm (Lp.aestronglyMeasurable f)]

/-- The L¹ mass of a fixed function on an eventually vanishing sequence of
measurable sets tends to zero. -/
theorem tendsto_norm_lpOneRestrict_zero (f : Lp E 1 μ) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n))
    (hvanish : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ A n) :
    Tendsto (fun n ↦ ‖lpOneRestrict (𝕜 := 𝕜) (hA n) f‖) atTop (𝓝 0) := by
  have hDCT := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ↦ (A n).indicator (fun x ↦ ‖f x‖)) (f := fun _ ↦ 0)
    (fun x ↦ ‖f x‖)
    (fun n ↦ (Lp.aestronglyMeasurable f).norm.indicator (hA n))
    ((memLp_one_iff_integrable.mp (Lp.memLp f)).norm)
    (fun n ↦ Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ A n <;> simp [hx])
    (hvanish.mono fun x hx ↦
      tendsto_const_nhds.congr' (hx.mono fun n hn ↦ (indicator_of_notMem hn _).symm))
  have heq (n : ℕ) :
      ‖lpOneRestrict (𝕜 := 𝕜) (hA n) f‖ = ∫ x, (A n).indicator (fun x ↦ ‖f x‖) x ∂μ := by
    rw [lpOne_norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [lpOneRestrict_ae (𝕜 := 𝕜) (hA n) f] with x hx
    by_cases h : x ∈ A n <;> simp [hx, h]
  simpa only [heq, integral_zero] using hDCT

end JdLG

