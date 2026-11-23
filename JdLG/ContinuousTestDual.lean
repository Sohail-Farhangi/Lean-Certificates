/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.SeparateAveraging
public import JdLG.StableMeans
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Weak continuity of compact separately continuous families

The pairing argument decomposes a real bounded functional on continuous
functions into the difference of positive functionals. Riesz representation
then turns weak continuity of a family of sections into separate averaging.
-/

@[expose] public section

open MeasureTheory Set
open scoped CompactlySupported Topology

namespace JdLG

section Dual

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

local notation "C₀" => C(K, ℝ)

private def pairing : C₀ × ℝ →ₗ[ℝ] C₀ × C₀ where
  toFun v := (v.1 + v.2 • 1, -v.1 + v.2 • 1)
  map_add' v w := by
    apply Prod.ext <;> ext t <;> simp <;> ring
  map_smul' a v := by
    apply Prod.ext <;> ext t <;> simp

omit [CompactSpace K] in
private theorem pairing_injective : Function.Injective (pairing (K := K)) := by
  intro v w h
  have h₁ (t : K) : v.1 t + v.2 = w.1 t + w.2 := by
    simpa [pairing] using congrArg (fun f : C₀ × C₀ ↦ f.1 t) h
  have h₂ (t : K) : -v.1 t + v.2 = -w.1 t + w.2 := by
    simpa [pairing] using congrArg (fun f : C₀ × C₀ ↦ f.2 t) h
  refine Prod.ext (ContinuousMap.ext fun t ↦ ?_) ?_
  · linarith [h₁ t, h₂ t]
  · obtain ⟨t⟩ := ‹Nonempty K›
    linarith [h₁ t, h₂ t]

private theorem norm_add_abs_le_pairing (v : C₀ × ℝ) :
    ‖v.1‖ + |v.2| ≤ ‖pairing v‖ := by
  have h₁ (t : K) : |v.1 t + v.2| ≤ ‖pairing v‖ := by
    have h := ((pairing v).1.norm_coe_le_norm t).trans (le_max_left ‖(pairing v).1‖ ‖(pairing v).2‖)
    simpa [pairing, Prod.norm_def, Real.norm_eq_abs] using h
  have h₂ (t : K) : |-v.1 t + v.2| ≤ ‖pairing v‖ := by
    have h := ((pairing v).2.norm_coe_le_norm t).trans
      (le_max_right ‖(pairing v).1‖ ‖(pairing v).2‖)
    simpa [pairing, Prod.norm_def, Real.norm_eq_abs] using h
  have hp (t : K) : |v.1 t| + |v.2| ≤ ‖pairing v‖ := by
    obtain ⟨h₁l, h₁u⟩ := abs_le.mp (h₁ t)
    obtain ⟨h₂l, h₂u⟩ := abs_le.mp (h₂ t)
    rcases le_total 0 (v.1 t) with hf | hf <;> rcases le_total 0 v.2 with hg | hg
    · rw [abs_of_nonneg hf, abs_of_nonneg hg]
      exact h₁u
    · rw [abs_of_nonneg hf, abs_of_nonpos hg]
      linarith
    · rw [abs_of_nonpos hf, abs_of_nonneg hg]
      exact h₂u
    · rw [abs_of_nonpos hf, abs_of_nonpos hg]
      linarith
  have hnonneg : 0 ≤ ‖pairing v‖ - |v.2| := by
    obtain ⟨t⟩ := ‹Nonempty K›
    linarith [hp t, abs_nonneg (v.1 t)]
  have hd := (ContinuousMap.norm_le _ hnonneg).2 fun t ↦ by
    rw [Real.norm_eq_abs]
    linarith [hp t]
  linarith

set_option maxHeartbeats 600000 in
-- Elaborating the operator norm on the Hahn–Banach extension exceeds the default budget.
/-- A real continuous dual functional on a compact space can be represented
as the difference of two positive functionals on continuous tests. -/
theorem exists_positive_sub_of_continuous_dual (Λ : StrongDual ℝ C₀) :
    ∃ Φ Ψ : C_c(K, ℝ) →ₚ[ℝ] ℝ, ∀ f, Λ f.toContinuousMap = Φ f - Ψ f := by
  let M := ‖Λ‖
  let j := LinearEquiv.ofInjective (pairing (K := K)) pairing_injective
  let eval : C₀ × ℝ →ₗ[ℝ] ℝ :=
    Λ.toLinearMap.comp (LinearMap.fst ℝ C₀ ℝ) +
      (LinearMap.snd ℝ C₀ ℝ).smulRight M
  let φ₀ := eval.comp j.symm.toLinearMap
  have hbound (v : LinearMap.range (pairing (K := K))) : ‖φ₀ v‖ ≤ M * ‖v‖ := by
    obtain ⟨u, rfl⟩ := j.surjective v
    change ‖eval (j.symm (j u))‖ ≤ M * ‖pairing u‖
    rw [j.symm_apply_apply]
    change ‖Λ u.1 + u.2 * M‖ ≤ M * ‖pairing u‖
    calc
      _ ≤ ‖Λ u.1‖ + ‖u.2 * M‖ := norm_add_le _ _
      _ ≤ M * ‖u.1‖ + (|u.2| * M) := by
        rw [norm_mul, Real.norm_eq_abs u.2, Real.norm_of_nonneg (norm_nonneg Λ)]
        exact add_le_add (Λ.le_opNorm u.1) (le_refl _)
      _ = M * (‖u.1‖ + |u.2|) := by ring
      _ ≤ M * ‖pairing u‖ := mul_le_mul_of_nonneg_left (norm_add_abs_le_pairing u) (norm_nonneg Λ)
  have hcont : Continuous (‖Λ‖₊ • normSeminorm ℝ (C₀ × C₀)) :=
    continuous_norm.const_smul ‖Λ‖₊
  obtain ⟨g, hg, hgn⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    (LinearMap.range (pairing (K := K))) φ₀ hcont hbound
  have hn : ‖g‖ ≤ M := g.opNorm_le_bound (norm_nonneg Λ) hgn
  have hpair (v : C₀ × ℝ) : g (pairing v) = Λ v.1 + v.2 * M := by
    have h := hg (j v)
    change g (pairing v) = eval (j.symm (j v)) at h
    rwa [j.symm_apply_apply] at h
  have hone : g (1, 1) = M := by
    have h := hpair (0, 1)
    simpa [pairing] using h
  have hpos (v : C₀ × C₀) (h₁ : 0 ≤ v.1) (h₂ : 0 ≤ v.2) : 0 ≤ g v := by
    let R := ‖v‖
    have h₁n (t : K) : ‖v.1 t‖ ≤ R := (v.1.norm_coe_le_norm t).trans (le_max_left _ _)
    have h₂n (t : K) : ‖v.2 t‖ ≤ R := (v.2.norm_coe_le_norm t).trans (le_max_right _ _)
    have hdiff : ‖R • ((1, 1) : C₀ × C₀) - v‖ ≤ R := by
      refine max_le ?_ ?_
      · refine (ContinuousMap.norm_le _ (norm_nonneg v)).2 fun t ↦ ?_
        change |(R * 1) - v.1 t| ≤ R
        rw [mul_one, abs_of_nonneg]
        · exact sub_le_self _ (h₁ t)
        · have hp : 0 ≤ v.1 t := h₁ t
          have ht : v.1 t ≤ R := by simpa only [Real.norm_of_nonneg hp] using h₁n t
          exact sub_nonneg.mpr ht
      · refine (ContinuousMap.norm_le _ (norm_nonneg v)).2 fun t ↦ ?_
        change |(R * 1) - v.2 t| ≤ R
        rw [mul_one, abs_of_nonneg]
        · exact sub_le_self _ (h₂ t)
        · have hp : 0 ≤ v.2 t := h₂ t
          have ht : v.2 t ≤ R := by simpa only [Real.norm_of_nonneg hp] using h₂n t
          exact sub_nonneg.mpr ht
    have hb := g.le_of_opNorm_le hn (R • ((1, 1) : C₀ × C₀) - v)
    have hupper : ‖g (R • ((1, 1) : C₀ × C₀) - v)‖ ≤ M * R :=
      hb.trans (mul_le_mul_of_nonneg_left hdiff (norm_nonneg Λ))
    rw [map_sub, map_smul, hone, smul_eq_mul, Real.norm_eq_abs] at hupper
    linarith [le_abs_self (R * M - g v)]
  let addL : C_c(K, ℝ) →ₗ[ℝ] C₀ × C₀ :=
    { toFun := fun f ↦ (f.toContinuousMap, 0)
      map_add' := fun _ _ ↦ Prod.ext rfl (zero_add 0).symm
      map_smul' := fun _ _ ↦ Prod.ext rfl (smul_zero _).symm }
  let addR : C_c(K, ℝ) →ₗ[ℝ] C₀ × C₀ :=
    { toFun := fun f ↦ (0, f.toContinuousMap)
      map_add' := fun _ _ ↦ Prod.ext (zero_add 0).symm rfl
      map_smul' := fun _ _ ↦ Prod.ext (smul_zero _).symm rfl }
  let Φ : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
    { __ := g.toLinearMap.comp addL
      monotone' := fun f k hfk ↦ by
        have h := hpos ((k - f).toContinuousMap, 0) (fun t ↦ sub_nonneg.mpr (hfk t)) le_rfl
        change 0 ≤ g (addL (k - f)) at h
        rw [map_sub, map_sub] at h
        exact sub_nonneg.mp h }
  let Ψ : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
    { __ := g.toLinearMap.comp addR
      monotone' := fun f k hfk ↦ by
        have h := hpos (0, (k - f).toContinuousMap) le_rfl (fun t ↦ sub_nonneg.mpr (hfk t))
        change 0 ≤ g (addR (k - f)) at h
        rw [map_sub, map_sub] at h
        exact sub_nonneg.mp h }
  refine ⟨Φ, Ψ, fun f ↦ ?_⟩
  have he : pairing ((f.toContinuousMap, 0) : C₀ × ℝ) = addL f - addR f := by
    apply Prod.ext <;> ext t <;> simp [pairing, addL, addR]
  have h := hpair (f.toContinuousMap, 0)
  rw [he, map_sub] at h
  change Λ f.toContinuousMap = g (addL f) - g (addR f)
  simpa using h.symm

end Dual

section WeakContinuity

variable {X K : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace K] [CompactSpace K] [Nonempty K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

/-- A pointwise-continuous family of continuous functions on a compact
space is weakly continuous when its parameter space is compact and the
functions have a common bound. -/
theorem continuous_dual_of_separatelyContinuous (F : X → C(K, ℝ))
    (hF : ∀ t : K, Continuous fun x ↦ F x t) (C : ℝ) (hC : ∀ x t, ‖F x t‖ ≤ C)
    (Λ : StrongDual ℝ C(K, ℝ)) : Continuous fun x ↦ Λ (F x) := by
  obtain ⟨Φ, Ψ, hΛ⟩ := exists_positive_sub_of_continuous_dual Λ
  have hpos (M : C_c(K, ℝ) →ₚ[ℝ] ℝ) :
      Continuous fun x ↦ M (compactRealFunction (F x) (F x).continuous) := by
    let μ := RealRMK.rieszMeasure M
    have h := continuous_integral_of_separatelyContinuous μ (fun x t ↦ F x t)
      hF (fun x ↦ (F x).continuous) C hC
    have he (x : X) : (∫ t, F x t ∂μ) = M (compactRealFunction (F x) (F x).continuous) :=
      RealRMK.integral_rieszMeasure M (compactRealFunction (F x) (F x).continuous)
    simpa only [he] using h
  have he (x : X) : Λ (F x) =
      Φ (compactRealFunction (F x) (F x).continuous) -
        Ψ (compactRealFunction (F x) (F x).continuous) :=
    hΛ (compactRealFunction (F x) (F x).continuous)
  exact ((hpos Φ).sub (hpos Ψ)).congr fun x ↦ (he x).symm

end WeakContinuity

end JdLG
