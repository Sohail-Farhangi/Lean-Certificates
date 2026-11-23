/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Distribution

/-! # Lag Pairs -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace VdC

/-- The two polarization identities are valid even when the lagged correlation
form fails to be Hermitian. -/
theorem corr_polarization (u v : ℕ → ℂ) (h N : ℕ) :
    let a n := u n + v n
    let b n := u n + Complex.I * v n
    corr u v h N = ((corr a a h N - corr u u h N - corr v v h N) +
      Complex.I * (corr b b h N - corr u u h N - corr v v h N)) / 2 := by
  have h₁ : ∀ n, (u (n + h) + v (n + h)) * star (u n + v n) =
      u (n + h) * star (u n) + v (n + h) * star (v n) +
        (u (n + h) * star (v n) + v (n + h) * star (u n)) := by
    intro n
    simp only [star_add]
    ring
  have h₂ : ∀ n, (u (n + h) + Complex.I * v (n + h)) * star (u n + Complex.I * v n) =
      u (n + h) * star (u n) + v (n + h) * star (v n) +
        ((-Complex.I) * (u (n + h) * star (v n)) + Complex.I * (v (n + h) * star (u n))) := by
    intro n
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I]
    linear_combination -(v (n + h) * conj (v n)) * Complex.I_sq
  dsimp only
  simp only [corr, h₁, h₂, cesaro_add, cesaro_mul_const]
  linear_combination (cesaro (fun n => u (n + h) * star (v n)) N -
    cesaro (fun n => v (n + h) * star (u n)) N) / 2 * Complex.I_sq

section CompactSpace

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def center (f : C(X, ℂ)) : C(X, ℂ) := f - ContinuousMap.const X (testMean μ f)

@[simp] theorem testMean_center (f : C(X, ℂ)) : testMean μ (center μ f) = 0 := by
  rw [center, testMean_sub, testMean_const, sub_self]

theorem equidistributed_of_centered_tests (x : ℕ → X)
    (h : ∀ f : C(X, ℂ), testMean μ f = 0 →
      Tendsto (cesaro fun n => f (x n)) atTop (𝓝 0)) : Equidistributed μ x := by
  intro f
  have hh := (h (center μ f) (testMean_center μ f)).add (cesaro_tendsto_const (testMean μ f))
  simp only [zero_add] at hh
  convert hh using 1
  ext1 N
  rw [← cesaro_add]
  congr 1
  ext1 n
  simp [center]

theorem OrthogonalDistribution.equidistributed {x : ℕ → X} (hx : OrthogonalDistribution μ x) :
    Equidistributed μ x :=
  equidistributed_of_centered_tests μ x fun f hf => (hx f hf).tendsto_cesaro_zero

theorem OrthogonalDistribution.mixed_corr_zero {x : ℕ → X} (hx : OrthogonalDistribution μ x)
    (f g : C(X, ℂ)) (hf : testMean μ f = 0) (hg : testMean μ g = 0) {h : ℕ} (hh : 0 < h) :
    Tendsto (corr (fun n => f (x n)) (fun n => g (x n)) h) atTop (𝓝 0) := by
  have hf' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test f x)).1 (hx f hf) h hh
  have hg' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test g x)).1 (hx g hg) h hh
  have h₁ : testMean μ (f + g) = 0 := by simp [testMean_add, hf, hg]
  have h₂ : testMean μ (f + Complex.I • g) = 0 := by simp [testMean_add, testMean_smul, hf, hg]
  have h₁' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test (f + g) x)).1 (hx _ h₁) h hh
  have h₂' := (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test (f + Complex.I • g) x)).1 (hx _ h₂) h hh
  have hl := (((h₁'.sub hf').sub hg').add
    (((h₂'.sub hf').sub hg').const_mul Complex.I)).div_const (2 : ℂ)
  simp only [sub_zero, mul_zero, add_zero, zero_div] at hl
  exact hl.congr fun N => (corr_polarization (fun n => f (x n)) (fun n => g (x n)) h N).symm

theorem product_means_of_centered_tests (ν : Measure X) [IsProbabilityMeasure ν]
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (σ : Measure Y) [IsProbabilityMeasure σ] (x : ℕ → X) (y : ℕ → Y)
    (hx : Equidistributed ν x) (hy : Equidistributed σ y)
    (h : ∀ (f : C(X, ℂ)) (g : C(Y, ℂ)), testMean ν f = 0 → testMean σ g = 0 →
      Tendsto (cesaro fun n => f (x n) * g (y n)) atTop (𝓝 0))
    (f : C(X, ℂ)) (g : C(Y, ℂ)) :
    Tendsto (cesaro fun n => f (x n) * g (y n)) atTop (𝓝 (testMean ν f * testMean σ g)) := by
  let a := testMean ν f
  let b := testMean σ g
  have h₀ := h (center ν f) (center σ g) (testMean_center ν f) (testMean_center σ g)
  have h₁ := (tendsto_const_nhds (x := b)).mul (hx (center ν f))
  have h₂ := (tendsto_const_nhds (x := a)).mul (hy (center σ g))
  have hsum := (((h₀.add h₁).add h₂).add (cesaro_tendsto_const (a * b)))
  simp only [testMean_center, mul_zero, add_zero, zero_add] at hsum
  refine hsum.congr fun N => ?_
  rw [← cesaro_mul_const, ← cesaro_mul_const, ← cesaro_add, ← cesaro_add, ← cesaro_add]
  congr 1
  ext1 n
  simp only [center, ContinuousMap.sub_apply, ContinuousMap.const_apply, a, b]
  ring

/-- CharacterizationOfOsequences, with an arbitrary compact probability space
in place of the cube and uniform distribution tested by continuous functions. -/
theorem orthogonalDistribution_iff_lag_pairs [T2Space X] [SecondCountableTopology X]
    (x : ℕ → X) : OrthogonalDistribution μ x ↔ ∀ h : ℕ, 0 < h →
      Equidistributed (μ.prod μ) (fun n => (x n, x (n + h))) := by
  constructor
  · intro hx h hh
    apply (equidistributed_prod_iff μ μ _ _).2
    have hs : Equidistributed μ (fun n => x (n + h)) := fun f =>
      tendsto_cesaro_shift (bounded_test f x) h strictMono_id (hx.equidistributed μ f)
    apply product_means_of_centered_tests μ μ x _ (hx.equidistributed μ) hs
    intro f g hf hg
    refine (hx.mixed_corr_zero μ g (star f) hg (by simp [testMean_star, hf]) hh).congr ?_
    intro N
    simp [corr, mul_comm]
  · intro hx f hf
    apply (nearlyOrthogonal_iff_corr_tendsto_zero (bounded_test f x)).2
    intro h hh
    have hl := (equidistributed_prod_iff μ μ _ _).1 (hx h hh) (star f) f
    have hl' : Tendsto (cesaro fun n => star (f (x n)) * f (x (n + h))) atTop (𝓝 0) := by
      simpa [testMean_star, hf] using hl
    exact hl'.congr fun N => by simp [corr, mul_comm]

end CompactSpace

end VdC
