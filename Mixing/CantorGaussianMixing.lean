/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorGaussianDensity
public import Mixing.CantorGaussianSpectrum

/-! # The Gaussian mixing witness in Example 5 -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate InnerProductSpace Topology

namespace Mixing

private theorem conj_gaussianCylChar {ι : Type*} [Fintype ι]
    (j : ι → ℤ) (a : ι → ℝ) (z : ℤ → ℝ) :
    conj (gaussianCylChar j a z) = gaussianCylChar j (fun i ↦ -a i) z := by
  simp only [gaussianCylChar, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, neg_mul, Finset.sum_neg_distrib, Complex.ofReal_neg, mul_neg]

private theorem gaussianTest_koopman_inner (a b : GaussianTest) (g : Multiplicative ℤ) :
    ⟪a.vector, example5GaussianSystem.koopmanRep g b.vector⟫_ℂ =
      ∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x *
        gaussianCylChar b.times b.frequencies (example5GaussianSystem.act g x)
        ∂example5GaussianMeasure := by
  let fa : Lp ℂ 2 example5GaussianSystem.measure := a.vector
  let fb : Lp ℂ 2 example5GaussianSystem.measure := b.vector
  change ⟪fa, example5GaussianSystem.koopmanRep g fb⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have ha : fa =ᵐ[example5GaussianSystem.measure] a.observable :=
    a.observable.coe_l2 example5GaussianMeasure
  have hb := (Lp.coeFn_compMeasurePreserving fb (example5GaussianSystem.preserves g)).trans
    ((example5GaussianSystem.preserves g).quasiMeasurePreserving.ae_eq_comp
      (b.observable.coe_l2 example5GaussianMeasure))
  filter_upwards [ha, hb] with x hxa hxb
  change fa x = gaussianCylChar a.times a.frequencies x at hxa
  change example5GaussianSystem.koopmanRep g fb x =
    gaussianCylChar b.times b.frequencies (example5GaussianSystem.act g x) at hxb
  rw [hxa, hxb, RCLike.inner_apply', conj_gaussianCylChar]

private theorem gaussianTest_correlation_limit (a b : GaussianTest)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    Tendsto (fun g ↦ ⟪a.vector, example5GaussianSystem.koopmanRep g b.vector⟫_ℂ)
      (p : Filter (Multiplicative ℤ))
      (𝓝 (star (∫ x, a.vector x ∂example5GaussianMeasure) *
        ∫ x, b.vector x ∂example5GaussianMeasure)) := by
  simp_rw [gaussianTest_koopman_inner]
  have ha : (∫ x, a.vector x ∂example5GaussianMeasure) =
      ∫ x, gaussianCylChar a.times a.frequencies x ∂example5GaussianMeasure :=
    integral_congr_ae (a.observable.coe_l2 _)
  have hb : (∫ x, b.vector x ∂example5GaussianMeasure) =
      ∫ x, gaussianCylChar b.times b.frequencies x ∂example5GaussianMeasure :=
    integral_congr_ae (b.observable.coe_l2 _)
  rw [ha, hb, Complex.star_def, ← integral_conj]
  simp_rw [conj_gaussianCylChar]
  exact example5Gaussian_cylindrical_correlations a.times (fun i ↦ -a.frequencies i)
    b.times b.frequencies p hp hsupp

private theorem zero_of_dense_test_coefficients
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Set H) (hS : (Submodule.span ℂ S).topologicalClosure = ⊤)
    (D : H →L[ℂ] H) (hD : ∀ x ∈ S, ∀ y ∈ S, ⟪x, D y⟫_ℂ = 0) : D = 0 := by
  have hker (L : H →L[ℂ] ℂ) (hL : S ⊆ L.ker) : ∀ x, L x = 0 := by
    have h := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hL) L.isClosed_ker
    rw [hS] at h
    exact fun x ↦ h (Submodule.mem_top (x := x))
  have hD' : ∀ y ∈ S, D y = 0 := by
    intro y hy
    have h := hker (innerSL ℂ (D y)) (by
      intro x hx
      change ⟪D y, x⟫_ℂ = 0
      rw [← inner_conj_symm, hD x hx y hy]
      exact map_zero _) (D y)
    exact inner_self_eq_zero.mp h
  apply ContinuousLinearMap.ext
  intro x
  rw [zero_apply]
  have hDker : S ⊆ D.ker := hD'
  have h := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hDker) D.isClosed_ker
  rw [hS] at h
  exact h (Submodule.mem_top (x := x))

/-- The stationary Gaussian system with the Cantor covariance is mixing along the
same ultrafilter along which the Cantor skew rotation is generated. -/
theorem example5Gaussian_isUMixing (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    example5GaussianSystem.IsUMixing {p} := by
  let S := example5GaussianSystem
  rw [S.isUMixing_iff_lp_correlations]
  intro q hq f k
  have hqp : q = p := Set.mem_singleton_iff.mp hq
  subst q
  let c := constantOne S.measure
  let Q := InnerProductSpace.rankOne ℂ c c
  let A := ultrafilterOperator S.koopmanRep p
  have hQ (f k : Lp ℂ 2 S.measure) :
      ⟪f, Q k⟫_ℂ = star (∫ x, f x ∂S.measure) * ∫ x, k x ∂S.measure := by
    simp only [Q, InnerProductSpace.rankOne_apply, inner_smul_right]
    rw [mul_comm, ← inner_conj_symm]
    exact congrArg₂ (· * ·) (congrArg star (inner_constantOne_left _ f))
      (inner_constantOne_left _ k)
  have hzero : A - Q = 0 := by
    apply zero_of_dense_test_coefficients _ example5Gaussian_testVectors_dense
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    let fa : Lp ℂ 2 S.measure := a.vector
    let fb : Lp ℂ 2 S.measure := b.vector
    change ⟪fa, (A - Q) fb⟫_ℂ = 0
    rw [sub_apply, inner_sub_right, hQ]
    apply sub_eq_zero.mpr
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff S.koopmanRep p fa fb)
      (gaussianTest_correlation_limit a b p hp hsupp)
  have hAQ : A = Q := sub_eq_zero.mp hzero
  have hl := tendsto_ultrafilterOperator_coeff S.koopmanRep p f k
  change Tendsto _ _ (𝓝 (⟪f, A k⟫_ℂ)) at hl
  rwa [hAQ, hQ] at hl

/-- Example 5 supplies a generated Cantor system and a mixing Gaussian system with
non-disjoint reduced Koopman spectra, for the same ultrafilter. -/
theorem example5_generated_and_mixing_spectral_overlap :
    ∃ p : Ultrafilter (Multiplicative ℤ),
      (p : Filter (Multiplicative ℤ)) ≤ cofinite ∧
      Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p ∧
      example5CantorSystem.IsUGenerated {p} ∧ example5GaussianSystem.IsUMixing {p} ∧
      ¬ SpectrallyDisjoint example5CantorSystem.koopmanZeroRep example5GaussianSystem.koopmanZeroRep := by
  obtain ⟨p, hp, hsupp, hGen⟩ := example5_exists_cantor_generating_ultrafilter
  exact ⟨p, hp, hsupp, hGen, example5Gaussian_isUMixing p hp hsupp,
    example5Gaussian_not_spectrallyDisjoint⟩

end Mixing
