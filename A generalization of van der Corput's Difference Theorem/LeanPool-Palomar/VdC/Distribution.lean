/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Orthogonal
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Distribution -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped BigOperators ComplexConjugate Topology

namespace VdC

section CompactSpace

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

noncomputable def testMean (μ : Measure X) (f : C(X, ℂ)) : ℂ := ∫ x, f x ∂μ

def Equidistributed (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f))

def OrthogonalDistribution (μ : Measure X) (x : ℕ → X) : Prop :=
  ∀ f : C(X, ℂ), testMean μ f = 0 → NearlyOrthogonal (fun n => f (x n))

omit [MeasurableSpace X] [BorelSpace X] in
theorem bounded_test (f : C(X, ℂ)) (x : ℕ → X) : BoundedSeq (fun n => f (x n)) :=
  ⟨‖f‖, norm_nonneg _, fun n => ContinuousMap.norm_coe_le_norm f (x n)⟩

theorem test_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Eventually.of_forall fun a => ContinuousMap.norm_coe_le_norm f a)

theorem testMean_add (μ : Measure X) [IsFiniteMeasure μ] (f g : C(X, ℂ)) :
    testMean μ (f + g) = testMean μ f + testMean μ g :=
  integral_add (test_integrable μ f) (test_integrable μ g)

theorem testMean_sub (μ : Measure X) [IsFiniteMeasure μ] (f g : C(X, ℂ)) :
    testMean μ (f - g) = testMean μ f - testMean μ g :=
  integral_sub (test_integrable μ f) (test_integrable μ g)

omit [BorelSpace X] [CompactSpace X] in
theorem testMean_smul (μ : Measure X) (c : ℂ) (f : C(X, ℂ)) :
    testMean μ (c • f) = c * testMean μ f := integral_const_mul _ _

omit [BorelSpace X] [CompactSpace X] in
theorem testMean_const (μ : Measure X) [IsProbabilityMeasure μ] (c : ℂ) :
    testMean μ (ContinuousMap.const X c) = c := by simp [testMean]

omit [BorelSpace X] [CompactSpace X] in
theorem testMean_star (μ : Measure X) (f : C(X, ℂ)) :
    testMean μ (star f) = star (testMean μ f) := integral_conj

private noncomputable def testError (μ : Measure X) (x : ℕ → X) (f : C(X, ℂ)) (N : ℕ) :=
  cesaro (fun n => f (x n)) N - testMean μ f

private theorem norm_error_difference (μ : Measure X) [IsProbabilityMeasure μ] (x : ℕ → X)
    (f g : C(X, ℂ)) (N : ℕ) : ‖testError μ x f N - testError μ x g N‖ ≤ 2 * ‖f - g‖ := by
  have hf : ‖cesaro (fun n => (f - g) (x n)) N‖ ≤ ‖f - g‖ :=
    norm_cesaro_le _ (norm_nonneg _) (fun n => ContinuousMap.norm_coe_le_norm _ _) _
  have hg : ‖testMean μ (f - g)‖ ≤ ‖f - g‖ :=
    by simpa [testMean] using
      (norm_integral_le_of_norm_le_const (μ := μ)
        (Eventually.of_forall fun a => ContinuousMap.norm_coe_le_norm (f - g) a))
  have he : testError μ x f N - testError μ x g N = testError μ x (f - g) N := by
    unfold testError
    rw [testMean_sub]
    change _ = cesaro (fun n => f (x n) - g (x n)) N - _
    rw [cesaro_sub]
    abel
  rw [he, testError]
  linarith only [(norm_sub_le _ _).trans (add_le_add hf hg)]

omit [BorelSpace X] [CompactSpace X] in
private theorem tendency_testError_iff (μ : Measure X) (x : ℕ → X) (f : C(X, ℂ)) :
    Tendsto (testError μ x f) atTop (𝓝 0) ↔
    Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f)) := by
  constructor
  · intro h
    simpa [testError] using h.add (tendsto_const_nhds (x := testMean μ f))
  · intro h
    unfold testError
    simpa only [sub_self] using h.sub (tendsto_const_nhds (x := testMean μ f))

noncomputable def convergenceTests (μ : Measure X) [IsProbabilityMeasure μ] (x : ℕ → X) :
    Submodule ℂ C(X, ℂ) where
  carrier := {f | Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f))}
  zero_mem' := by
    change Tendsto (cesaro fun _ => 0) atTop (𝓝 (testMean μ (0 : C(X, ℂ))))
    simpa only [testMean, ContinuousMap.zero_apply, integral_zero] using cesaro_tendsto_const 0
  add_mem' := by
    intro f g hf hg
    change Tendsto (fun N => cesaro (fun n => f (x n) + g (x n)) N) atTop (𝓝 (testMean μ (f + g)))
    simp only [cesaro_add, testMean_add]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change Tendsto (fun N => cesaro (fun n => c * f (x n)) N) atTop (𝓝 (testMean μ (c • f)))
    simp only [cesaro_mul_const, testMean_smul]
    exact tendsto_const_nhds.mul hf

theorem equidistributed_of_dense_tests (μ : Measure X) [IsProbabilityMeasure μ] (x : ℕ → X)
    (s : Set C(X, ℂ)) (hd : (Submodule.span ℂ s).topologicalClosure = ⊤)
    (hs : ∀ f ∈ s, Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean μ f))) :
    Equidistributed μ x := by
  intro f
  apply (tendency_testError_iff μ x f).1
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hf : f ∈ closure (↑(Submodule.span ℂ s) : Set C(X, ℂ)) := by
    change f ∈ (Submodule.span ℂ s).topologicalClosure
    rw [hd]
    trivial
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf (ε / 4) (by positivity)
  have hh : g ∈ convergenceTests μ x :=
    (Submodule.span_le.2 (fun u hu => hs u hu)) hg
  have ht := (Metric.tendsto_nhds.mp ((tendency_testError_iff μ x g).2 hh)) (ε / 2) (by positivity)
  filter_upwards [ht] with N hN
  rw [dist_zero_right] at hN ⊢
  rw [dist_eq_norm] at hdist
  have htri : ‖testError μ x f N‖ ≤ ‖testError μ x f N - testError μ x g N‖ + ‖testError μ x g N‖ := by
    simpa only [sub_add_cancel] using norm_add_le (testError μ x f N - testError μ x g N) (testError μ x g N)
  linarith only [hN, hdist, htri, norm_error_difference μ x f g N]

def productTest (f : C(X, ℂ)) (g : C(Y, ℂ)) : C(X × Y, ℂ) :=
  ⟨fun p => f p.1 * g p.2, (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] in
@[simp] theorem productTest_apply (f : C(X, ℂ)) (g : C(Y, ℂ)) (p : X × Y) :
    productTest f g p = f p.1 * g p.2 := rfl

private def productTests : Set C(X × Y, ℂ) := {u | ∃ f g, productTest f g = u}

private noncomputable def productAlgebra : StarSubalgebra ℂ C(X × Y, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (productTests (X := X) (Y := Y))
  star_mem' := by
    change Algebra.adjoin ℂ (productTests (X := X) (Y := Y)) ≤
      star (Algebra.adjoin ℂ (productTests (X := X) (Y := Y)))
    apply Algebra.adjoin_le
    rintro _ ⟨f, g, rfl⟩
    change star (productTest f g) ∈ Algebra.adjoin ℂ productTests
    apply Algebra.subset_adjoin
    exact ⟨star f, star g, by ext p; simp⟩

variable [T2Space X] [T2Space Y]

private theorem complex_test_separates {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    {a b : Z} (h : a ≠ b) : ∃ f : C(Z, ℂ), f a ≠ f b := by
  obtain ⟨f, ha, hb, _⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := a)) (isClosed_singleton (x := b))
    (Set.disjoint_singleton.2 h)
  refine ⟨⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩, ?_⟩
  change (f a : ℂ) ≠ (f b : ℂ)
  simp [ha (Set.mem_singleton a), hb (Set.mem_singleton b)]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
private theorem productTests_dense : (Submodule.span ℂ (productTests (X := X) (Y := Y))).topologicalClosure = ⊤ := by
  have hsep : (productAlgebra (X := X) (Y := Y)).SeparatesPoints := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    by_cases hac : a = c
    · have hbd : b ≠ d := by intro he; exact h (Prod.ext hac he)
      obtain ⟨g, hg⟩ := complex_test_separates hbd
      refine ⟨_, ⟨productTest 1 g, Algebra.subset_adjoin ⟨1, g, rfl⟩, rfl⟩, ?_⟩
      simpa using hg
    · obtain ⟨f, hf⟩ := complex_test_separates hac
      refine ⟨_, ⟨productTest f 1, Algebra.subset_adjoin ⟨f, 1, rfl⟩, rfl⟩, ?_⟩
      simpa using hf
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have had : (productAlgebra (X := X) (Y := Y)).toSubalgebra.toSubmodule = Submodule.span ℂ productTests := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans ?_ Submodule.subset_span
    intro x hx
    refine Submonoid.closure_induction (fun _ h => h) ⟨1, 1, ?_⟩ ?_ hx
    · ext p; simp
    · rintro _ _ - - ⟨f, g, rfl⟩ ⟨f', g', rfl⟩
      exact ⟨f * f', g * g', by ext p; simp; ring⟩
  rw [← had]
  exact congrArg (fun A : StarSubalgebra ℂ C(X × Y, ℂ) => A.toSubalgebra.toSubmodule) hd

theorem equidistributed_prod_iff [SecondCountableTopology X] [SecondCountableTopology Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : ℕ → X) (y : ℕ → Y) :
    Equidistributed (μ.prod ν) (fun n => (x n, y n)) ↔ ∀ (f : C(X, ℂ)) (g : C(Y, ℂ)),
      Tendsto (cesaro fun n => f (x n) * g (y n)) atTop (𝓝 (testMean μ f * testMean ν g)) := by
  have hp (f : C(X, ℂ)) (g : C(Y, ℂ)) :
      testMean (μ.prod ν) (productTest f g) = testMean μ f * testMean ν g := integral_prod_mul _ _
  constructor
  · intro h f g
    simpa only [hp, productTest_apply] using h (productTest f g)
  · intro h
    apply equidistributed_of_dense_tests _ _ productTests productTests_dense
    rintro _ ⟨f, g, rfl⟩
    simpa only [hp, productTest_apply] using h f g

end CompactSpace

end VdC
