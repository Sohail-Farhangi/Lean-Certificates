/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CorrespondenceInverse
public import SixProblems.CorrespondenceTiling
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

@[expose] public section
noncomputable section

namespace SixProblems

open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

variable {G K : Type} [DecidableEq G] [MetricSpace K] [CompactSpace K]

/-- Two configurations agreeing on `D` have the same value under this test. -/
def IsCylinderOn (D : Finset G) (f : C(G → K, ℝ)) : Prop :=
  ∀ x y, (∀ g ∈ D, x g = y g) → f x = f y

private def cylinderAlgebra : Subalgebra ℝ C(G → K, ℝ) where
  carrier := {f | ∃ D, IsCylinderOn D f}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A ∪ B, fun x y h ↦ ?_⟩
    change f x * g x = f y * g y
    rw [hA x y (fun a ha ↦ h a (Finset.mem_union_left _ ha)),
      hB x y (fun b hb ↦ h b (Finset.mem_union_right _ hb))]
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A ∪ B, fun x y h ↦ ?_⟩
    change f x + g x = f y + g y
    rw [hA x y (fun a ha ↦ h a (Finset.mem_union_left _ ha)),
      hB x y (fun b hb ↦ h b (Finset.mem_union_right _ hb))]
  algebraMap_mem' := fun _ ↦ ⟨∅, fun _ _ _ ↦ rfl⟩

private theorem cylinderAlgebra_dense :
    Dense (↑(cylinderAlgebra (G := G) (K := K)) : Set C(G → K, ℝ)) := by
  have hsep : (cylinderAlgebra : Subalgebra ℝ C(G → K, ℝ)).SeparatesPoints := by
    intro x y hxy
    have hex : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := hex
    let f : C(G → K, ℝ) := ⟨fun z ↦ dist (z i) (x i), (continuous_apply i).dist continuous_const⟩
    refine ⟨f, ⟨f, ⟨{i}, fun a b h ↦ ?_⟩, rfl⟩, ?_⟩
    · change dist (a i) (x i) = dist (b i) (x i)
      rw [h i (Finset.mem_singleton_self i)]
    · change dist (x i) (x i) ≠ dist (y i) (x i)
      rw [dist_self]
      exact (dist_ne_zero.mpr hi.symm).symm
  intro f
  exact ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints cylinderAlgebra hsep f

variable [Countable G]

/-- A countable family of continuous tests, each depending on finitely many
coordinates, is uniformly dense in the real continuous functions on the shift. -/
theorem exists_dense_cylinderTests : ∃ (f : ℕ → C(G → K, ℝ)) (D : ℕ → Finset G),
    DenseRange f ∧ ∀ i, IsCylinderOn (D i) (f i) := by
  obtain ⟨t, ht, htc, htd⟩ := (cylinderAlgebra_dense (G := G) (K := K)).exists_countable_dense_subset
  have : Countable t := htc.to_subtype
  have : Nonempty t := htd.nonempty.to_subtype
  obtain ⟨enum, hEnum⟩ := exists_surjective_nat t
  let f : ℕ → C(G → K, ℝ) := fun i ↦ (enum i).val
  have hf : ∀ i, ∃ D, IsCylinderOn D (f i) := fun i ↦ ht (enum i).property
  choose D hD using hf
  refine ⟨f, D, ?_, hD⟩
  have hr : Set.range f = t := by
    ext u
    refine ⟨?_, fun hu ↦ ?_⟩
    · rintro ⟨i, rfl⟩
      exact (enum i).property
    · obtain ⟨i, hi⟩ := hEnum ⟨u, hu⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  rw [DenseRange, hr]
  exact htd

variable [MeasurableSpace K] [BorelSpace K]

omit [DecidableEq G] in
private theorem continuous_testIntegral (ν : ProbabilityMeasure (G → K)) :
    Continuous (fun f : C(G → K, ℝ) ↦ ∫ z, f z ∂(ν : Measure (G → K))) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f h
  have hintegrable (u : C(G → K, ℝ)) : Integrable u (ν : Measure (G → K)) :=
    u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Real.dist_eq, ← integral_sub (hintegrable f) (hintegrable h), dist_eq_norm]
  simpa using norm_integral_le_of_norm_le_const (μ := (ν : Measure (G → K)))
    (C := ‖f - h‖) (Eventually.of_forall fun z ↦ ContinuousMap.norm_coe_le_norm (f - h) z)

variable [Group G] [Infinite G]

/-- Local finite models on congruent tiling cells. The boundary condition lets
the local tests be transferred to a single configuration across the cells. -/
def HasTiledCylinderApproximations (K : Type) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] {G : Type} [Group G] [DecidableEq G]
    (F : LeftFolnerSequence G) : Prop :=
  ∀ (ν : ProbabilityMeasure (G → K)) (f : ℕ → C(G → K, ℝ)) (D : ℕ → Finset G),
    (∀ a : G, (ν : Measure (G → K)).map (fun x j ↦ x (j * a)) = (ν : Measure (G → K))) →
    (∀ i, IsCylinderOn (D i) (f i)) →
    ∃ (P : ℕ → BoundedTilePartition G) (sample : ℕ → Finset G → G → K)
      (bad : ℕ → Set G) (δs : ℕ → ℝ),
      (∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g) ∧
      (∀ k g h, h ∈ (P k).cell g → (h ∈ bad k ↔ g ∈ bad k)) ∧
      (∀ k, 0 ≤ δs k) ∧ Summable δs ∧
      (∀ k, ∀ᶠ n in atTop, blockProportion (F.blocks n) (bad k) ≤ δs k) ∧
      (∀ k g i, i ≤ k → g ∉ bad k →
        ‖finiteAverage ((P k).cell g) (fun a ↦ f i (correspondenceShift a (sample k ((P k).cell g))) -
          ∫ z, f i z ∂(ν : Measure (G → K)))‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ k g i, i ≤ k → g ∉ bad k →
        ((leftBoundary (D i) ((P k).cell g)).card : ℝ) / ((P k).cell g).card ≤
          1 / ((k : ℝ) + 1))

omit [Countable G] [Group G] [Infinite G] [DecidableEq G] in
private theorem finiteAverage_sub_constant {A : Finset G} (hA : A.Nonempty) (f : G → ℝ) (c : ℝ) :
    finiteAverage A (fun g ↦ f g - c) = finiteAverage A f - c := by
  have hc : ((A.card : ℝ)) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  simp only [finiteAverage, smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Finite models on congruent tilings yield a generic configuration for every
invariant full-shift measure along the prescribed Følner sequence. -/
theorem hasFolnerGenericRealizations_of_tiledCylinderApproximations (F : LeftFolnerSequence G)
    (hTiles : HasTiledCylinderApproximations K F) : HasFolnerGenericRealizations F K := by
  intro ν hInvariant
  obtain ⟨f, D, hDense, hD⟩ := exists_dense_cylinderTests (G := G) (K := K)
  obtain ⟨P, sample, bad, δs, hP, hBad, hδs, hSum, hSparse, hTest, hSmall⟩ :=
    hTiles ν f D hInvariant hD
  let m (i : ℕ) := ∫ z, f i z ∂(ν : Measure (G → K))
  let C (i : ℕ) := ‖f i‖ + ‖m i‖
  let q (i : ℕ) (x : G → K) (a : G) := f i (correspondenceShift a x) - m i
  have hC (i : ℕ) : 0 ≤ C i := by dsimp [C]; positivity
  have hNorm (i : ℕ) (x : G → K) (a : G) : ‖q i x a‖ ≤ C i :=
    (norm_sub_le _ _).trans (add_le_add (ContinuousMap.norm_coe_le_norm (f i) _) (le_refl _))
  have hLocal (i : ℕ) (x y : G → K) (a : G) (h : ∀ g ∈ D i, x (g * a) = y (g * a)) :
      q i x a = q i y a := by
    change f i (fun g ↦ x (g * a)) - m i = f i (fun g ↦ y (g * a)) - m i
    rw [hD i _ _ fun g hg ↦ h g hg]
  obtain ⟨x, hx⟩ := exists_tendsto_finiteTimeTests_of_tiledApproximations F P hP bad hBad δs hδs hSum hSparse D q C
    hC hNorm hLocal sample hTest hSmall
  let v := correspondenceOrbitLaw F x
  have hTests (i : ℕ) : Tendsto
      (fun n ↦ ∫ z, f i z ∂(v n : Measure (G → K))) atTop (𝓝 (m i)) := by
    have h := (hx i).add_const (m i)
    rw [zero_add] at h
    refine h.congr (fun n ↦ ?_)
    change finiteAverage (F.blocks n) (fun a ↦ f i (correspondenceShift a x) - m i) + m i =
      ∫ z, f i z ∂(correspondenceOrbitLaw F x n : Measure (G → K))
    rw [finiteAverage_sub_constant (F.nonempty n), sub_add_cancel, correspondenceOrbitLaw,
      integral_finiteEmpiricalLaw]
    rfl
  refine ⟨x, ?_⟩
  change Tendsto v atTop (𝓝 ν)
  rw [tendsto_iff_ultrafilter]
  intro p hp
  let μ := (p.map v).lim
  have hμ : Tendsto v p (𝓝 μ) := (p.map v).le_nhds_lim
  have hAgree (i : ℕ) : (∫ z, f i z ∂(μ : Measure (G → K))) = m i :=
    tendsto_nhds_unique
      (((ProbabilityMeasure.continuous_integral_continuousMap (f i)).tendsto μ).comp hμ)
      ((hTests i).mono_left hp)
  have hClosed : IsClosed {u : C(G → K, ℝ) |
      (∫ z, u z ∂(μ : Measure (G → K))) = ∫ z, u z ∂(ν : Measure (G → K))} :=
    isClosed_eq (continuous_testIntegral μ) (continuous_testIntegral ν)
  have hEq : μ = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro u
    apply closure_minimal _ hClosed (hDense u.toContinuousMap)
    rintro v ⟨i, rfl⟩
    exact hAgree i
  exact hEq ▸ hμ

end SixProblems
