/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrenceGaussianCharacters
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Density of finite Gaussian characteristic tests -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate Topology ENNReal

namespace SixProblems.Gaussian

/-- A finite list of coordinate indices and real frequencies for a cylindrical character. -/
structure GaussianTest (G : Type*) where
  size : ℕ
  times : Fin size → G
  frequencies : Fin size → ℝ

variable {G : Type*}

/-- A cylindrical character belongs to L² for any finite path measure. -/
theorem GaussianTest.memLp (a : GaussianTest G) (μ : Measure (G → ℝ))
    [IsFiniteMeasure μ] : MemLp (gaussianCylChar a.times a.frequencies) 2 μ :=
  MemLp.of_bound (measurable_gaussianCylChar _ _).aestronglyMeasurable 1
    (.of_forall fun _ ↦ (norm_gaussianCylChar _ _ _).le)

/-- The L² vector associated to a finite Gaussian character. -/
noncomputable def GaussianTest.toVector (a : GaussianTest G) (μ : Measure (G → ℝ))
    [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  (a.memLp μ).toLp _

local notation "Paths" => ((G × ℕ) → Circle)

noncomputable local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private noncomputable def compactGaussianEncoding (x : G → ℝ) (i : G × ℕ) : Circle :=
  Circle.exp (x i.1 / ((i.2 : ℝ) + 1))

private theorem compactGaussianEncoding_continuous : Continuous (compactGaussianEncoding (G := G)) := by
  refine continuous_pi fun i ↦ ?_
  have hi : Continuous (fun x : G → ℝ ↦ x i.1) := continuous_apply i.1
  exact Circle.exp.continuous.comp (hi.div_const ((i.2 : ℝ) + 1))

private theorem compactGaussianEncoding_injective : Function.Injective
    (compactGaussianEncoding (G := G)) := by
  intro x y h
  funext i
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (|x i| + |y i|) / Real.pi)
  let d : ℝ := N + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hπ := Real.pi_pos
  have hb := (div_lt_iff₀ hπ).mp hN
  have hxd : |x i| ≤ (Real.pi / 2) * d := by
    dsimp only [d]
    nlinarith [abs_nonneg (y i)]
  have hyd : |y i| ≤ (Real.pi / 2) * d := by
    dsimp only [d]
    nlinarith [abs_nonneg (x i)]
  have hx : x i / d ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rcases abs_le.mp hxd with ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hd).mpr (by linarith only [hl]), (div_le_iff₀ hd).mpr hu⟩
  have hy : y i / d ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rcases abs_le.mp hyd with ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hd).mpr (by linarith only [hl]), (div_le_iff₀ hd).mpr hu⟩
  have he : Circle.exp (x i / d) = Circle.exp (y i / d) := congrFun h (i, N)
  have hEq := Circle.exp_injOn_Icc (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (by linarith) hx hy he
  exact mul_right_cancel₀ hd.ne' ((div_eq_div_iff hd.ne' hd.ne').mp hEq)

section Pullback

variable [Countable G]

private theorem compactGaussianEncoding_embedding : MeasurableEmbedding
    (compactGaussianEncoding (G := G)) :=
  compactGaussianEncoding_continuous.measurableEmbedding compactGaussianEncoding_injective

variable (μ : Measure (G → ℝ)) [IsProbabilityMeasure μ]

private noncomputable def compactGaussianMeasure : Measure Paths :=
  μ.map compactGaussianEncoding

private instance : IsProbabilityMeasure (compactGaussianMeasure μ) :=
  (Measure.isProbabilityMeasure_map_iff compactGaussianEncoding_embedding.measurable.aemeasurable).mpr
    inferInstance

omit [IsProbabilityMeasure μ] in
private theorem compactGaussianEncoding_preserving :
    MeasurePreserving compactGaussianEncoding μ (compactGaussianMeasure μ) :=
  ⟨compactGaussianEncoding_embedding.measurable, rfl⟩

omit [IsProbabilityMeasure μ] in
private theorem compactGaussianRecovery_preserving :
    MeasurePreserving compactGaussianEncoding_embedding.invFun (compactGaussianMeasure μ)
      μ := by
  refine ⟨compactGaussianEncoding_embedding.measurable_invFun, ?_⟩
  rw [compactGaussianMeasure, Measure.map_map compactGaussianEncoding_embedding.measurable_invFun
    compactGaussianEncoding_embedding.measurable,
    compactGaussianEncoding_embedding.leftInverse_invFun.comp_eq_id, Measure.map_id]

private noncomputable def compactGaussianPullback :
    Lp ℂ 2 (compactGaussianMeasure μ) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (compactGaussianEncoding_preserving μ)

omit [IsProbabilityMeasure μ] in
private theorem compactGaussianPullback_surjective : Function.Surjective (compactGaussianPullback μ) := by
  intro f
  refine ⟨Lp.compMeasurePreserving _ (compactGaussianRecovery_preserving μ) f, ?_⟩
  change Lp.compMeasurePreserving _ (compactGaussianEncoding_preserving μ)
    (Lp.compMeasurePreserving _ (compactGaussianRecovery_preserving μ) f) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h (x : G → ℝ) : (compactGaussianEncoding_embedding.invFun ∘ compactGaussianEncoding) x = x :=
    compactGaussianEncoding_embedding.leftInverse_invFun x
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving f
    ((compactGaussianRecovery_preserving μ).comp (compactGaussianEncoding_preserving μ))).trans
      (.of_forall fun x ↦ congrArg f (h x))

end Pullback

local notation "Letter" => ((G × ℕ) × ℤ)

private noncomputable def compactCoordinatePower (a : Letter) : C(Paths, ℂ) where
  toFun x := (x a.1 ^ a.2 : Circle)
  continuous_toFun := by fun_prop

private noncomputable def compactGaussianWord (w : List Letter) : C(Paths, ℂ) :=
  (w.map compactCoordinatePower).prod

private theorem compactGaussianWord_append (u v : List Letter) :
    compactGaussianWord (u ++ v) = compactGaussianWord u * compactGaussianWord v := by
  simp [compactGaussianWord, List.prod_append]

private def flipLetter (a : Letter) : Letter := (a.1, -a.2)

private theorem compactCoordinatePower_star (a : Letter) :
    star (compactCoordinatePower a) = compactCoordinatePower (flipLetter a) := by
  ext z
  change star ((z a.1 ^ a.2 : Circle) : ℂ) = ((z a.1 ^ (-a.2) : Circle) : ℂ)
  rw [zpow_neg, Circle.coe_inv_eq_conj, starRingEnd_apply]

private theorem compactGaussianWord_star (w : List Letter) :
    star (compactGaussianWord w) = compactGaussianWord (w.map flipLetter) := by
  induction w with
  | nil => simp [compactGaussianWord]
  | cons a w ih =>
    change star (compactCoordinatePower a * compactGaussianWord w) =
      compactCoordinatePower (flipLetter a) * compactGaussianWord (w.map flipLetter)
    rw [star_mul, compactCoordinatePower_star, ih, mul_comm]

private noncomputable def compactGaussianAlgebra : StarSubalgebra ℂ C(Paths, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range compactGaussianWord)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range compactGaussianWord) ≤
      star (Algebra.adjoin ℂ (Set.range compactGaussianWord))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨w, rfl⟩
    exact Algebra.subset_adjoin ⟨w.map flipLetter, (compactGaussianWord_star w).symm⟩

private theorem compactGaussianAlgebra_separates :
    (compactGaussianAlgebra (G := G)).SeparatesPoints := by
  intro x y h
  obtain ⟨i, hi⟩ := not_forall.mp (fun he ↦ h (funext he))
  refine ⟨_, ⟨compactGaussianWord [(i, 1)], Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
  change ((x i ^ (1 : ℤ) : Circle) : ℂ) * 1 ≠ ((y i ^ (1 : ℤ) : Circle) : ℂ) * 1
  simp only [zpow_one, mul_one]
  exact fun he ↦ hi (Subtype.ext he)

private theorem compactGaussianWords_span :
    (Submodule.span ℂ (Set.range (compactGaussianWord (G := G)))).topologicalClosure = ⊤ := by
  have hs : (compactGaussianAlgebra (G := G)).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range compactGaussianWord) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans (fun _ hx ↦ ?_) Submodule.subset_span
    refine Submonoid.closure_induction (fun _ h ↦ h) ⟨[], rfl⟩ ?_ hx
    rintro _ _ _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u ++ v, compactGaussianWord_append u v⟩
  rw [← hs]
  exact congrArg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      compactGaussianAlgebra_separates)

private noncomputable def wordTest (w : List Letter) : GaussianTest G where
  size := w.length
  times i := (w.get i).1.1
  frequencies i := ((w.get i).2 : ℝ) / (((w.get i).1.2 : ℝ) + 1)

private theorem compactGaussianWord_encode (w : List Letter) (x : G → ℝ) :
    compactGaussianWord w (compactGaussianEncoding x) =
      gaussianCylChar (wordTest w).times (wordTest w).frequencies x := by
  have hget : w.map compactCoordinatePower = List.ofFn (fun i ↦ compactCoordinatePower (w.get i)) := by
    change w.map compactCoordinatePower = List.ofFn (compactCoordinatePower ∘ w.get)
    rw [← List.map_ofFn, List.ofFn_get]
  rw [compactGaussianWord, hget, List.prod_ofFn]
  simp only [ContinuousMap.prod_apply, compactCoordinatePower, ContinuousMap.coe_mk,
    compactGaussianEncoding, Circle.coe_zpow, Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_sum]
  unfold gaussianCylChar
  congr 1
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold wordTest
  push_cast
  ring

variable [Countable G] (μ : Measure (G → ℝ)) [IsProbabilityMeasure μ]

/-- The Gaussian cylindrical test vectors span a dense subspace of the full complex L² space. -/
theorem gaussianTestVectors_dense :
    (Submodule.span ℂ (Set.range (fun a : GaussianTest G => a.toVector μ))).topologicalClosure = ⊤ := by
  let L := ContinuousMap.toLp (E := ℂ) 2 (compactGaussianMeasure μ) ℂ
  have hLdense : DenseRange L :=
    ContinuousMap.toLp_denseRange ℂ (compactGaussianMeasure μ) ℂ (by norm_num : (2 : ENNReal) ≠ ⊤)
  have ht := hLdense.topologicalClosure_map_submodule compactGaussianWords_span
  have hPullback : DenseRange (compactGaussianPullback μ).toContinuousLinearMap :=
    (compactGaussianPullback_surjective μ).denseRange
  have hu := hPullback.topologicalClosure_map_submodule ht
  have hIncluded : ((Submodule.span ℂ (Set.range compactGaussianWord)).map L.toLinearMap).map
      (compactGaussianPullback μ).toLinearMap ≤ Submodule.span ℂ (Set.range (fun a : GaussianTest G => a.toVector μ)) := by
    rw [Submodule.map_span, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨_, ⟨w, rfl⟩, rfl⟩, rfl⟩
    refine ⟨wordTest w, ?_⟩
    apply Lp.ext
    refine ((wordTest w).memLp μ).coeFn_toLp.trans ?_
    have hc := (Lp.coeFn_compMeasurePreserving (L (compactGaussianWord w))
      (compactGaussianEncoding_preserving μ)).trans
      ((compactGaussianEncoding_preserving μ).quasiMeasurePreserving.ae_eq_comp
        (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (compactGaussianMeasure μ) (compactGaussianWord w)))
    have hw : gaussianCylChar (wordTest w).times (wordTest w).frequencies =ᵐ[μ]
        (fun x ↦ compactGaussianWord w (compactGaussianEncoding x)) :=
      .of_forall fun x ↦ (compactGaussianWord_encode w x).symm
    exact hw.trans hc.symm
  have hle := Submodule.topologicalClosure_mono hIncluded
  change ((Submodule.span ℂ (Set.range compactGaussianWord)).map L.toLinearMap
    |>.map (compactGaussianPullback μ).toLinearMap).topologicalClosure = ⊤ at hu
  rw [hu] at hle
  exact le_antisymm le_top hle

end SixProblems.Gaussian
