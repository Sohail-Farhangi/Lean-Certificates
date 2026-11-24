/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.OperatorialRecurrenceGaussianKernel
public import SixProblems.PositiveDefinite
public import Mixing.System

@[expose] public section

open Function MeasureTheory ProbabilityTheory WithLp
open scoped Classical NNReal ProbabilityTheory

namespace SixProblems

noncomputable section

variable {G : Type*} [Group G]

theorem groupCovariance_posSemidef (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (I : Finset G) :
    (Matrix.of fun i j : I ↦ φ ((i : G)⁻¹ * (j : G))).PosSemidef := by
  simpa only [inv_inv] using hφ.reindex (fun i : I ↦ (i : G)⁻¹)

/-- The left shift on group-indexed real paths. -/
def gaussianShift (g : G) (x : G → ℝ) (i : G) : ℝ := x (g⁻¹ * i)

variable [Countable G]

/-- The real Gaussian path measure with covariance `φ (i⁻¹ * j)`. -/
def gaussianPathMeasure (φ : G → ℝ) (hφ : RealPositiveDefinite φ) : Measure (G → ℝ) :=
  Gaussian.pathLaw (fun i j : G ↦ φ (i⁻¹ * j)) (groupCovariance_posSemidef φ hφ)

instance gaussianPathMeasure_isProbability (φ : G → ℝ) (hφ : RealPositiveDefinite φ) :
    IsProbabilityMeasure (gaussianPathMeasure φ hφ) :=
  Gaussian.pathLaw_isProbability _ _

theorem gaussianShift_preserves (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (g : G) :
    MeasurePreserving (gaussianShift g) (gaussianPathMeasure φ hφ) (gaussianPathMeasure φ hφ) := by
  change MeasurePreserving (fun x : G → ℝ ↦ x ∘ (fun k : G ↦ g⁻¹ * k)) _ _
  apply Gaussian.pathLaw_invariant
  intro i j
  simp [mul_assoc]

/-- The measure-preserving Gaussian translation on the path space. -/
def gaussianPathSystem (φ : G → ℝ) (hφ : RealPositiveDefinite φ) : Mixing.System G (G → ℝ) where
  measure := gaussianPathMeasure φ hφ
  probability := inferInstance
  act := gaussianShift
  act_one := by
    funext x i
    simp [gaussianShift]
  act_mul g h := by
    funext x i
    simp [gaussianShift, mul_assoc]
  preserves := gaussianShift_preserves φ hφ

theorem gaussianPath_tuple (φ : G → ℝ) (hφ : RealPositiveDefinite φ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G) :
    MeasurePreserving (fun x : G → ℝ ↦ toLp 2 (fun i ↦ x (g i))) (gaussianPathMeasure φ hφ)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι)
        (Matrix.of fun i j ↦ φ ((g i)⁻¹ * g j))) :=
  Gaussian.pathLaw_tuple _ _ g

theorem gaussianPath_coordinate_law (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i : G) :
    MeasurePreserving (fun x : G → ℝ ↦ x i) (gaussianPathMeasure φ hφ)
      (gaussianReal 0 (φ 1).toNNReal) := by
  simpa only [gaussianPathMeasure, inv_mul_cancel] using
    Gaussian.pathLaw_coordinate (fun i j : G ↦ φ (i⁻¹ * j)) (groupCovariance_posSemidef φ hφ) i

theorem gaussianPath_coordinate_memLp (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i : G) :
    MemLp (fun x : G → ℝ ↦ x i) 2 (gaussianPathMeasure φ hφ) :=
  Gaussian.pathLaw_coordinate_memLp _ _ i

theorem gaussianPath_coordinate_mean (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i : G) :
    (∫ x, x i ∂(gaussianPathMeasure φ hφ)) = 0 :=
  Gaussian.pathLaw_coordinate_mean _ _ i

theorem gaussianPath_covariance (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i j : G) :
    (∫ x, x i * x j ∂(gaussianPathMeasure φ hφ)) = φ (i⁻¹ * j) :=
  Gaussian.pathLaw_covariance _ _ i j

/-- Lemma 5.1. Existence and uniqueness of the law are stated for all finite tuples,
    including those with repeated coordinates. -/
theorem lemma5_1 (φ : G → ℝ) (hφ : RealPositiveDefinite φ) :
    ∃ μ : Measure (G → ℝ), IsProbabilityMeasure μ ∧
      (∀ (n : ℕ) (g : Fin n → G), μ.map (fun x ↦ toLp 2 (fun i ↦ x (g i))) =
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
          (Matrix.of fun i j ↦ φ ((g i)⁻¹ * g j))) ∧
      (∀ ν : Measure (G → ℝ),
        (∀ (n : ℕ) (g : Fin n → G), ν.map (fun x ↦ toLp 2 (fun i ↦ x (g i))) =
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            (Matrix.of fun i j ↦ φ ((g i)⁻¹ * g j))) → ν = μ) ∧
      (∀ i j : G, (∫ x, x i * x j ∂μ) = φ (i⁻¹ * j)) ∧
      ∀ a : G, MeasurePreserving (gaussianShift a) μ μ := by
  refine ⟨gaussianPathMeasure φ hφ, inferInstance, fun _ g ↦ (gaussianPath_tuple φ hφ g).map_eq,
    ?_, gaussianPath_covariance φ hφ, gaussianShift_preserves φ hφ⟩
  intro ν hν
  apply Gaussian.pathLaw_unique
  intro I
  let e := Fintype.equivFin I
  let v : Fin (Fintype.card I) → G := fun i ↦ (e.symm i : G)
  let C : G → G → ℝ := fun i j ↦ φ (i⁻¹ * j)
  have hC := groupCovariance_posSemidef φ hφ
  have h := Gaussian.euclideanGaussian_reindex (hC I) (Gaussian.kernel_posSemidef_tuple C hC v)
    e (fun i j ↦ by simp [C, v])
  rw [← h.map_eq, ← hν _ v, Measure.map_map h.measurable (by fun_prop)]
  congr 1
  funext x
  apply PiLp.ext
  intro i
  change x i = x (v (e i))
  simp [v]

end

end SixProblems
