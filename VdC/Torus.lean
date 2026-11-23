/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.Distribution
public import VdC.Spectrum
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Torus -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev Torus (d : ℕ) := Fin d → UnitAddCircle

def torusHaar (d : ℕ) : Measure (Torus d) := Measure.pi fun _ => circleHaar

instance torusHaar_probability (d : ℕ) : IsProbabilityMeasure (torusHaar d) := by
  unfold torusHaar
  infer_instance

def torusCharacter {d : ℕ} (m : Fin d → ℤ) : C(Torus d, ℂ) :=
  ⟨fun x => ∏ i, fourier (m i) (x i), continuous_finsetProd _ fun i _ =>
    (fourier (m i)).continuous.comp (continuous_apply i)⟩

@[simp] theorem torusCharacter_apply {d : ℕ} (m : Fin d → ℤ) (x : Torus d) :
    torusCharacter m x = ∏ i, fourier (m i) (x i) := rfl

@[simp] theorem torusCharacter_zero (d : ℕ) : torusCharacter (0 : Fin d → ℤ) = 1 := by
  ext x
  simp

theorem torusCharacter_mul {d : ℕ} (m k : Fin d → ℤ) :
    torusCharacter (m + k) = torusCharacter m * torusCharacter k := by
  ext x
  simp only [torusCharacter_apply, Pi.add_apply, fourier_add, Finset.prod_mul_distrib, ContinuousMap.mul_apply]

theorem torusCharacter_neg {d : ℕ} (m : Fin d → ℤ) :
    torusCharacter (-m) = star (torusCharacter m) := by
  ext x
  simp only [torusCharacter_apply, Pi.neg_apply, fourier_neg, ContinuousMap.star_apply, Complex.star_def, map_prod]

theorem torusCharacter_norm {d : ℕ} (m : Fin d → ℤ) (x : Torus d) :
    ‖torusCharacter m x‖ = 1 := by
  simp [fourier_apply]

theorem torusCharacter_point_add {d : ℕ} (m : Fin d → ℤ) (x y : Torus d) :
    torusCharacter m (x + y) = torusCharacter m x * torusCharacter m y := by
  simp [fourier_apply, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem torusCharacter_point_sub {d : ℕ} (m : Fin d → ℤ) (x y : Torus d) :
    torusCharacter m (x - y) = torusCharacter m x * star (torusCharacter m y) := by
  rw [sub_eq_add_neg, torusCharacter_point_add]
  congr 1
  simp only [torusCharacter_apply, Pi.neg_apply, fourier_apply, zsmul_neg, fourier_neg',
    Complex.star_def, map_prod]

private def torusCharacterAlgebra (d : ℕ) : StarSubalgebra ℂ C(Torus d, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (torusCharacter (d := d)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (torusCharacter (d := d))) ≤ star (Algebra.adjoin ℂ _)
    apply Algebra.adjoin_le
    rintro _ ⟨m, rfl⟩
    exact Algebra.subset_adjoin ⟨-m, torusCharacter_neg m⟩

theorem torusCharacter_single {d : ℕ} (i : Fin d) (u : Torus d) :
    torusCharacter (Pi.single i (1 : ℤ)) u = fourier 1 (u i) := by
  classical
  rw [torusCharacter_apply, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem torusCharacters_dense (d : ℕ) :
    (Submodule.span ℂ (Set.range (torusCharacter (d := d)))).topologicalClosure = ⊤ := by
  have hsep : (torusCharacterAlgebra d).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by contrapose! hxy; exact funext hxy
    refine ⟨_, ⟨torusCharacter (Pi.single i 1), Algebra.subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
    change torusCharacter (Pi.single i 1) x ≠ torusCharacter (Pi.single i 1) y
    rw [torusCharacter_single, torusCharacter_single, fourier_one, fourier_one]
    exact fun h => hi (AddCircle.injective_toCircle one_ne_zero (Subtype.coe_injective h))
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have had : (torusCharacterAlgebra d).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (torusCharacter (d := d))) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans ?_ Submodule.subset_span
    intro u hu
    refine Submonoid.closure_induction (fun _ => id) ⟨0, torusCharacter_zero d⟩ ?_ hu
    rintro _ _ - - ⟨m, rfl⟩ ⟨k, rfl⟩
    exact ⟨m + k, torusCharacter_mul m k⟩
  rw [← had]
  exact congrArg (fun A : StarSubalgebra ℂ C(Torus d, ℂ) => A.toSubalgebra.toSubmodule) hd

theorem testMean_circle_character (m : ℤ) :
    testMean circleHaar (fourier (T := 1) m) = if m = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) m) 0
  simpa [testMean, circleHaar, fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

theorem testMean_torusCharacter {d : ℕ} (m : Fin d → ℤ) :
    testMean (torusHaar d) (torusCharacter m) = if m = 0 then 1 else 0 := by
  classical
  simp only [testMean, torusHaar, torusCharacter_apply, integral_fintype_prod_eq_prod]
  change (∏ i, testMean circleHaar (fourier (m i))) = _
  by_cases hm : m = 0
  · subst m
    simp [testMean_circle_character]
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by contrapose! hm; exact funext hm
    rw [ite_eq_right hm]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [testMean_circle_character, hi])

/-- Weyl's criterion on the d-dimensional torus. -/
theorem equidistributed_torus_iff {d : ℕ} (x : ℕ → Torus d) :
    Equidistributed (torusHaar d) x ↔
      ∀ m : Fin d → ℤ, m ≠ 0 → Tendsto (cesaro fun n => torusCharacter m (x n)) atTop (𝓝 0) := by
  constructor
  · intro h m hm
    simpa only [testMean_torusCharacter, ite_eq_right hm] using h (torusCharacter m)
  · intro h
    apply equidistributed_of_dense_tests _ _ _ (torusCharacters_dense d)
    rintro _ ⟨m, rfl⟩
    by_cases hm : m = 0
    · subst m
      rw [testMean_torusCharacter, ite_eq_left rfl, torusCharacter_zero]
      exact cesaro_tendsto_const 1
    · simpa only [testMean_torusCharacter, ite_eq_right hm] using h m hm

end
end VdC
