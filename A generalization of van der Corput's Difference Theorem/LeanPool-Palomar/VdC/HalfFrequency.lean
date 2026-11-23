/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.CubeDifference
public import VdC.CompactClosure

/-! # Half Frequency -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace VdC

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def halfTorusMap {d : ℕ} (x : Cube d) : Torus d :=
  fun i => (((x i : ℝ) / (2 : ℝ) : ℝ) : UnitAddCircle)

theorem halfTorusMap_continuous (d : ℕ) : Continuous (halfTorusMap (d := d)) := by
  refine continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp ?_
  exact (continuous_subtype_val.comp (continuous_apply i)).div_const 2

private theorem halfTorusMap_injective (d : ℕ) : Function.Injective (halfTorusMap (d := d)) := by
  intro x y h
  funext i
  have hb (u : Cube d) : (u i : ℝ) / 2 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    have hu := (u i).property
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h' := congrArg (AddCircle.equivIco (1 : ℝ) (0 : ℝ)) (congrFun h i)
  change AddCircle.equivIco (1 : ℝ) (0 : ℝ) (((x i : ℝ) / 2 : ℝ) : UnitAddCircle) =
    AddCircle.equivIco (1 : ℝ) (0 : ℝ) (((y i : ℝ) / 2 : ℝ) : UnitAddCircle) at h'
  rw [AddCircle.equivIco_coe_eq (hb x), AddCircle.equivIco_coe_eq (hb y)] at h'
  apply Subtype.ext
  have h'' := congrArg Subtype.val h'
  dsimp at h''
  linarith

/-- The manuscript's half-frequency character exp(π i m·x) on the closed cube. -/
def halfFrequency {d : ℕ} (m : Fin d → ℤ) : C(Cube d, ℂ) :=
  (torusCharacter m).comp ⟨halfTorusMap, halfTorusMap_continuous d⟩

private theorem halfFrequency_mul {d : ℕ} (m k : Fin d → ℤ) :
    halfFrequency (m + k) = halfFrequency m * halfFrequency k := by
  ext x
  change torusCharacter (m + k) (halfTorusMap x) = torusCharacter m (halfTorusMap x) * torusCharacter k (halfTorusMap x)
  rw [torusCharacter_mul]
  rfl

private theorem halfFrequency_neg {d : ℕ} (m : Fin d → ℤ) :
    halfFrequency (-m) = star (halfFrequency m) := by
  ext x
  change torusCharacter (-m) (halfTorusMap x) = star (torusCharacter m (halfTorusMap x))
  rw [torusCharacter_neg]
  rfl

private theorem halfFrequency_zero (d : ℕ) : halfFrequency (0 : Fin d → ℤ) = 1 := by
  ext x
  simp [halfFrequency]

private def halfFrequencyAlgebra (d : ℕ) : StarSubalgebra ℂ C(Cube d, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (halfFrequency (d := d)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (halfFrequency (d := d))) ≤ star (Algebra.adjoin ℂ _)
    apply Algebra.adjoin_le
    rintro _ ⟨m, rfl⟩
    exact Algebra.subset_adjoin ⟨-m, halfFrequency_neg m⟩

theorem halfFrequencies_dense (d : ℕ) :
    (Submodule.span ℂ (Set.range (halfFrequency (d := d)))).topologicalClosure = ⊤ := by
  have hsep : (halfFrequencyAlgebra d).SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, halfTorusMap x i ≠ halfTorusMap y i := by
      contrapose! hxy
      exact halfTorusMap_injective d (funext hxy)
    refine ⟨_, ⟨halfFrequency (Pi.single i 1), Algebra.subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
    change torusCharacter (Pi.single i 1) (halfTorusMap x) ≠ torusCharacter (Pi.single i 1) (halfTorusMap y)
    rw [torusCharacter_single, torusCharacter_single, fourier_one, fourier_one]
    exact fun h => hi (AddCircle.injective_toCircle one_ne_zero (Subtype.coe_injective h))
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have had : (halfFrequencyAlgebra d).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (halfFrequency (d := d))) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans ?_ Submodule.subset_span
    intro u hu
    refine Submonoid.closure_induction (fun _ => id) ⟨0, halfFrequency_zero d⟩ ?_ hu
    rintro _ _ - - ⟨m, rfl⟩ ⟨k, rfl⟩
    exact ⟨m + k, halfFrequency_mul m k⟩
  rw [← had]
  exact congrArg (fun A : StarSubalgebra ℂ C(Cube d, ℂ) => A.toSubalgebra.toSubmodule) hd

theorem cube_property_of_halfFrequencies {d : ℕ} (x : ℕ → Cube d)
    (P : (ℕ → ℂ) → Prop) (hzero : P (fun _ => 0))
    (hadd : ∀ u v, P u → P v → P (fun n => u n + v n))
    (hsmul : ∀ u, ∀ c : ℂ, P u → P (fun n => c * u n))
    (hclosed : ∀ u, BoundedSeq u → (∀ ε : ℝ, 0 < ε → ∃ v, P v ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖u n - v n‖ ^ 2) N ≤ ε) → P u)
    (hchar : ∀ m : Fin d → ℤ, P (fun n => halfFrequency m (x n))) :
    ∀ f : C(Cube d, ℂ), P (fun n => f (x n)) := by
  intro f
  apply hclosed _ (bounded_test f x)
  intro ε hε
  let S := Submodule.span ℂ (Set.range (halfFrequency (d := d)))
  have hspan : ∀ g ∈ S, P (fun n => g (x n)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨m, rfl⟩ := hg
      exact hchar m
    | zero => exact hzero
    | add g k _ _ hg hk => exact hadd _ _ hg hk
    | smul c g _ hg => exact hsmul _ c hg
  have hf : f ∈ closure (S : Set C(Cube d, ℂ)) := by
    change f ∈ S.topologicalClosure
    rw [halfFrequencies_dense d]
    trivial
  obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.mp hf (Real.sqrt ε) (by positivity)
  rw [dist_eq_norm] at hd
  refine ⟨fun n => g (x n), hspan g hg, Eventually.of_forall fun N => ?_⟩
  have hsq (n : ℕ) : ‖f (x n) - g (x n)‖ ^ 2 ≤ ε := by
    rw [← Real.sq_sqrt hε.le]
    gcongr
    exact (ContinuousMap.norm_coe_le_norm (f - g) (x n)).trans hd.le
  by_cases hN : 0 < N
  · exact (realCesaro_mono hsq N).trans_eq (realCesaro_const_pos ε hN)
  · simp [realCesaro, Nat.eq_zero_of_not_pos hN, hε.le]

theorem cube_sSingular_iff_halfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    SpectrallySingularDistribution x ↔
      ∀ m : Fin d → ℤ, SpectrallySingular (fun n => halfFrequency m (x n)) := by
  constructor
  · exact fun h m => h (halfFrequency m)
  · exact cube_property_of_halfFrequencies x SpectrallySingular spectrallySingular_zero
      (fun _ _ hu hv => hu.add hv) (fun _ c hu => hu.const_mul c)
      (fun _ hu h => spectrallySingular_of_meanSquare_approximation hu h)

theorem cube_compact_iff_halfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    CompactDistribution x ↔ ∀ m : Fin d → ℤ, CompactSeq (fun n => halfFrequency m (x n)) := by
  constructor
  · exact fun h m => h (halfFrequency m)
  · exact cube_property_of_halfFrequencies x CompactSeq (compactAlong_const 0 strictMono_id)
      (fun _ _ hu hv => CompactAlong.add hu hv) (fun _ c hu => CompactAlong.const_mul hu c)
      (fun _ hu h => compactAlong_of_meanSquare_approximation hu strictMono_id h)

def centeredHalfFrequency {d : ℕ} (m : Fin d → ℤ) : C(Cube d, ℂ) :=
  center (cubeLebesgue d) (halfFrequency m)

theorem cube_sSingular_iff_centeredHalfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    SpectrallySingularDistribution x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      SpectrallySingular (fun n => centeredHalfFrequency m (x n)) := by
  constructor
  · exact fun hx m _ => hx (centeredHalfFrequency m)
  · intro h
    apply (cube_sSingular_iff_halfFrequencies x).2
    intro m
    by_cases hm : m = 0
    · subst m
      simpa only [halfFrequency_zero, ContinuousMap.one_apply] using spectrallySingular_one
    · simpa [centeredHalfFrequency, center] using
        (h m hm).add (spectrallySingular_const (testMean (cubeLebesgue d) (halfFrequency m)))

theorem cube_compact_iff_centeredHalfFrequencies {d : ℕ} (x : ℕ → Cube d) :
    CompactDistribution x ↔ ∀ m : Fin d → ℤ, m ≠ 0 →
      CompactSeq (fun n => centeredHalfFrequency m (x n)) := by
  constructor
  · exact fun hx m _ => hx (centeredHalfFrequency m)
  · intro h
    apply (cube_compact_iff_halfFrequencies x).2
    intro m
    by_cases hm : m = 0
    · subst m
      simpa only [halfFrequency_zero, ContinuousMap.one_apply, CompactSeq] using compactAlong_const 1 strictMono_id
    · simpa [centeredHalfFrequency, center, CompactSeq] using
        CompactAlong.add (h m hm) (compactAlong_const (testMean (cubeLebesgue d) (halfFrequency m)) strictMono_id)

end
end VdC
