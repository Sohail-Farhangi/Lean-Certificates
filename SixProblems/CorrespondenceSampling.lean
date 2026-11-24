/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Probability.Moments.Variance

@[expose] public section

namespace SixProblems

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical Topology ProbabilityTheory

section Sampling

variable {A B I X : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Fintype I] [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
/-- Independent samples for a finite set of labels simultaneously control all
    centered test sums. The squared error bound is linear in the number of
    terms and in the largest label class. -/
theorem exists_small_groupedSums (μ : Measure X) [IsProbabilityMeasure μ]
    (label : A → B) (q : I → A → X → ℝ) (C : I → ℝ)
    (hBound : ∀ i a x, ‖q i a x‖ ≤ C i)
    (hMeas : ∀ i a, Measurable (q i a)) (hMean : ∀ i a, (∫ x, q i a x ∂μ) = 0)
    (M : ℕ) (hM : ∀ b, (Finset.univ.filter (fun a ↦ label a = b)).card ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (hSmall : (Fintype.card A : ℝ) * M * (∑ i, C i ^ 2) < ε ^ 2) :
    ∃ y : B → X, ∀ i, ‖∑ a, q i a (y (label a))‖ < ε := by
  let fiber (b : B) := Finset.univ.filter (fun a ↦ label a = b)
  let ν : Measure (B → X) := Measure.pi (fun _ : B ↦ μ)
  let Z (i : I) (b : B) (x : X) := ∑ a ∈ fiber b, q i a x
  let Y (i : I) (y : B → X) := ∑ b, Z i b (y b)
  have hZMeas (i : I) (b : B) : Measurable (Z i b) :=
    Finset.measurable_sum _ fun a _ ↦ hMeas i a
  have hZBound (i : I) (b : B) (x : X) : ‖Z i b x‖ ≤ ((fiber b).card : ℝ) * C i := calc
    _ ≤ ∑ a ∈ fiber b, ‖q i a x‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ fiber b, C i := Finset.sum_le_sum fun a _ ↦ hBound i a x
    _ = _ := by simp [nsmul_eq_mul]
  have hZLp (i : I) (b : B) : MemLp (Z i b) 2 μ :=
    MemLp.of_bound (hZMeas i b).aestronglyMeasurable _ (.of_forall fun x ↦ hZBound i b x)
  have hZMean (i : I) (b : B) : (∫ x, Z i b x ∂μ) = 0 := by
    have hInt (a : A) : Integrable (q i a) μ :=
      Integrable.of_bound (hMeas i a).aestronglyMeasurable _ (.of_forall (hBound i a))
    unfold Z
    rw [integral_finsetSum _ (fun a _ ↦ hInt a)]
    simp [hMean]
  have hYInt (i : I) (b : B) : Integrable (fun y : B → X ↦ Z i b (y b)) ν :=
    (measurePreserving_eval (fun _ : B ↦ μ) b).integrable_comp_of_integrable
      ((hZLp i b).integrable (by norm_num))
  have hYLp (i : I) : MemLp (Y i) 2 ν :=
    memLp_finsetSum _ fun b _ ↦ (hZLp i b).comp_measurePreserving
      (measurePreserving_eval (fun _ : B ↦ μ) b)
  have hYMean (i : I) : (∫ y, Y i y ∂ν) = 0 := by
    unfold Y
    rw [integral_finsetSum _ (fun b _ ↦ hYInt i b)]
    apply Finset.sum_eq_zero
    intro b _
    have hp := measurePreserving_eval (fun _ : B ↦ μ) b
    rw [← hZMean i b, ← hp.map_eq, integral_map hp.measurable.aemeasurable
      (hZMeas i b).aestronglyMeasurable]
  have hSize : ∑ b, ((fiber b).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset B))
      (f := label) (fun _ _ ↦ Finset.mem_univ _)).symm
  have hVar (i : I) : (∫ y, Y i y ^ 2 ∂ν) ≤ (Fintype.card A : ℝ) * M * C i ^ 2 := by
    have hv₁ : variance (Y i) ν = ∫ y, Y i y ^ 2 ∂ν := by
      rw [variance_eq_sub (hYLp i), hYMean i]
      simp [Pi.pow_apply]
    have hv₂ : variance (Y i) ν = ∑ b, variance (Z i b) μ := by
      have hYEq : Y i = ∑ b, (fun y : B → X ↦ Z i b (y b)) := by
        funext y
        simp only [Y, Finset.sum_apply]
      rw [hYEq]
      exact variance_sum_pi (μ := fun _ : B ↦ μ) (hZLp i)
    rw [← hv₁, hv₂, ← hSize, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    let c := ((fiber b).card : ℝ) * C i
    have hb : ∀ᵐ x ∂μ, Z i b x ∈ Icc (-c) c := .of_forall fun x ↦
      abs_le.mp (hZBound i b x)
    calc
      _ ≤ ((c - -c) / 2) ^ 2 := variance_le_sq_of_bounded hb (hZMeas i b).aemeasurable
      _ = ((fiber b).card : ℝ) ^ 2 * C i ^ 2 := by dsimp [c]; ring
      _ ≤ ((fiber b).card : ℝ) * M * C i ^ 2 := by
        rw [pow_two ((fiber b).card : ℝ)]
        gcongr
        exact_mod_cast hM b
  let loss (y : B → X) := ∑ i, Y i y ^ 2
  have hLossInt : Integrable loss ν :=
    integrable_finsetSum _ fun i _ ↦ (hYLp i).integrable_sq
  have hLoss : (∫ y, loss y ∂ν) < ε ^ 2 := by
    refine lt_of_le_of_lt ?_ hSmall
    unfold loss
    rw [integral_finsetSum _ (fun i _ ↦ (hYLp i).integrable_sq), Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hVar i
  obtain ⟨y, hy⟩ : ∃ y, loss y < ε ^ 2 := by
    by_contra! hn
    have hge : ε ^ 2 ≤ ∫ y, loss y ∂ν := by
      simpa using integral_mono (integrable_const (ε ^ 2)) hLossInt hn
    exact (not_lt_of_ge hge) hLoss
  refine ⟨y, fun i ↦ ?_⟩
  have hYi : Y i y ^ 2 ≤ loss y :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (Y j y)) (Finset.mem_univ i)
  have hI : ‖Y i y‖ < ε := by
    rw [Real.norm_eq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) hε.le).mp (by simpa only [sq_abs] using hYi.trans_lt hy)
  have hsum : Y i y = ∑ a, q i a (y (label a)) := by
    unfold Y Z
    calc
      _ = ∑ b, ∑ a ∈ fiber b, q i a (y (label a)) := by
        refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a ha ↦ ?_
        rw [(Finset.mem_filter.mp ha).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset A))
        (t := (Finset.univ : Finset B)) (g := label) (fun _ _ ↦ Finset.mem_univ _)
        (fun a ↦ q i a (y (label a)))
  rwa [← hsum]

end Sampling

end

end SixProblems
