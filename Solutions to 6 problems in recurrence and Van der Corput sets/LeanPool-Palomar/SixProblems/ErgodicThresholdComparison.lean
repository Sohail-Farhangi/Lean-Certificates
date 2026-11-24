/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.BernoulliProposition
public import SixProblems.PartitionRegularity
public import SixProblems.NiceRecurrence
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set

variable {G X : Type} [Group G] [MeasurableSpace X]

/-- Ergodic realization up to an arbitrarily small uniform error in the
coefficient; this is the form of realization needed for nice recurrence. -/
def HasBoundedErgodicPDApproximation (G : Type) [Group G] : Prop :=
  ∀ φ : G → ℝ, RealPositiveDefinite φ → ∀ δ > 0,
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      S.IsErgodic ∧ Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ ∀ g,
      |(∫ x, f (S.act g x) * f x ∂S.measure) - φ g| < δ

private theorem integral_affine_half (S : System G X) {f : X → ℝ}
    (hf : Integrable f S.measure) (b : ℝ) :
    ∫ x, 1/2 + b*f x ∂S.measure = 1/2 + b*(∫ x, f x ∂S.measure) := by
  rw [integral_add (integrable_const _) (hf.const_mul _), integral_const, integral_const_mul,
    probReal_univ, one_smul]

private theorem integral_affine_half_mul (S : System G X) {f : X → ℝ}
    (hf : Integrable f S.measure) (b : ℝ) (g : G)
    (hmul : Integrable (fun x ↦ f (S.act g x) * f x) S.measure) :
    (∫ x, (1/2 + b*f (S.act g x))*(1/2 + b*f x) ∂S.measure) =
      1/4 + b*(∫ x, f x ∂S.measure) + b^2*(∫ x, f (S.act g x) * f x ∂S.measure) := by
  have hfg := (S.preserves g).integrable_comp_of_integrable hf
  have hmf : AEStronglyMeasurable f (S.measure.map (S.act g)) :=
    (S.preserves g).map_eq.symm ▸ hf.aestronglyMeasurable
  have he := integral_map (S.preserves g).aemeasurable hmf
  rw [(S.preserves g).map_eq] at he
  have hp (x : X) : (1/2 + b*f (S.act g x))*(1/2 + b*f x) =
      (1/4 + (b/2)*f (S.act g x)) + (b/2)*f x + b^2*(f (S.act g x)*f x) := by ring
  have hconst : Integrable (fun _ : X ↦ (1/4 : ℝ)) S.measure := integrable_const _
  have hshift : Integrable (fun x ↦ (b/2)*f (S.act g x)) S.measure := hfg.const_mul _
  have hterm : Integrable (fun x ↦ (b/2)*f x) S.measure := hf.const_mul _
  have hprod : Integrable (fun x ↦ b^2*(f (S.act g x)*f x)) S.measure := hmul.const_mul _
  have hsum : Integrable (fun x ↦ 1/4 + (b/2)*f (S.act g x)) S.measure := hconst.add hshift
  have hsum' : Integrable (fun x ↦ 1/4 + (b/2)*f (S.act g x) + (b/2)*f x) S.measure := hsum.add hterm
  simp_rw [hp]
  rw [integral_add hsum' hprod, integral_add hsum hterm, integral_add hconst hshift,
    integral_const, probReal_univ, one_smul]
  simp_rw [integral_const_mul]
  change _ = (∫ x, f (S.act g x) ∂S.measure) at he
  rw [← he]
  ring

/-- With the ergodic realization established, this is the implication
from condition (b) to condition (d) of Theorem 2.2. -/
theorem nonnegativePD_of_ergodicNiceRecurrence [Countable G] [Infinite G]
    (hRealize : HasBoundedErgodicPDApproximation G) {R : Set G}
    (hNice : ErgodicNiceRecurrence R) : NonnegativeOnPositiveDefinite R := by
  classical
  intro φ hφ ε hε
  by_contra! hneg
  obtain ⟨X,mX,hX,S,f,hS,hf,⟨C,hC⟩,hApprox⟩ := hRealize φ hφ (ε/2) (half_pos hε)
  let := mX
  let := hX
  let b := (2*(|C|+1))⁻¹
  have hb : 0 < b := inv_pos.mpr (by positivity)
  have hB (x : X) : |b * f x| ≤ 1/2 := by
    rw [abs_mul, abs_of_pos hb]
    change (2*(|C|+1))⁻¹ * |f x| ≤ 1/2
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    have hx := (hC x).trans (le_abs_self C)
    change |f x| ≤ |C| at hx
    linarith
  let F (x : X) := 1/2 + b*f x
  have hF : Measurable F := measurable_const.add (measurable_const.mul hf)
  have hF0 (x : X) : 0 ≤ F x := by dsimp [F]; linarith [(abs_le.mp (hB x)).1]
  have hF1 (x : X) : F x ≤ 1 := by dsimp [F]; linarith [(abs_le.mp (hB x)).2]
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let A := bernoulliThreshold (G := G) F
  have hA : MeasurableSet A := measurableSet_bernoulliThreshold hF
  have hT : T.IsErgodic := bernoulli_prod_isErgodic unitIntervalLaw S hS
  have hη : 0 < b^2*(ε/2) := mul_pos (sq_pos_of_pos hb) (half_pos hε)
  obtain ⟨r,hr,hret⟩ := hNice T hT A hA (b^2*(ε/2)) hη
  have hr₁ : r ≠ 1 := by
    intro h
    have hφ0 := hφ.one_nonneg
    have hrneg := hneg r hr
    rw [h] at hrneg
    linarith
  have hMass : (T.measure A).toReal = ∫ x, F x ∂S.measure := by
    have h := bernoulliThreshold_pattern S hF hF0 hF1 {1}
    change (T.measure {z | ∀ g ∈ ({1} : Finset G), z ∈ T.act g ⁻¹' A}).toReal = _ at h
    have he : {z | ∀ g ∈ ({1} : Finset G), z ∈ T.act g ⁻¹' A} = A := by
      ext z
      simp [T.act_one]
    rw [he] at h
    simpa only [Finset.prod_singleton,S.act_one,id_eq] using h
  have hRet : (T.measure (A ∩ T.act r ⁻¹' A)).toReal = ∫ x, F (S.act r x) * F x ∂S.measure := by
    have h := bernoulliThreshold_pattern S hF hF0 hF1 {r,1}
    change (T.measure {z | ∀ g ∈ ({r,1} : Finset G), z ∈ T.act g ⁻¹' A}).toReal = _ at h
    have he : {z | ∀ g ∈ ({r,1} : Finset G), z ∈ T.act g ⁻¹' A} = A ∩ T.act r ⁻¹' A := by
      ext z
      simp [T.act_one,and_comm]
    rw [he] at h
    have hn : r ∉ ({1} : Finset G) := by simpa using hr₁
    simpa only [Finset.prod_insert hn,Finset.prod_singleton,S.act_one,id_eq] using h
  have hL : MemLp f 2 S.measure := MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hi := hL.integrable (by norm_num)
  have hCorr := integral_affine_half_mul S hi b r
    ((hL.comp_measurePreserving (S.preserves r)).integrable_mul hL)
  change (∫ x, F (S.act r x) * F x ∂S.measure) = _ at hCorr
  rw [hMass,hRet,hCorr,integral_affine_half S hi] at hret
  have hSmall := (abs_lt.mp (hApprox r)).2
  have hStrict : (∫ x, f (S.act r x) * f x ∂S.measure) < -(ε/2) := by linarith [hneg r hr]
  have hLarge : -(ε/2) ≤ (∫ x, f (S.act r x) * f x ∂S.measure) := by
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hb)
    nlinarith [sq_nonneg (b * (∫ x, f x ∂S.measure))]
  exact hStrict.not_ge hLarge

end SixProblems
