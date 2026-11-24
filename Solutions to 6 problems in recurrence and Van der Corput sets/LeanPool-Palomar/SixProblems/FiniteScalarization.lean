/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Definitions
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped ENNReal InnerProductSpace

variable {G X I : Type*} [Group G] [MeasurableSpace X]

/-- The identity action on a probability space. -/
def identityAction (G : Type*) [Group G] {I : Type*} [MeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ] : System G I where
  measure := μ
  probability := inferInstance
  act := fun _ ↦ id
  act_one := rfl
  act_mul _ _ := rfl
  preserves _ := MeasurePreserving.id μ

section Finite

variable [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Uniform finite law, using the same weight at every index. -/
def uniformIndex (I : Type*) [Fintype I] [MeasurableSpace I] : Measure I :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure (uniformIndex I) := by
  constructor
  rw [uniformIndex, smul_apply, smul_eq_mul, Measure.count_univ]
  simp [ENNReal.inv_mul_cancel, Fintype.card_ne_zero]

omit [Nonempty I] in
theorem integral_uniformIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : I → E) :
    ∫ i, f i ∂uniformIndex I = (Fintype.card I : ℝ)⁻¹ • ∑ i, f i := by
  rw [uniformIndex, integral_smul_measure, integral_count, ENNReal.toReal_inv, ENNReal.toReal_natCast]

variable {𝕜 : Type*} [RCLike 𝕜]

omit [Nonempty I] in
theorem measurable_finiteSelection (v : X → I → 𝕜)
    (hv : ∀ i, Measurable (fun x ↦ v x i)) (s : I → Bool) :
    Measurable (fun z : X × I ↦ if s z.2 then -(v z.1 z.2) else v z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  change Measurable (fun x ↦ if s i then -v x i else v x i)
  split_ifs
  · exact (hv i).neg
  · exact hv i

/-- Selecting one coordinate on a finite identity factor, with any choice
of signs, preserves the summed scalar correlations up to normalization. -/
theorem finiteSelection_correlation
    (S : System G X) (v : X → I → 𝕜) (hv : ∀ i, Measurable (fun x ↦ v x i))
    (C : ℝ) (hC : ∀ x i, ‖v x i‖ ≤ C) (s : I → Bool) (g : G) :
    let T := S.prod (identityAction G (uniformIndex I))
    let q (z : X × I) := if s z.2 then -(v z.1 z.2) else v z.1 z.2
    ∫ z, q (T.act g z) * (starRingEnd 𝕜) (q z) ∂T.measure =
      (Fintype.card I : ℝ)⁻¹ • ∑ i,
        ∫ x, v (S.act g x) i * (starRingEnd 𝕜) (v x i) ∂S.measure := by
  classical
  let f (z : X × I) := v (S.act g z.1) z.2 * (starRingEnd 𝕜) (v z.1 z.2)
  let T := S.prod (identityAction G (uniformIndex I))
  let q (z : X × I) := if s z.2 then -(v z.1 z.2) else v z.1 z.2
  change (∫ z, q (T.act g z) * (starRingEnd 𝕜) (q z) ∂T.measure) = _
  have hpt (z : X × I) : q (T.act g z) * (starRingEnd 𝕜) (q z) = f z := by
    change (if s z.2 then -v (S.act g z.1) z.2 else v (S.act g z.1) z.2) *
      (starRingEnd 𝕜) (if s z.2 then -v z.1 z.2 else v z.1 z.2) = f z
    split_ifs <;> simp [f]
  simp_rw [hpt]
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro i
    exact ((hv i).comp (S.preserves g).measurable).mul (RCLike.continuous_conj.measurable.comp (hv i))
  have hB : 0 ≤ C := (norm_nonneg (v (Classical.choice (nonempty_of_isProbabilityMeasure S.measure))
    (Classical.choice inferInstance))).trans (hC _ _)
  have hi : Integrable f T.measure := Integrable.of_bound hf.aestronglyMeasurable (C*C)
    (ae_of_all _ fun z ↦ by
      change ‖v (S.act g z.1) z.2 * (starRingEnd 𝕜) (v z.1 z.2)‖ ≤ _
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hC _ _) (hC _ _) (norm_nonneg _) hB)
  change (∫ z, f z ∂S.measure.prod (uniformIndex I)) = _
  change Integrable f (S.measure.prod (uniformIndex I)) at hi
  rw [integral_prod_symm f hi, integral_uniformIndex]

theorem finiteSelection_integral
    (S : System G X) (v : X → I → 𝕜) (hv : ∀ i, Measurable (fun x ↦ v x i))
    (C : ℝ) (hC : ∀ x i, ‖v x i‖ ≤ C) (s : I → Bool) :
    let T := S.prod (identityAction G (uniformIndex I))
    ∫ z : X × I, (if s z.2 then -(v z.1 z.2) else v z.1 z.2) ∂T.measure =
      (Fintype.card I : ℝ)⁻¹ • ∑ i, if s i then -(∫ x, v x i ∂S.measure) else ∫ x, v x i ∂S.measure := by
  let q (z : X × I) := if s z.2 then -(v z.1 z.2) else v z.1 z.2
  have hq : Measurable q := measurable_finiteSelection v hv s
  have hqB (z : X × I) : ‖q z‖ ≤ C := by
    unfold q
    split_ifs <;> simpa only [norm_neg] using hC z.1 z.2
  change (∫ z, q z ∂S.measure.prod (uniformIndex I)) = _
  rw [integral_prod_symm q (Integrable.of_bound hq.aestronglyMeasurable C (ae_of_all _ hqB)),
    integral_uniformIndex]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (∫ x, if s i then -v x i else v x i ∂S.measure) = _
  split_ifs with h
  · exact integral_neg (fun x ↦ v x i)
  · rfl

/-- If some coordinate mean is nonzero, at least one choice of signs has
nonzero mean after selection. Flipping one coordinate changes the sum by
twice that coordinate. -/
theorem exists_finiteSelection_nonzero_integral
    (S : System G X) (v : X → I → 𝕜) (hv : ∀ i, Measurable (fun x ↦ v x i))
    (C : ℝ) (hC : ∀ x i, ‖v x i‖ ≤ C) (j : I)
    (hj : ∫ x, v x j ∂S.measure ≠ 0) :
    ∃ s : I → Bool, let T := S.prod (identityAction G (uniformIndex I))
      (∫ z : X × I, (if s z.2 then -(v z.1 z.2) else v z.1 z.2) ∂T.measure) ≠ 0 := by
  classical
  by_contra! h
  let A (i : I) := ∫ x, v x i ∂S.measure
  have hWeight : (Fintype.card I : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hs (s : I → Bool) : (∑ i, if s i then -A i else A i) = 0 := by
    have he : (∫ z : X × I, (if s z.2 then -(v z.1 z.2) else v z.1 z.2)
        ∂(S.prod (identityAction G (uniformIndex I))).measure) = 0 := not_not.mp (h s)
    rw [finiteSelection_integral S v hv C hC s] at he
    exact (smul_eq_zero.mp he).resolve_left hWeight
  have hsum : ∑ i, A i = 0 := by simpa using hs (fun _ ↦ false)
  let s : I → Bool := fun i ↦ decide (i = j)
  have hdiff : (∑ i, ((if s i then -A i else A i) - A i)) = -A j - A j := by
    rw [Finset.sum_eq_single j]
    · simp [s]
    · intro i _ hi
      simp [s,hi]
    · simp
  rw [Finset.sum_sub_distrib, hs, hsum, sub_zero] at hdiff
  have he : (2 : 𝕜) * A j = 0 := calc
    _ = -(-A j - A j) := by ring
    _ = 0 := by rw [← hdiff, neg_zero]
  exact hj ((mul_eq_zero.mp he).resolve_left two_ne_zero)

end Finite

/-- Lemma 4.2. The scalar van der Corput test implies the finite-dimensional
test, including the zero-dimensional case. -/
theorem lemma4_2 {G X : Type} [Group G] [MeasurableSpace X] [StandardBorelSpace X]
    {R : Set G} (hR : IsVdC R) (S : System G X) {d : ℕ}
    (V : X → EuclideanSpace ℂ (Fin d)) (hV : Measurable V)
    (hB : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (hZero : ∀ r ∈ R, ∫ x, ⟪V x,V (S.act r x)⟫_ℂ ∂S.measure = 0) :
    (∫ x, V x ∂S.measure) = 0 := by
  classical
  obtain ⟨C,hC⟩ := hB
  let v (x : X) (i : Fin d) := V x i
  have hv (i : Fin d) : Measurable (fun x ↦ v x i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.measurable.comp hV
  have hvC (x : X) (i : Fin d) : ‖v x i‖ ≤ C :=
    (PiLp.norm_apply_le (V x) i).trans (hC x)
  have hInt : Integrable V S.measure := Integrable.of_bound hV.aestronglyMeasurable C (ae_of_all _ hC)
  ext i
  change EuclideanSpace.proj i (∫ x, V x ∂S.measure) = 0
  rw [← (EuclideanSpace.proj i).integral_comp_comm hInt]
  change ∫ x, v x i ∂S.measure = 0
  by_contra hi
  let : Nonempty (Fin d) := ⟨i⟩
  let T := S.prod (identityAction G (uniformIndex (Fin d)))
  obtain ⟨s, hs⟩ := exists_finiteSelection_nonzero_integral S v hv C hvC i hi
  let q (z : X × Fin d) : ℂ := if s z.2 then -v z.1 z.2 else v z.1 z.2
  have hqB (z : X × Fin d) : ‖q z‖ ≤ C := by
    unfold q
    split_ifs <;> simpa only [norm_neg] using hvC z.1 z.2
  apply hs
  apply hR T q (measurable_finiteSelection v hv s) ⟨C,hqB⟩
  intro r hr
  have hC0 : 0 ≤ C := (norm_nonneg (v (Classical.choice (nonempty_of_isProbabilityMeasure S.measure)) i)).trans (hvC _ _)
  rw [correlation, finiteSelection_correlation S v hv C hvC s r]
  have hi₀ (j : Fin d) : Integrable (fun x ↦ v (S.act r x) j * (starRingEnd ℂ) (v x j)) S.measure :=
    Integrable.of_bound (((hv j).comp (S.preserves r).measurable).mul
      (Complex.continuous_conj.measurable.comp (hv j))).aestronglyMeasurable
      (C*C) (ae_of_all _ fun x ↦ by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hvC _ _) (hvC _ _) (norm_nonneg _) hC0)
  rw [← integral_finsetSum _ (fun j _ ↦ hi₀ j)]
  have hsum (x : X) : (∑ j, v (S.act r x) j * (starRingEnd ℂ) (v x j)) = ⟪V x,V (S.act r x)⟫_ℂ := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [RCLike.inner_apply']
    exact mul_comm _ _
  simp_rw [hsum]
  rw [hZero r hr, smul_zero]

end SixProblems
