/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.BernoulliSigns
public import SixProblems.FiniteScalarization
public import SixProblems.Koopman
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing
open scoped InnerProductSpace

variable {G : Type} [Group G]

theorem isVdC_of_one_mem {R : Set G} (h : 1 ∈ R) : IsVdC R := by
  intro X _ _ S f hm hb hz
  let hf := bounded_measurable_memLp S hm hb
  have he := inner_systemKoopman_of_memLp S hf 1
  rw [map_one, inv_one, hz _ h] at he
  have hLp := inner_self_eq_zero.mp he
  apply integral_eq_zero_of_ae
  apply hf.coeFn_toLp.symm.trans
  rw [hLp]
  exact Lp.coeFn_zero _ _ _

/-- A complex counterexample to the dynamical van der Corput test gives
a real counterexample on a finite identity extension. -/
theorem exists_real_counterexample {R : Set G} (h : ¬ IsVdC R) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
      (∀ r ∈ R, ∫ x, f (S.act r x) * f x ∂S.measure = 0) ∧
      (∫ x, f x ∂S.measure) ≠ 0 := by
  classical
  by_contra hn
  apply h
  intro X mX hX S f hf hB hZ
  by_contra hM
  obtain ⟨C, hC⟩ := hB
  let v (x : X) (i : Bool) := if i then (f x).im else (f x).re
  have hv (i : Bool) : Measurable (fun x ↦ v x i) := by
    cases i
    · exact Complex.continuous_re.measurable.comp hf
    · exact Complex.continuous_im.measurable.comp hf
  have hvB (x : X) (i : Bool) : ‖v x i‖ ≤ C := by
    cases i
    · exact (Complex.abs_re_le_norm (f x)).trans (hC x)
    · exact (Complex.abs_im_le_norm (f x)).trans (hC x)
  have hInt : Integrable f S.measure :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hVMean : ∃ i : Bool, (∫ x, v x i ∂S.measure) ≠ 0 := by
    by_contra! hAll
    apply hM
    apply Complex.ext
    · have hr := Complex.reCLM.integral_comp_comm hInt
      change (∫ x, v x false ∂S.measure) = (∫ x, f x ∂S.measure).re at hr
      rw [← hr]
      exact hAll false
    · have hi := Complex.imCLM.integral_comp_comm hInt
      change (∫ x, v x true ∂S.measure) = (∫ x, f x ∂S.measure).im at hi
      rw [← hi]
      exact hAll true
  obtain ⟨i, hi⟩ := hVMean
  obtain ⟨s, hs⟩ := exists_finiteSelection_nonzero_integral S v hv C hvB i hi
  let T := S.prod (identityAction G (uniformIndex Bool))
  let q (z : X × Bool) : ℝ := if s z.2 then -v z.1 z.2 else v z.1 z.2
  refine hn ⟨X × Bool, inferInstance, inferInstance, T, q,
    measurable_finiteSelection v hv s, ⟨C, ?_⟩, ?_, hs⟩
  · intro z
    unfold q
    split_ifs <;> simpa only [norm_neg] using hvB z.1 z.2
  · intro r hr
    have hq := finiteSelection_correlation S v hv C hvB s r
    change (∫ z, q (T.act r z) * q z ∂T.measure) = _ at hq
    rw [hq]
    have hC0 : 0 ≤ C := (norm_nonneg (f (Classical.choice
      (nonempty_of_isProbabilityMeasure S.measure)))).trans (hC _)
    have hI (j : Bool) : Integrable (fun x ↦ v (S.act r x) j * v x j) S.measure :=
      Integrable.of_bound (((hv j).comp (S.preserves r).measurable).mul (hv j)).aestronglyMeasurable
        (C*C) (ae_of_all _ fun x ↦ by
          rw [norm_mul]
          exact mul_le_mul (hvB _ _) (hvB _ _) (norm_nonneg _) hC0)
    change (Fintype.card Bool : ℝ)⁻¹ • (∑ j, ∫ x, v (S.act r x) j * v x j ∂S.measure) = 0
    rw [← integral_finsetSum _ (fun j _ ↦ hI j)]
    let k (x : X) := f (S.act r x) * (starRingEnd ℂ) (f x)
    have hk : Integrable k S.measure := Integrable.of_bound
      ((hf.comp (S.preserves r).measurable).mul (Complex.continuous_conj.measurable.comp hf)).aestronglyMeasurable
      (C*C) (ae_of_all _ fun x ↦ by
        change ‖f (S.act r x) * (starRingEnd ℂ) (f x)‖ ≤ _
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0)
    have he (x : X) : (∑ j, v (S.act r x) j * v x j) = (k x).re := by
      have hu : (Finset.univ : Finset Bool) = {false,true} := by decide
      rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
      simp [v, k, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    simp_rw [he]
    change (Fintype.card Bool : ℝ)⁻¹ • (∫ x, Complex.reCLM (k x) ∂S.measure) = 0
    rw [Complex.reCLM.integral_comp_comm hk]
    change (Fintype.card Bool : ℝ)⁻¹ • (correlation S f r).re = 0
    simp [hZ r hr]

/-- Lemma 4.3. Failure of the van der Corput test can be witnessed by a
two-valued observable. -/
theorem lemma4_3 [Countable G] {R : Set G} (h : ¬ IsVdC R) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      Measurable f ∧ (∀ x, f x = 1 ∨ f x = -1) ∧
      (∀ r ∈ R, ∫ x, f (S.act r x) * f x ∂S.measure = 0) ∧
      (∫ x, f x ∂S.measure) ≠ 0 := by
  obtain ⟨X, mX, hX, S, f, hf, ⟨C, hC⟩, hZ, hM⟩ := exists_real_counterexample h
  let := mX
  let := hX
  let B := |C| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let t (x : X) := (B⁻¹ * f x + 1) / 2
  have ht : Measurable t := ((measurable_const.mul hf).add measurable_const).div_const _
  have hb (x : X) : ‖B⁻¹ * f x‖ ≤ 1 := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB), ← div_eq_inv_mul]
    exact (div_le_iff₀ hB).2 (by
      rw [one_mul]
      exact (hC x).trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one)))
  have hb' (x : X) := abs_le.mp (show |B⁻¹ * f x| ≤ 1 from hb x)
  have ht0 (x : X) : 0 ≤ t x := by dsimp [t]; linarith [(hb' x).1]
  have ht1 (x : X) : t x ≤ 1 := by dsimp [t]; linarith [(hb' x).2]
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let s := bernoulliSign (G := G) t
  have he (x : X) : 2 * t x - 1 = B⁻¹ * f x := by dsimp [t]; ring
  refine ⟨X × (G → ℝ), inferInstance, inferInstance, T, s,
    measurable_bernoulliSign ht, ?_, ?_, ?_⟩
  · intro z
    unfold s bernoulliSign thresholdSign
    split_ifs <;> simp
  · intro r hr
    have hr1 : r ≠ 1 := fun e ↦ h (isVdC_of_one_mem (e ▸ hr))
    rw [integral_bernoulliSign_correlation S ht ht0 ht1 r hr1]
    simp_rw [he, show ∀ a b : ℝ, (B⁻¹ * a) * (B⁻¹ * b) = B⁻¹^2 * (a*b) by intro a b; ring]
    rw [integral_const_mul, hZ r hr, mul_zero]
  · rw [integral_bernoulliSign S ht ht0 ht1]
    simp_rw [he]
    rw [integral_const_mul]
    exact mul_ne_zero (inv_ne_zero hB.ne') hM

end SixProblems
