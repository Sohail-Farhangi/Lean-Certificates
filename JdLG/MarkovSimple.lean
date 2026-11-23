/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MarkovLp
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul

/-! # Markov contractions on simple functions -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace JdLG

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The equivalence class of a complex simple function in the specified Lᵖ space. -/
noncomputable def simpleFunctionLp (p : ℝ≥0∞) (f : SimpleFunc X ℂ) : Lp ℂ p μ :=
  (f.memLp_of_isFiniteMeasure p μ).toLp f

theorem simpleFunctionLp_coeFn (p : ℝ≥0∞) (f : SimpleFunc X ℂ) :
    (simpleFunctionLp μ p f : X → ℂ) =ᵐ[μ] f :=
  (f.memLp_of_isFiniteMeasure p μ).coeFn_toLp

/-- The constant one in L¹ of a probability measure. -/
noncomputable def probabilityLpOneConstant : Lp ℂ 1 μ :=
  (memLp_const (1 : ℂ)).toLp (fun _ ↦ 1)

/-- Positivity of a complex L¹ vector means that its values are real and
nonnegative almost everywhere. -/
def ProbabilityLpNonnegative (f : Lp ℂ 1 μ) : Prop :=
  ∀ᵐ x ∂μ, (f x : ℂ) = (f x).re ∧ 0 ≤ (f x).re

/-- Markov operators as in Eisner–Farkas–Haase–Nagel, §13.1:
positivity, preservation of one, and preservation of the integral. -/
structure IsProbabilityMarkovOperator (T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ) : Prop where
  map_nonnegative : ∀ f, ProbabilityLpNonnegative μ f → ProbabilityLpNonnegative μ (T f)
  map_one : T (probabilityLpOneConstant μ) = probabilityLpOneConstant μ
  integral_map : ∀ f, (∫ x, T f x ∂μ) = ∫ x, f x ∂μ

omit [IsProbabilityMeasure μ] in
private theorem coeFn_finsetSum_mul {I : Type*} (s : Finset I) (c : I → ℂ)
    (f : I → Lp ℂ 1 μ) :
    (fun x ↦ (∑ i ∈ s, c i • f i) x) =ᵐ[μ] fun x ↦ ∑ i ∈ s, c i * f i x := by
  filter_upwards [Lp.coeFn_finsetSum s (fun i ↦ c i • f i),
    (eventually_all_finset s).2 fun i _ ↦ Lp.coeFn_smul (c i) (f i)] with x hx hsmul
  rw [Finset.sum_apply] at hx
  rw [hx]
  exact Finset.sum_congr rfl fun i hi ↦ hsmul i hi

/-- The indicator in L¹ of the fiber of a simple function at a single value. -/
noncomputable def simpleFunctionFiber (f : SimpleFunc X ℂ) (b : ℂ) : Lp ℂ 1 μ :=
  indicatorConstLp 1 (f.measurable (measurableSet_singleton b)) (measure_ne_top μ _) 1

private theorem simpleFunctionFiber_coeFn (f : SimpleFunc X ℂ) (b : ℂ) :
    (simpleFunctionFiber μ f b : X → ℂ) =ᵐ[μ] (f ⁻¹' {b}).indicator (fun _ ↦ 1) :=
  indicatorConstLp_coeFn

private theorem simpleFunctionFiber_nonnegative (f : SimpleFunc X ℂ) (b : ℂ) :
    ProbabilityLpNonnegative μ (simpleFunctionFiber μ f b) := by
  filter_upwards [simpleFunctionFiber_coeFn μ f b] with x hx
  by_cases h : f x = b <;> simp [hx, Set.indicator, h]

private theorem simpleFunctionLp_map_eq_sum_fibers (f : SimpleFunc X ℂ) (c : ℂ → ℂ) :
    simpleFunctionLp μ 1 (f.map c) = ∑ b ∈ f.range, c b • simpleFunctionFiber μ f b := by
  classical
  apply Lp.ext
  filter_upwards [simpleFunctionLp_coeFn μ 1 (f.map c),
    coeFn_finsetSum_mul μ f.range c (simpleFunctionFiber μ f),
    (eventually_all_finset f.range).2 fun b _ ↦ simpleFunctionFiber_coeFn μ f b] with x hx hsum h
  rw [hx, hsum]
  change c (f x) = ∑ b ∈ f.range, c b * simpleFunctionFiber μ f b x
  rw [Finset.sum_eq_single (f x)]
  · rw [h _ (f.mem_range_self x)]
    simp
  · intro b hb hxb
    rw [h _ hb]
    simp [Set.indicator, Ne.symm hxb]
  · exact fun hx ↦ hx (f.mem_range_self x) |>.elim

private theorem probabilityLpOneConstant_eq_sum_fibers (f : SimpleFunc X ℂ) :
    probabilityLpOneConstant μ = ∑ b ∈ f.range, simpleFunctionFiber μ f b := by
  have he : probabilityLpOneConstant μ = simpleFunctionLp μ 1 (f.map fun _ ↦ 1) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp (memLp_const (1 : ℂ))).trans
      (simpleFunctionLp_coeFn μ 1 (f.map fun _ ↦ 1)).symm
  rw [he, simpleFunctionLp_map_eq_sum_fibers]
  simp only [one_smul]

variable {μ}

/-- Finite-partition Jensen inequality for a Markov operator applied to a
complex simple function. Taking k = 1 and k = 2 gives both contraction bounds. -/
theorem IsProbabilityMarkovOperator.ae_norm_pow_le
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T)
    (f : SimpleFunc X ℂ) (k : ℕ) :
    ∀ᵐ x ∂μ, ‖T (simpleFunctionLp μ 1 f) x‖ ^ k ≤
      (T (simpleFunctionLp μ 1 (f.map fun b ↦ (‖b‖ ^ k : ℝ))) x).re := by
  classical
  let I := simpleFunctionFiber μ f
  let c : ℂ → ℂ := fun b ↦ (‖b‖ ^ k : ℝ)
  have hTsum (d : ℂ → ℂ) :
      T (simpleFunctionLp μ 1 (f.map d)) = ∑ b ∈ f.range, d b • T (I b) := by
    rw [simpleFunctionLp_map_eq_sum_fibers, map_sum]
    simp only [map_smul, I]
  have hone : ∑ b ∈ f.range, T (I b) = probabilityLpOneConstant μ := by
    rw [← map_sum, ← probabilityLpOneConstant_eq_sum_fibers μ f, hT.map_one]
  have honeAE : (fun x ↦ ∑ b ∈ f.range, T (I b) x) =ᵐ[μ] fun _ ↦ (1 : ℂ) := by
    have hc : (probabilityLpOneConstant μ : X → ℂ) =ᵐ[μ] fun _ ↦ 1 :=
      (memLp_const (1 : ℂ)).coeFn_toLp
    filter_upwards [Lp.coeFn_finsetSum f.range (fun b ↦ T (I b)), hc] with x hx hh
    rw [hone, Finset.sum_apply] at hx
    exact hx.symm.trans hh
  have hE (d : ℂ → ℂ) : (fun x ↦ T (simpleFunctionLp μ 1 (f.map d)) x) =ᵐ[μ]
      fun x ↦ ∑ b ∈ f.range, d b * T (I b) x := by
    rw [hTsum]
    exact coeFn_finsetSum_mul μ f.range d (T ∘ I)
  have hpos : ∀ᵐ x ∂μ, ∀ b ∈ f.range, (T (I b) x : ℂ) = (T (I b) x).re ∧
      0 ≤ (T (I b) x).re := (eventually_all_finset f.range).2 fun b _ ↦
    hT.map_nonnegative _ (simpleFunctionFiber_nonnegative μ f b)
  filter_upwards [honeAE, hE id, hE c, hpos] with x hsum hf hc h
  let w (b : ℂ) := (T (I b) x).re
  have hw₀ : ∀ b ∈ f.range, 0 ≤ w b := fun b hb ↦ (h b hb).2
  have hw₁ : ∑ b ∈ f.range, w b = 1 := by
    change ∑ b ∈ f.range, Complex.re (T (I b) x) = 1
    rw [← Complex.re_sum, hsum, Complex.one_re]
  have hb (b : ℂ) (hb : b ∈ f.range) : ‖T (I b) x‖ = w b := by
    rw [(h b hb).1, Complex.norm_real, Real.norm_of_nonneg (hw₀ b hb)]
  have hnorm : ‖T (simpleFunctionLp μ 1 f) x‖ ≤ ∑ b ∈ f.range, w b * ‖b‖ := by
    have hf' : f.map id = f := SimpleFunc.ext fun _ ↦ rfl
    rw [hf'] at hf
    rw [hf]
    calc
      ‖∑ b ∈ f.range, b * T (I b) x‖ ≤ ∑ b ∈ f.range, ‖b * T (I b) x‖ := norm_sum_le _ _
      _ = ∑ b ∈ f.range, w b * ‖b‖ := by
        exact Finset.sum_congr rfl fun b hb' ↦ by rw [norm_mul, hb b hb', mul_comm]
  have hpow := (convexOn_pow (𝕜 := ℝ) k).map_sum_le hw₀ hw₁
    (fun b (_ : b ∈ f.range) ↦ show ‖b‖ ∈ Ici (0 : ℝ) from norm_nonneg b)
  calc
    ‖T (simpleFunctionLp μ 1 f) x‖ ^ k ≤ (∑ b ∈ f.range, w b * ‖b‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm k
    _ ≤ ∑ b ∈ f.range, w b * ‖b‖ ^ k := by
      simpa only [smul_eq_mul] using hpow
    _ = (T (simpleFunctionLp μ 1 (f.map c)) x).re := by
      rw [hc, Complex.re_sum]
      exact Finset.sum_congr rfl fun b hb ↦ by
        rw [(h b hb).1]
        change w b * ‖b‖ ^ k = Complex.re (((‖b‖ ^ k : ℝ) : ℂ) * (w b : ℂ))
        rw [← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

/-- The integral estimate for powers of the norm of a transformed simple
function. The left-hand integrand is integrable as part of the conclusion. -/
theorem IsProbabilityMarkovOperator.integral_norm_pow_le
    {T : Lp ℂ 1 μ →L[ℂ] Lp ℂ 1 μ} (hT : IsProbabilityMarkovOperator μ T)
    (f : SimpleFunc X ℂ) (k : ℕ) :
    Integrable (fun x ↦ ‖T (simpleFunctionLp μ 1 f) x‖ ^ k) μ ∧
      (∫ x, ‖T (simpleFunctionLp μ 1 f) x‖ ^ k ∂μ) ≤ ∫ x, ‖f x‖ ^ k ∂μ := by
  let g := f.map (fun b ↦ ((‖b‖ ^ k : ℝ) : ℂ))
  let y := T (simpleFunctionLp μ 1 f)
  let z := T (simpleFunctionLp μ 1 g)
  have hzi : Integrable (fun x ↦ z x) μ := (Lp.memLp z).integrable le_rfl
  have hzre : Integrable (fun x ↦ (z x).re) μ := Complex.reCLM.integrable_comp hzi
  have hyi : Integrable (fun x ↦ ‖y x‖ ^ k) μ := hzre.mono'
    ((Lp.memLp y).aestronglyMeasurable.norm.pow k) (by
      filter_upwards [hT.ae_norm_pow_le f k] with x hx
      simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hx)
  refine ⟨hyi, (integral_mono_ae hyi hzre (hT.ae_norm_pow_le f k)).trans_eq ?_⟩
  change (∫ x, RCLike.re (z x) ∂μ) = _
  rw [integral_re hzi]
  change Complex.re (∫ x, T (simpleFunctionLp μ 1 g) x ∂μ) = _
  rw [hT.integral_map]
  have hgf : (∫ x, (simpleFunctionLp μ 1 g) x ∂μ) =
      ∫ x, ((‖f x‖ ^ k : ℝ) : ℂ) ∂μ :=
    integral_congr_ae (simpleFunctionLp_coeFn μ 1 g)
  rw [hgf, integral_complex_ofReal, Complex.ofReal_re]

end JdLG
