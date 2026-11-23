/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import VdC.CubeDifference
public import VdC.RectangleMeasure
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Order.ProjIcc

/-! The permissible-pair formulations in the thesis's weak-mixing characterization. -/

@[expose] public section

open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace VdC

noncomputable section

/-- Each lag has a discrepancy limit along the same increasing averaging lengths. -/
def PermissiblePair (D : ℕ → ℕ → ℝ) (M : ℕ → ℕ) (δ : ℕ → ℝ) : Prop :=
  StrictMono M ∧ ∀ h, Tendsto (fun q => D h (M q)) atTop (𝓝 (δ h))

def MeanPermissibleDiscrepancyZero (D : ℕ → ℕ → ℝ) : Prop :=
  ∀ M δ, PermissiblePair D M δ → Tendsto (realCesaro δ) atTop (𝓝 0)

/-- Concatenate the two coordinate blocks at lag h+1. -/
def cubeLagPair {d e : ℕ} (x : ℕ → Cube d) (y : ℕ → Cube e) (h n : ℕ) : Cube (d + e) :=
  Fin.addCases (x n) (y (n + (h + 1)))

def jointDiscrepancy {d e : ℕ} (x : ℕ → Cube d) (y : ℕ → Cube e) (h N : ℕ) : ℝ :=
  rectangleDiscrepancy (cubeLagPair x y h) N

def ThesisCrossDiscrepancy {d : ℕ} (x : ℕ → Cube d) : Prop :=
  ∀ e : ℕ, 0 < e → ∀ y : ℕ → Cube e, Equidistributed (cubeLebesgue e) y →
    MeanPermissibleDiscrepancyZero (jointDiscrepancy x y)

def ThesisSelfDiscrepancy {d : ℕ} (x : ℕ → Cube d) : Prop :=
  MeanPermissibleDiscrepancyZero (jointDiscrepancy x x)

def ThesisDifferenceDiscrepancy {d : ℕ} (x : ℕ → Cube d) : Prop :=
  MeanPermissibleDiscrepancyZero (differenceDiscrepancy (fun n => cubeToTorus (x n)))

/-- The discrepancy limits can always be made to exist by one further extraction. -/
theorem exists_permissible_pair_refinement {D : ℕ → ℕ → ℝ} {M : ℕ → ℕ}
    (hM : StrictMono M) (hB : ∀ h N, D h N ∈ Set.Icc (0 : ℝ) 1) :
    ∃ φ δ, StrictMono φ ∧ PermissiblePair D (M ∘ φ) δ := by
  obtain ⟨φ, c, hφ, hc⟩ := exists_common_subsequence
    (fun (q h : ℕ) => (D h (M q) : ℂ)) (fun h =>
    ⟨1, zero_le_one, fun n => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hB h (M n)).1]
        using (hB h (M n)).2⟩)
  refine ⟨φ, fun h => (c h).re, hφ, hM.comp hφ, fun h => ?_⟩
  have hh := Complex.continuous_re.continuousAt.tendsto.comp (hc h)
  simpa only [Function.comp_def, Complex.ofReal_re] using hh

private theorem nearlyWeakMixing_of_permissible_discrepancies {u : ℕ → ℂ}
    (hu : BoundedSeq u) (D : ℕ → ℕ → ℝ) (hB : ∀ h N, D h N ∈ Set.Icc (0 : ℝ) 1)
    (K : ℝ) (hbound : ∀ h N, ‖corr u u (h+1) N‖ ≤ K * D h N)
    (hD : MeanPermissibleDiscrepancyZero D) : NearlyWeakMixing u := by
  apply nearlyWeakMixing_of_self_mean hu
  intro M r hM hr
  obtain ⟨φ, δ, hφ, hp⟩ := exists_permissible_pair_refinement hM hB
  have hlim := (hD _ _ hp).const_mul K
  rw [mul_zero] at hlim
  have hg (h : ℕ) : ‖r (h+1)‖ ≤ K * δ h := by
    exact le_of_tendsto_of_tendsto ((hr (h+1)).comp hφ.tendsto_atTop).norm
      ((hp.2 h).const_mul K) (Eventually.of_forall fun q => hbound h ((M ∘ φ) q))
  apply squeeze_zero (realCesaro_nonneg (fun _ => norm_nonneg _)) _ hlim
  intro H
  rw [← realCesaro_const_mul]
  exact realCesaro_mono hg H

/-- The difference-discrepancy condition implies weak mixing, (iv) → (i).
The extraction here is from an arbitrary permissible autocorrelation subsequence. -/
theorem weakMixing_of_thesisDifferenceDiscrepancy {d : ℕ} {x : ℕ → Cube d}
    (hx : ThesisDifferenceDiscrepancy x) : WeaklyMixingDistribution (cubeLebesgue d) x := by
  apply (cube_weakMixing_iff_characters x).2
  intro m hm
  let z : ℕ → Torus d := fun n => cubeToTorus (x n)
  obtain ⟨K, _, hbound⟩ := characterRectangleEstimate_all z m hm
  apply nearlyWeakMixing_of_permissible_discrepancies (bounded_test (torusCharacter m) z)
    (differenceDiscrepancy z) (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) K _ hx
  intro h N
  simpa only [corr, torusCharacter_point_sub] using hbound h N

private theorem pair_character_eq {d e : ℕ} (a : Fin d → ℤ) (b : Fin e → ℤ)
    (x : Cube d) (y : Cube e) :
    torusCharacter (Fin.addCases a b) (cubeToTorus (Fin.addCases x y)) =
      torusCharacter a (cubeToTorus x) * torusCharacter b (cubeToTorus y) := by
  rw [torusCharacter_apply, Fin.prod_univ_add]
  simp only [cubeToTorus, Fin.addCases_left, Fin.addCases_right, torusCharacter_apply]

private theorem pair_frequency_ne_zero {d e : ℕ} {a : Fin d → ℤ} {b : Fin e → ℤ}
    (ha : a ≠ 0) : (Fin.addCases a b : Fin (d + e) → ℤ) ≠ 0 := by
  intro h
  exact ha (funext fun i => by simpa using congrFun h (Fin.castAdd e i))

/-- The joint self-discrepancy condition implies weak mixing, (iii) → (i). -/
theorem weakMixing_of_thesisSelfDiscrepancy {d : ℕ} {x : ℕ → Cube d}
    (hx : ThesisSelfDiscrepancy x) : WeaklyMixingDistribution (cubeLebesgue d) x := by
  apply (cube_weakMixing_iff_characters x).2
  intro m hm
  let k : Fin (d+d) → ℤ := Fin.addCases (-m) m
  have hk : k ≠ 0 := pair_frequency_ne_zero (neg_ne_zero.mpr hm)
  apply nearlyWeakMixing_of_permissible_discrepancies
    (bounded_test (torusCharacter m) (fun n => cubeToTorus (x n)))
    (jointDiscrepancy x x) (fun _ _ => rectangleDiscrepancy_mem_Icc _ _)
    (fourierDiscrepancyConstant k) _ hx
  intro h N
  have he (n : ℕ) :
      torusCharacter k (cubeToTorus (cubeLagPair x x h n)) =
        torusCharacter m (cubeToTorus (x (n+(h+1)))) * star (torusCharacter m (cubeToTorus (x n))) := by
    change torusCharacter (Fin.addCases (-m) m)
      (cubeToTorus (Fin.addCases (x n) (x (n + (h + 1))))) = _
    rw [pair_character_eq, torusCharacter_neg, ContinuousMap.star_apply, mul_comm]
  have hb := finite_fourier_rectangle_bound k hk (cubeLagPair x x h) N
  change ‖cesaro (fun n => torusCharacter k (cubeToTorus (cubeLagPair x x h n))) N‖ ≤ _ at hb
  simpa only [corr, ← he, jointDiscrepancy] using hb

/-- The cross condition tested at the self sequence, once that sequence is uniformly distributed. -/
theorem thesisSelfDiscrepancy_of_cross_of_equidistributed {d : ℕ} (hd : 0 < d)
    {x : ℕ → Cube d} (hx : ThesisCrossDiscrepancy x) (hU : Equidistributed (cubeLebesgue d) x) :
    ThesisSelfDiscrepancy x := hx d hd x hU

private theorem tendsto_zero_of_permissible_bound {u : ℕ → ℂ} (hu : BoundedSeq u)
    {D : ℕ → ℕ → ℝ} (hB : ∀ h N, D h N ∈ Set.Icc (0 : ℝ) 1)
    (hD : MeanPermissibleDiscrepancyZero D) (K : ℝ)
    (hbound : ∀ h N, ‖u N‖ ≤ K * D h N) : Tendsto u atTop (𝓝 0) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ψ, _, hψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨φ, c, hφ, hc⟩ := exists_common_subsequence
    (fun (q : ℕ) (_ : Unit) => u ((ns ∘ ψ) q)) (fun _ => by
      obtain ⟨C, hC, hC'⟩ := hu
      exact ⟨C, hC, fun _ => hC' _⟩)
  obtain ⟨τ, δ, hτ, hp⟩ := exists_permissible_pair_refinement (hψ.comp hφ) hB
  have huc := (hc ()).comp hτ.tendsto_atTop
  have h' (h : ℕ) : ‖c ()‖ ≤ K * δ h :=
    le_of_tendsto_of_tendsto huc.norm ((hp.2 h).const_mul K)
      (Eventually.of_forall fun _ => hbound h _)
  have hlimit : ‖c ()‖ ≤ 0 := by
    have hr := (hD _ _ hp).const_mul K
    rw [mul_zero] at hr
    apply le_of_tendsto_of_tendsto (realCesaro_const_tendsto ‖c ()‖) hr
    filter_upwards [] with H
    rw [← realCesaro_const_mul]
    exact realCesaro_mono h' H
  have hz : c () = 0 := norm_le_zero_iff.mp hlimit
  rw [hz] at huc
  exact ⟨ψ ∘ φ ∘ τ, huc⟩

/-- The cross condition already forces the unshifted marginal to be uniformly distributed
as soon as there is one uniformly distributed comparison sequence of positive dimension. -/
theorem equidistributed_of_thesisCross_with_comparison {d e : ℕ} (he : 0 < e)
    {x : ℕ → Cube d} (hx : ThesisCrossDiscrepancy x) (y : ℕ → Cube e)
    (hy : Equidistributed (cubeLebesgue e) y) : Equidistributed (cubeLebesgue d) x := by
  apply equidistributed_of_cubeToTorus
  apply (equidistributed_torus_iff _).2
  intro m hm
  let u (N : ℕ) : ℂ := cesaro (fun n => torusCharacter m (cubeToTorus (x n))) N
  let k : Fin (d + e) → ℤ := Fin.addCases m 0
  have hk : k ≠ 0 := pair_frequency_ne_zero hm
  refine tendsto_zero_of_permissible_bound (u := u) ⟨1, zero_le_one, fun N => ?_⟩
    (fun _ _ => rectangleDiscrepancy_mem_Icc _ _) (hx e he y hy)
    (fourierDiscrepancyConstant k) ?_
  · exact norm_cesaro_le _ zero_le_one (fun n => (torusCharacter_norm m _).le) N
  · intro h N
    have hb := finite_fourier_rectangle_bound k hk (cubeLagPair x y h) N
    change ‖cesaro (fun n => torusCharacter k (cubeToTorus (cubeLagPair x y h n))) N‖ ≤ _ at hb
    have heq (n : ℕ) :
        torusCharacter k (cubeToTorus (cubeLagPair x y h n)) = torusCharacter m (cubeToTorus (x n)) := by
      change torusCharacter (Fin.addCases m 0) (cubeToTorus (Fin.addCases (x n) (y (n+(h+1))))) = _
      rw [pair_character_eq, torusCharacter_zero]
      simp
    simpa only [heq, u, jointDiscrepancy] using hb

/-- There exists a uniformly distributed sequence in the one-dimensional cube. -/
theorem exists_equidistributed_one_cube : ∃ y : ℕ → Cube 1, Equidistributed (cubeLebesgue 1) y := by
  let c : UnitAddCircle := ((Real.sqrt 2 : ℝ) : UnitAddCircle)
  let y (n : ℕ) (_ : Fin 1) : UnitInterval := unitRepresentative (n • c)
  refine ⟨y, equidistributed_of_cubeToTorus ((equidistributed_torus_iff _).2 ?_)⟩
  intro m hm
  have hnon : m 0 ≠ 0 := by
    intro h
    exact hm (funext fun i => by change m i = 0; rw [Fin.eq_zero i]; exact h)
  let ω : ℂ := fourier (m 0) c
  have hω1 : ‖ω‖ = 1 := by simp [ω, fourier_apply]
  have hω : ω ≠ 1 := by
    intro h
    have hc' : (m 0) • c = 0 := by
      apply AddCircle.injective_toCircle one_ne_zero
      apply Subtype.ext
      simpa [ω, fourier_apply] using h
    rw [show c = ((Real.sqrt 2 : ℝ) : UnitAddCircle) from rfl, ← AddCircle.coe_zsmul,
      AddCircle.coe_eq_zero_iff] at hc'
    obtain ⟨j, hj⟩ := hc'
    exact (irrational_iff_ne_rational _).1 irrational_sqrt_two j (m 0) hnon
      ((eq_div_iff (by exact_mod_cast hnon)).2 (by simpa [zsmul_eq_mul, mul_comm] using hj.symm))
  have hz (n : ℕ) : fourier (m 0) (n • c) = ω ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      simp only [ω, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
  have hf (n : ℕ) : torusCharacter m (cubeToTorus (y n)) = ω ^ n := by
    simpa only [torusCharacter_apply, Fin.prod_univ_one, cubeToTorus, y, unitRepresentative_coe] using hz n
  simp_rw [hf]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖ω - 1‖))
  rw [cesaro, geom_sum_eq hω, norm_div, norm_div, Complex.norm_natCast]
  have hωp : ‖ω ^ N - 1‖ ≤ 2 := by
    simpa only [norm_pow, hω1, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (ω ^ N) 1
  exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hωp (norm_nonneg _)) (by positivity)

/-- The cross condition implies the joint self condition, (ii) → (iii). -/
theorem thesisSelfDiscrepancy_of_cross {d : ℕ} (hd : 0 < d) {x : ℕ → Cube d}
    (hx : ThesisCrossDiscrepancy x) : ThesisSelfDiscrepancy x := by
  obtain ⟨y, hy⟩ := exists_equidistributed_one_cube
  exact thesisSelfDiscrepancy_of_cross_of_equidistributed hd hx
    (equidistributed_of_thesisCross_with_comparison (by decide) hx y hy)

/-- The cube probability assigned to the first N observations, for N positive. -/
def cubeEmpirical {d : ℕ} (u : ℕ → Cube d) (N : ℕ) (hN : 0 < N) :
    ProbabilityMeasure (Cube d) := by
  refine ⟨(N : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range N, Measure.dirac (u n), ⟨?_⟩⟩
  rw [smul_apply, sum_apply, smul_eq_mul]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

theorem integral_cubeEmpirical {d : ℕ} (u : ℕ → Cube d) (N : ℕ) (hN : 0 < N)
    (f : Cube d → ℂ) :
    (∫ x, f x ∂(cubeEmpirical u N hN : Measure (Cube d))) = cesaro (fun n => f (u n)) N := by
  change (∫ x, f x ∂((N : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range N, Measure.dirac (u n))) = _
  rw [integral_smul_measure, integral_finsetSum_measure (fun _ _ => integrable_dirac eNorm_lt_top), cesaro]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]

theorem cubeEmpirical_real_closedRectangle {d : ℕ} (u : ℕ → Cube d) (N : ℕ) (hN : 0 < N)
    (a b : Cube d) :
    (cubeEmpirical u N hN : Measure (Cube d)).real (closedRectangle a b) =
      rectangleFrequency u N a b := by
  classical
  let s := closedRectangle a b
  have h := integral_cubeEmpirical u N hN (s.indicator fun _ => (1 : ℂ))
  rw [integral_indicator (measurableSet_closedRectangle a b), setIntegral_const,
    Complex.real_smul, mul_one] at h
  apply_fun Complex.re at h
  rw [rectangleFrequency_eq_indicator_average]
  simpa [s, cesaro, realCesaro, Set.indicator, ← Complex.ofReal_div, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast] using h

private theorem cube_ae_coordinate_ne {d : ℕ} (i : Fin d) (a : UnitInterval) :
    ∀ᵐ x ∂cubeLebesgue d, x i ≠ a := by
  have h : ∀ᵐ t ∂unitIntervalLebesgue, t ≠ a := by
    apply ae_iff.mpr
    change unitIntervalLebesgue {t : UnitInterval | ¬t ≠ a} = 0
    rw [show {t : UnitInterval | ¬t ≠ a} = {a} by ext t; simp,
      unitIntervalLebesgue, comap_subtype_coe_apply measurableSet_Icc]
    simp
  exact (measurePreserving_eval (μ := fun _ : Fin d => unitIntervalLebesgue) i).quasiMeasurePreserving.ae h

/-- All closed boxes are continuity sets of cube Lebesgue measure. -/
theorem cubeLebesgue_frontier_closedRectangle {d : ℕ} (a b : Cube d) :
    cubeLebesgue d (frontier (closedRectangle a b)) = 0 := by
  have hclosed : IsClosed (closedRectangle a b) := by
    rw [show closedRectangle a b = ⋂ i, (fun x : Cube d => (x i : ℝ)) ⁻¹'
      Set.Icc (a i : ℝ) (b i : ℝ) by
      ext x
      simp only [closedRectangle, Set.mem_univ_pi, Set.mem_iInter, Set.mem_preimage]]
    exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_subtype_val.comp (continuous_apply i))
  let U := ⋂ i, (fun x : Cube d => (x i : ℝ)) ⁻¹' Set.Ioo (a i : ℝ) (b i : ℝ)
  have hU : IsOpen U := isOpen_iInter_of_finite fun i =>
    isOpen_Ioo.preimage (continuous_subtype_val.comp (continuous_apply i))
  have hUB : U ⊆ closedRectangle a b := by
    intro x hx
    rw [closedRectangle, Set.mem_univ_pi]
    intro i
    exact Set.Ioo_subset_Icc_self (Set.mem_iInter.mp hx i)
  have ha : ∀ᵐ x ∂cubeLebesgue d, ∀ i, x i ≠ a i :=
    ae_all_iff.mpr fun i => cube_ae_coordinate_ne i (a i)
  have hb : ∀ᵐ x ∂cubeLebesgue d, ∀ i, x i ≠ b i :=
    ae_all_iff.mpr fun i => cube_ae_coordinate_ne i (b i)
  have h : ∀ᵐ x ∂cubeLebesgue d, x ∉ frontier (closedRectangle a b) := by
    filter_upwards [ha, hb] with x hxa hxb
    intro hxf
    rw [frontier, hclosed.closure_eq] at hxf
    have hxU : x ∈ U := by
      apply Set.mem_iInter.mpr
      intro i
      have h := Set.mem_univ_pi.mp hxf.1 i
      change (a i : ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ (b i : ℝ) at h
      exact ⟨lt_of_le_of_ne h.1 (fun eq => hxa i (Subtype.ext eq.symm)),
        lt_of_le_of_ne h.2 (fun eq => hxb i (Subtype.ext eq))⟩
    exact hxf.2 (interior_maximal hUB hU hxU)
  simpa using ae_iff.mp h

def uniformCube (d : ℕ) : ProbabilityMeasure (Cube d) := ⟨cubeLebesgue d, inferInstance⟩

theorem tendsto_rectangleFrequency_of_empirical_tendsto {d : ℕ} {ι : Type*} {l : Filter ι}
    {u : ι → ℕ → Cube d} {N : ι → ℕ} {hN : ∀ q, 0 < N q}
    (ht : Tendsto (fun q => cubeEmpirical (u q) (N q) (hN q)) l (𝓝 (uniformCube d)))
    (a b : Cube d) :
    Tendsto (fun q => rectangleFrequency (u q) (N q) a b) l (𝓝 (rectangleVolume a b)) := by
  have hB := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto ht
    (E := closedRectangle a b) (by
      change (cubeLebesgue d (frontier (closedRectangle a b))).toNNReal = 0
      rw [cubeLebesgue_frontier_closedRectangle]; rfl)
  have h := NNReal.continuous_coe.continuousAt.tendsto.comp hB
  change Tendsto (fun q => (cubeEmpirical (u q) (N q) (hN q) : Measure (Cube d)).real
    (closedRectangle a b)) l (𝓝 ((cubeLebesgue d).real (closedRectangle a b))) at h
  simpa only [cubeEmpirical_real_closedRectangle, ← rectangleVolume_eq_measure] using h

private def translateEndpoints {d : ℕ} (p : Cube d) (t : ℝ) : Cube d :=
  fun i => Set.projIcc 0 1 zero_le_one ((p i : ℝ) + t)

private theorem continuous_translateEndpoints {d : ℕ} (p : Cube d) :
    Continuous (translateEndpoints p) := by
  exact continuous_pi fun i => continuous_projIcc.comp (continuous_const.add continuous_id)

@[simp] private theorem translateEndpoints_zero {d : ℕ} (p : Cube d) :
    translateEndpoints p 0 = p := by
  ext i
  simp [translateEndpoints]

private theorem rectangleVolume_continuous {d : ℕ} :
    Continuous (fun p : Cube d × Cube d => rectangleVolume p.1 p.2) := by
  unfold rectangleVolume
  apply continuous_finsetProd
  intro i _
  exact continuous_const.max
    ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)).sub
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)))

private theorem translateEndpoints_bounds {d : ℕ} {x y : Cube d} {r : ℝ} (hx : dist y x < r) :
    ∀ i, ((translateEndpoints x (-r) i : UnitInterval) : ℝ) ≤ (y i : ℝ) ∧
      (y i : ℝ) ≤ ((translateEndpoints x r i : UnitInterval) : ℝ) := by
  intro i
  have hi : dist (y i) (x i) < r := (dist_le_pi_dist y x i).trans_lt hx
  change dist (y i : ℝ) (x i : ℝ) < r at hi
  rw [Real.dist_eq, abs_lt] at hi
  change max 0 (min 1 ((x i : ℝ) + -r)) ≤ (y i : ℝ) ∧
    (y i : ℝ) ≤ max 0 (min 1 ((x i : ℝ) + r))
  constructor
  · exact max_le (y i).property.1 ((min_le_right _ _).trans (by linarith [hi.1]))
  · exact (le_min (y i).property.2 (by linarith [hi.2])).trans (le_max_right _ _)

private theorem closedRectangle_subset {d : ℕ} {a b c e : Cube d}
    (ha : ∀ i, (c i : ℝ) ≤ a i) (hb : ∀ i, (b i : ℝ) ≤ e i) :
    closedRectangle a b ⊆ closedRectangle c e := by
  intro x hx
  apply Set.mem_univ_pi.mpr
  intro i
  have hi := Set.mem_univ_pi.mp hx i
  exact ⟨(ha i).trans hi.1, hi.2.trans (hb i)⟩

private theorem rectangleVolume_mono {d : ℕ} {a b c e : Cube d}
    (h : closedRectangle a b ⊆ closedRectangle c e) :
    rectangleVolume a b ≤ rectangleVolume c e := by
  rw [rectangleVolume_eq_measure, rectangleVolume_eq_measure]
  exact measureReal_mono h

private theorem rectangleFrequency_mono {d : ℕ} (u : ℕ → Cube d) (N : ℕ)
    {a b c e : Cube d} (h : closedRectangle a b ⊆ closedRectangle c e) :
    rectangleFrequency u N a b ≤ rectangleFrequency u N c e := by
  classical
  rw [rectangleFrequency_eq_indicator_average, rectangleFrequency_eq_indicator_average]
  apply realCesaro_mono
  intro j
  by_cases hj : u j ∈ closedRectangle a b
  · simp [hj, h hj]
  · by_cases hj' : u j ∈ closedRectangle c e <;> simp [hj, hj']

/-- Convergence on fixed closed boxes implies convergence uniformly over all boxes.
The comparison uses finite lower and upper brackets for the compact endpoint space. -/
theorem tendsto_rectangleDiscrepancy_of_frequency {d : ℕ} {ι : Type*} {l : Filter ι}
    (u : ι → ℕ → Cube d) (N : ι → ℕ)
    (hf : ∀ a b : Cube d, Tendsto (fun q => rectangleFrequency (u q) (N q) a b) l
      (𝓝 (rectangleVolume a b))) :
    Tendsto (fun q => rectangleDiscrepancy (u q) (N q)) l (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  let volDiff (p : Cube d × Cube d) (t : ℝ) : ℝ :=
    rectangleVolume (translateEndpoints p.1 (-t)) (translateEndpoints p.2 t) -
      rectangleVolume (translateEndpoints p.1 t) (translateEndpoints p.2 (-t))
  have hc (p : Cube d × Cube d) : Continuous (volDiff p) := by
    unfold volDiff
    apply Continuous.sub
    · exact rectangleVolume_continuous.comp
        (((continuous_translateEndpoints p.1).comp continuous_neg).prodMk (continuous_translateEndpoints p.2))
    · exact rectangleVolume_continuous.comp
        ((continuous_translateEndpoints p.1).prodMk ((continuous_translateEndpoints p.2).comp continuous_neg))
  have hchoose (p : Cube d × Cube d) : ∃ r : ℝ, 0 < r ∧ volDiff p r < ε/3 := by
    have hv : volDiff p 0 = 0 := by simp [volDiff]
    have hlt := (hc p).continuousAt.tendsto.eventually
      (gt_mem_nhds (show volDiff p 0 < ε/3 by rw [hv]; positivity))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp hlt
    refine ⟨δ/2, by positivity, hδ' ?_⟩
    change dist (δ/2) 0 < δ
    rw [Real.dist_eq, sub_zero, abs_of_pos (show 0 < δ/2 by positivity)]
    linarith
  choose r hr hvol using hchoose
  let U (p : Cube d × Cube d) := Metric.ball p (r p)
  have hcover : (Set.univ : Set (Cube d × Cube d)) ⊆ ⋃ p, U p :=
    fun p _ => Set.mem_iUnion.mpr ⟨p, Metric.mem_ball_self (hr p)⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  have hfe (p : Cube d × Cube d) : ∀ᶠ q in l,
      |rectangleFrequency (u q) (N q) (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p)) -
        rectangleVolume (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p))| < ε/3 ∧
      |rectangleFrequency (u q) (N q) (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p)) -
        rectangleVolume (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p))| < ε/3 := by
    have hup := (Metric.tendsto_nhds.mp
      (hf (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p)))) (ε/3) (by positivity)
    have hlo := (Metric.tendsto_nhds.mp
      (hf (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p)))) (ε/3) (by positivity)
    exact (hup.and hlo).mono (fun q h => by simpa only [Real.dist_eq] using h)
  filter_upwards [(eventually_all_finset T).2 (fun p _ => hfe p)] with q hq
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (rectangleDiscrepancy_mem_Icc _ _).1]
  suffices h : rectangleDiscrepancy (u q) (N q) ≤ 2*ε/3 by linarith
  unfold rectangleDiscrepancy
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨⟨a,b⟩, rfl⟩
  obtain ⟨p, hpT, hp⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ (a,b)))
  have hdist : max (dist a p.1) (dist b p.2) < r p := hp
  have ha := translateEndpoints_bounds (max_lt_iff.mp hdist).1
  have hb := translateEndpoints_bounds (max_lt_iff.mp hdist).2
  have hlo : closedRectangle (translateEndpoints p.1 (r p)) (translateEndpoints p.2 (-r p)) ⊆
      closedRectangle a b := closedRectangle_subset (fun i => (ha i).2) (fun i => (hb i).1)
  have hhi : closedRectangle a b ⊆
      closedRectangle (translateEndpoints p.1 (-r p)) (translateEndpoints p.2 (r p)) :=
    closedRectangle_subset (fun i => (ha i).1) (fun i => (hb i).2)
  have hvlo := rectangleVolume_mono hlo
  have hvhi := rectangleVolume_mono hhi
  have hflo := rectangleFrequency_mono (u q) (N q) hlo
  have hfhi := rectangleFrequency_mono (u q) (N q) hhi
  have hv := hvol p
  unfold volDiff at hv
  have hq' := hq p hpT
  apply abs_le.mpr
  constructor
  · linarith [(abs_lt.mp hq'.2).1]
  · linarith [(abs_lt.mp hq'.1).2]

/-- Uniform distribution on the cube implies vanishing closed-rectangle discrepancy. -/
theorem tendsto_rectangleDiscrepancy_of_equidistributed {d : ℕ} {u : ℕ → Cube d}
    (hu : Equidistributed (cubeLebesgue d) u) :
    Tendsto (rectangleDiscrepancy u) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => cubeEmpirical u (n+1) (Nat.succ_pos n)) atTop (𝓝 (uniformCube d)) := by
    apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
    intro f
    simp_rw [integral_cubeEmpirical]
    exact (hu f.toContinuousMap).comp (tendsto_add_atTop_nat 1)
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact tendsto_rectangleDiscrepancy_of_frequency (fun _ => u) (fun n => n+1)
    (tendsto_rectangleFrequency_of_empirical_tendsto ht)

/-- The finite Fourier estimate and Weyl's criterion give the converse on the
closed cube, with the torus-to-cube lift handling the endpoints. -/
theorem equidistributed_of_rectangleDiscrepancy_tendsto_zero {d : ℕ} {u : ℕ → Cube d}
    (hu : Tendsto (rectangleDiscrepancy u) atTop (𝓝 0)) :
    Equidistributed (cubeLebesgue d) u := by
  apply equidistributed_of_cubeToTorus
  apply (equidistributed_torus_iff _).2
  intro m hm
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (finite_fourier_rectangle_bound m hm u) ?_
  simpa only [mul_zero] using hu.const_mul (fourierDiscrepancyConstant m)

theorem equidistributed_iff_rectangleDiscrepancy_tendsto_zero {d : ℕ} (u : ℕ → Cube d) :
    Equidistributed (cubeLebesgue d) u ↔ Tendsto (rectangleDiscrepancy u) atTop (𝓝 0) :=
  ⟨tendsto_rectangleDiscrepancy_of_equidistributed, equidistributed_of_rectangleDiscrepancy_tendsto_zero⟩

private def pullbackTorus {d : ℕ} (g : C(Torus d, ℂ)) : C(Cube d, ℂ) :=
  g.comp ⟨cubeToTorus, continuous_cubeToTorus d⟩

private def integralPullbackCLM {d : ℕ} (μ : ProbabilityMeasure (Cube d)) :
    C(Torus d, ℂ) →L[ℂ] ℂ := by
  let I : C(Torus d, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => testMean (μ : Measure (Cube d)) (pullbackTorus g)
      map_add' := fun f g => testMean_add _ (pullbackTorus f) (pullbackTorus g)
      map_smul' := fun c f => testMean_smul _ c (pullbackTorus f) }
  refine I.mkContinuous 1 fun g => ?_
  change ‖∫ x, g (cubeToTorus x) ∂(μ : Measure (Cube d))‖ ≤ 1 * ‖g‖
  simpa using norm_integral_le_of_norm_le_const (ae_of_all (μ : Measure (Cube d))
    fun x => g.norm_coe_le_norm (cubeToTorus x))

private theorem integrals_pullback_eq_of_characters {d : ℕ} (μ : ProbabilityMeasure (Cube d))
    (h : ∀ m : Fin d → ℤ, m ≠ 0 →
      testMean (μ : Measure (Cube d)) (pullbackTorus (torusCharacter m)) = 0) :
    ∀ g : C(Torus d, ℂ), testMean (μ : Measure (Cube d)) (pullbackTorus g) =
      testMean (cubeLebesgue d) (pullbackTorus g) := by
  let Δ := integralPullbackCLM μ - integralPullbackCLM (uniformCube d)
  let K := LinearMap.ker Δ.toLinearMap
  have hc : IsClosed (K : Set C(Torus d, ℂ)) := isClosed_eq Δ.continuous continuous_const
  have hs : Submodule.span ℂ (Set.range (torusCharacter (d := d))) ≤ K := by
    apply Submodule.span_le.2
    rintro _ ⟨m, rfl⟩
    change testMean (μ : Measure (Cube d)) (pullbackTorus (torusCharacter m)) -
      testMean (cubeLebesgue d) (pullbackTorus (torusCharacter m)) = 0
    apply sub_eq_zero.mpr
    by_cases hm : m = 0
    · subst m
      rw [torusCharacter_zero, show pullbackTorus (1 : C(Torus d, ℂ)) = 1 from by ext; rfl]
      simp [testMean]
    rw [h m hm]
    have hh : testMean (cubeLebesgue d) (pullbackTorus (torusCharacter m)) =
        testMean (torusHaar d) (torusCharacter m) := by
      unfold testMean
      rw [← (cubeToTorus_measurePreserving d).map_eq,
        integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable
          (torusCharacter m).continuous.stronglyMeasurable]
      rfl
    simp [hh, testMean_torusCharacter, hm]
  have htop := (Submodule.span ℂ (Set.range (torusCharacter (d := d)))).topologicalClosure_minimal hs hc
  rw [torusCharacters_dense] at htop
  intro g
  have hg := htop (Submodule.mem_top : g ∈ (⊤ : Submodule ℂ C(Torus d, ℂ)))
  change testMean (μ : Measure (Cube d)) (pullbackTorus g) -
    testMean (cubeLebesgue d) (pullbackTorus g) = 0 at hg
  exact sub_eq_zero.mp hg

private theorem measure_is_uniform_of_characters {d : ℕ} (μ : ProbabilityMeasure (Cube d))
    (h : ∀ m : Fin d → ℤ, m ≠ 0 →
      testMean (μ : Measure (Cube d)) (pullbackTorus (torusCharacter m)) = 0) : μ = uniformCube d := by
  have ht : Tendsto (fun _ : ℕ => μ) atTop (𝓝 (uniformCube d)) := by
    apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
    intro f
    let F := f.toContinuousMap
    let M : Measure (Cube d) := μ
    have hcut (K : ℕ) (g : C(Cube d, ℂ)) : testMean M (cubeCutoffTest K g) =
        testMean (cubeLebesgue d) (cubeCutoffTest K g) := by
      obtain ⟨p, hp⟩ := exists_cubeCutoff_descend K g
      have hh : pullbackTorus p = cubeCutoffTest K g := by ext x; exact hp x
      simpa only [hh] using integrals_pullback_eq_of_characters μ h p
    let e (K : ℕ) (x : Cube d) : ℝ := 1 - cubeCutoff K x
    have he (K : ℕ) : (∫ x, e K x ∂M) = ∫ x, e K x ∂cubeLebesgue d := by
      have hh := hcut K 1
      unfold testMean at hh
      change (∫ x, (1 : ℂ) * (cubeCutoff K x : ℂ) ∂M) =
        ∫ x, (1 : ℂ) * (cubeCutoff K x : ℂ) ∂cubeLebesgue d at hh
      simp only [one_mul, integral_complex_ofReal] at hh
      unfold e
      rw [integral_sub (integrable_const _)
          ((continuous_cubeCutoff K).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        integral_sub (integrable_const _)
          ((continuous_cubeCutoff K).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
      rw [Complex.ofReal_injective hh]
    have hnorm (K : ℕ) :
        ‖testMean M (cubeCutoffTest K F) - testMean M F‖ ≤ ‖F‖ * ∫ x, e K x ∂M := by
      rw [norm_sub_rev, ← testMean_sub]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      apply integral_mono
      · exact (test_integrable M (F - cubeCutoffTest K F)).norm
      · exact (continuous_const.mul (continuous_const.sub (continuous_cubeCutoff K))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      intro x
      change ‖F x - cubeCutoffTest K F x‖ ≤ ‖F‖ * (1 - cubeCutoff K x)
      rw [norm_sub_cubeCutoffTest]
      exact mul_le_mul_of_nonneg_right (F.norm_coe_le_norm x) (sub_nonneg.mpr (cubeCutoff_le_one K x))
    have hlim : Tendsto (fun K => testMean M (cubeCutoffTest K F)) atTop (𝓝 (testMean M F)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.2
      have h0 := (tendsto_cutoffDeficit_integral d).const_mul ‖F‖
      rw [mul_zero] at h0
      apply squeeze_zero (fun _ => norm_nonneg _) _ h0
      intro K
      rw [← he K]
      exact hnorm K
    have hlim' := tendsto_testMean_cubeCutoffTest F
    simp_rw [hcut] at hlim
    have hf := tendsto_nhds_unique hlim hlim'
    change (∫ x, f x ∂M) = (∫ x, f x ∂cubeLebesgue d) at hf
    change Tendsto (fun _ : ℕ => ∫ x, f x ∂M) atTop (𝓝 (∫ x, f x ∂cubeLebesgue d))
    rw [← hf]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds ht

private theorem continuous_probability_test {d : ℕ} (f : C(Cube d, ℂ)) :
    Continuous (fun μ : ProbabilityMeasure (Cube d) => testMean (μ : Measure (Cube d)) f) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 tendsto_id
    ((ContinuousMap.equivBoundedOfCompact (Cube d) ℂ) f)

/-- A qualitative inverse discrepancy estimate. For every tolerance, only finitely
many Fourier coefficients are needed, with positive weights independent of the sample. -/
theorem finite_character_discrepancy_bound {d : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ((Fin d → ℤ) × ℝ), (∀ p ∈ S, p.1 ≠ 0 ∧ 0 < p.2) ∧
      ∀ (u : ℕ → Cube d) (N : ℕ), 0 < N →
      rectangleDiscrepancy u N ≤ ε + ∑ p ∈ S,
        ‖cesaro (fun n => torusCharacter p.1 (cubeToTorus (u n))) N‖ / p.2 := by
  classical
  let I := (ℕ → Cube d) × ℕ+
  let E (q : I) : ProbabilityMeasure (Cube d) := cubeEmpirical q.1 q.2.val q.2.property
  let A : Set (ProbabilityMeasure (Cube d)) :=
    E '' {q : I | ε ≤ rectangleDiscrepancy q.1 q.2.val}
  let l : Filter I := comap E (𝓝 (uniformCube d))
  have he : Tendsto E l (𝓝 (uniformCube d)) := tendsto_comap
  have hd : Tendsto (fun q : I => rectangleDiscrepancy q.1 q.2.val) l (𝓝 0) :=
    tendsto_rectangleDiscrepancy_of_frequency _ _ (tendsto_rectangleFrequency_of_empirical_tendsto he)
  have hnA : uniformCube d ∉ closure A := by
    intro hc
    have hp := eventually_comap.mp (hd.eventually (gt_mem_nhds hε))
    obtain ⟨ν, hν, hνA⟩ := (mem_closure_iff_nhds.mp hc) _ hp
    obtain ⟨q, hq, heq⟩ := hνA
    exact (not_lt_of_ge hq) (hν q heq)
  let coeff (p : Fin d → ℤ) (ν : ProbabilityMeasure (Cube d)) :=
    testMean (ν : Measure (Cube d)) (pullbackTorus (torusCharacter p))
  have hm (ν : closure A) : ∃ m : Fin d → ℤ, m ≠ 0 ∧ 0 < ‖coeff m ν.1‖ := by
    by_contra! h
    have heq := measure_is_uniform_of_characters ν.1 (fun m hm => norm_le_zero_iff.mp (h m hm))
    exact hnA (heq ▸ ν.2)
  choose m hm0 hmpos using hm
  let U (ν : closure A) : Set (ProbabilityMeasure (Cube d)) :=
    {ξ | ‖coeff (m ν) ν.1‖ / 2 < ‖coeff (m ν) ξ‖}
  have ho (ν : closure A) : IsOpen (U ν) :=
    isOpen_lt continuous_const (continuous_probability_test _).norm
  have hcover : closure A ⊆ ⋃ ν, U ν := by
    intro ξ hξ
    exact Set.mem_iUnion.mpr ⟨⟨ξ, hξ⟩, (show ‖coeff (m ⟨ξ,hξ⟩) ξ‖ / 2 < ‖coeff (m ⟨ξ,hξ⟩) ξ‖ by
      linarith only [hmpos ⟨ξ,hξ⟩])⟩
  obtain ⟨T, hT⟩ := isClosed_closure.isCompact.elim_finite_subcover U ho hcover
  let pt (ν : closure A) := (m ν, ‖coeff (m ν) ν.1‖ / 2)
  let S := T.image pt
  have hS (p : (Fin d → ℤ) × ℝ) (hp : p ∈ S) : p.1 ≠ 0 ∧ 0 < p.2 := by
    obtain ⟨ν, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hm0 ν, half_pos (hmpos ν)⟩
  refine ⟨S, hS, fun u N hN => ?_⟩
  let q : I := (u, ⟨N, hN⟩)
  let V (p : (Fin d → ℤ) × ℝ) := ‖coeff p.1 (E q)‖ / p.2
  have hV (p : (Fin d → ℤ) × ℝ) :
      V p = ‖cesaro (fun n => torusCharacter p.1 (cubeToTorus (u n))) N‖ / p.2 := by
    change ‖∫ x, pullbackTorus (torusCharacter p.1) x ∂(cubeEmpirical u N hN : Measure (Cube d))‖ /
      p.2 = _
    rw [integral_cubeEmpirical]
    rfl
  simp_rw [← hV]
  have hnon : ∀ p ∈ S, 0 ≤ V p := fun p hp =>
    div_nonneg (norm_nonneg _) (hS p hp).2.le
  by_cases hbad : ε ≤ rectangleDiscrepancy u N
  · have hEA : E q ∈ closure A := subset_closure ⟨q, hbad, rfl⟩
    obtain ⟨ν, hν, hq⟩ := Set.mem_iUnion₂.mp (hT hEA)
    have hsmall : 1 ≤ V (pt ν) := (le_div_iff₀ (half_pos (hmpos ν))).2 (by
      rw [one_mul]
      exact (show ‖coeff (m ν) ν.1‖ / 2 < ‖coeff (m ν) (E q)‖ from hq).le)
    have hsum := (hsmall.trans (Finset.single_le_sum hnon (Finset.mem_image_of_mem pt hν)))
    linarith only [(rectangleDiscrepancy_mem_Icc u N).2, hsum, hε]
  · have := Finset.sum_nonneg hnon
    linarith

def lagFourierAverage {d : ℕ} (u : ℕ → ℕ → Cube d) (m : Fin d → ℤ) (h N : ℕ) : ℂ :=
  cesaro (fun n => torusCharacter m (cubeToTorus (u h n))) N

/-- The relevant Fourier means are Cesàro-small in h after every common
refinement on which the individual lag limits exist. -/
def MeanPermissibleFourierZero {d : ℕ} (u : ℕ → ℕ → Cube d) : Prop :=
  ∀ (m : Fin d → ℤ), m ≠ 0 → ∀ (M : ℕ → ℕ) (r : ℕ → ℂ), StrictMono M →
    (∀ h, Tendsto (fun q => lagFourierAverage u m h (M q)) atTop (𝓝 (r h))) →
    Tendsto (realCesaro (fun h => ‖r h‖)) atTop (𝓝 0)

theorem meanPermissibleDiscrepancyZero_of_fourier {d : ℕ} (u : ℕ → ℕ → Cube d)
    (hFourier : MeanPermissibleFourierZero u) :
    MeanPermissibleDiscrepancyZero (fun h N => rectangleDiscrepancy (u h) N) := by
  intro M δ hp
  have hδ (h : ℕ) : 0 ≤ δ h :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hp.2 h)
      (Eventually.of_forall fun q => (rectangleDiscrepancy_mem_Icc (u h) (M q)).1)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS, hb⟩ := finite_character_discrepancy_bound (d := d) (ε/2) (by positivity)
  obtain ⟨φ, r, hφ, hr⟩ := exists_common_subsequence
    (fun (q : ℕ) (i : (Fin d → ℤ) × ℕ) => lagFourierAverage u i.1 i.2 (M q))
    (fun ⟨m,h⟩ => ⟨1, zero_le_one, fun q =>
      norm_cesaro_le _ zero_le_one (fun n => (torusCharacter_norm m _).le) (M q)⟩)
  have hlig (p : (Fin d → ℤ) × ℝ) (hpS : p ∈ S) :
      Tendsto (realCesaro (fun h => ‖r (p.1,h)‖ / p.2)) atTop (𝓝 0) := by
    have hg := hFourier p.1 (hS _ hpS).1 (M ∘ φ) (fun h => r (p.1,h)) (hp.1.comp hφ)
      (fun h => hr (p.1,h))
    rw [show (fun h => ‖r (p.1,h)‖ / p.2) = (fun h => p.2⁻¹ * ‖r (p.1,h)‖) from
      funext fun h => by rw [div_eq_mul_inv, mul_comm]]
    change Tendsto (fun H => realCesaro (fun h => p.2⁻¹ * ‖r (p.1,h)‖) H) atTop (𝓝 0)
    simp_rw [realCesaro_const_mul]
    simpa only [mul_zero] using hg.const_mul p.2⁻¹
  have hδbd (h : ℕ) : δ h ≤ ε/2 + ∑ p ∈ S, ‖r (p.1,h)‖ / p.2 := by
    have hlim : Tendsto (fun q => ε/2 + ∑ p ∈ S,
        ‖lagFourierAverage u p.1 h (M (φ q))‖ / p.2) atTop
        (𝓝 (ε/2 + ∑ p ∈ S, ‖r (p.1,h)‖ / p.2)) :=
      tendsto_const_nhds.add (tendsto_finsetSum S (fun p _ => ((hr (p.1,h)).norm).div_const p.2))
    have hlimδ := (hp.2 h).comp hφ.tendsto_atTop
    apply le_of_tendsto_of_tendsto hlimδ hlim
    filter_upwards [(hp.1.comp hφ).tendsto_atTop.eventually (eventually_gt_atTop 0)] with q hq
    exact hb (u h) ((M ∘ φ) q) hq
  have hmean : Tendsto (fun H => realCesaro (fun h => ε/2 + ∑ p ∈ S, ‖r (p.1,h)‖ / p.2) H)
      atTop (𝓝 (ε/2)) := by
    simp_rw [realCesaro_add, realCesaro_sum]
    simpa only [Finset.sum_const_zero, add_zero] using
      (realCesaro_const_tendsto (ε/2)).add (tendsto_finsetSum S hlig)
  filter_upwards [hmean.eventually (gt_mem_nhds (show ε/2 < ε by linarith))] with H hH
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (realCesaro_nonneg hδ H)]
  exact (realCesaro_mono hδbd H).trans_lt hH

/-- Weak mixing implies the difference-discrepancy condition, (i) → (iv). -/
theorem thesisDifferenceDiscrepancy_of_weakMixing {d : ℕ} {x : ℕ → Cube d}
    (hx : WeaklyMixingDistribution (cubeLebesgue d) x) : ThesisDifferenceDiscrepancy x := by
  let z : ℕ → Torus d := fun n => cubeToTorus (x n)
  let u (h n : ℕ) (i : Fin d) := unitRepresentative (z (n+(h+1)) i - z n i)
  apply meanPermissibleDiscrepancyZero_of_fourier u
  intro m hm M r hM hr
  let a (n : ℕ) : ℂ := torusCharacter m (z n)
  have ha : NearlyWeakMixing a := (cube_weakMixing_iff_characters x).1 hx m hm
  let s (h : ℕ) : ℂ := Nat.casesOn h 1 r
  have hr' : CorrLimits a a M s := by
    intro h
    cases h with
    | zero =>
      have hval (q : ℕ) (hq : M q ≠ 0) : corr a a 0 (M q) = 1 := by
        simp only [corr, Nat.add_zero, a]
        have he (n : ℕ) : torusCharacter m (z n) * star (torusCharacter m (z n)) = 1 := by
          rw [show torusCharacter m (z n) * star (torusCharacter m (z n)) =
            (‖torusCharacter m (z n)‖ : ℂ)^2 from Complex.mul_conj' _, torusCharacter_norm]
          norm_num
        simp_rw [he]
        exact cesaro_const 1 (Nat.pos_of_ne_zero hq)
      exact tendsto_const_nhds.congr' ((hM.tendsto_atTop.eventually (eventually_gt_atTop 0)).mono
        (fun q hq => (hval q hq.ne').symm))
    | succ h =>
      have hZ (n : ℕ) : cubeToTorus (u h n) = z (n+(h+1)) - z n := by
        funext i
        exact unitRepresentative_coe _
      simpa only [s, a, lagFourierAverage, hZ, torusCharacter_point_sub, corr] using hr h
  have hp : PermissibleTriple a a M := ⟨ha.1, ha.1, hM, ⟨s,hr'⟩, ⟨s,hr'⟩, ⟨s,hr'⟩, ⟨s,hr'⟩⟩
  exact ha.2 a M s hp hr'

theorem thesisDifferenceDiscrepancy_iff_weakMixing {d : ℕ} (x : ℕ → Cube d) :
    ThesisDifferenceDiscrepancy x ↔ WeaklyMixingDistribution (cubeLebesgue d) x :=
  ⟨weakMixing_of_thesisDifferenceDiscrepancy, thesisDifferenceDiscrepancy_of_weakMixing⟩

/-- A weakly mixing distribution has Cesàro-small joint discrepancy against
every uniformly distributed second sequence, (i) → (ii). -/
theorem thesisCrossDiscrepancy_of_weakMixing {d : ℕ} {x : ℕ → Cube d}
    (hx : WeaklyMixingDistribution (cubeLebesgue d) x) : ThesisCrossDiscrepancy x := by
  intro e _ y hy
  apply meanPermissibleDiscrepancyZero_of_fourier (cubeLagPair x y)
  intro m hm M r hM hr
  let a (i : Fin d) := m (Fin.castAdd e i)
  let b (i : Fin e) := m (Fin.natAdd d i)
  have hab : m = Fin.addCases a b := by
    funext i
    refine Fin.addCases (motive := fun i => m i = Fin.addCases a b i) ?_ ?_ i
    · intro i; simp [a]
    · intro i; simp [b]
  let u (n : ℕ) := torusCharacter (-a) (cubeToTorus (x n))
  let v (n : ℕ) := torusCharacter b (cubeToTorus (y n))
  have hU : BoundedSeq u := bounded_test (torusCharacter (-a)) (fun n => cubeToTorus (x n))
  have hV : BoundedSeq v := bounded_test (torusCharacter b) (fun n => cubeToTorus (y n))
  have he (h N : ℕ) :
      lagFourierAverage (cubeLagPair x y) m h N = corr v u (h+1) N := by
    unfold lagFourierAverage corr
    congr 1
    funext n
    change torusCharacter m (cubeToTorus (Fin.addCases (x n) (y (n+(h+1))))) =
      v (n+(h+1)) * star (u n)
    rw [hab, pair_character_eq]
    simp only [u, v, torusCharacter_neg, ContinuousMap.star_apply, star_star, mul_comm]
  simp_rw [he] at hr
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hz
      apply hm
      rw [hab, ha, hz]
      funext i
      change ((Fin.addCases (0 : Fin d → ℤ) (0 : Fin e → ℤ)) : Fin (d+e) → ℤ) i = 0
      refine Fin.addCases (motive := fun i =>
        ((Fin.addCases (0 : Fin d → ℤ) (0 : Fin e → ℤ)) : Fin (d+e) → ℤ) i = 0) ?_ ?_ i <;> simp
    have hv0 : Tendsto (cesaro v) atTop (𝓝 0) :=
      (equidistributed_torus_iff _).1 (equidistributed_cubeToTorus hy) b hb
    have hzero (h : ℕ) : r h = 0 := by
      have hu0 : u = fun _ => 1 := by funext n; simp [u, ha]
      have hvh := tendsto_cesaro_shift hV (h+1) hM (hv0.comp hM.tendsto_atTop)
      have hh := hr h
      simp only [corr, hu0, star_one, mul_one] at hh
      exact tendsto_nhds_unique hh hvh
    simpa only [hzero, norm_zero] using realCesaro_const_tendsto 0
  have huwm : NearlyWeakMixing u :=
    (cube_weakMixing_iff_characters x).1 hx (-a) (neg_ne_zero.mpr ha)
  obtain ⟨φ, hφ, hp⟩ := exists_permissible_refinement hU hV hM
  obtain ⟨s, hs⟩ := hp.yx
  have hEq (h : ℕ) : r h = s (h+1) :=
    tendsto_nhds_unique ((hr h).comp hφ.tendsto_atTop) (hs (h+1))
  simpa only [← hEq] using huwm.reverse_corr hp hs

/-- Theorem 2.4.17, in the closed-rectangle convention of this certificate. -/
theorem thesis_four_characterizations_weakMixing {d : ℕ} (hd : 0 < d) (x : ℕ → Cube d) :
    (WeaklyMixingDistribution (cubeLebesgue d) x ↔ ThesisCrossDiscrepancy x) ∧
    (WeaklyMixingDistribution (cubeLebesgue d) x ↔ ThesisSelfDiscrepancy x) ∧
    (WeaklyMixingDistribution (cubeLebesgue d) x ↔ ThesisDifferenceDiscrepancy x) :=
  ⟨⟨thesisCrossDiscrepancy_of_weakMixing, fun h =>
      weakMixing_of_thesisSelfDiscrepancy (thesisSelfDiscrepancy_of_cross hd h)⟩,
    ⟨fun h => thesisSelfDiscrepancy_of_cross hd (thesisCrossDiscrepancy_of_weakMixing h),
      weakMixing_of_thesisSelfDiscrepancy⟩,
    ⟨thesisDifferenceDiscrepancy_of_weakMixing, weakMixing_of_thesisDifferenceDiscrepancy⟩⟩

/-- Uniform over the starting point, the discrepancy of any irrational circle
rotation tends to zero. This qualitative estimate needs no algebraicity. -/
theorem eventually_uniform_rotation_discrepancy (α : ℝ) (hα : Irrational α)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ β : UnitAddCircle,
      rectangleDiscrepancy (fun n (_ : Fin 1) =>
        unitRepresentative (β + n • (α : UnitAddCircle))) N < ε := by
  let t : UnitAddCircle := (α : UnitAddCircle)
  let u (β : UnitAddCircle) (n : ℕ) (_ : Fin 1) := unitRepresentative (β+n • t)
  obtain ⟨S, hS, hbound⟩ := finite_character_discrepancy_bound (d := 1) (ε/2) (by positivity)
  let c (m : Fin 1 → ℤ) := 2 / ‖fourier (m 0) t - 1‖
  have hf (m : Fin 1 → ℤ) (hm : m ≠ 0) (N : ℕ) (β : UnitAddCircle) :
      ‖cesaro (fun n => torusCharacter m (cubeToTorus (u β n))) N‖ ≤ c m / (N : ℝ) := by
    have hnon : m 0 ≠ 0 := by
      intro h
      exact hm (funext fun i => by change m i = 0; rw [Fin.eq_zero i]; exact h)
    let ω : ℂ := fourier (m 0) t
    have hω1 : ‖ω‖ = 1 := by simp [ω, fourier_apply]
    have hω : ω ≠ 1 := by
      intro h
      have ht' : (m 0) • t = 0 := by
        apply AddCircle.injective_toCircle one_ne_zero
        apply Subtype.ext
        simpa [ω, fourier_apply] using h
      rw [show t = (α : UnitAddCircle) from rfl, ← AddCircle.coe_zsmul,
        AddCircle.coe_eq_zero_iff] at ht'
      obtain ⟨j, hj⟩ := ht'
      exact (irrational_iff_ne_rational _).1 hα j (m 0) hnon
        ((eq_div_iff (by exact_mod_cast hnon)).2 (by simpa [zsmul_eq_mul, mul_comm] using hj.symm))
    have hz (n : ℕ) : fourier (m 0) (n • t) = ω ^ n := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [succ_nsmul, pow_succ, ← ih]
        simp only [ω, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    have hprod (n : ℕ) : torusCharacter m (cubeToTorus (u β n)) =
        fourier (m 0) β * ω ^ n := by
      simp only [torusCharacter_apply, Fin.prod_univ_one, cubeToTorus, u, unitRepresentative_coe]
      rw [← hz]
      simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    simp_rw [hprod, cesaro_mul_const]
    rw [norm_mul]
    have hnorm : ‖fourier (T:=1) (m 0) β‖ = 1 := by simp [fourier_apply]
    rw [hnorm, one_mul, cesaro, geom_sum_eq hω, norm_div, norm_div, Complex.norm_natCast]
    have hωp : ‖ω ^ N - 1‖ ≤ 2 := by
      simpa only [norm_pow, hω1, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (ω ^ N) 1
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hωp (norm_nonneg _)) (by positivity)
  let C : ℝ := ∑ p ∈ S, c p.1 / p.2
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat C).eventually
    (gt_mem_nhds (show 0 < ε/2 by positivity)), eventually_gt_atTop 0] with N hC hN
  intro β
  change rectangleDiscrepancy (u β) N < ε
  have hb := hbound (u β) N hN
  have hc : (∑ p ∈ S, ‖cesaro (fun n => torusCharacter p.1 (cubeToTorus (u β n))) N‖ / p.2) ≤
      C / (N : ℝ) := by
    unfold C
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    rw [div_right_comm (c p.1) p.2 (N : ℝ)]
    exact div_le_div_of_nonneg_right (hf p.1 (hS _ hp).1 N β) (hS _ hp).2.le
  linarith

end
end VdC
