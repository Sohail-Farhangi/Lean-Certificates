/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.LagPairs
public import VdC.Torus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Cube -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace VdC

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev UnitInterval := Set.Icc (0 : ℝ) 1
abbrev Cube (d : ℕ) := Fin d → UnitInterval

/-- Lebesgue measure pulled back to the closed unit interval. -/
noncomputable def unitIntervalLebesgue : Measure UnitInterval :=
  Measure.comap ((↑) : UnitInterval → ℝ) volume

instance unitIntervalLebesgue_probability : IsProbabilityMeasure unitIntervalLebesgue := by
  constructor
  rw [unitIntervalLebesgue, comap_subtype_coe_apply measurableSet_Icc, Set.image_univ,
    Subtype.range_coe, Real.volume_Icc]
  simp

noncomputable def cubeLebesgue (d : ℕ) : Measure (Cube d) :=
  Measure.pi fun _ => unitIntervalLebesgue

instance cubeLebesgue_probability (d : ℕ) : IsProbabilityMeasure (cubeLebesgue d) := by
  unfold cubeLebesgue
  infer_instance

/-- The `o`-sequence characterization on the paper's actual closed cube.
The lag-pair measure is the product of two copies of cube Lebesgue measure. -/
theorem cube_orthogonal_iff_lag_pairs {d : ℕ} (x : ℕ → Cube d) :
    OrthogonalDistribution (cubeLebesgue d) x ↔ ∀ h : ℕ, 0 < h →
      Equidistributed ((cubeLebesgue d).prod (cubeLebesgue d)) (fun n => (x n, x (n+h))) :=
  orthogonalDistribution_iff_lag_pairs (cubeLebesgue d) x

def cubeToTorus {d : ℕ} (x : Cube d) : Torus d := fun i => ((x i : ℝ) : UnitAddCircle)

theorem continuous_cubeToTorus (d : ℕ) : Continuous (cubeToTorus (d := d)) := by
  exact continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_subtype_val.comp (continuous_apply i))

private theorem map_unitIntervalLebesgue :
    unitIntervalLebesgue.map (fun x : UnitInterval => ((x : ℝ) : UnitAddCircle)) = circleHaar := by
  have hq := UnitAddCircle.measurePreserving_mk 0
  rw [show (fun x : UnitInterval => ((x : ℝ) : UnitAddCircle)) =
      (((↑) : ℝ → UnitAddCircle) ∘ ((↑) : UnitInterval → ℝ)) from rfl,
    ← Measure.map_map hq.measurable measurable_subtype_coe, unitIntervalLebesgue,
    map_comap_subtype_coe measurableSet_Icc, ← restrict_Ioc_eq_restrict_Icc]
  have h : (volume : Measure UnitAddCircle) = circleHaar := by
    simpa [circleHaar] using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  simpa only [zero_add, h] using hq.map_eq

theorem cubeToTorus_measurePreserving (d : ℕ) :
    MeasurePreserving (cubeToTorus (d := d)) (cubeLebesgue d) (torusHaar d) := by
  refine ⟨(continuous_cubeToTorus d).measurable, ?_⟩
  let f (_ : Fin d) (x : UnitInterval) := ((x : ℝ) : UnitAddCircle)
  have hσ : ∀ i : Fin d, SigmaFinite (unitIntervalLebesgue.map (f i)) := by
    intro i
    rw [show f i = (fun x : UnitInterval => ((x : ℝ) : UnitAddCircle)) from rfl, map_unitIntervalLebesgue]
    infer_instance
  change (Measure.pi fun _ : Fin d => unitIntervalLebesgue).map (fun x i => f i (x i)) = _
  rw [Measure.pi_map_pi (μ := fun _ : Fin d => unitIntervalLebesgue) (hμ := hσ)]
  · simp only [f, map_unitIntervalLebesgue, torusHaar]
  · intro i
    exact ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val).measurable.aemeasurable

/-- Continuous-test uniform distribution on the cube descends to the torus. -/
theorem equidistributed_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (cubeLebesgue d) x) :
    Equidistributed (torusHaar d) (fun n => cubeToTorus (x n)) := by
  intro f
  let g : C(Cube d, ℂ) := f.comp ⟨cubeToTorus, continuous_cubeToTorus d⟩
  have hg : testMean (cubeLebesgue d) g = testMean (torusHaar d) f := by
    unfold testMean
    rw [← (cubeToTorus_measurePreserving d).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable f.continuous.stronglyMeasurable]
    rfl
  exact hg ▸ hx g

def CubeInterior {d : ℕ} (x : Cube d) : Prop :=
  ∀ i : Fin d, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1

theorem cubeToTorus_surjective (d : ℕ) : Function.Surjective (cubeToTorus (d := d)) := by
  intro y
  let f (i : Fin d) := AddCircle.equivIco (1 : ℝ) 0 (y i)
  exact ⟨fun i => ⟨f i, (f i).2.1, by simpa using (f i).2.2.le⟩,
    funext fun i => AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := y i)⟩

private theorem cubeToTorus_eq_of_interior {d : ℕ} {x y : Cube d} (hx : CubeInterior x)
    (h : cubeToTorus x = cubeToTorus y) : x = y := by
  funext i
  apply Subtype.ext
  have he : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
  by_cases hy : 0 < (y i : ℝ)
  · exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := (1 : ℝ)) (a := 0)
      ⟨(hx i).1, by simpa using (x i).2.2⟩ ⟨hy, by simpa using (y i).2.2⟩).mp he
  have hy' : (y i : ℝ) = 0 := le_antisymm (le_of_not_gt hy) (y i).2.1
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨(x i).2.1, by simpa using (hx i).2⟩ ⟨(y i).2.1, by simp [hy']⟩).mp he

/-- Continuous boundary cutoff, increasing to one at every interior point. -/
noncomputable def cubeCutoff {d : ℕ} (K : ℕ) (x : Cube d) : ℝ :=
  ∏ i : Fin d, min 1 ((K : ℝ) * min (x i : ℝ) (1 - (x i : ℝ)))

theorem cubeCutoff_nonneg {d : ℕ} (K : ℕ) (x : Cube d) : 0 ≤ cubeCutoff K x := by
  unfold cubeCutoff
  apply Finset.prod_nonneg
  intro i _
  exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg K) (le_min (x i).2.1 (sub_nonneg.mpr (x i).2.2)))

theorem cubeCutoff_le_one {d : ℕ} (K : ℕ) (x : Cube d) : cubeCutoff K x ≤ 1 := by
  have hp : (∏ i : Fin d, min 1 ((K : ℝ) * min (x i : ℝ) (1 - (x i : ℝ)))) ≤ ∏ _i : Fin d, (1 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg K) (le_min (x i).2.1 (sub_nonneg.mpr (x i).2.2)))
    · intro i _
      exact min_le_left _ _
  simpa only [cubeCutoff, Finset.prod_const_one] using hp

theorem continuous_cubeCutoff {d : ℕ} (K : ℕ) : Continuous (cubeCutoff (d := d) K) := by
  apply continuous_finsetProd
  intro i _
  have hi : Continuous (fun x : Cube d => (x i : ℝ)) := continuous_subtype_val.comp (continuous_apply i)
  exact continuous_const.min ((hi.min (continuous_const.sub hi)).const_mul _)

theorem cubeCutoff_eq_zero_of_boundary {d : ℕ} (K : ℕ) {x : Cube d} (hx : ¬ CubeInterior x) :
    cubeCutoff K x = 0 := by
  unfold CubeInterior at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  have he : (x i : ℝ) = 0 ∨ (x i : ℝ) = 1 := by
    by_cases h0 : 0 < (x i : ℝ)
    · right
      exact le_antisymm (x i).2.2 (hi h0)
    · left
      exact le_antisymm (le_of_not_gt h0) (x i).2.1
  unfold cubeCutoff
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases he with h | h <;> simp [h]

theorem cubeCutoff_eventually_one {d : ℕ} {x : Cube d} (hx : CubeInterior x) :
    ∀ᶠ K : ℕ in atTop, cubeCutoff K x = 1 := by
  have hk : ∀ i : Fin d, ∀ᶠ K : ℕ in atTop, 1 ≤ (K : ℝ) * min (x i : ℝ) (1 - (x i : ℝ)) := by
    intro i
    have hd : 0 < min (x i : ℝ) (1 - (x i : ℝ)) := lt_min (hx i).1 (sub_pos.mpr (hx i).2)
    obtain ⟨K, hK⟩ := exists_nat_ge (1 / min (x i : ℝ) (1 - (x i : ℝ)))
    filter_upwards [eventually_ge_atTop K] with n hn
    exact (div_le_iff₀ hd).mp (hK.trans (by exact_mod_cast hn))
  filter_upwards [eventually_all.mpr hk] with K hK
  apply Finset.prod_eq_one
  intro i _
  exact min_eq_left (hK i)

theorem ae_cubeInterior (d : ℕ) : ∀ᵐ x ∂cubeLebesgue d, CubeInterior x := by
  have h1 : ∀ᵐ (x : UnitInterval) ∂unitIntervalLebesgue, 0 < (x : ℝ) ∧ (x : ℝ) < 1 := by
    apply (ae_restrict_iff_subtype (μ := (volume : Measure ℝ))
      (p := fun x : ℝ => 0 < x ∧ x < 1) (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))).mp
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (μ := fun _ : Fin d => unitIntervalLebesgue) i).quasiMeasurePreserving.ae h1

noncomputable def cubeCutoffTest {d : ℕ} (K : ℕ) (f : C(Cube d, ℂ)) : C(Cube d, ℂ) :=
  ⟨fun x => f x * (cubeCutoff K x : ℂ), f.continuous.mul (Complex.continuous_ofReal.comp (continuous_cubeCutoff K))⟩

theorem exists_cubeCutoff_descend {d : ℕ} (K : ℕ) (f : C(Cube d, ℂ)) :
    ∃ g : C(Torus d, ℂ), ∀ x : Cube d, g (cubeToTorus x) = cubeCutoffTest K f x := by
  classical
  let u := cubeCutoffTest K f
  have hcompat {x y : Cube d} (h : cubeToTorus x = cubeToTorus y) : u x = u y := by
    by_cases hx : CubeInterior x
    · rw [cubeToTorus_eq_of_interior hx h]
    have hy : ¬ CubeInterior y := fun hy => hx ((cubeToTorus_eq_of_interior hy h.symm).symm ▸ hy)
    simp only [u, cubeCutoffTest, ContinuousMap.coe_mk, cubeCutoff_eq_zero_of_boundary K hx,
      cubeCutoff_eq_zero_of_boundary K hy, Complex.ofReal_zero, mul_zero]
  let g : Torus d → ℂ := u ∘ Function.surjInv (cubeToTorus_surjective d)
  have hcomp (x : Cube d) : g (cubeToTorus x) = u x :=
    hcompat (Function.surjInv_eq (cubeToTorus_surjective d) (cubeToTorus x))
  have hq := Topology.IsQuotientMap.of_surjective_continuous (cubeToTorus_surjective d) (continuous_cubeToTorus d)
  have hcont : Continuous g := hq.continuous_iff.mpr (by simpa only [Function.comp_def, hcomp] using u.continuous)
  exact ⟨⟨g, hcont⟩, hcomp⟩

theorem tendsto_cutoffDeficit_integral (d : ℕ) :
    Tendsto (fun K : ℕ => ∫ x : Cube d, 1 - cubeCutoff K x ∂cubeLebesgue d) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := cubeLebesgue d) (F := fun K x => 1 - cubeCutoff K x) (f := fun _ => (0 : ℝ))
    (fun _ => 1) (fun K => (continuous_const.sub (continuous_cubeCutoff K)).aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro K
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (cubeCutoff_le_one K x))]
      exact sub_le_self _ (cubeCutoff_nonneg K x)
  · filter_upwards [ae_cubeInterior d] with x hx
    exact tendsto_const_nhds.congr' ((cubeCutoff_eventually_one hx).mono fun K hk => by simp [hk])

theorem norm_sub_cubeCutoffTest {d : ℕ} (K : ℕ) (f : C(Cube d, ℂ)) (x : Cube d) :
    ‖f x - cubeCutoffTest K f x‖ = ‖f x‖ * (1 - cubeCutoff K x) := by
  change ‖f x - f x * (cubeCutoff K x : ℂ)‖ = _
  rw [show f x - f x * (cubeCutoff K x : ℂ) = f x * ((1 - cubeCutoff K x : ℝ) : ℂ) by
    push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (cubeCutoff_le_one K x))]

theorem tendsto_testMean_cubeCutoffTest {d : ℕ} (f : C(Cube d, ℂ)) :
    Tendsto (fun K : ℕ => testMean (cubeLebesgue d) (cubeCutoffTest K f)) atTop
      (𝓝 (testMean (cubeLebesgue d) f)) := by
  apply tendsto_integral_of_dominated_convergence (bound := fun _ => ‖f‖)
  · exact fun K => (cubeCutoffTest K f).continuous.aestronglyMeasurable
  · exact integrable_const _
  · intro K
    exact ae_of_all _ fun x => by
      change ‖f x * (cubeCutoff K x : ℂ)‖ ≤ ‖f‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cubeCutoff_nonneg K x)]
      exact (mul_le_of_le_one_right (norm_nonneg _) (cubeCutoff_le_one K x)).trans
        (ContinuousMap.norm_coe_le_norm f x)
  · filter_upwards [ae_cubeInterior d] with x hx
    exact tendsto_const_nhds.congr' ((cubeCutoff_eventually_one hx).mono fun K hk => by
      simp [cubeCutoffTest, hk])

theorem tendsto_cubeCutoffTest_l2 {d : ℕ} (f : C(Cube d, ℂ)) :
    Tendsto (fun K : ℕ => ∫ x : Cube d, ‖f x - cubeCutoffTest K f x‖ ^ 2 ∂cubeLebesgue d)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := cubeLebesgue d)
    (F := fun K x => ‖f x - cubeCutoffTest K f x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun _ => ‖f‖^2) (fun K => ((f.continuous.sub (cubeCutoffTest K f).continuous).norm.pow 2).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro K
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_sub_cubeCutoffTest]
      apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (cubeCutoff_le_one K x))) _ 2
      exact (mul_le_of_le_one_right (norm_nonneg _) (sub_le_self _ (cubeCutoff_nonneg K x))).trans
        (ContinuousMap.norm_coe_le_norm f x)
  · filter_upwards [ae_cubeInterior d] with x hx
    exact tendsto_const_nhds.congr' ((cubeCutoff_eventually_one hx).mono fun K hk => by
      simp [cubeCutoffTest, hk])

theorem tends_to_cube_test_of_pullback {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n)))
    {f : C(Cube d, ℂ)} {g : C(Torus d, ℂ)} (hg : ∀ x : Cube d, g (cubeToTorus x) = f x) :
    Tendsto (cesaro fun n => f (x n)) atTop (𝓝 (testMean (cubeLebesgue d) f)) := by
  have hmean : testMean (torusHaar d) g = testMean (cubeLebesgue d) f := by
    unfold testMean
    rw [← (cubeToTorus_measurePreserving d).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable g.continuous.stronglyMeasurable]
    simp only [hg]
  simpa only [hg, hmean] using hx g

private theorem tendsto_cubeCutoffDeficit {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n))) (K : ℕ) :
    Tendsto (realCesaro fun n => 1 - cubeCutoff K (x n)) atTop
      (𝓝 (∫ y : Cube d, 1 - cubeCutoff K y ∂cubeLebesgue d)) := by
  obtain ⟨g, hg⟩ := exists_cubeCutoff_descend K (1 : C(Cube d, ℂ))
  let deficit (y : Cube d) := 1 - cubeCutoff K y
  let F : C(Cube d, ℂ) := ⟨fun y => (deficit y : ℂ),
    Complex.continuous_ofReal.comp (continuous_const.sub (continuous_cubeCutoff K))⟩
  have hcomp (y : Cube d) : (1 - g) (cubeToTorus y) = F y := by
    rw [ContinuousMap.sub_apply, ContinuousMap.one_apply, hg]
    change 1 - ((1:ℂ) * (cubeCutoff K y : ℂ)) = ((1 - cubeCutoff K y : ℝ) : ℂ)
    push_cast
    ring
  have ht := tends_to_cube_test_of_pullback hx hcomp
  have hRe := Complex.continuous_re.continuousAt.tendsto.comp ht
  have hmean : testMean (cubeLebesgue d) F = (∫ y : Cube d, deficit y ∂cubeLebesgue d : ℝ) :=
    integral_complex_ofReal
  rw [hmean, Complex.ofReal_re] at hRe
  simpa only [Function.comp_def, ← realCesaro_re, F, ContinuousMap.coe_mk, Complex.ofReal_re] using hRe

private theorem norm_cesaro_le_realCesaro {u : ℕ → ℂ} {v : ℕ → ℝ} (h : ∀ n, ‖u n‖ ≤ v n) (N : ℕ) :
    ‖cesaro u N‖ ≤ realCesaro v N := by
  rw [cesaro, realCesaro, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => h n)) (by positivity)

/-- Distribution on the torus lifts to the closed cube. The periodic cutoff
handles both representatives of each seam, including sequences that meet the seams. -/
theorem equidistributed_of_cubeToTorus {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n))) :
    Equidistributed (cubeLebesgue d) x := by
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hDef := (tendsto_cutoffDeficit_integral d).const_mul ‖f‖
  have hsmall : ∀ᶠ K : ℕ in atTop,
      ‖f‖ * (∫ y : Cube d, 1 - cubeCutoff K y ∂cubeLebesgue d) < ε/3 := by
    have h := hDef.eventually (gt_mem_nhds (show ‖f‖ * (0:ℝ) < ε/3 by
      simpa only [mul_zero] using (show 0 < ε/3 by positivity)))
    exact h
  have hv := Metric.tendsto_nhds.mp (tendsto_testMean_cubeCutoffTest f) (ε/3) (by positivity)
  obtain ⟨K, hK, hMean⟩ := (hsmall.and hv).exists
  let u := cubeCutoffTest K f
  obtain ⟨g, hg⟩ := exists_cubeCutoff_descend K f
  have hU := tends_to_cube_test_of_pullback hx hg
  have hAvg := (tendsto_cubeCutoffDeficit hx K).const_mul ‖f‖
  have hErr : ∀ᶠ N : ℕ in atTop, ‖f‖ * realCesaro (fun n => 1 - cubeCutoff K (x n)) N < ε/3 :=
    hAvg.eventually (gt_mem_nhds hK)
  filter_upwards [Metric.tendsto_nhds.mp hU (ε/3) (by positivity), hErr] with N hUavg hN
  rw [dist_eq_norm] at hUavg hMean ⊢
  have hDiff : ‖cesaro (fun n => f (x n)) N - cesaro (fun n => u (x n)) N‖ ≤
      ‖f‖ * realCesaro (fun n => 1 - cubeCutoff K (x n)) N := by
    rw [← cesaro_sub, ← realCesaro_const_mul]
    apply norm_cesaro_le_realCesaro
    intro n
    rw [norm_sub_cubeCutoffTest K f (x n)]
    exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f (x n))
      (sub_nonneg.mpr (cubeCutoff_le_one K (x n)))
  let a := cesaro (fun n => f (x n)) N
  let b := cesaro (fun n => u (x n)) N
  let c := testMean (cubeLebesgue d) u
  let e := testMean (cubeLebesgue d) f
  have hTri : ‖a-e‖ ≤ ‖a-b‖ + ‖b-c‖ + ‖c-e‖ := by
    rw [show a-e = (a-b+(b-c))+(c-e) by ring]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le (a-b) (b-c)) le_rfl)
  change ‖a - e‖ < ε
  change ‖b - c‖ < ε / 3 at hUavg
  change ‖c - e‖ < ε / 3 at hMean
  change ‖a - b‖ ≤ _ at hDiff
  linarith only [hUavg, hMean, hN, hDiff, hTri]

/-- A zero-mean cube test is an L² limit of zero-mean periodic tests. -/
theorem exists_centered_periodic_test_approx_l2 {d : ℕ} (f : C(Cube d, ℂ))
    (hf : testMean (cubeLebesgue d) f = 0) :
    ∃ g : ℕ → C(Torus d, ℂ), (∀ K, testMean (torusHaar d) (g K) = 0) ∧
      Tendsto (fun K : ℕ => ∫ x : Cube d, ‖g K (cubeToTorus x) - f x‖ ^ 2 ∂cubeLebesgue d)
        atTop (𝓝 0) := by
  choose raw hraw using fun K : ℕ => exists_cubeCutoff_descend K f
  let m (K : ℕ) := testMean (torusHaar d) (raw K)
  let g (K : ℕ) := raw K - ContinuousMap.const (Torus d) (m K)
  have hmean (K : ℕ) : m K = testMean (cubeLebesgue d) (cubeCutoffTest K f) := by
    unfold m testMean
    rw [← (cubeToTorus_measurePreserving d).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus d).measurable (raw K).continuous.stronglyMeasurable]
    simp only [hraw K]
  have hm : Tendsto m atTop (𝓝 0) := by
    have ht := tendsto_testMean_cubeCutoffTest f
    rw [hf] at ht
    exact ht.congr' (Eventually.of_forall fun K => (hmean K).symm)
  have hg (K : ℕ) : testMean (torusHaar d) (g K) = 0 := by
    unfold g
    rw [testMean_sub, testMean_const]
    exact sub_self _
  refine ⟨g, hg, ?_⟩
  have hbound (K : ℕ) : ‖m K‖ ≤ ‖f‖ := by
    rw [hmean, testMean]
    have h : ∀ᵐ x ∂cubeLebesgue d, ‖cubeCutoffTest K f x‖ ≤ ‖f‖ := ae_of_all _ fun x => by
      change ‖f x * (cubeCutoff K x : ℂ)‖ ≤ ‖f‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cubeCutoff_nonneg K x)]
      exact (mul_le_of_le_one_right (norm_nonneg _) (cubeCutoff_le_one K x)).trans
        (ContinuousMap.norm_coe_le_norm f x)
    simpa using norm_integral_le_of_norm_le_const h
  have herror (K : ℕ) (x : Cube d) : ‖g K (cubeToTorus x) - f x‖ ≤ 2 * ‖f‖ := by
    have ht : g K (cubeToTorus x) - f x = (cubeCutoffTest K f x - f x) - m K := by
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.const_apply, hraw]
      ring
    rw [ht]
    have ha : ‖cubeCutoffTest K f x - f x‖ ≤ ‖f‖ := by
      rw [norm_sub_rev (cubeCutoffTest K f x), norm_sub_cubeCutoffTest]
      exact (mul_le_of_le_one_right (norm_nonneg _) (sub_le_self _ (cubeCutoff_nonneg K x))).trans
        (ContinuousMap.norm_coe_le_norm f x)
    have hh := (norm_sub_le _ _).trans (add_le_add ha (hbound K))
    linarith only [hh]
  have ht := tendsto_integral_of_dominated_convergence (μ := cubeLebesgue d)
    (F := fun K x => ‖g K (cubeToTorus x) - f x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * ‖f‖)^2) (fun K => ((((g K).continuous.comp (continuous_cubeToTorus d)).sub
      f.continuous).norm.pow 2).aestronglyMeasurable) (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using ht
  · intro K
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (herror K x) 2
  · filter_upwards [ae_cubeInterior d] with x hx
    have heq : ∀ᶠ K : ℕ in atTop, g K (cubeToTorus x) - f x = -(m K) := by
      filter_upwards [cubeCutoff_eventually_one hx] with K hK
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.const_apply, hraw, cubeCutoffTest,
        ContinuousMap.coe_mk, hK, Complex.ofReal_one, mul_one]
      ring
    simpa only [neg_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((hm.neg.congr' (heq.mono fun _ h => h.symm)).norm.pow 2)

theorem tendsto_realCesaro_cube_test {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (cubeLebesgue d) x) {u : Cube d → ℝ} (hu : Continuous u) :
    Tendsto (realCesaro fun n => u (x n)) atTop (𝓝 (∫ y, u y ∂cubeLebesgue d)) := by
  let F : C(Cube d, ℂ) := ⟨fun y => (u y : ℂ), Complex.continuous_ofReal.comp hu⟩
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (hx F)
  have hm : testMean (cubeLebesgue d) F = Complex.ofReal (∫ y, u y ∂cubeLebesgue d) :=
    integral_complex_ofReal
  rw [hm, Complex.ofReal_re] at ht
  simpa only [Function.comp_def, ← realCesaro_re, F, ContinuousMap.coe_mk, Complex.ofReal_re] using ht

/-- Periodic mean-zero approximants tested along an equidistributed cube sequence. -/
theorem exists_centered_periodic_sequence_approx_l2 {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (cubeLebesgue d) x) (f : C(Cube d, ℂ))
    (hf : testMean (cubeLebesgue d) f = 0) :
    ∃ g : ℕ → C(Torus d, ℂ), (∀ K, testMean (torusHaar d) (g K) = 0) ∧
      Tendsto (fun K : ℕ => limsup (fun N : ℕ =>
        realCesaro (fun n => ‖g K (cubeToTorus (x n)) - f (x n)‖ ^ 2) N) atTop) atTop (𝓝 0) := by
  obtain ⟨g, hg, hlim⟩ := exists_centered_periodic_test_approx_l2 f hf
  refine ⟨g, hg, ?_⟩
  refine hlim.congr' (Eventually.of_forall fun K => ?_)
  symm
  apply Tendsto.limsup_eq
  let U (y : Cube d) : ℝ := ‖g K (cubeToTorus y) - f y‖ ^ 2
  have hU : Continuous U := ((((g K).continuous.comp (continuous_cubeToTorus d)).sub
    f.continuous).norm.pow 2)
  exact tendsto_realCesaro_cube_test hx hU

/-- An eventual mean-square periodic approximation, directly on the original cube sequence. -/
theorem exists_centered_torus_approx {d : ℕ} {x : ℕ → Cube d}
    (hx : Equidistributed (torusHaar d) (fun n => cubeToTorus (x n))) (f : C(Cube d, ℂ))
    (hf : testMean (cubeLebesgue d) f = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(Torus d, ℂ), testMean (torusHaar d) g = 0 ∧
      ∀ᶠ N in atTop, realCesaro (fun n => ‖f (x n) - g (cubeToTorus (x n))‖ ^ 2) N ≤ ε := by
  obtain ⟨g, hg, hlim⟩ := exists_centered_periodic_test_approx_l2 f hf
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨g K, hg K, ?_⟩
  let U (y : Cube d) : ℝ := ‖g K (cubeToTorus y) - f y‖ ^ 2
  have hU : Continuous U := ((((g K).continuous.comp (continuous_cubeToTorus d)).sub f.continuous).norm.pow 2)
  have h := tendsto_realCesaro_cube_test (equidistributed_of_cubeToTorus hx) hU
  filter_upwards [h.eventually (gt_mem_nhds hK)] with N hN
  simpa only [U, norm_sub_rev] using hN.le

end VdC
