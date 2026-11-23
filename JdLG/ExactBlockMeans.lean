/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.MeasuredTransfer
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Order.Compact

/-!
# Two-sided means from finite blocks with eventual exact invariance

Ultrafilter limits of ordinary finite averages give a mean on counting
measure L∞. Both invariance identities pass to the limit for translation
maps that are eventually permutations of the averaging blocks.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace JdLG

variable {G : Type*} [Group G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
  (F : ℕ → Finset G) (hF : ∀ n, (F n).Nonempty)

private noncomputable def finiteBlockAverage (f : G → ℝ) (n : ℕ) : ℝ :=
  (∑ s ∈ F n, f s) / (F n).card

omit [Group G] in
private theorem bounded_count_function {f : G → ℝ} (hf : MemLp f ∞ Measure.count) :
    ∃ C : ℝ, ∀ s, ‖f s‖ ≤ C := by
  refine ⟨(eLpNorm f ∞ Measure.count).toReal, fun s ↦ ?_⟩
  simpa using ENNReal.toReal_mono hf.eLpNorm_ne_top (eNorm_le_eLpNorm_count f s (by simp))

omit [Group G] in
include hF in
private theorem exists_finiteBlockAverage_limit {f : G → ℝ} (hf : MemLp f ∞ Measure.count) :
    ∃ x : ℝ, Tendsto (finiteBlockAverage F f) (hyperfilter ℕ : Filter ℕ) (𝓝 x) := by
  obtain ⟨C, hC⟩ := bounded_count_function hf
  have hb (n : ℕ) : ‖finiteBlockAverage F f n‖ ≤ C := by
    have hn : 0 < ((F n).card : ℝ) := Nat.cast_pos.2 (hF n).card_pos
    rw [finiteBlockAverage, norm_div, Real.norm_of_nonneg hn.le, div_le_iff₀ hn]
    calc
      _ ≤ ∑ s ∈ F n, ‖f s‖ := norm_sum_le _ _
      _ ≤ ∑ _s ∈ F n, C := Finset.sum_le_sum fun s _ ↦ hC s
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hmem : Metric.closedBall (0 : ℝ) C ∈ (hyperfilter ℕ).map (finiteBlockAverage F f) := by
    change ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), finiteBlockAverage F f n ∈ Metric.closedBall 0 C
    exact Eventually.of_forall fun n ↦ by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hb n
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : ℝ) C).ultrafilter_le_nhds' _ hmem
  exact ⟨x, hx⟩

include hF in
/-- A two-sided invariant mean for exact two-sided Følner blocks in a
discrete group. Both block identities need only hold eventually. -/
theorem exists_measuredBiInvariantMean_of_exactBlocks
    (hl : ∀ s : G, ∀ᶠ n in atTop, (s * ·) '' (F n : Set G) = (F n : Set G))
    (hr : ∀ s : G, ∀ᶠ n in atTop, (· * s) '' (F n : Set G) = (F n : Set G)) :
    ∃ m : MeasuredMean (Measure.count : Measure G), m.IsLeftInvariant ∧ m.IsRightInvariant := by
  classical
  let u : Filter ℕ := hyperfilter ℕ
  have hu : u ≤ atTop := hyperfilter_le_cofinite.trans_eq Nat.cofinite_eq_atTop
  let a := fun f : Lp ℝ ∞ (Measure.count : Measure G) ↦
    (exists_finiteBlockAverage_limit F hF (Lp.memLp f)).choose
  have ha (f : Lp ℝ ∞ (Measure.count : Measure G)) :
      Tendsto (finiteBlockAverage F f) u (𝓝 (a f)) :=
    (exists_finiteBlockAverage_limit F hF (Lp.memLp f)).choose_spec
  let Φ : (Lp ℝ ∞ (Measure.count : Measure G)) →ₗ[ℝ] ℝ :=
    { toFun := a
      map_add' f g := by
        have h (n : ℕ) : finiteBlockAverage F (⇑(f + g)) n =
            finiteBlockAverage F f n + finiteBlockAverage F g n := by
          simp_rw [finiteBlockAverage, Measure.ae_count_iff.mp (Lp.coeFn_add f g),
            Pi.add_apply, Finset.sum_add_distrib, add_div]
        exact tendsto_nhds_unique (ha (f + g))
          (((ha f).add (ha g)).congr' (Eventually.of_forall fun n ↦ (h n).symm))
      map_smul' c f := by
        have h (n : ℕ) : finiteBlockAverage F (⇑(c • f)) n = c * finiteBlockAverage F f n := by
          simp_rw [finiteBlockAverage, Measure.ae_count_iff.mp (Lp.coeFn_smul c f),
            Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc]
        change a (c • f) = c * a f
        exact tendsto_nhds_unique (ha (c • f))
          (((ha f).const_mul c).congr' (Eventually.of_forall fun n ↦ (h n).symm)) }
  let m : MeasuredMean (Measure.count : Measure G) :=
    { functional := Φ
      monotone' f g h := by
        apply le_of_tendsto_of_tendsto' (ha f) (ha g)
        intro n
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum fun s _ ↦ Measure.ae_count_iff.mp h s) (Nat.cast_nonneg _)
      unit' := by
        let z := (memLp_top_constant (μ := (Measure.count : Measure G)) 1).toLp (fun _ ↦ 1)
        change a z = 1
        have h (n : ℕ) : finiteBlockAverage F z n = 1 := by
          unfold finiteBlockAverage
          have hz : (⇑z : G → ℝ) = (fun _ ↦ 1) := funext
            (Measure.ae_count_iff.mp (MemLp.coeFn_toLp (memLp_top_constant
              (μ := (Measure.count : Measure G)) 1)))
          rw [hz, Finset.sum_const, nsmul_eq_mul, mul_one]
          apply div_self
          exact_mod_cast (hF n).card_ne_zero
        exact tendsto_nhds_unique (ha z) ((tendsto_const_nhds (x := (1 : ℝ))).congr'
          (Eventually.of_forall fun n ↦ (h n).symm)) }
  have hm {f : G → ℝ} (hf : MemLp f ∞ Measure.count) :
      Tendsto (finiteBlockAverage F f) u (𝓝 (m.value f hf)) := by
    refine (ha (hf.toLp f)).congr' (Eventually.of_forall fun n ↦ ?_)
    unfold finiteBlockAverage
    simp_rw [Measure.ae_count_iff.mp (MemLp.coeFn_toLp hf)]
  have hinv (t : G → G) (hinj : Function.Injective t)
      (ht : ∀ᶠ n in atTop, t '' (F n : Set G) = (F n : Set G))
      {f : G → ℝ} (hf : MemLp f ∞ Measure.count) (hft : MemLp (f ∘ t) ∞ Measure.count) :
      m.value (f ∘ t) hft = m.value f hf := by
    apply tendsto_nhds_unique (hm hft)
    apply (hm hf).congr'
    filter_upwards [ht.filter_mono hu] with n hn
    have hfin : (F n).image t = F n :=
      Finset.coe_injective (by simpa only [Finset.coe_image] using hn)
    unfold finiteBlockAverage
    conv_lhs => rw [← hfin, Finset.sum_image (fun _ _ _ _ he ↦ hinj he), hfin]
    rfl
  exact ⟨m, fun s _ hf hft ↦ hinv (s * ·) (fun _ _ ↦ mul_left_cancel) (hl s) hf hft,
    fun s _ hf hft ↦ hinv (· * s) (fun _ _ ↦ mul_right_cancel) (hr s) hf hft⟩

end JdLG
