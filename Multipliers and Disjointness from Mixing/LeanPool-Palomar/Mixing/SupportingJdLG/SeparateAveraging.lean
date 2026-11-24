/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic.NormNum

/-!
# Averaging a separately continuous function on compact spaces

The sequential selection lemma gives a pointwise approximating sequence from
any prescribed subset. It permits ordinary dominated convergence in the
passage from invariance on a dense representing semigroup to invariance on
its weak operator closure.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Mixing.JdLGBridge

section Selection

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y]

omit [TopologicalSpace X] [CompactSpace X] in
private theorem finite_samples (F : X → Y → ℝ) (hF : ∀ x, Continuous (F x))
    (A : Finset X) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset Y, ∀ y, ∃ z ∈ C, ∀ a ∈ A, dist (F a y) (F a z) < ε := by
  let U (z : Y) : Set Y := ⋂ a ∈ A, F a ⁻¹' Metric.ball (F a z) ε
  have hU (z : Y) : IsOpen (U z) :=
    isOpen_biInter_finset fun a _ ↦ Metric.isOpen_ball.preimage (hF a)
  have hcover : (Set.univ : Set Y) ⊆ ⋃ z, U z := by
    intro y _
    exact mem_iUnion.2 ⟨y, mem_iInter.2 fun _ ↦
      mem_iInter.2 fun _ ↦ Metric.mem_ball_self hε⟩
  obtain ⟨C, hC⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨C, fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ := mem_iUnion.1 (hC (mem_univ y))
  obtain ⟨hzC, hy⟩ := mem_iUnion.1 hz
  exact ⟨z, hzC, fun a ha ↦ mem_iInter.1 (mem_iInter.1 hy a) ha⟩

omit [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] in
private theorem approx_from_closure (F : X → Y → ℝ)
    (hF : ∀ y, Continuous fun x ↦ F x y) {D : Set X} {x : X} (hx : x ∈ closure D)
    (C : Finset Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ D, ∀ z ∈ C, dist (F a z) (F x z) < ε := by
  let U : Set X := ⋂ z ∈ C, (fun a ↦ F a z) ⁻¹' Metric.ball (F x z) ε
  have hU : IsOpen U := isOpen_biInter_finset fun z _ ↦ Metric.isOpen_ball.preimage (hF z)
  have hxU : x ∈ U := mem_iInter.2 fun _ ↦ mem_iInter.2 fun _ ↦ Metric.mem_ball_self hε
  obtain ⟨a, haU, haD⟩ := (mem_closure_iff.1 hx) U hU hxU
  exact ⟨a, haD, fun z hz ↦ mem_iInter.1 (mem_iInter.1 haU z) hz⟩

private theorem cluster_eq_of_dist_lt {Z : Type*} [TopologicalSpace Z] {u : ℕ → Z}
    {z : Z} (hz : MapClusterPt z atTop u) {g : Z → ℝ} (hg : Continuous g)
    {b : ℝ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsmall : ∀ᶠ n in atTop, dist (g (u n)) b < ε n) : g z = b := by
  by_contra hn
  have hp : 0 < dist (g z) b / 2 := half_pos (dist_pos.2 hn)
  have hf : ∃ᶠ n in atTop, dist (g z) b / 2 < dist (g (u n)) b :=
    hz.frequently ((hg.continuousAt.dist continuousAt_const)
      (lt_mem_nhds (half_lt_self (dist_pos.2 hn))))
  have he := hε.eventually (gt_mem_nhds hp)
  obtain ⟨n, hlarge, hnSmall, hnε⟩ := (hf.and_eventually (hsmall.and he)).exists
  exact (not_lt_of_ge (hnε.le.trans hlarge.le)) hnSmall

/-- This version of the Grothendieck sequential selection argument works for
compact spaces that need not be metrizable. -/
theorem exists_seq_pointwise_of_mem_closure_of_separatelyContinuous
    (F : X → Y → ℝ) (hleft : ∀ y, Continuous fun x ↦ F x y)
    (hright : ∀ x, Continuous (F x)) {D : Set X} {x : X} (hx : x ∈ closure D) :
    ∃ a : ℕ → X, (∀ n, a n ∈ D) ∧ ∀ y, Tendsto (fun n ↦ F (a n) y) atTop (𝓝 (F x y)) := by
  classical
  let ε : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
  have hεpos (n : ℕ) : 0 < ε n := pow_pos (by norm_num) n
  have hε : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hx₀ := approx_from_closure F hleft hx ∅ (hεpos 0)
  let Sample (n : ℕ) (A : Finset X) : Finset Y :=
    (finite_samples F hright A (hεpos n)).choose
  let Pick (n : ℕ) (C : Finset Y) : X :=
    (approx_from_closure F hleft hx C (hεpos n)).choose
  let state : ℕ → X × Finset X × Finset Y := fun n ↦ Nat.rec
    (hx₀.choose, {x, hx₀.choose}, ∅)
    (fun k prev ↦
      let C := prev.2.2 ∪ Sample k prev.2.1
      let a := Pick k C
      (a, insert a prev.2.1, C)) n
  let a (n : ℕ) : X := (state n).1
  let A (n : ℕ) : Finset X := (state n).2.1
  let C (n : ℕ) : Finset Y := (state n).2.2
  have hC (n : ℕ) : C (n + 1) = C n ∪ Sample n (A n) := rfl
  have ha (n : ℕ) : a (n + 1) = Pick n (C (n + 1)) := rfl
  have hA (n : ℕ) : A (n + 1) = insert (a (n + 1)) (A n) := rfl
  have hAmono : Monotone A := monotone_nat_of_le_succ fun n ↦ by
    rw [hA]
    exact Finset.subset_insert _ _
  have hCmono : Monotone C := monotone_nat_of_le_succ fun n ↦ by
    rw [hC]
    exact Finset.subset_union_left
  have hxA (n : ℕ) : x ∈ A n := hAmono (Nat.zero_le n) (Finset.mem_insert_self _ _)
  have haA (n : ℕ) : a n ∈ A n := by
    cases n with
    | zero => exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    | succ n => rw [hA]; exact Finset.mem_insert_self _ _
  refine ⟨a, ?_, fun y ↦ ?_⟩
  · intro n
    cases n with
    | zero => exact hx₀.choose_spec.1
    | succ n =>
      rw [ha]
      exact (approx_from_closure F hleft hx (C (n + 1)) (hεpos n)).choose_spec.1
  have hsample (n : ℕ) := (finite_samples F hright (A n) (hεpos n)).choose_spec y
  let z (n : ℕ) : Y := (hsample n).choose
  have hzC (n : ℕ) : z n ∈ C (n + 1) := by
    rw [hC]
    exact Finset.mem_union_right _ (hsample n).choose_spec.1
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, MapClusterPt z₀ atTop z :=
    exists_clusterPt_of_compactSpace (map z atTop)
  have htest {b : X} (i : ℕ) (hb : b ∈ A i) : F b z₀ = F b y := by
    apply cluster_eq_of_dist_lt hz₀ (hright b) hε
    filter_upwards [eventually_ge_atTop i] with n hin
    rw [dist_comm]
    exact (hsample n).choose_spec.2 b (hAmono hin hb)
  have hxz : F x z₀ = F x y := htest 0 (hxA 0)
  have hcluster (w : X) (hw : MapClusterPt w atTop a) : F w y = F x y := by
    have hsample_equal (i : ℕ) : F w (z i) = F x (z i) := by
      have hshift : MapClusterPt w atTop (a ∘ (fun n : ℕ ↦ n + 1)) ↔
          MapClusterPt w (map (fun n : ℕ ↦ n + 1) atTop) a := mapClusterPt_comp
      have hws : MapClusterPt w atTop (fun n ↦ a (n + 1)) :=
        hshift.2 (by rwa [map_add_atTop_eq_nat])
      apply cluster_eq_of_dist_lt hws (hleft (z i)) hε
      filter_upwards [eventually_ge_atTop i] with n hin
      rw [ha]
      exact (approx_from_closure F hleft hx (C (n + 1)) (hεpos n)).choose_spec.2
        (z i) (hCmono (Nat.succ_le_succ hin) (hzC i))
    have hwz : F w z₀ = F x z₀ :=
      (isClosed_eq (hright w) (hright x)).mem_of_mapClusterPt hz₀
        (Eventually.of_forall hsample_equal)
    have hwy : F w z₀ = F w y :=
      (isClosed_eq (hleft z₀) (hleft y)).mem_of_mapClusterPt hw
        (Eventually.of_forall fun n ↦ htest n (haA n))
    exact hwy.symm.trans (hwz.trans hxz)
  have hnear : Tendsto a atTop (𝓝ˢ { w | F w y = F x y }) :=
    isCompact_univ.tendsto_nhdsSet_of_mapClusterPt (Eventually.of_forall fun _ ↦ mem_univ _)
      fun w _ hw ↦ hcluster w hw
  apply Metric.tendsto_nhds.2
  intro δ hδ
  exact hnear.eventually ((Metric.isOpen_ball.preimage (hleft y)).mem_nhdsSet.2
    fun w (hw : F w y = F x y) ↦ by
      change F w y ∈ Metric.ball (F x y) δ
      rw [hw]
      exact Metric.mem_ball_self hδ)

/-- Integration against a finite measure preserves continuity of the
other variable of a bounded separately continuous real function. -/
theorem continuous_integral_of_separatelyContinuous [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (F : X → Y → ℝ)
    (hleft : ∀ y, Continuous fun x ↦ F x y) (hright : ∀ x, Continuous (F x))
    (M : ℝ) (hM : ∀ x y, ‖F x y‖ ≤ M) :
    Continuous fun x ↦ ∫ y, F x y ∂μ := by
  apply continuous_iff_isClosed.2
  intro K hK
  apply closure_subset_iff_isClosed.1
  intro x hx
  let D := (fun x ↦ ∫ y, F x y ∂μ) ⁻¹' K
  obtain ⟨a, ha, halim⟩ :=
    exists_seq_pointwise_of_mem_closure_of_separatelyContinuous F hleft hright (D := D) hx
  have h := tendsto_integral_of_dominated_convergence (fun _ ↦ M)
    (fun n ↦ (hright (a n)).aestronglyMeasurable) (integrable_const M)
    (fun n ↦ ae_of_all μ (hM (a n))) (ae_of_all μ halim)
  exact hK.mem_of_tendsto h (Eventually.of_forall ha)

end Selection

end Mixing.JdLGBridge
