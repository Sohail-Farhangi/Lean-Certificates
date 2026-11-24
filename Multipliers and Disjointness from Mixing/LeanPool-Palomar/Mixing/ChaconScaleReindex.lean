/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconScaleDecomposition
public import Mixing.ChaconMovingRemainders

/-! # Variable-scale reindexing of the moving-remainder estimate -/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology Classical ENNReal

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The size of the remainder as a fraction of the height. -/
noncomputable def chaconRelativeRemainder (n : ℕ) (s : ℤ) : ℝ :=
  (s.natAbs : ℝ) / chaconTowerHeight n

/-- A moving-remainder estimate proved along all heights also holds along
any filter of heights tending to infinity. A bad sample would give a
counterexample along a strictly increasing sequence of heights, which
can be extended by zero remainders on unused heights. -/
theorem tendsto_chaconRelativeRemainder_reindex {ι Y : Type*} [PseudoMetricSpace Y]
    {F : Filter ι} {n : ι → ℕ} {s : ι → ℤ} (hn : Tendsto n F atTop)
    (hs : Tendsto (fun j ↦ chaconRelativeRemainder (n j) (s j)) F (𝓝 0))
    {P : ℕ → ℤ → Y} {y : Y}
    (h : ∀ r : ℕ → ℤ, Tendsto (fun k ↦ chaconRelativeRemainder k (r k)) atTop (𝓝 0) →
      Tendsto (fun k ↦ P k (r k)) atTop (𝓝 y)) :
    Tendsto (fun j ↦ P (n j) (s j)) F (𝓝 y) := by
  by_contra hFail
  have hBad : ∃ ε > 0, ∃ᶠ j in F, ε ≤ dist (P (n j) (s j)) y := by
    simpa only [Metric.tendsto_nhds, not_forall, not_eventually, not_lt, exists_prop]
      using hFail
  obtain ⟨ε, hε, hεBad⟩ := hBad
  have hSamples (k : ℕ) : ∃ j : ι, k ≤ n j ∧
      chaconRelativeRemainder (n j) (s j) < 1 / ((k : ℝ) + 1) ∧ ε ≤ dist (P (n j) (s j)) y := by
    have hLarge := hn.eventually (eventually_ge_atTop k)
    have hSmall := hs.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by
      positivity))
    obtain ⟨j, hBad, hL, hS⟩ := (hεBad.and_eventually (hLarge.and hSmall)).exists
    exact ⟨j, hL, hS, hBad⟩
  choose j hjN hjs hjBad using hSamples
  have hDepth : Tendsto (n ∘ j) atTop atTop :=
    tendsto_atTop_mono hjN tendsto_id
  have hRelative : Tendsto (fun k ↦ chaconRelativeRemainder (n (j k)) (s (j k))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ ↦ by unfold chaconRelativeRemainder; positivity)
      (fun k ↦ (hjs k).le)
  obtain ⟨φ, hφ, ht⟩ := strictMono_subseq_of_tendsto_atTop hDepth
  let t (i : ℕ) := n (j (φ i))
  have ht' : StrictMono t := ht
  let r (k : ℕ) := if hk : k ∈ Set.range t then s (j (φ (Classical.choose hk))) else 0
  have hr (i : ℕ) : r (t i) = s (j (φ i)) := by
    have hi : t i ∈ Set.range t := Set.mem_range_self i
    dsimp only [r]
    rw [dite_eq_left hi, ht'.injective (Classical.choose_spec hi)]
  have hRelative' : Tendsto (fun i ↦ chaconRelativeRemainder (t i) (s (j (φ i))))
      atTop (𝓝 0) := hRelative.comp hφ.tendsto_atTop
  have hR : Tendsto (fun k ↦ chaconRelativeRemainder k (r k)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hRelative' δ hδ)
    filter_upwards [eventually_ge_atTop (t N)] with k hk
    by_cases hkt : k ∈ Set.range t
    · obtain ⟨i, rfl⟩ := hkt
      rw [hr]
      exact hN i (ht'.le_iff_le.mp hk)
    · simpa only [r, dite_eq_right hkt, chaconRelativeRemainder, Int.natAbs_zero,
        Nat.cast_zero, zero_div, dist_self] using hδ
  have hY : Tendsto (fun i ↦ P (t i) (s (j (φ i)))) atTop (𝓝 y) := by
    have htP := (h r hR).comp ht'.tendsto_atTop
    change Tendsto (fun i ↦ P (t i) (r (t i))) atTop (𝓝 y) at htP
    simpa only [hr] using htP
  obtain ⟨i, hi⟩ := ((Metric.tendsto_nhds.1 hY) ε hε).exists
  exact (hjBad (φ i)).not_gt hi

/-- The moving-remainder correlation estimate with an arbitrary escaping
scale filter, applied to the actual Chacon tower. -/
theorem tendsto_chaconTower_movingRemainder_error_reindex {ι : Type*} {F : Filter ι}
    {n : ι → ℕ} {s : ι → ℤ} (hn : Tendsto n F atTop)
    (hs : Tendsto (fun j ↦ ((s j).natAbs : ℝ) / chaconTowerHeight (n j)) F (𝓝 0))
    (m N : ℕ) {f g : ChaconOdometer × Bool → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hprefix : ∀ (x : ChaconOdometer) (b : Bool), g (x, b) = g (chaconPrefix N x, b))
    {C D : ℝ} (hD : 0 ≤ D) (hfb : ∀ x, ‖f x‖ ≤ C) (hgb : ∀ x, ‖g x‖ ≤ D) :
    Tendsto (fun j ↦ (∫ x, g x *
      f (chaconTowerSystem.act (Multiplicative.ofAdd ((m*chaconTowerHeight (n j) : ℕ) + s j)) x)
        ∂chaconTowerSystem.measure) -
      ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
        ∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ)+s j)) x)
          ∂chaconTowerSystem.measure) F (𝓝 0) := by
  let P (v : ℕ) (w : ℤ) := (∫ x, g x *
    f (chaconTowerSystem.act (Multiplicative.ofAdd ((m*chaconTowerHeight v : ℕ) + w)) x)
      ∂chaconTowerSystem.measure) -
      ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
        ∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd (-(k : ℤ)+w)) x)
          ∂chaconTowerSystem.measure
  exact tendsto_chaconRelativeRemainder_reindex hn hs (P := P)
    (fun r hr ↦ tendsto_chaconTower_movingRemainder_error m N r hr hf hg hprefix hD hfb hgb)

end Mixing
