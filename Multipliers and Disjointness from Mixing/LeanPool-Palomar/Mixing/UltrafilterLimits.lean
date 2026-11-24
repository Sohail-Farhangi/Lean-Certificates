/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.UltrafilterAction

/-! # Detecting ultrafilter operations by compact metric limits -/

@[expose] public section

open Filter Set
open scoped Mixing Topology

namespace Mixing

/-- An iterated limit in any compact Hausdorff target computes the Stone–Čech product. -/
theorem ultrafilterExtend_comp_mul {G X : Type*} [Mul G] [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (f : G → X) (p q : Ultrafilter G) :
    haveI := Ultrafilter.mul (M := G)
    Ultrafilter.extend f (p * q) =
      Ultrafilter.extend (fun a => Ultrafilter.extend (fun b => f (a * b)) q) p := by
  let _ := Ultrafilter.mul (M := G)
  apply ultrafilter_extend_eq_iff.mpr
  change Tendsto f ((p * q : Ultrafilter G) : Filter G) _
  rw [Filter.tendsto_def]
  intro V hV
  obtain ⟨O, hOV, hOpen, hlim⟩ := mem_nhds_iff.mp hV
  change ∀ᶠ c in ((p * q : Ultrafilter G) : Filter G), f c ∈ V
  rw [Ultrafilter.eventually_mul]
  have hOuter : ∀ᶠ a in (p : Filter G), Ultrafilter.extend (fun b => f (a * b)) q ∈ O :=
    (tendsto_ultrafilterExtend _ p).eventually (hOpen.mem_nhds hlim)
  filter_upwards [hOuter] with a ha
  have hInner : ∀ᶠ b in (q : Filter G), f (a * b) ∈ O :=
    (tendsto_ultrafilterExtend _ q).eventually (hOpen.mem_nhds ha)
  filter_upwards [hInner] with b hb
  exact hOV hb

/-- Compact Hausdorff limits commute with pushforward of the index ultrafilter. -/
theorem ultrafilterExtend_comp_map {A B X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (f : B → X) (g : A → B) (p : Ultrafilter A) :
    Ultrafilter.extend f (p.map g) = Ultrafilter.extend (f ∘ g) p := by
  symm
  apply ultrafilter_extend_eq_iff.mpr
  exact (tendsto_ultrafilterExtend f (p.map g)).comp tendsto_map

/-- Compact metric test functions distinguish ultrafilters. The test is the
indicator of an arbitrary subset with values in the two-point subspace of ℝ. -/
theorem ultrafilter_eq_of_compact_metric_tests {A : Type*} {p q : Ultrafilter A}
    (h : ∀ (X : Type) [MetricSpace X] [CompactSpace X] (f : A → X),
      Ultrafilter.extend f p = Ultrafilter.extend f q) : p = q := by
  classical
  let C : Set ℝ := {0, 1}
  have hC : C.Finite := (finite_singleton (1 : ℝ)).insert 0
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  let one : C := ⟨1, Or.inr rfl⟩
  let zero : C := ⟨0, Or.inl rfl⟩
  have hne : zero ≠ one := fun he => zero_ne_one (congrArg Subtype.val he)
  apply Ultrafilter.coe_inj.mp
  apply le_antisymm
  all_goals
    intro S hS
    let f : A → C := fun a => if a ∈ S then one else zero
    have ht {r : Ultrafilter A} (hr : S ∈ r) : Ultrafilter.extend f r = one := by
      apply ultrafilter_extend_eq_iff.mpr
      apply tendsto_const_nhds.congr'
      filter_upwards [hr] with a ha
      exact (ite_eq_left ha).symm
    have hf {r : Ultrafilter A} (hr : S ∉ r) : Ultrafilter.extend f r = zero := by
      apply ultrafilter_extend_eq_iff.mpr
      apply tendsto_const_nhds.congr'
      filter_upwards [Ultrafilter.compl_mem_iff_notMem.mpr hr] with a ha
      exact (ite_eq_right ha).symm
  · by_contra hSn
    exact hne (calc zero = Ultrafilter.extend f p := (hf hSn).symm
      _ = Ultrafilter.extend f q := @h C _ _ f
      _ = one := ht hS)
  · by_contra hSn
    exact hne (calc zero = Ultrafilter.extend f q := (hf hSn).symm
      _ = Ultrafilter.extend f p := (@h C _ _ f).symm
      _ = one := ht hS)

/-- Proposition 1(i). The Stone–Čech product is characterized by its iterated
limits in compact metric spaces. -/
theorem ultrafilter_mul_iff_compact_metric_tests {G : Type*} [Semigroup G] (p q r : Ultrafilter G) :
    r = p * q ↔ ∀ (X : Type) [MetricSpace X] [CompactSpace X] (f : G → X),
      Ultrafilter.extend f r =
        Ultrafilter.extend (fun a => Ultrafilter.extend (fun b => f (a * b)) q) p := by
  constructor
  · rintro rfl X _ _ f
    exact ultrafilterExtend_comp_mul f p q
  · intro h
    apply ultrafilter_eq_of_compact_metric_tests
    intro X _ _ f
    rw [ultrafilterExtend_comp_mul]
    exact @h X _ _ f

/-- Proposition 1(ii). Inverting the indices characterizes the inverse
ultrafilter. -/
theorem inverseUltrafilter_iff_compact_metric_tests {G : Type*} [Group G] (p r : Ultrafilter G) :
    r = inverseUltrafilter p ↔ ∀ (X : Type) [MetricSpace X] [CompactSpace X] (f : G → X),
      Ultrafilter.extend f r = Ultrafilter.extend (fun a => f a⁻¹) p := by
  constructor
  · rintro rfl X _ _ f
    exact ultrafilterExtend_comp_map f Inv.inv p
  · intro h
    apply ultrafilter_eq_of_compact_metric_tests
    intro X _ _ f
    rw [inverseUltrafilter, ultrafilterExtend_comp_map]
    exact @h X _ _ f

/-- Remark 4. Convergence on an injective sequence is equivalent to convergence
along every free ultrafilter containing the range of the sequence. -/
theorem tendsto_injective_sequence_iff {G X : Type*} [TopologicalSpace X]
    (g : ℕ → G) (hg : Function.Injective g) (f : G → X) (x : X) :
    Tendsto (f ∘ g) atTop (𝓝 x) ↔
      ∀ p : Ultrafilter G, (p : Filter G) ≤ cofinite → Set.range g ∈ p →
        Tendsto f (p : Filter G) (𝓝 x) := by
  rw [← Filter.tendsto_map'_iff, Filter.tendsto_iff_ultrafilter]
  have hFilter (p : Ultrafilter G) :
      (p : Filter G) ≤ Filter.map g atTop ↔
      (p : Filter G) ≤ cofinite ∧ Set.range g ∈ p := by
    constructor
    · intro hp
      refine ⟨hp.trans (Nat.cofinite_eq_atTop ▸ hg.tendsto_cofinite), hp ?_⟩
      exact Filter.mem_map.mpr (Filter.Eventually.of_forall fun n => Set.mem_range_self n)
    · rintro ⟨hp, hRange⟩
      intro S hS
      have hFin : (g ⁻¹' S)ᶜ.Finite := by
        apply Filter.mem_cofinite.mp
        exact Nat.cofinite_eq_atTop.symm ▸ Filter.mem_map.mp hS
      have hCompl : (g '' (g ⁻¹' S)ᶜ)ᶜ ∈ p := hp (hFin.image g).compl_mem_cofinite
      filter_upwards [hRange, hCompl] with a ha haz
      obtain ⟨n, rfl⟩ := ha
      by_contra hn
      exact haz ⟨n, hn, rfl⟩
  simp only [hFilter, and_imp]

end Mixing
