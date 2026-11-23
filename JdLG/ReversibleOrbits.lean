/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Orbits
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.MetricSpace.Sequences

/-! # Compact norms of reversible orbits

A countable monoid generates a compact subgroup in a compact semitopological
group. An orbit of that subgroup is norm-separable by Hahn–Banach separation.
Baire category on the compact subgroup then upgrades weak orbit continuity
to norm continuity. The sequential criterion for compactness applies this
argument to an arbitrary sequence of points in the original orbit.
-/

@[expose] public section

open Filter Set Topology

namespace JdLG

section Bounds

variable {X 𝕜 E : Type*} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A weakly operator-continuous family indexed by a compact space is uniformly
bounded in operator norm on a Banach space. -/
theorem exists_operatorBound_of_compact_wot [CompleteSpace E] (A : X → E →L[𝕜] E)
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a, ‖A a‖ ≤ C := by
  have hpoint (x : E) : ∃ C, ∀ a, ‖A a x‖ ≤ C := by
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun a ↦ NormedSpace.inclusionInDoubleDual 𝕜 E (A a x)) fun f ↦ by
        have hcont : Continuous fun a ↦ ‖f (A a x)‖ :=
          ((ContinuousLinearMapWOT.continuous_dual_apply x f).comp hA).norm
        obtain ⟨B, hB⟩ := (isCompact_range hcont).bddAbove
        exact ⟨B, fun a ↦ hB (mem_range_self a)⟩
    refine ⟨C, fun a ↦ ?_⟩
    rw [← (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).norm_map (A a x)]
    exact hC a
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun a ↦ (hC a).trans (le_max_left _ _)⟩

end Bounds

section CompactGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [SeparatelyContinuousMul G]

private theorem exists_subgroup_topologicalClosure (M : Submonoid G) :
    ∃ H : Subgroup G, (H : Set G) = (M.topologicalClosure : Set G) := by
  let N := M.topologicalClosure
  have hInv {a : G} (ha : a ∈ N) : a⁻¹ ∈ N := by
    let A := (a * ·) '' (N : Set G)
    have hcompact : IsCompact A := M.isClosed_topologicalClosure.isCompact.image
      (continuous_const_mul a)
    have hnonempty : A.Nonempty := ⟨a * 1, 1, N.one_mem, rfl⟩
    have hmul : ∀ p ∈ A, ∀ q ∈ A, p * q ∈ A := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      exact ⟨p * (a * q), N.mul_mem hp (N.mul_mem ha hq), (mul_assoc a p (a * q)).symm⟩
    obtain ⟨e, he, hee⟩ := exists_idempotent_in_compact_subsemigroup continuous_mul_const
      A hnonempty hcompact hmul
    have he1 : e = 1 := mul_left_cancel (hee.trans (mul_one e).symm)
    obtain ⟨y, hy, hay⟩ := he
    change a * y = e at hay
    have hy1 : y = a⁻¹ := by calc
      y = a⁻¹ * (a * y) := by simp
      _ = a⁻¹ := by rw [hay, he1, mul_one]
    exact hy1 ▸ hy
  exact ⟨{ N with inv_mem' := hInv }, rfl⟩

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem isClosed_image_convex_toWeakSpace {C : Set E} [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [LocallyConvexSpace ℝ E] (hC : IsClosed C) (hcC : Convex ℝ C) :
    IsClosed (toWeakSpace 𝕜 E '' C) := by
  rw [← hC.closure_eq, hcC.toWeakSpace_closure 𝕜]
  exact isClosed_closure

variable (A : G →ₙ* (E →L[𝕜] E))

omit [CompactSpace G] [T2Space G] [SeparatelyContinuousMul G] in
private theorem continuous_weak_eval
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) (x : E) :
    Continuous fun a ↦ toWeakSpace 𝕜 E (A a x) :=
  WeakBilin.continuous_of_continuous_eval _ fun f ↦
    (ContinuousLinearMapWOT.continuous_dual_apply x f).comp hA

private theorem continuous_orbit_of_separable
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ a, ‖A a‖ ≤ C) (x : E)
    (hs : TopologicalSpace.IsSeparable (range fun a ↦ A a x)) :
    Continuous fun a ↦ A a x := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  have hweak := continuous_weak_eval A hA x
  obtain ⟨D, hcD, hD⟩ := hs
  let : Countable D := hcD.to_subtype
  apply continuous_iff_continuousAt.2
  intro b
  apply Metric.tendsto_nhds.2
  intro ε hε
  let r := ε / (4 * C)
  have hr : 0 < r := div_pos hε (mul_pos (by norm_num) hC)
  let F (v : D) : Set G := {a | A a x ∈ Metric.closedBall (v : E) r}
  have hclosed (v : D) : IsClosed (F v) := by
    have hweakClosed := isClosed_image_convex_toWeakSpace (𝕜 := 𝕜)
      (Metric.isClosed_closedBall (x := (v : E)) (ε := r)) (convex_closedBall _ _)
    convert hweakClosed.preimage hweak using 1
    ext a
    simp only [F, mem_ofPred_eq, mem_preimage, mem_image]
    exact ⟨fun h ↦ ⟨_, h, rfl⟩,
      fun ⟨y, hy, heq⟩ ↦ (toWeakSpace 𝕜 E).injective heq ▸ hy⟩
  have hcover : (⋃ v, F v) = univ := by
    apply eq_univ_of_forall
    intro a
    obtain ⟨v, hv, hva⟩ := Metric.mem_closure_iff.1 (hD (mem_range_self a)) r hr
    exact mem_iUnion.2 ⟨⟨v, hv⟩, hva.le⟩
  obtain ⟨v, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have hba : (a * b⁻¹) * b = a := by simp [mul_assoc]
  have hev : ∀ᶠ g in 𝓝 b, (a * b⁻¹) * g ∈ F v := by
    apply (continuous_const_mul (a * b⁻¹)).continuousAt (x := b)
    change F v ∈ 𝓝 ((a * b⁻¹) * b)
    rw [hba]
    exact mem_interior_iff_mem_nhds.1 ha
  have hau : a ∈ F v := interior_subset ha
  have hav : A a x ∈ Metric.closedBall (v : E) r := hau
  filter_upwards [hev] with g hg
  have hd : dist (A ((a * b⁻¹) * g) x) (A a x) ≤ r + r :=
    (dist_triangle_right _ _ _).trans (add_le_add hg hav)
  have hfirst : A (b * a⁻¹) (A ((a * b⁻¹) * g) x) = A g x := by
    change (A (b * a⁻¹) * A ((a * b⁻¹) * g)) x = _
    rw [← map_mul]
    simp [mul_assoc]
  have hsecond : A (b * a⁻¹) (A a x) = A b x := by
    change (A (b * a⁻¹) * A a) x = _
    rw [← map_mul]
    simp [mul_assoc]
  calc
    dist (A g x) (A b x) =
        ‖A (b * a⁻¹) (A ((a * b⁻¹) * g) x - A a x)‖ := by
      rw [map_sub, hfirst, hsecond, dist_eq_norm]
    _ ≤ C * dist (A ((a * b⁻¹) * g) x) (A a x) := by
      rw [dist_eq_norm]
      exact (A (b * a⁻¹)).le_of_opNorm_le (hbound _) _
    _ ≤ C * (r + r) := mul_le_mul_of_nonneg_left hd hC.le
    _ < ε := by
      have hEq : C * (r + r) = ε / 2 := by
        dsimp only [r]
        field_simp
        ring
      rw [hEq]
      linarith

private theorem countable_submonoid_of_countable {M : Type*} [Monoid M] {s : Set M}
    (hs : s.Countable) : (Submonoid.closure s : Set M).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := FreeMonoid.toListEquiv.injective.countable
  rw [Submonoid.closure_eq_mrange]
  exact countable_range _

/-- A weakly continuous action of a compact semitopological group by bounded
operators on a Banach space has norm-compact orbits. The representation need
only be multiplicative. Its identity operator may be a projection. -/
theorem isCompact_normOrbit_of_wot [CompleteSpace E]
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) (x : E) :
    IsCompact (range fun a ↦ A a x) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot (fun a ↦ A a) hA
  apply IsSeqCompact.isCompact
  intro u hu
  choose g hg using hu
  let M : Submonoid G := Submonoid.closure (range g)
  obtain ⟨H, hH⟩ := exists_subgroup_topologicalClosure M
  have hMc : (M : Set G).Countable := countable_submonoid_of_countable (countable_range g)
  let D := (fun a : G ↦ A a x) '' (M : Set G)
  let V : Set E := Submodule.span ℝ D
  have hV : Convex ℝ V := (Submodule.span ℝ D).convex
  have hWeakClosed := isClosed_image_convex_toWeakSpace (𝕜 := 𝕜) isClosed_closure hV.closure
  have hWeakSub : (M : Set G) ⊆
      (fun a : G ↦ toWeakSpace 𝕜 E (A a x)) ⁻¹' (toWeakSpace 𝕜 E '' closure V) :=
    fun a ha ↦ ⟨A a x, subset_closure (Submodule.subset_span ⟨a, ha, rfl⟩), rfl⟩
  have hHclosed : IsClosed (H : Set G) := hH ▸ isClosed_closure
  let : CompactSpace H := isCompact_iff_compactSpace.1 hHclosed.isCompact
  let : SeparatelyContinuousMul H := IsInducing.separatelyContinuousMul H.subtype (by
    rw [H.coe_subtype]
    exact IsInducing.subtypeVal)
  have hclosure := closure_minimal hWeakSub (hWeakClosed.preimage (continuous_weak_eval A hA x))
  have hOrbitSub : range (fun a : H ↦ A a.1 x) ⊆ closure V := by
    rintro _ ⟨a, rfl⟩
    have ha : a.1 ∈ closure (M : Set G) := by
      change a.1 ∈ (M.topologicalClosure : Set G)
      rw [← hH]
      exact a.2
    obtain ⟨z, hz, he⟩ := hclosure ha
    change A a.1 x ∈ closure V
    rwa [← (toWeakSpace 𝕜 E).injective he]
  have hsep : TopologicalSpace.IsSeparable (range fun a : H ↦ A a.1 x) :=
    ((hMc.image _).isSeparable.span.closure).mono hOrbitSub
  have hcont := continuous_orbit_of_separable (A.comp H.subtype.toMulHom)
    (hA.comp continuous_subtype_val) hC (fun a ↦ hbound a) x hsep
  have hseq := (isCompact_range hcont).isSeqCompact
  have huH (n : ℕ) : u n ∈ range (fun a : H ↦ A a.1 x) := by
    have hn : g n ∈ H := by
      change g n ∈ (H : Set G)
      rw [hH]
      exact M.le_topologicalClosure (Submonoid.subset_closure (mem_range_self n))
    exact ⟨⟨g n, hn⟩, hg n⟩
  obtain ⟨y, ⟨a, rfl⟩, φ, hφ, huφ⟩ := hseq huH
  exact ⟨A a.1 x, mem_range_self a.1, φ, hφ, huφ⟩

end CompactGroup

end JdLG
