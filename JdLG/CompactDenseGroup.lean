/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import JdLG.CompactSeparateOscillation
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Algebra.Monoid

/-! # A compact semitopological monoid with a dense group image -/

@[expose] public section

open Set Filter
open scoped Topology

namespace JdLG

section DenseGroup

variable {G T : Type*} [Group G] [Monoid T] [TopologicalSpace T] [CompactSpace T]
    [T2Space T] [SeparatelyContinuousMul T]

private def leftActionOnIdeal {L : Set T} (hL : LeftIdeal L) (a : T) (x : L) : L :=
  ⟨a * (x : T), hL a x.property⟩

omit [CompactSpace T] [T2Space T] in
private theorem continuous_leftActionOnIdeal_left {L : Set T}
    (hL : LeftIdeal L) (x : L) :
    Continuous (leftActionOnIdeal hL · x) :=
  (continuous_mul_const (x : T)).subtype_mk _

omit [CompactSpace T] [T2Space T] in
private theorem continuous_leftActionOnIdeal_right {L : Set T}
    (hL : LeftIdeal L) (a : T) :
    Continuous (leftActionOnIdeal hL a) :=
  ((continuous_const_mul a).comp continuous_subtype_val).subtype_mk _

omit [TopologicalSpace T] [CompactSpace T] [T2Space T] [SeparatelyContinuousMul T] in
private theorem leftActionOnIdeal_mul {L : Set T} (hL : LeftIdeal L) (a b : T) (x : L) :
    leftActionOnIdeal hL a (leftActionOnIdeal hL b x) = leftActionOnIdeal hL (a * b) x :=
  Subtype.ext (mul_assoc a b x.val).symm

omit [CompactSpace T] [T2Space T] in
private theorem denseRange_leftActionOnMinimalLeftIdeal (i : G →* T) (hi : DenseRange i)
    {L : Set T} (hL : MinimalLeftIdeal L) (x : L) :
    DenseRange (fun g : G ↦ leftActionOnIdeal hL.2.1 (i g) x) := by
  have hs : Function.Surjective (leftActionOnIdeal hL.2.1 · x) := by
    intro y
    have hy : (y : T) ∈ range (· * (x : T)) :=
      (principal_eq_of_minimalLeftIdeal hL x.property).symm ▸ y.property
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, Subtype.ext ha⟩
  exact hs.denseRange.comp hi (continuous_leftActionOnIdeal_left hL.2.1 x)

/-- Every ambient left translation is injective on a compact minimal left
ideal if the ambient semitopological monoid has a dense group image. -/
theorem left_mul_injOn_minimalLeftIdeal_of_denseGroup (i : G →* T) (hi : DenseRange i)
    {L : Set T} (hL : MinimalLeftIdeal L) (hCompact : IsCompact L) (a : T) :
    InjOn (fun x ↦ a * x) L := by
  let : CompactSpace L := isCompact_iff_compactSpace.mp hCompact
  let : Nonempty L := hL.1.coe_sort
  let act := leftActionOnIdeal hL.2.1
  have hActL (x : L) : Continuous (act · x) :=
    continuous_leftActionOnIdeal_left hL.2.1 x
  have hActR (a : T) : Continuous (act a) :=
    continuous_leftActionOnIdeal_right hL.2.1 a
  have hAct (a b : T) (x : L) : act a (act b x) = act (a * b) x :=
    leftActionOnIdeal_mul hL.2.1 a b x
  intro x₀ hx₀ y₀ hy₀ hxy
  let x : L := ⟨x₀, hx₀⟩
  let y : L := ⟨y₀, hy₀⟩
  have hxy' : act a x = act a y := Subtype.ext hxy
  by_contra hNot
  have hxyNe : x ≠ y := fun h ↦ hNot (congrArg Subtype.val h)
  have hd : Disjoint ({x} : Set L) {y} := by simpa only [disjoint_singleton] using hxyNe
  obtain ⟨f, hfx, hfy, _⟩ :=
    exists_continuous_zero_one_of_isClosed isClosed_singleton isClosed_singleton hd
  have hfx' : f x = 0 := hfx (mem_singleton x)
  have hfy' : f y = 1 := hfy (mem_singleton y)
  let F (x : L) (s : T) := f (act s x)
  obtain ⟨U, hU, hU0, hSmall⟩ := exists_open_small_oscillation F
    (fun s ↦ f.continuous.comp (hActR s)) (fun z ↦ f.continuous.comp (hActL z))
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨g, hg⟩ := DenseRange.exists_mem_open
    (denseRange_leftActionOnMinimalLeftIdeal i hi hL (act a x)) hU hU0
  let W := (fun (s : T) ↦ act (i g) (act s x)) ⁻¹' U ∩
    (fun (s : T) ↦ act (i g) (act s y)) ⁻¹' U
  have hW : IsOpen W :=
    (hU.preimage ((hActR (i g)).comp (hActL x))).inter
      (hU.preimage ((hActR (i g)).comp (hActL y)))
  have haW : a ∈ W := ⟨hg, show act (i g) (act a y) ∈ U from hxy' ▸ hg⟩
  obtain ⟨k, hk⟩ := hi.exists_mem_open hW ⟨a, haW⟩
  have hx' : act (i (g * k)) x ∈ U := by
    rw [map_mul, ← hAct]
    exact hk.1
  have hy' : act (i (g * k)) y ∈ U := by
    rw [map_mul, ← hAct]
    exact hk.2
  have hBack (z : L) : act (i (g * k)⁻¹) (act (i (g * k)) z) = z := by
    rw [hAct, ← map_mul, inv_mul_cancel, map_one]
    exact Subtype.ext (one_mul z.val)
  have hSmall' := hSmall _ hx' _ hy' (i (g * k)⁻¹)
  change dist (f (act (i (g * k)⁻¹) (act (i (g * k)) x)))
    (f (act (i (g * k)⁻¹) (act (i (g * k)) y))) ≤ (1 / 2 : ℝ) at hSmall'
  rw [hBack, hBack, hfx', hfy'] at hSmall'
  norm_num [Real.dist_eq] at hSmall'

private theorem exists_minimalLeftIdeal_of_minimalIdempotent {e : T}
    (he : IsMinimalIdempotent e) :
    ∃ L : Set T, IsCompact L ∧ MinimalLeftIdeal L ∧ e ∈ L := by
  obtain ⟨L, hCompact, hL⟩ := exists_compact_minimalLeftIdeal
    (fun s : T ↦ continuous_mul_const s)
  let M := (· * e) '' L
  have hM : MinimalLeftIdeal M := minimalLeftIdeal_image hL e
  have hMc : IsCompact M := hCompact.image (continuous_mul_const e)
  obtain ⟨p, hp, hpp⟩ := exists_idempotent_in_compact_subsemigroup continuous_mul_const
    M hM.1 hMc (fun a _ _ hb ↦ hM.2.1 a hb)
  have hpe : p * e = p := by
    obtain ⟨q, _, rfl⟩ := hp
    change (q * e) * e = q * e
    rw [mul_assoc, he.1]
  have hef : e * (e * p) = e * p := by rw [← mul_assoc, he.1]
  have hfe : (e * p) * e = e * p := by rw [mul_assoc, hpe]
  have hff : (e * p) * (e * p) = e * p := by rw [← mul_assoc, hfe, mul_assoc, hpp]
  have hEq := he.2 (e * p) hff hfe hef
  exact ⟨M, hMc, hM, hEq ▸ hM.2.1 e hp⟩

private theorem idempotent_mul_minimalIdempotent_of_denseGroup (i : G →* T) (hi : DenseRange i)
    {a e : T} (ha : a * a = a) (he : IsMinimalIdempotent e) : a * e = e := by
  obtain ⟨L, hCompact, hL, heL⟩ := exists_minimalLeftIdeal_of_minimalIdempotent he
  exact left_mul_injOn_minimalLeftIdeal_of_denseGroup i hi hL hCompact a
    (hL.2.1 a heL) heL (by change a * (a * e) = a * e; rw [← mul_assoc, ha])

/-- A compact Hausdorff semitopological monoid with a dense group image has
a unique minimal idempotent. No amenability of the group is needed. -/
theorem existsUnique_minimalIdempotent_of_denseGroup (i : G →* T) (hi : DenseRange i) :
    ∃! e : T, IsMinimalIdempotent e := by
  obtain ⟨L, hCompact, hL⟩ := exists_compact_minimalLeftIdeal
    (fun s : T ↦ continuous_mul_const s)
  obtain ⟨e, heL, hee⟩ := exists_idempotent_in_compact_subsemigroup continuous_mul_const
    L hL.1 hCompact (fun a _ _ hb ↦ hL.2.1 a hb)
  have he := isMinimalIdempotent_of_mem_minimalLeftIdeal hL heL hee
  refine ⟨e, he, fun f hf ↦ ?_⟩
  have hfe := idempotent_mul_minimalIdempotent_of_denseGroup i hi hf.1 he
  let j : Gᵐᵒᵖ →* Tᵐᵒᵖ :=
    { toFun := fun g ↦ MulOpposite.op (i (MulOpposite.unop g))
      map_one' := by simp
      map_mul' := by intro a b; simp }
  have hOp : DenseRange (fun g : G ↦ MulOpposite.op (i g)) :=
    MulOpposite.op_surjective.denseRange.comp hi MulOpposite.continuous_op
  have hj : DenseRange j := by
    intro a
    exact closure_mono (by rintro _ ⟨g, rfl⟩; exact ⟨MulOpposite.op g, rfl⟩) (hOp a)
  have hfOp : IsMinimalIdempotent (MulOpposite.op f) := by
    refine ⟨congrArg MulOpposite.op hf.1, fun p hpp hpf hfp ↦ ?_⟩
    exact MulOpposite.unop_injective
      (hf.2 (MulOpposite.unop p) (congrArg MulOpposite.unop hpp)
        (congrArg MulOpposite.unop hfp) (congrArg MulOpposite.unop hpf))
  have hOpp := idempotent_mul_minimalIdempotent_of_denseGroup j hj
    (congrArg MulOpposite.op he.1) hfOp
  have hfe' : f * e = f := congrArg MulOpposite.unop hOpp
  exact hfe'.symm.trans hfe

end DenseGroup

end JdLG
