/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Small weak neighborhoods in weakly compact sets

A binary splitting argument gives norm fragmentation of weakly compact
sets. The countably many points used at finite stages generate a separable
closed span. If the splitting continued forever, its compact weak closure
would contain uniformly norm-separated points indexed by all binary sequences.
-/

@[expose] public section

namespace JdLG

open Set TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "W" => WeakSpace ℂ E

/-- Distance in the original norm topology of two points of the weak space. -/
noncomputable abbrev weakDist (x y : W) : ℝ :=
  dist ((toWeakSpace ℂ E).symm x) ((toWeakSpace ℂ E).symm y)

/-- A norm-closed convex set is closed in the weak topology. -/
theorem isClosed_weak_image_of_closed_convex {C : Set E}
    (hC : IsClosed C) (hc : Convex ℝ C) :
    IsClosed (toWeakSpace ℂ E '' C) := by
  rw [← hC.closure_eq, hc.toWeakSpace_closure ℂ]
  exact isClosed_closure

private theorem separated_open_descendants (K : Set W) (ε : ℝ) (hε : 0 < ε)
    (U : Set K) (hU : IsOpen U) (x y : K) (hx : x ∈ U) (hy : y ∈ U)
    (hd : ε ≤ weakDist x.val y.val) :
    ∃ V₀ V₁ : Set K, IsOpen V₀ ∧ V₀.Nonempty ∧ V₀ ⊆ U ∧
      IsOpen V₁ ∧ V₁.Nonempty ∧ V₁ ⊆ U ∧
      ∀ a ∈ closure V₀, ∀ b ∈ closure V₁, ε / 2 ≤ weakDist a.val b.val := by
  let val (a : K) : E := (toWeakSpace ℂ E).symm a.val
  obtain ⟨f, hf, hfxy⟩ := exists_dual_vector'' ℂ (val x - val y)
  let g := f ∘ val
  have hcont : Continuous g :=
    (WeakBilin.eval_continuous (topDualPairing ℂ E).flip f).comp continuous_subtype_val
  have hgdist (a b : K) : dist (g a) (g b) ≤ weakDist a.val b.val := by
    change dist (f (val a)) (f (val b)) ≤ dist (val a) (val b)
    simp only [dist_eq_norm, ← map_sub]
    exact ((f.le_opNorm _).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg _))).trans_eq
      (one_mul _)
  have hgxy : dist (g x) (g y) = weakDist x.val y.val := by
    change dist (f (val x)) (f (val y)) = dist (val x) (val y)
    simp only [dist_eq_norm, ← map_sub, hfxy, RCLike.norm_ofReal, abs_norm]
  let V₀ := U ∩ g ⁻¹' Metric.ball (g x) (ε / 4)
  let V₁ := U ∩ g ⁻¹' Metric.ball (g y) (ε / 4)
  refine ⟨V₀, V₁, hU.inter (Metric.isOpen_ball.preimage hcont), ⟨x, hx, ?_⟩, inter_subset_left,
    hU.inter (Metric.isOpen_ball.preimage hcont), ⟨y, hy, ?_⟩, inter_subset_left, ?_⟩
  · exact Metric.mem_ball_self (by positivity)
  · exact Metric.mem_ball_self (by positivity)
  · intro a ha b hb
    have ha' : dist (g a) (g x) ≤ ε / 4 := closure_minimal (show V₀ ⊆
        g ⁻¹' Metric.closedBall (g x) (ε / 4) from
          fun _ hz ↦ Metric.ball_subset_closedBall hz.2)
        (Metric.isClosed_closedBall.preimage hcont) ha
    have hb' : dist (g b) (g y) ≤ ε / 4 := closure_minimal (show V₁ ⊆
        g ⁻¹' Metric.closedBall (g y) (ε / 4) from
          fun _ hz ↦ Metric.ball_subset_closedBall hz.2)
        (Metric.isClosed_closedBall.preimage hcont) hb
    have h₁ := dist_triangle (g x) (g a) (g y)
    have h₂ := dist_triangle (g a) (g b) (g y)
    rw [dist_comm (g x) (g a), hgxy] at h₁
    linarith [hgdist a b]

private theorem no_uniformly_separated_binary_family {X : Type*} [MetricSpace X]
    [SeparableSpace X] (f : (ℕ → Bool) → X) (ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ a b, dist (f a) (f b) < ε → a = b) : False := by
  obtain ⟨D, hD, hd⟩ := exists_countable_dense X
  choose d hdD hdlt using fun a ↦ hd.exists_dist_lt (f a) (by linarith : 0 < ε / 3)
  let g (a : ℕ → Bool) : D := ⟨d a, hdD a⟩
  have hi : Function.Injective g := by
    intro a b h
    have he : d a = d b := congrArg Subtype.val h
    apply hsep
    have h₁ := hdlt a
    have ht := dist_triangle (f a) (d a) (f b)
    rw [he] at h₁
    rw [dist_comm (d a) (f b), he] at ht
    linarith [hdlt b]
  let : Countable D := hD
  let : Countable (ℕ → Bool) := hi.countable
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := he (fun n ↦ !(e n n))
  exact (Bool.not_eq_self (e n n)).1 (congrFun hn n).symm

private def binaryPrefix (a : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => a n :: binaryPrefix a n

/-- Every nonempty weakly compact set contains a nonempty relatively weak-open
subset whose pairwise norm distances are smaller than any given positive
number. -/
theorem exists_small_weakOpen_of_weakCompact {K : Set W} (hK : IsCompact K) (hKn : K.Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set K, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, ∀ y ∈ U, weakDist x.val y.val < ε := by
  classical
  by_contra hcontra
  let : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let : Nonempty K := hKn.to_subtype
  let Node := {U : Set K // IsOpen U ∧ U.Nonempty}
  have hlarge (U : Node) : ∃ x ∈ U.val, ∃ y ∈ U.val, ε ≤ weakDist x.val y.val := by
    by_contra! h
    exact hcontra ⟨U.val, U.property.1, U.property.2, h⟩
  have hspl (U : Node) : ∃ V₀ V₁ : Node, V₀.val ⊆ U.val ∧ V₁.val ⊆ U.val ∧
      ∀ a ∈ closure V₀.val, ∀ b ∈ closure V₁.val, ε / 2 ≤ weakDist a.val b.val := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hlarge U
    obtain ⟨V₀, V₁, hV₀, hn₀, hs₀, hV₁, hn₁, hs₁, hs⟩ :=
      separated_open_descendants K ε hε U.val U.property.1 x y hx hy hxy
    exact ⟨⟨V₀, hV₀, hn₀⟩, ⟨V₁, hV₁, hn₁⟩, hs₀, hs₁, hs⟩
  choose left right hleft hright hsep using hspl
  let tree : List Bool → Node := List.rec ⟨univ, isOpen_univ, univ_nonempty⟩
    (fun b _ U ↦ if b then right U else left U)
  have htree (b : Bool) (t : List Bool) : (tree (b :: t)).val ⊆ (tree t).val := by
    cases b
    · exact hleft _
    · exact hright _
  let z (t : List Bool) : K := (tree t).property.2.choose
  let base (t : List Bool) : E := (toWeakSpace ℂ E).symm (z t).val
  let M := (Submodule.span ℂ (range base)).topologicalClosure
  have hM : IsSeparable (M : Set E) := (countable_range base).isSeparable.span.closure
  let : SeparableSpace M := hM.separableSpace
  let D : Set K := closure (range z)
  have hD (a : K) (ha : a ∈ D) : (toWeakSpace ℂ E).symm a.val ∈ M := by
    have hc : IsClosed (toWeakSpace ℂ E '' (M : Set E)) :=
      isClosed_weak_image_of_closed_convex (Submodule.isClosed_topologicalClosure _)
        ((M.restrictScalars ℝ).convex)
    have hm : a ∈ (Subtype.val : K → W) ⁻¹' (toWeakSpace ℂ E '' (M : Set E)) :=
      closure_minimal (fun p hp ↦ by
        obtain ⟨t, rfl⟩ := hp
        exact ⟨base t, Submodule.le_topologicalClosure _
          (Submodule.subset_span (mem_range_self t)), LinearEquiv.apply_symm_apply _ _⟩)
        (hc.preimage continuous_subtype_val) ha
    obtain ⟨v, hv, hveq⟩ := hm
    rw [← hveq, LinearEquiv.symm_apply_apply]
    exact hv
  have hbranch (b : ℕ → Bool) :
      ∃ a ∈ D, ∀ n, a ∈ closure (tree (binaryPrefix b n)).val := by
    let A (n : ℕ) := D ∩ closure (tree (binaryPrefix b n)).val
    have hclosed (n : ℕ) : IsClosed (A n) := isClosed_closure.inter isClosed_closure
    obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed A
      (fun n ↦ inter_subset_inter_right _ (closure_mono (htree _ _)))
      (fun n ↦ ⟨z (binaryPrefix b n), subset_closure (mem_range_self _),
        subset_closure (tree (binaryPrefix b n)).property.2.choose_spec⟩)
      (hclosed 0).isCompact hclosed
    exact ⟨a, (mem_iInter.1 ha 0).1, fun n ↦ (mem_iInter.1 ha n).2⟩
  choose p hpD hp using hbranch
  let f (b : ℕ → Bool) : M := ⟨(toWeakSpace ℂ E).symm (p b).val, hD _ (hpD b)⟩
  refine no_uniformly_separated_binary_family f (ε / 2) (by positivity) fun a b hab ↦ ?_
  change weakDist (p a).val (p b).val < ε / 2 at hab
  have hprefix (n : ℕ) : binaryPrefix a n = binaryPrefix b n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hbit : a n = b n := by
        have ha := hp a (n + 1)
        have hb := hp b (n + 1)
        cases h₀ : a n <;> cases h₁ : b n
        · rfl
        · have ha' : p a ∈ closure (left (tree (binaryPrefix b n))).val := by
            rw [binaryPrefix, h₀, ih] at ha
            exact ha
          have hb' : p b ∈ closure (right (tree (binaryPrefix b n))).val := by
            rw [binaryPrefix, h₁] at hb
            exact hb
          exact ((not_lt_of_ge (hsep _ _ ha' _ hb')) hab).elim
        · have hb' : p b ∈ closure (left (tree (binaryPrefix b n))).val := by
            rw [binaryPrefix, h₁] at hb
            exact hb
          have ha' : p a ∈ closure (right (tree (binaryPrefix b n))).val := by
            rw [binaryPrefix, h₀, ih] at ha
            exact ha
          have he := hsep _ _ hb' _ ha'
          have hcomm : weakDist (p b).val (p a).val = weakDist (p a).val (p b).val :=
            dist_comm _ _
          have he' := he.trans_eq hcomm
          exact ((not_lt_of_ge he') hab).elim
        · rfl
      simp only [binaryPrefix, hbit, ih]
  funext n
  exact Option.some.inj (congrArg List.head? (hprefix (n + 1)))

/-- The small weak-open subset may be chosen inside any given nonempty
relatively weak-open subset of a weakly compact set. -/
theorem exists_small_weakOpen_subset {K : Set W} (hK : IsCompact K)
    {O : Set K} (hO : IsOpen O) (hOn : O.Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set K, IsOpen U ∧ U.Nonempty ∧ U ⊆ O ∧
      ∀ x ∈ U, ∀ y ∈ U, weakDist x.val y.val < ε := by
  let C := closure ((Subtype.val : K → W) '' O)
  have hC : C ⊆ K := closure_minimal (image_subset_iff.2 fun x _ ↦ x.property) hK.isClosed
  obtain ⟨V, hV, ⟨v, hv⟩, hsmall⟩ := exists_small_weakOpen_of_weakCompact
    (hK.of_isClosed_subset isClosed_closure hC) (hOn.image _ |>.mono subset_closure) ε hε
  obtain ⟨V', hV', rfl⟩ := isOpen_induced_iff.1 hV
  have hhit := mem_closure_iff.1 v.property V' hV' hv
  obtain ⟨x, hxV', x', hx'O, rfl⟩ := hhit
  refine ⟨O ∩ (Subtype.val : K → W) ⁻¹' V', hO.inter (hV'.preimage continuous_subtype_val),
    ⟨x', hx'O, hxV'⟩, inter_subset_left, fun x hx y hy ↦ ?_⟩
  let xC : C := ⟨x.val, subset_closure (mem_image_of_mem _ hx.1)⟩
  let yC : C := ⟨y.val, subset_closure (mem_image_of_mem _ hy.1)⟩
  exact hsmall xC hx.2 yC hy.2

end JdLG
