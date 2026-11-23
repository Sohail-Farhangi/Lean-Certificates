/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Tactic.Linarith

/-! # Small oscillation for separate continuity on compact Hausdorff spaces

The compact case of Namioka's argument uses a minimal closed set projecting
onto the first factor and then a double sequence. Only a single nonempty
open set of small oscillation is needed here.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace JdLG

section Oscillation

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]

private def FiberCover (C : Set (X × Y)) : Prop :=
  ∀ x : X, ∃ y : Y, (x, y) ∈ C

omit [CompactSpace X] [T2Space X] [T2Space Y] in
private theorem exists_minimal_closed_fiberCover {C : Set (X × Y)}
    (hC : IsClosed C) (hc : FiberCover C) :
    ∃ D : Set (X × Y), IsClosed D ∧ D ⊆ C ∧ FiberCover D ∧
      ∀ U : Set (X × Y), IsClosed U → U ⊆ D → FiberCover U → U = D := by
  let P : Set (Set (X × Y)) := {D | IsClosed D ∧ D ⊆ C ∧ FiberCover D}
  have hMin : ∃ D, Minimal (· ∈ P) D := by
    refine zorn_superset _ fun A hA hChain ↦ ?_
    obtain hEmpty | hNonempty := A.eq_empty_or_nonempty
    · refine ⟨C, ⟨hC, subset_rfl, hc⟩, ?_⟩
      simp only [hEmpty, forall_mem_empty]
    · refine ⟨⋂₀ A, ⟨isClosed_sInter (fun U hU ↦ (hA hU).1), ?_, ?_⟩,
        fun U hU ↦ sInter_subset_of_mem hU⟩
      · obtain ⟨U, hU⟩ := hNonempty
        exact (sInter_subset_of_mem hU).trans (hA hU).2.1
      · intro x
        let : Nonempty A := hNonempty.coe_sort
        let F (a : A) := (fun y ↦ (x, y)) ⁻¹' (a : Set (X × Y))
        have hClosed (a : A) : IsClosed (F a) :=
          (hA a.property).1.preimage (continuous_const.prodMk continuous_id)
        have hNE (a : A) : (F a).Nonempty := (hA a.property).2.2 x
        have hDir : Directed (· ⊇ ·) F := by
          intro a b
          rcases hChain.total a.property b.property with h | h
          · exact ⟨a, subset_rfl, preimage_mono h⟩
          · exact ⟨b, preimage_mono h, subset_rfl⟩
        obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          F hDir hNE (fun a ↦ (hClosed a).isCompact) hClosed
        exact ⟨y, mem_sInter.mpr fun U hU ↦ mem_iInter.mp hy ⟨U, hU⟩⟩
  obtain ⟨D, hD⟩ := hMin
  exact ⟨D, hD.prop.1, hD.prop.2.1, hD.prop.2.2,
    fun U hU huD hCo ↦ hD.eq_of_subset ⟨hU, huD.trans hD.prop.2.1, hCo⟩ huD⟩

private def rectangleGood (f : X → Y → ℝ) (ε : ℝ) : Set (X × Y) :=
  ⋃₀ {R | ∃ U : Set X, ∃ V : Set Y, IsOpen U ∧ IsOpen V ∧ R = U ×ˢ V ∧
    ∀ x ∈ U, ∀ y ∈ V, ∀ u ∈ U, ∀ v ∈ V, dist (f x y) (f u v) ≤ ε}

omit [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y] in
private theorem isOpen_rectangleGood (f : X → Y → ℝ) (ε : ℝ) :
    IsOpen (rectangleGood f ε) := by
  apply isOpen_sUnion
  rintro _ ⟨U, V, hU, hV, rfl, _⟩
  exact hU.prod hV

omit [CompactSpace X] [T2Space X] [T2Space Y] in
private theorem exists_open_small_oscillation_of_fiber
    (f : X → Y → ℝ) (ε : ℝ) {x : X} (hx : ∀ y, (x, y) ∈ rectangleGood f ε) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ a ∈ U, ∀ b ∈ U, ∀ y, dist (f a y) (f b y) ≤ ε := by
  have hRect (y : Y) := mem_sUnion.mp (hx y)
  choose R hR hmem using hRect
  have hRect' (y : Y) :
      ∃ U : Set X, ∃ V : Set Y, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
          ∀ a ∈ U, ∀ v ∈ V, ∀ b ∈ U, ∀ w ∈ V, dist (f a v) (f b w) ≤ ε := by
    obtain ⟨U, V, hU, hV, hEq, hDist⟩ := hR y
    have hxy := hmem y
    rw [hEq] at hxy
    exact ⟨U, V, hU, hV, hxy.1, hxy.2, hDist⟩
  choose U V hU hV hxU hyV hDist using hRect'
  have hCover : univ ⊆ ⋃ y, V y := fun y _ ↦ mem_iUnion.mpr ⟨y, hyV y⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover V hV hCover
  refine ⟨⋂ y ∈ I, U y, isOpen_biInter_finset (fun y _ ↦ hU y), ?_, ?_⟩
  · exact mem_iInter.mpr fun y ↦ mem_iInter.mpr fun _ ↦ hxU y
  · intro a ha b hb y
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hI (mem_univ y))
    obtain ⟨hiI, hy⟩ := mem_iUnion.mp hi
    exact hDist i a (mem_iInter.mp (mem_iInter.mp ha i) hiI) y hy
      b (mem_iInter.mp (mem_iInter.mp hb i) hiI) y hy

omit [T2Space Y] in
private theorem exists_oscillation_witness (f : X → Y → ℝ)
    (hLeft : ∀ y, Continuous (fun x ↦ f x y)) {ε : ℝ} (hε : 0 < ε)
    {D : Set (X × Y)} (hD : IsClosed D) (hBad : D ⊆ (rectangleGood f ε)ᶜ)
    (hCo : FiberCover D)
    (hMin : ∀ D' : Set (X × Y), IsClosed D' → D' ⊆ D → FiberCover D' → D' = D)
    {V : Set X} (hV : IsOpen V) {W : Set Y} (hW : IsOpen W) (hMeet : (D ∩ (V ×ˢ W)).Nonempty) :
    ∃ (u : X) (v w : Y), u ∈ V ∧ v ∈ W ∧ w ∈ W ∧ (u, w) ∈ D ∧
      ε / 6 ≤ dist (f u v) (f u w) := by
  classical
  let D' := D \ (V ×ˢ W)
  have hD' : IsClosed D' := hD.sdiff (hV.prod hW)
  have hNot : ¬ FiberCover D' := by
    intro h
    obtain ⟨p, hpD, hpR⟩ := hMeet
    have heq := hMin D' hD' sdiff_subset h
    exact ((heq.symm ▸ hpD : p ∈ D').2) hpR
  have hxTrue : ∃ x : X, ∀ y : Y, (x, y) ∉ D' := by
    simpa only [FiberCover, not_forall, not_exists] using hNot
  obtain ⟨x, hx⟩ := hxTrue
  obtain ⟨z, hz⟩ := hCo x
  have hzR : (x, z) ∈ V ×ˢ W := not_not.mp (fun hzR ↦ hx z ⟨hz, hzR⟩)
  let N : Set X := V ∩ (Prod.fst '' D')ᶜ ∩
    (fun u ↦ f u z) ⁻¹' Metric.ball (f x z) (ε / 6)
  have hN : IsOpen N :=
    (hV.inter (hD'.isCompact.image continuous_fst).isClosed.isOpen_compl).inter
      (Metric.isOpen_ball.preimage (hLeft z))
  have hxN : x ∈ N := ⟨⟨hzR.1, by
    rintro ⟨⟨u, v⟩, huv, rfl⟩
    exact hx v huv⟩, Metric.mem_ball_self (by positivity)⟩
  have hPick (u : X) (hu : u ∈ N) :
      ∃ w ∈ W, (u, w) ∈ D := by
    obtain ⟨w, hw⟩ := hCo u
    have hwR : (u, w) ∈ V ×ˢ W := not_not.mp (fun hwR ↦ hu.1.2 ⟨(u, w), ⟨hw, hwR⟩, rfl⟩)
    exact ⟨w, hwR.2, hw⟩
  by_contra hNo
  have hNear (u : X) (hu : u ∈ N) (v : Y) (hv : v ∈ W) :
      dist (f u v) (f x z) < ε / 2 := by
    obtain ⟨w, hw, huw⟩ := hPick u hu
    have h₁ (v : Y) (hv : v ∈ W) : dist (f u v) (f u w) < ε / 6 :=
      lt_of_not_ge (fun hh ↦ hNo ⟨u, v, w, hu.1.1, hv, hw, huw, hh⟩)
    have h₂ : dist (f u z) (f x z) < ε / 6 := hu.2
    have h₃ := dist_triangle_right (f u v) (f u z) (f u w)
    have h₄ := dist_triangle (f u v) (f u z) (f x z)
    linarith [h₁ v hv, h₁ z hzR.2]
  have hf : (x, z) ∈ rectangleGood f ε := by
    refine mem_sUnion.mpr ⟨N ×ˢ W, ⟨N, W, hN, hW, rfl, ?_⟩, hxN, hzR.2⟩
    intro a ha v hv b hb w hw
    linarith [dist_triangle_right (f a v) (f b w) (f x z), hNear a ha v hv, hNear b hb w hw]
  exact hBad hz hf

end Oscillation

private structure OscillationHistory {A : Type*} (P : A → Prop) (R : A → A → Prop) where
  latest : A
  rest : List A
  good : ∀ a ∈ latest :: rest, P a
  ordered : (latest :: rest).Pairwise (fun x y ↦ R y x)

private theorem exists_sequence_of_prepend {A : Type*} {P : A → Prop} {R : A → A → Prop}
    (hStart : ∃ a, P a)
    (hExtend : ∀ t : OscillationHistory P R,
      ∃ a, P a ∧ ∀ b ∈ t.latest :: t.rest, R b a) :
    ∃ a : ℕ → A, (∀ n, P (a n)) ∧ ∀ i j, i < j → R (a i) (a j) := by
  obtain ⟨a₀, h₀⟩ := hStart
  let t₀ : OscillationHistory P R := ⟨a₀, [], by simp [h₀], by simp⟩
  let next (t : OscillationHistory P R) : OscillationHistory P R := by
    let a := (hExtend t).choose
    have ha := (hExtend t).choose_spec
    refine ⟨a, t.latest :: t.rest, ?_, List.pairwise_cons.mpr ⟨ha.2, t.ordered⟩⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha.1
    · exact t.good b hb
  let t : ℕ → OscillationHistory P R := Nat.rec t₀ (fun _ ↦ next)
  let a (n : ℕ) := (t n).latest
  have hEarlier {i j : ℕ} (h : i < j) : a i ∈ (t j).rest := by
    induction j with
    | zero => omega
    | succ j ih =>
      change a i ∈ a j :: (t j).rest
      by_cases hij : i = j
      · exact List.mem_cons.mpr (Or.inl (congrArg a hij))
      · exact List.mem_cons_of_mem _ (ih (by omega))
  exact ⟨a, fun n ↦ (t n).good _ (List.mem_cons_self ..),
    fun i j hij ↦ (List.pairwise_cons.mp (t j).ordered).1 _ (hEarlier hij)⟩

section Oscillation

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]

omit [T2Space Y] in
/-- A separately continuous real function on a product of compact Hausdorff
spaces has arbitrarily small uniform oscillation on suitable open sets
in the first factor. -/
theorem exists_open_small_oscillation [Nonempty X] (f : X → Y → ℝ)
    (hLeft : ∀ y, Continuous (fun x ↦ f x y)) (hRight : ∀ x, Continuous (f x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∀ x ∈ U, ∀ x' ∈ U, ∀ y, dist (f x y) (f x' y) ≤ ε := by
  classical
  by_contra hContra
  have hCover : FiberCover (rectangleGood f ε)ᶜ := by
    intro x
    by_contra hNot
    have hF : ∀ y, (x, y) ∈ rectangleGood f ε := by
      intro y
      by_contra hn
      exact hNot ⟨y, hn⟩
    obtain ⟨U, hU, hxU, hδ⟩ := exists_open_small_oscillation_of_fiber f ε hF
    exact hContra ⟨U, hU, ⟨x, hxU⟩, hδ⟩
  obtain ⟨D, hD, hBad, hCo, hMin⟩ := exists_minimal_closed_fiberCover
    (isOpen_rectangleGood f ε).isClosed_compl hCover
  let δ := ε / 6
  let r := δ / 3
  have hr : 0 < r := by dsimp [δ, r]; positivity
  let P (a : X × Y × Y) := (a.1, a.2.2) ∈ D ∧ δ ≤ dist (f a.1 a.2.1) (f a.1 a.2.2)
  let R (a b : X × Y × Y) :=
    dist (f b.1 a.2.1) (f a.1 a.2.1) < r ∧
    dist (f a.1 b.2.1) (f a.1 a.2.2) < r ∧
    dist (f a.1 b.2.2) (f a.1 a.2.2) < r
  have hStart : ∃ a, P a := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y, hy⟩ := hCo x
    obtain ⟨u, v, w, _, _, _, hDuw, hd⟩ :=
      exists_oscillation_witness f hLeft hε hD hBad hCo hMin isOpen_univ isOpen_univ
        ⟨(x, y), hy, mem_univ _, mem_univ _⟩
    exact ⟨(u, v, w), hDuw, hd⟩
  have hExtend (t : OscillationHistory P R) :
      ∃ a, P a ∧ ∀ b ∈ t.latest :: t.rest, R b a := by
    let l := t.latest :: t.rest
    let V := ⋂ b ∈ l.toFinset, (fun x ↦ f x b.2.1) ⁻¹' Metric.ball (f b.1 b.2.1) r
    let W := ⋂ b ∈ l.toFinset, f b.1 ⁻¹' Metric.ball (f b.1 b.2.2) r
    have hV : IsOpen V := isOpen_biInter_finset fun b _ ↦
      Metric.isOpen_ball.preimage (hLeft b.2.1)
    have hW : IsOpen W := isOpen_biInter_finset fun b _ ↦ Metric.isOpen_ball.preimage (hRight b.1)
    have hV' : t.latest.1 ∈ V := by
      refine mem_iInter.mpr fun b ↦ mem_iInter.mpr fun hb ↦ ?_
      change dist (f t.latest.1 b.2.1) (f b.1 b.2.1) < r
      rcases List.mem_cons.mp (List.mem_toFinset.mp hb) with rfl | hb
      · simpa only [dist_self] using hr
      · exact ((List.pairwise_cons.mp t.ordered).1 b hb).1
    have hW' : t.latest.2.2 ∈ W := by
      refine mem_iInter.mpr fun b ↦ mem_iInter.mpr fun hb ↦ ?_
      change dist (f b.1 t.latest.2.2) (f b.1 b.2.2) < r
      rcases List.mem_cons.mp (List.mem_toFinset.mp hb) with rfl | hb
      · simpa only [dist_self] using hr
      · exact ((List.pairwise_cons.mp t.ordered).1 b hb).2.2
    have hD' : (t.latest.1, t.latest.2.2) ∈ D :=
      (t.good t.latest (List.mem_cons_self ..)).1
    obtain ⟨u, v, w, hu, hv, hw, hDuw, hδ⟩ :=
      exists_oscillation_witness f hLeft hε hD hBad hCo hMin hV hW
        ⟨(t.latest.1, t.latest.2.2), hD', hV', hW'⟩
    refine ⟨(u, v, w), ⟨hDuw, hδ⟩, fun b hb ↦ ?_⟩
    have hb' : b ∈ l.toFinset := List.mem_toFinset.mpr hb
    exact ⟨mem_iInter.mp (mem_iInter.mp hu b) hb', mem_iInter.mp (mem_iInter.mp hv b) hb',
      mem_iInter.mp (mem_iInter.mp hw b) hb'⟩
  obtain ⟨a, hGood, hPairs⟩ := exists_sequence_of_prepend hStart hExtend
  let z (n : ℕ) : X × Y := ((a n).1, (a n).2.1)
  obtain ⟨p, hp⟩ : ∃ p : X × Y, MapClusterPt p atTop z :=
    exists_clusterPt_of_compactSpace (map z atTop)
  have hDistance (i j : ℕ) (hij : i < j) :
      r ≤ dist (f (a j).1 (a i).2.1) (f (a i).1 (a j).2.1) := by
    have hPair := hPairs i j hij
    have h₁ := dist_triangle (f (a i).1 (a i).2.1) (f (a j).1 (a i).2.1)
      (f (a i).1 (a i).2.2)
    have h₂ := dist_triangle (f (a j).1 (a i).2.1) (f (a i).1 (a j).2.1)
      (f (a i).1 (a i).2.2)
    have h₃ : dist (f (a i).1 (a i).2.1) (f (a j).1 (a i).2.1) < r := by
      rw [dist_comm]
      exact hPair.1
    dsimp only [R] at hPair
    have h₄ := (hGood i).2
    dsimp only [r] at *
    linarith [hPair.2.1]
  have hDist (i : ℕ) : r ≤ dist (f p.1 (a i).2.1) (f (a i).1 p.2) := by
    have hcont : Continuous (fun q : X × Y ↦ dist (f q.1 (a i).2.1) (f (a i).1 q.2)) :=
      ((hLeft (a i).2.1).comp continuous_fst).dist ((hRight (a i).1).comp continuous_snd)
    exact (isClosed_le continuous_const hcont).mem_of_mapClusterPt hp
      ((eventually_gt_atTop i).mono (fun j hj ↦ hDistance i j hj))
  have hcont : Continuous (fun q : X × Y ↦ dist (f p.1 q.2) (f q.1 p.2)) :=
    ((hRight p.1).comp continuous_snd).dist ((hLeft p.2).comp continuous_fst)
  have hWrong : r ≤ dist (f p.1 p.2) (f p.1 p.2) :=
    (isClosed_le continuous_const hcont).mem_of_mapClusterPt hp
      (Eventually.of_forall hDist)
  rw [dist_self] at hWrong
  exact (not_le_of_gt hr) hWrong

end Oscillation

end JdLG
