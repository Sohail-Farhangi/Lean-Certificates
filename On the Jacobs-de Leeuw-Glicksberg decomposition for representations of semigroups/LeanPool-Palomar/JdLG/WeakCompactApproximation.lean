/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesWapAction
public import JdLG.ReflexiveCompactness

/-! # Norm approximation by weakly compact subsets -/

@[expose] public section

open NormedSpace Set

namespace JdLG

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A set that can be uniformly approximated in norm by weakly compact sets
has compact weak closure. The weak-star bidual gives compact sets containing
the weak-star closure at every scale, so the latter lies in the norm-closed
image of the original Banach space. -/
theorem isCompact_closure_weak_of_approx (A : Set (WeakSpace ℂ E))
    (hA : ∀ ε > 0, ∃ K : Set (WeakSpace ℂ E), IsCompact K ∧
      ∀ x ∈ A, ∃ y ∈ K, ‖(toWeakSpace ℂ E).symm x - (toWeakSpace ℂ E).symm y‖ ≤ ε) :
    IsCompact (closure A) := by
  let D := WeakDual ℂ (StrongDual ℂ E)
  let j := inclusionInDoubleDualWeak ℂ E
  let J := inclusionInDoubleDualLi ℂ (E := E)
  let B (r : ℝ) : Set D := {u | ‖WeakDual.toStrongDual u‖ ≤ r}
  let Z := closure (j '' A)
  let add (u : D × D) := u.1 + u.2
  have hB (r : ℝ) : IsCompact (B r) := by
    have he : B r = WeakDual.toStrongDual ⁻¹' Metric.closedBall
        (0 : StrongDual ℂ (StrongDual ℂ E)) r := by
      ext u
      change ‖WeakDual.toStrongDual u‖ ≤ r ↔
        WeakDual.toStrongDual u ∈ Metric.closedBall (0 : StrongDual ℂ (StrongDual ℂ E)) r
      exact (mem_closedBall_zero_iff (a := WeakDual.toStrongDual u) (r := r)).symm
    rw [he]
    exact WeakDual.isCompact_closedBall (0 : StrongDual ℂ (StrongDual ℂ E)) r
  have hj (w : WeakSpace ℂ E) : WeakDual.toStrongDual (j w) = J ((toWeakSpace ℂ E).symm w) :=
    rfl
  have hsum (r : ℝ) (hr : 0 < r) : ∃ K : Set (WeakSpace ℂ E), IsCompact K ∧
      Z ⊆ add '' ((j '' K) ×ˢ B r) := by
    obtain ⟨K, hK, hnear⟩ := hA r hr
    refine ⟨K, hK, closure_minimal ?_ ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hnear x hx
      refine ⟨(j y, j x - j y), ⟨⟨y, hy, rfl⟩, ?_⟩, ?_⟩
      · change ‖WeakDual.toStrongDual (j x - j y)‖ ≤ r
        rw [← map_sub j, hj, J.norm_map, map_sub]
        exact hxy
      · change j y + (j x - j y) = j x
        abel
    · exact (((hK.image j.continuous).prod (hB r)).image
        (continuous_fst.add continuous_snd)).isClosed
  have hZ : IsCompact Z := by
    obtain ⟨K, hK, hZ⟩ := hsum 1 zero_lt_one
    exact (((hK.image j.continuous).prod (hB 1)).image
      (continuous_fst.add continuous_snd)).of_isClosed_subset isClosed_closure hZ
  have hZ' : Z ⊆ range j := by
    intro z hz
    have hjiso : Isometry (J : E → StrongDual ℂ (StrongDual ℂ E)) := J.isometry
    have hclosed := hjiso.isClosedEmbedding.isClosed_range
    have hrange : WeakDual.toStrongDual z ∈ range J := by
      rw [← hclosed.closure_eq]
      apply Metric.mem_closure_iff.2
      intro ε hε
      obtain ⟨K, _, hZ⟩ := hsum (ε / 2) (by linarith)
      obtain ⟨⟨_, b⟩, ⟨⟨w, _, rfl⟩, hb⟩, he⟩ := hZ hz
      refine ⟨J ((toWeakSpace ℂ E).symm w), mem_range_self _, ?_⟩
      change j w + b = z at he
      change ‖WeakDual.toStrongDual b‖ ≤ ε / 2 at hb
      rw [dist_eq_norm, ← hj, ← he, map_add]
      have hcancel : WeakDual.toStrongDual (j w) + WeakDual.toStrongDual b -
          WeakDual.toStrongDual (j w) = WeakDual.toStrongDual b := by abel
      rw [hcancel]
      exact hb.trans_lt (by linarith)
    obtain ⟨x, hx⟩ := hrange
    refine ⟨toWeakSpace ℂ E x, WeakDual.toStrongDual.injective ?_⟩
    rw [hj, LinearEquiv.symm_apply_apply, hx]
  have he := isEmbedding_inclusionInDoubleDualWeak ℂ E
  rw [he.closure_eq_preimage_closure_image]
  exact he.isCompact_preimage' hZ hZ'

/-- An orbit uniformly approximable in norm by weakly compact sets is weakly
almost periodic. -/
theorem isWapVector_of_approx {S : Type*} [Semigroup S] (ρ : S →ₙ* (E →L[ℂ] E)) (x : E)
    (hx : ∀ ε > 0, ∃ K : Set (WeakSpace ℂ E), IsCompact K ∧
      ∀ s, ∃ y ∈ K, ‖ρ s x - (toWeakSpace ℂ E).symm y‖ ≤ ε) :
    IsWapVector ρ x := by
  apply isCompact_closure_weak_of_approx (range fun s ↦ toWeakSpace ℂ E (ρ s x))
  intro ε hε
  obtain ⟨K, hK, hw⟩ := hx ε hε
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨s, rfl⟩
  simpa only [LinearEquiv.symm_apply_apply] using hw s

/-- Uniformly bounded representations have weakly compact orbit closures at
all vectors once this holds at a dense set of vectors. -/
theorem isWapVector_of_dense {S : Type*} [Semigroup S] (ρ : S →ₙ* (E →L[ℂ] E))
    {P : Set E} (hP : Dense P) (h : ∀ y ∈ P, IsWapVector ρ y) {C : ℝ}
    (hC : ∀ s, ‖ρ s‖ ≤ C) (x : E) : IsWapVector ρ x := by
  apply isWapVector_of_approx
  intro ε hε
  let B := max 1 C
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨y, hyx, hy⟩ := Metric.dense_iff.1 hP x (ε / B) (div_pos hε hB)
  refine ⟨weakVectorOrbit ρ y, h y hy, fun s ↦
    ⟨toWeakSpace ℂ E (ρ s y), subset_closure (mem_range_self s), ?_⟩⟩
  rw [LinearEquiv.symm_apply_apply, ← map_sub]
  have hdist : ‖x - y‖ < ε / B := by
    change dist y x < ε / B at hyx
    simpa only [dist_comm y x, dist_eq_norm] using hyx
  exact ((ρ s).le_of_opNorm_le ((hC s).trans (le_max_right _ _)) _).trans
    ((lt_div_iff₀' hB).1 hdist).le

end JdLG
