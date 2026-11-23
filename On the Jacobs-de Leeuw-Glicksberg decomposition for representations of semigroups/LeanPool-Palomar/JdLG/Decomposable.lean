/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ContractiveCriterion
public import JdLG.ReversibleHaar

/-! # The invariant splitting and the minimal idempotent criterion -/

@[expose] public section

open Set

namespace JdLG

variable {S E : Type*} [Semigroup S] [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : S →ₙ* (E →L[ℂ] E))

/-- The paper's definition of JdLG decomposability. Its two vector sets must
be closed complementary subspaces invariant under the whole WOT closure. -/
def IsJdLGDecomposable : Prop :=
  IsCompact (weakOperatorClosure π : Set (E →WOT[ℂ] E)) ∧
    ∃ R W : Submodule ℂ E,
      IsClosed (R : Set E) ∧ IsClosed (W : Set E) ∧ IsCompl R W ∧
      (∀ s : weakOperatorClosure π, ∀ x ∈ R, closureAction π s x ∈ R) ∧
      (∀ s : weakOperatorClosure π, ∀ x ∈ W, closureAction π s x ∈ W) ∧
      (∀ x, x ∈ R ↔ IsReversible (closureAction π) x) ∧
      (∀ x, x ∈ W ↔ IsAlmostWeaklyStable (closureAction π) x)

/-- The direct-sum condition and the unique minimal idempotent condition
in Theorem 1.1 are equivalent. -/
theorem isJdLGDecomposable_iff_isJdLGAdmissible [Nonempty S] :
    IsJdLGDecomposable π ↔ IsJdLGAdmissible π := by
  constructor
  · rintro ⟨hcompact, R, W, _, _, hRW, hR, hW, hr, hw⟩
    let T := weakOperatorClosure π
    let : CompactSpace T := isCompact_iff_compactSpace.mp hcompact
    let : Nonempty T := ⟨closureInclusion π (Classical.choice inferInstance)⟩
    let ρ := closureAction π
    have hfix (e : T) (he : e * e = e) {x : E} (hx : x ∈ R) : ρ e x = x := by
      have hRdiff : x - ρ e x ∈ R := R.sub_mem hx (hR e x hx)
      have hWdiff : x - ρ e x ∈ W := (hw _).2 ⟨e, by
        rw [map_sub, show ρ e (ρ e x) = ρ e x from DFunLike.congr_fun
          ((map_mul ρ e e).symm.trans (congrArg ρ he)) x, sub_self]⟩
      have h : x - ρ e x ∈ R ⊓ W := ⟨hRdiff, hWdiff⟩
      rw [hRW.inf_eq_bot] at h
      have hz : x - ρ e x = 0 := (Submodule.mem_bot ℂ).1 h
      exact (sub_eq_zero.mp hz).symm
    have hkill (e : T) (he : IsMinimalIdempotent e) {x : E} (hx : x ∈ W) : ρ e x = 0 := by
      obtain ⟨a, ha⟩ := (hw _).1 (hW e x hx)
      obtain ⟨t, ht, _⟩ := inverse_in_minimal_corner he a
      have h := DFunLike.congr_fun (congrArg ρ ht) x
      simp only [map_mul] at h
      change ρ t (ρ e (ρ a (ρ e x))) = ρ e x at h
      change ρ a (ρ e x) = 0 at ha
      rw [ha, map_zero, map_zero] at h
      exact h.symm
    obtain ⟨L, hLc, hL⟩ := exists_compact_minimalLeftIdeal (fun s : T ↦ continuous_mul_const s)
    obtain ⟨e, heL, hee⟩ := exists_idempotent_in_compact_subsemigroup
      (fun s : T ↦ continuous_mul_const s) L hL.1 hLc (fun a _ _ hb ↦ hL.2.1 a hb)
    have he := isMinimalIdempotent_of_mem_minimalLeftIdeal hL heL hee
    refine ⟨hcompact, ⟨e, he, fun f hf ↦ ?_⟩⟩
    apply Subtype.ext
    apply ContinuousLinearMapWOT.toCLM_injective
    change ρ f = ρ e
    apply ContinuousLinearMap.ext
    intro x
    have hx : x ∈ R ⊔ W := by rw [hRW.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, map_add, hfix f hf.1 hy, hfix e he.1 hy, hkill f hf hz, hkill e he hz]
  · intro hadm
    obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hadm
    let ρ := closureAction π
    let P := K.projection ρ
    refine ⟨hadm.1, P.range, P.ker, K.isClosed_range_projection ρ,
      K.isClosed_ker_projection ρ, K.range_isCompl_ker ρ, ?_, ?_,
      fun x ↦ (K.reversible_iff_mem_range ρ x).symm,
      fun x ↦ (K.stable_iff_mem_ker ρ x).symm⟩
    · intro s x hx
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ s y, K.projection_commutes ρ s y⟩
    · intro s x hx
      change P x = 0 at hx
      change P (ρ s x) = 0
      rw [K.projection_commutes, hx, map_zero]

/-- The two-sided invariant mean criterion for a closed invariant JdLG
splitting, stated on the actual compact operator semigroup. -/
theorem isJdLGDecomposable_iff_exists_biInvariantMean
    [Nonempty S] [CompleteSpace E] [CompactSpace (weakOperatorClosure π)]
    [MeasurableSpace (weakOperatorClosure π)] [BorelSpace (weakOperatorClosure π)] :
    IsJdLGDecomposable π ↔
      ∃ m : LeftInvariantContinuousMean
          (fun s : weakOperatorClosure π ↦ continuous_const_mul s),
        m.IsRightInvariant (fun s ↦ continuous_mul_const s) :=
  (isJdLGDecomposable_iff_isJdLGAdmissible π).trans
    (Iff.trans ⟨fun h ↦ h.2, fun h ↦ ⟨isCompact_iff_compactSpace.mpr inferInstance, h⟩⟩
      (existsUnique_minimalIdempotent_iff_exists_biInvariantMean π))

end JdLG
