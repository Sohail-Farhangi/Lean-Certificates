/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Dual
public import JdLG.HilbertCompactness
public import Mathlib.Analysis.Convex.LinearIsometry
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The contraction criterion for JdLG admissibility

For a minimal idempotent e, the compact corner eSe is a group.
The inverse of efe forces a contractive idempotent f to preserve norms
on the range of e. Strict convexity gives fe = e. Applying the same
argument to the dual gives ef = e and proves uniqueness.
-/

@[expose] public section

open Set

namespace JdLG

/-- In a compact semitopological semigroup the corner of a minimal
idempotent is a group with that idempotent as identity. -/
theorem inverse_in_minimal_corner {S : Type*} [Semigroup S] [TopologicalSpace S]
    [T2Space S] [CompactSpace S] [SeparatelyContinuousMul S]
    {e : S} (he : IsMinimalIdempotent e) (s : S) :
    ∃ t : S, t * (e * s * e) = e ∧ (e * s * e) * t = e := by
  let C : Subsemigroup S :=
    { carrier := {a | a * e = a ∧ e * a = a}
      mul_mem' := fun {a b} ha hb ↦ by
        change (a * b) * e = a * b ∧ e * (a * b) = a * b
        exact ⟨(mul_assoc a b e).trans (congrArg (a * ·) hb.1),
          (mul_assoc e a b).symm.trans (congrArg (· * b) ha.2)⟩ }
  have hcorner (a : S) : e * a * e ∈ C := by
    change (e * a * e) * e = e * a * e ∧ e * (e * a * e) = e * a * e
    refine ⟨by rw [mul_assoc (e * a), he.1], ?_⟩
    rw [← mul_assoc, ← mul_assoc e e a, he.1]
  have hset : (C : Set S) = range (fun a ↦ e * a * e) := by
    ext a
    constructor
    · exact fun ha ↦ ⟨a, by
        change e * a * e = a
        rw [ha.2, ha.1]⟩
    · rintro ⟨u, rfl⟩
      exact hcorner u
  have hcompact : IsCompact (C : Set S) := by
    rw [hset]
    exact isCompact_range ((continuous_const_mul e).mul_const e)
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let ec : C := ⟨e, he.1, he.1⟩
  have hec_idem : ec * ec = ec := Subtype.ext he.1
  have hunique (a : C) (ha : a * a = a) : a = ec :=
    Subtype.ext (he.2 a.1 (congrArg Subtype.val ha) a.2.1 a.2.2)
  obtain ⟨K, _⟩ := exists_compact_groupIdeal_of_existsUnique_minimalIdempotent
    (fun a : C ↦ continuous_mul_const a)
    ⟨ec, ⟨hec_idem, fun a ha _ _ ↦ hunique a ha⟩, fun a ha ↦ hunique a ha.1⟩
  have hKe : K.identity = ec := hunique _ K.identity_idempotent
  let u : C := ⟨e * s * e, hcorner s⟩
  have hu : u ∈ K.carrier := by
    have h : u * K.identity = u := by rw [hKe]; exact Subtype.ext u.2.1
    exact h ▸ K.mul_mem_left u K.identity_mem
  obtain ⟨v, _, hvu, huv⟩ := K.inverse_exists hu
  rw [hKe] at hvu huv
  exact ⟨v, congrArg Subtype.val hvu, congrArg Subtype.val huv⟩

private theorem contractive_idempotent_fixes_of_norm_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [StrictConvexSpace ℝ E] (B : E →L[ℂ] E)
    (hB : ‖B‖ ≤ 1) (hBB : B * B = B) (x : E) (hn : ‖B x‖ = ‖x‖) :
    B x = x := by
  by_contra hne
  let y := (1 / 2 : ℝ) • (x + B x)
  have hy : ‖y‖ < ‖x‖ := (norm_midpoint_lt_iff hn.symm).2 (Ne.symm hne)
  have hBx : B (B x) = B x := DFunLike.congr_fun hBB x
  have he : B y = B x := by
    change (B.restrictScalars ℝ) ((1 / 2 : ℝ) • (x + B x)) = B x
    rw [map_smul, map_add]
    change (1 / 2 : ℝ) • (B x + B (B x)) = B x
    rw [hBx, ← two_smul ℝ, smul_smul]
    norm_num
  have hb : ‖B y‖ ≤ 1 * ‖y‖ := B.le_of_opNorm_le hB y
  rw [he, hn, one_mul] at hb
  exact hy.not_ge hb

private theorem comp_eq_of_contractive_corner {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [StrictConvexSpace ℝ E] {A B R : E →L[ℂ] E}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hAA : A * A = A) (hBB : B * B = B) (hinv : R * (A * B * A) = A) :
    B * A = A := by
  ext x
  change B (A x) = A x
  refine contractive_idempotent_fixes_of_norm_eq B hB hBB (A x) (le_antisymm ?_ ?_)
  · simpa only [one_mul] using B.le_of_opNorm_le hB (A x)
  · have h : R (A (B (A x))) = A x := by
      have h₀ := DFunLike.congr_fun hinv (A x)
      change R (A (B (A (A x)))) = A (A x) at h₀
      rwa [show A (A x) = A x from DFunLike.congr_fun hAA x] at h₀
    calc
      ‖A x‖ = ‖R (A (B (A x)))‖ := congrArg norm h.symm
      _ ≤ ‖A (B (A x))‖ := by simpa only [one_mul] using R.le_of_opNorm_le hR (A (B (A x)))
      _ ≤ ‖B (A x)‖ := by simpa only [one_mul] using A.le_of_opNorm_le hA (B (A x))

private theorem norm_banachAdjoint_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E →L[ℂ] E} (hA : ‖A‖ ≤ 1) : ‖banachAdjoint A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro x
  exact (f.le_opNorm (A x)).trans (mul_le_mul_of_nonneg_left
    (by simpa only [one_mul] using A.le_of_opNorm_le hA x) (norm_nonneg f))

/-- A compact WOT closure of contractions on a space with strictly convex
primal and dual norms is JdLG-admissible. The contraction hypothesis is
the additional assumption in this variant of Theorem 1.2(iv). -/
theorem admissible_of_strictConvex_contractions {S E : Type*} [Semigroup S] [Nonempty S]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [StrictConvexSpace ℝ E]
    [StrictConvexSpace ℝ (StrongDual ℂ E)]
    (π : S →ₙ* (E →L[ℂ] E))
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[ℂ] E)))
    (hπ : ∀ s, ‖π s‖ ≤ 1) : IsJdLGAdmissible π := by
  let T := weakOperatorClosure π
  let : CompactSpace T := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty T := ⟨closureInclusion π (Classical.choice inferInstance)⟩
  let act := closureAction π
  have hcontract (t : T) : ‖act t‖ ≤ 1 := by
    have hc : IsClosed {a : E →WOT[ℂ] E | ‖a.toCLM‖ ≤ 1} := by
      have hset : {a : E →WOT[ℂ] E | ‖a.toCLM‖ ≤ 1} =
          ⋂ x : E, ⋂ f : StrongDual ℂ E, {a | ‖f (a x)‖ ≤ ‖f‖ * ‖x‖} := by
        ext a
        simp only [mem_ofPred_eq, mem_iInter]
        constructor
        · intro ha x f
          exact (f.le_opNorm (a x)).trans (mul_le_mul_of_nonneg_left
              (by
                change ‖a.toCLM x‖ ≤ ‖x‖
                simpa only [one_mul] using a.toCLM.le_of_opNorm_le ha x) (norm_nonneg f))
        · intro ha
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro x
          rw [one_mul]
          obtain ⟨f, hf, heq⟩ := exists_dual_vector'' ℂ (a.toCLM x)
          have h := ha x f
          change ‖f (a.toCLM x)‖ ≤ ‖f‖ * ‖x‖ at h
          rw [heq, RCLike.norm_ofReal, abs_norm] at h
          exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hf)
      rw [hset]
      exact isClosed_iInter fun x ↦ isClosed_iInter fun f ↦
        isClosed_le (ContinuousLinearMapWOT.continuous_dual_apply x f).norm continuous_const
    exact closure_minimal (by rintro _ ⟨s, rfl⟩; exact hπ s) hc t.2
  obtain ⟨L, hLcompact, hL⟩ := exists_compact_minimalLeftIdeal (fun t : T ↦ continuous_mul_const t)
  obtain ⟨e, heL, hee⟩ := exists_idempotent_in_compact_subsemigroup
    (fun t : T ↦ continuous_mul_const t) L hL.1 hLcompact
    (fun a _ _ hb ↦ hL.2.1 a hb)
  have he := isMinimalIdempotent_of_mem_minimalLeftIdeal hL heL hee
  refine ⟨hcompact, e, he, fun f hf ↦ ?_⟩
  obtain ⟨t, ht, htr⟩ := inverse_in_minimal_corner he f
  have hA : act e * act e = act e := by rw [← map_mul, he.1]
  have hB : act f * act f = act f := by rw [← map_mul, hf.1]
  have hR : act t * (act e * act f * act e) = act e := by simp_rw [← map_mul, ht]
  have hfe : act f * act e = act e :=
    comp_eq_of_contractive_corner (hcontract e) (hcontract f) (hcontract t) hA hB hR
  have hD (a : T) : ‖banachAdjoint (act a)‖ ≤ 1 := norm_banachAdjoint_le (hcontract a)
  have hAD : banachAdjoint (act e) * banachAdjoint (act e) = banachAdjoint (act e) := by
    rw [← banachAdjoint_mul, hA]
  have hBD : banachAdjoint (act f) * banachAdjoint (act f) = banachAdjoint (act f) := by
    rw [← banachAdjoint_mul, hB]
  have hRD : banachAdjoint (act t) *
      (banachAdjoint (act e) * banachAdjoint (act f) * banachAdjoint (act e)) =
      banachAdjoint (act e) := by
    have h : (act e * act f * act e) * act t = act e := by simp_rw [← map_mul, htr]
    simpa only [banachAdjoint_mul, mul_assoc] using congrArg banachAdjoint h
  have hdual := comp_eq_of_contractive_corner (hD e) (hD f) (hD t) hAD hBD hRD
  have hef : act e * act f = act e := by
    ext x
    apply (separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℂ E))
    ext g
    exact DFunLike.congr_fun (DFunLike.congr_fun hdual g) x
  have hinj : Function.Injective act := fun a b hab ↦
    Subtype.ext (ContinuousLinearMapWOT.toCLM_injective hab)
  have h₁ : e * f = e := hinj ((map_mul act e f).trans hef)
  have h₂ : f * e = e := hinj ((map_mul act f e).trans hfe)
  exact (hf.2 e he.1 h₁ h₂).symm

theorem strictConvexSpace_complexHilbert_dual {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : StrictConvexSpace ℝ (StrongDual ℂ E) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let e := (InnerProductSpace.toDual ℂ E).symm
  let f : StrongDual ℂ E →ₗᵢ[ℝ] E :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun r x ↦ by
        have h := e.map_smulₛₗ (r : ℂ) x
        have hstar : star (r : ℂ) = (r : ℂ) := by simp
        change e ((r : ℂ) • x) = star (r : ℂ) • e x at h
        rw [hstar] at h
        change e (r • x) = r • e x
        calc
          _ = e ((r : ℂ) • x) := congrArg e (RCLike.real_smul_eq_coe_smul (K := ℂ) r x)
          _ = (r : ℂ) • e x := h
          _ = r • e x := (RCLike.real_smul_eq_coe_smul (K := ℂ) r (e x)).symm
      norm_map' := e.norm_map }
  exact f.strictConvexSpace

/-- Theorem 1.2(ii) for complex Hilbert spaces. -/
theorem admissible_of_hilbert_contractions {S E : Type*} [Semigroup S] [Nonempty S]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : S →ₙ* (E →L[ℂ] E)) (hπ : ∀ s, ‖π s‖ ≤ 1) : IsJdLGAdmissible π := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let : StrictConvexSpace ℝ (StrongDual ℂ E) := strictConvexSpace_complexHilbert_dual
  exact admissible_of_strictConvex_contractions π
    (compact_weakOperatorClosure_hilbert_contractions π hπ) hπ

end JdLG
