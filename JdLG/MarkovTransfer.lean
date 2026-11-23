/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Quotient
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Dense-range transfer for weak operator closures -/

@[expose] public section

open Filter Set Topology

namespace JdLG

section Continuity

variable {X 𝕜 E F : Type*} [TopologicalSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Uniformly bounded operators have continuous scalar evaluations everywhere
if their scalar evaluations are continuous on a dense family of vectors. -/
theorem continuous_wot_of_dense_eval (T : X → F →L[𝕜] F) (j : E → F) (hj : DenseRange j)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ a, ‖T a‖ ≤ C)
    (hc : ∀ x : E, ∀ l : StrongDual 𝕜 F, Continuous (fun a ↦ l (T a (j x)))) :
    Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (T a) := by
  apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
  intro z l
  apply continuous_iff_continuousAt.2
  intro a
  apply Metric.tendsto_nhds.2
  intro ε hε
  let M := ‖l‖ * C
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) hC
  let δ := ε / (3 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨x, hx⟩ := hj.exists_dist_lt z hδ
  have hnoise (b : X) : dist (l (T b (j x))) (l (T b z)) ≤ ε / 3 := by
    calc
      dist (l (T b (j x))) (l (T b z)) ≤ ‖l‖ * (C * dist (j x) z) := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub]
        exact (l.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((T b).le_of_opNorm_le (hbound b) _) (norm_nonneg _))
      _ = M * dist z (j x) := by rw [dist_comm, mul_assoc]
      _ ≤ (M + 1) * dist z (j x) :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ ≤ (M + 1) * δ := mul_le_mul_of_nonneg_left (le_of_lt hx) (by positivity)
      _ = ε / 3 := by
        dsimp [δ]
        field_simp
  have hmid : ∀ᶠ b in 𝓝 a, dist (l (T b (j x))) (l (T a (j x))) < ε / 3 :=
    Metric.tendsto_nhds.1 (hc x l).continuousAt (ε / 3) (by positivity)
  filter_upwards [hmid] with b hb
  have hfirst := hnoise b
  have hlast := hnoise a
  rw [dist_comm] at hfirst
  calc
    dist (l (T b z)) (l (T a z)) ≤
        dist (l (T b z)) (l (T b (j x))) + dist (l (T b (j x))) (l (T a (j x))) +
          dist (l (T a (j x))) (l (T a z)) :=
      (dist_triangle _ (l (T a (j x))) _).trans
        (add_le_add_left (dist_triangle _ (l (T b (j x))) _) _)
    _ < ε := by linarith

end Continuity

section Transfer

variable {S 𝕜 E F : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {π : S →ₙ* (E →L[𝕜] E)} {τ : S →ₙ* (F →L[𝕜] F)}

/-- A dense-range Banach-space intertwiner from a weak operator compact closure
to a uniformly bounded action induces a continuous surjective semigroup map
between the weak operator closures. -/
theorem exists_closure_denseIntertwiner_map (j : E →L[𝕜] F) (hj : DenseRange j)
    (hinter : ∀ s x, τ s (j x) = j (π s x))
    {C : ℝ} (hC : 0 ≤ C) (hτ : ∀ s, ‖τ s‖ ≤ C)
    (hπ : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :
    ∃ φ : weakOperatorClosure π →ₙ* weakOperatorClosure τ,
      Continuous φ ∧ Function.Surjective φ ∧
        ∀ a x, closureAction τ (φ a) (j x) = j (closureAction π a x) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.1 hπ
  have hb (a : weakOperatorClosure π) (x : E) :
      ‖j (closureAction π a x)‖ ≤ C * ‖j x‖ := by
    obtain ⟨l, hl, hlv⟩ := exists_dual_vector'' 𝕜 (j (closureAction π a x))
    let V : Set (E →WOT[𝕜] E) := {b | ‖l (j (b x))‖ ≤ C * ‖j x‖}
    have hc : IsClosed V :=
      isClosed_le (ContinuousLinearMapWOT.continuous_dual_apply x (l.comp j)).norm continuous_const
    have hr : range (weakRepresentation π) ⊆ V := by
      rintro _ ⟨s, rfl⟩
      change ‖l (j (π s x))‖ ≤ C * ‖j x‖
      rw [← hinter]
      calc
        ‖l (τ s (j x))‖ ≤ ‖l‖ * ‖τ s (j x)‖ := l.le_opNorm _
        _ ≤ ‖τ s (j x)‖ := mul_le_of_le_one_left (norm_nonneg _) hl
        _ ≤ C * ‖j x‖ := (τ s).le_of_opNorm_le (hτ s) _
    have hav := closure_minimal hr hc a.2
    change ‖l (j (closureAction π a x))‖ ≤ C * ‖j x‖ at hav
    rw [hlv, RCLike.norm_ofReal, abs_norm] at hav
    exact hav
  let descend (a : weakOperatorClosure π) : F →L[𝕜] F :=
    (j.comp (closureAction π a)).toLinearMap.extendOfNorm j.toLinearMap
  have hdesc (a : weakOperatorClosure π) (x : E) :
      descend a (j x) = j (closureAction π a x) :=
    LinearMap.extendOfNorm_eq hj ⟨C, hb a⟩ x
  have hdBound (a : weakOperatorClosure π) : ‖descend a‖ ≤ C :=
    LinearMap.opNorm_extendOfNorm_le hj hC (hb a)
  let D : weakOperatorClosure π →ₙ* (F →L[𝕜] F) :=
    ⟨descend, fun a b ↦ by
      apply ContinuousLinearMap.ext
      intro z
      refine congrFun (hj.equalizer (descend (a * b)).continuous
        ((descend a).continuous.comp (descend b).continuous) ?_) z
      funext x
      change descend (a * b) (j x) = descend a (descend b (j x))
      rw [hdesc (a * b) x, hdesc b x, hdesc a, map_mul]
      rfl⟩
  have horiginal (s : S) : D (closureInclusion π s) = τ s := by
    apply ContinuousLinearMap.ext
    intro z
    refine congrFun (hj.equalizer (D (closureInclusion π s)).continuous (τ s).continuous ?_) z
    funext x
    change descend (closureInclusion π s) (j x) = τ s (j x)
    rw [hdesc, closureAction_inclusion, hinter]
  let W := weakRepresentation D
  have hW : Continuous W := continuous_wot_of_dense_eval descend j hj hC hdBound
    fun x l ↦ by
      simp_rw [hdesc]
      exact (ContinuousLinearMapWOT.continuous_dual_apply x (l.comp j)).comp continuous_subtype_val
  have hsame : W '' range (closureInclusion π) = range (weakRepresentation τ) := by
    rw [← range_comp]
    refine congrArg range (funext fun s ↦ ?_)
    exact congrArg ContinuousLinearMapWOT.ofCLM (horiginal s)
  have hRange : range W = (weakOperatorClosure τ : Set (F →WOT[𝕜] F)) := by
    change range W = closure (range (weakRepresentation τ))
    rw [← hsame]
    exact le_antisymm (hW.range_subset_closure_image_dense (denseRange_closureInclusion π))
      (closure_minimal (image_subset_range _ _) (isCompact_range hW).isClosed)
  let φ := W.codRestrict (weakOperatorClosure τ) fun a ↦ by
    change W a ∈ (weakOperatorClosure τ : Set (F →WOT[𝕜] F))
    rw [← hRange]
    exact mem_range_self _
  refine ⟨φ, hW.subtype_mk _, ?_, hdesc⟩
  intro b
  obtain ⟨a, ha⟩ : b.1 ∈ range W := hRange.symm ▸ b.2
  exact ⟨a, Subtype.ext ha⟩

/-- Admissibility passes through a dense-range intertwiner when the target
representation has a uniform operator bound. -/
theorem admissible_denseIntertwiner (j : E →L[𝕜] F) (hj : DenseRange j)
    (hinter : ∀ s x, τ s (j x) = j (π s x))
    {C : ℝ} (hC : 0 ≤ C) (hτ : ∀ s, ‖τ s‖ ≤ C)
    (hπ : IsJdLGAdmissible π) : IsJdLGAdmissible τ := by
  obtain ⟨φ, hφc, hφs, _⟩ := exists_closure_denseIntertwiner_map j hj hinter hC hτ hπ.1
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  let L := K.map φ hφs
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.1 hπ.1
  have heq : range (fun a ↦ (φ a : F →WOT[𝕜] F)) =
      (weakOperatorClosure τ : Set (F →WOT[𝕜] F)) := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact (φ a).2
    · intro hb
      obtain ⟨a, ha⟩ := hφs ⟨b, hb⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  refine ⟨?_, L.identity, L.isMinimalIdempotent_identity,
    fun _ h ↦ L.eq_identity_of_isMinimalIdempotent h⟩
  rw [← heq]
  exact isCompact_range (continuous_subtype_val.comp hφc)

end Transfer

end JdLG
