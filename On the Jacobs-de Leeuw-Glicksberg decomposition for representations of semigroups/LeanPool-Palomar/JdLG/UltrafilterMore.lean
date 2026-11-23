/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Orbits
public import JdLG.Ultrafilters

/-!
# Ultrafilter limits of reversible and stable vectors

The vector statements of Lemma 5.1 and the norm IP-star criterion from
Section 5 of Barthmann, Farhangi and Kuznetsova, arXiv:2509.24003v3.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace JdLG

section WeakLimits

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Evaluation of an operator at a fixed vector is continuous from the weak operator topology
to the weak topology on vectors. -/
theorem continuous_weakOrbit_eval (π : S →ₙ* (E →L[𝕜] E)) (x : E) :
    Continuous (fun A : weakOperatorClosure π ↦ toWeakSpace 𝕜 E (closureAction π A x)) := by
  refine WeakBilin.continuous_of_continuous_eval _ fun f ↦ ?_
  exact (ContinuousLinearMapWOT.continuous_dual_apply x f).comp continuous_subtype_val

variable [SeparatingDual 𝕜 E]

/-- Evaluating the Stone–Čech operator limit gives the weak limit of the vector orbit. -/
theorem tendsto_weakOrbit_ultrafilterExtend {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) (p : Ultrafilter S) (x : E) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S)
      (𝓝 (toWeakSpace 𝕜 E (closureAction π (Ultrafilter.extend (closureInclusion π) p) x))) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  exact ((continuous_weakOrbit_eval π x).tendsto _).comp
    (tendsto_ultrafilterExtend (closureInclusion π) p)

/-- Lemma 5.1(i). Every idempotent ultrafilter fixes every reversible vector in the weak
topology. -/
theorem reversible_tendsto_of_idempotent {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) {x : E} (hx : IsReversible (closureAction π) x)
    {p : Ultrafilter S} (hp : p * p = p) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 (toWeakSpace 𝕜 E x)) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  let A := Ultrafilter.extend (closureInclusion π) p
  have hret := congrArg Subtype.val
    (K.groupRetraction_ultrafilterExtend_eq_one_of_idempotent
      continuous_const_mul continuous_mul_const (closureInclusion π) hp)
  change K.identity * A = K.identity at hret
  have hfix := (K.reversible_iff_fixed (closureAction π) x).mp hx
  have hAx : closureAction π A x = x := by
    calc
      closureAction π A x = closureAction π A (closureAction π K.identity x) :=
        congrArg (closureAction π A) hfix.symm
      _ = closureAction π (A * K.identity) x := by rw [map_mul]; rfl
      _ = x := by rw [← K.identity_mul_eq_mul_identity, hret]; exact hfix
  have hLimit := tendsto_weakOrbit_ultrafilterExtend hπ p x
  change Tendsto _ _ (𝓝 (toWeakSpace 𝕜 E (closureAction π A x))) at hLimit
  rwa [hAx] at hLimit

/-- Lemma 5.1(iii). An ultrafilter in the closure of the smallest ideal sends each almost
weakly stable vector to zero. -/
theorem stable_tendsto_of_mem_closure_smallestIdeal {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) {x : E} (hx : IsAlmostWeaklyStable (closureAction π) x)
    {p : Ultrafilter S} (hp : p ∈ closure (smallestIdeal (Ultrafilter S))) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 0) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  let A := Ultrafilter.extend (closureInclusion π) p
  have hMem : A ∈ K.carrier := K.ultrafilterExtend_mem_of_mem_closure_smallestIdeal
    continuous_const_mul continuous_mul_const
    (closureInclusion π) (denseRange_closureInclusion π) hp
  have hzero := (K.stable_iff_projection_eq_zero (closureAction π) x).mp hx
  change closureAction π K.identity x = 0 at hzero
  have hAx : closureAction π A x = 0 := by
    conv_lhs => rw [← K.mul_identity hMem, map_mul]
    change closureAction π A (closureAction π K.identity x) = 0
    rw [hzero, map_zero]
  have hLimit := tendsto_weakOrbit_ultrafilterExtend hπ p x
  change Tendsto _ _ (𝓝 (toWeakSpace 𝕜 E (closureAction π A x))) at hLimit
  simpa only [hAx, map_zero] using hLimit

end WeakLimits

section NormReturns

variable {S 𝕜 F : Type*} [Semigroup S] [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a norm-precompact orbit, an ultrafilter's weak and norm limits agree. -/
theorem tendsto_normOrbit_of_precompact_of_weak {π : S →ₙ* (F →L[𝕜] F)} {x y : F}
    {p : Ultrafilter S} (hCompact : HasPrecompactOrbit π x)
    (h : Tendsto (fun s ↦ toWeakSpace 𝕜 F (π s x)) (p : Filter S)
      (𝓝 (toWeakSpace 𝕜 F y))) : Tendsto (fun s ↦ π s x) (p : Filter S) (𝓝 y) := by
  let C := closure (range fun s ↦ π s x)
  let : CompactSpace C := isCompact_iff_compactSpace.mp hCompact
  let f (s : S) : C := ⟨π s x, subset_closure ⟨s, rfl⟩⟩
  let z := Ultrafilter.extend f p
  have hNorm : Tendsto (fun s ↦ π s x) (p : Filter S) (𝓝 (z : F)) :=
    (continuous_subtype_val.tendsto z).comp (tendsto_ultrafilterExtend f p)
  have hWeak := ((toWeakSpaceCLM 𝕜 F).continuous.tendsto (z : F)).comp hNorm
  have hzy : (z : F) = y := (toWeakSpace 𝕜 F).injective (tendsto_nhds_unique hWeak h)
  rwa [hzy] at hNorm

/-- The reversible-to-IP-star direction of Theorem 5.3(i), using norm-precompactness of the
reversible orbit. -/
theorem norm_return_isIPStar_of_reversible_of_precompact
    {π : S →ₙ* (F →L[𝕜] F)} (hπ : IsJdLGAdmissible π) {x : F}
    (hx : IsReversible (closureAction π) x) (hCompact : HasPrecompactOrbit π x)
    {ε : ℝ} (hε : 0 < ε) : IsIPStar {s | ‖x - π s x‖ < ε} := by
  apply isIPStar_iff_forall_idempotent_mem.mpr
  intro p hp
  have hNorm := tendsto_normOrbit_of_precompact_of_weak hCompact
    (reversible_tendsto_of_idempotent hπ hx hp)
  have hBall := (Metric.tendsto_nhds.mp hNorm) ε hε
  change ∀ᶠ s in (p : Filter S), ‖x - π s x‖ < ε
  simpa only [dist_comm, dist_eq_norm] using hBall

/-- The IP-star-to-reversible direction of Theorem 5.3(i). -/
theorem reversible_of_norm_return_isIPStar [Nonempty S]
    {π : S →ₙ* (F →L[𝕜] F)} (hπ : IsJdLGAdmissible π) {x : F}
    (h : ∀ ε > (0 : ℝ), IsIPStar {s | ‖x - π s x‖ < ε}) :
    IsReversible (closureAction π) x := by
  obtain ⟨e, _, hProj, hRange, _⟩ := ultrafilter_limit_eq_jdlg_projection hπ
  obtain ⟨p, hp, hpp⟩ := exists_idempotent_ultrafilter_in_smallestIdeal (S := S)
  have hNorm : Tendsto (fun s ↦ π s x) (p : Filter S) (𝓝 x) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hReturn := isIPStar_iff_forall_idempotent_mem.mp (h ε hε) p hpp
    change ∀ᶠ s in (p : Filter S), ‖x - π s x‖ < ε at hReturn
    simpa only [dist_comm, dist_eq_norm] using hReturn
  let eval : (F →WOT[𝕜] F) → WeakSpace 𝕜 F := fun A ↦ toWeakSpace 𝕜 F (A x)
  have hEval : Continuous eval := WeakBilin.continuous_of_continuous_eval _ fun f ↦
    ContinuousLinearMapWOT.continuous_dual_apply x f
  have hWeak := (hEval.tendsto _).comp (hProj p (subset_closure hp) hpp)
  have hId : closureAction π e x = x := (toWeakSpace 𝕜 F).injective
    (tendsto_nhds_unique hWeak (((toWeakSpaceCLM 𝕜 F).continuous.tendsto x).comp hNorm))
  exact (hRange x).mpr ⟨x, hId⟩

end NormReturns

end JdLG
