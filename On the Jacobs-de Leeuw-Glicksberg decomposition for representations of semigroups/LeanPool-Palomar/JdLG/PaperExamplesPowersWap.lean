/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesPowersWeak
public import JdLG.PaperExamplesWapClosed
public import JdLG.ReversibleAction

/-!
# The perfect-powers counterexample on the WAP translation space

The ambient space is the subspace of all bounded functions on the integers
having relatively weakly compact translate orbit. Its translation
representation is JdLG-admissible, and the powers indicator has weak
limit zero along negative times while its polynomial coefficient is one.
-/

@[expose] public section

namespace JdLG.PaperExamplesPowers

open Filter
open scoped ENNReal Topology

local notation "W" => lp (fun _ : ℤ ↦ ℂ) ∞

/-- The full space of bounded weakly almost periodic functions on the integers. -/
noncomputable abbrev IntegerWap := wapVectorSubmodule translation

/-- Translation on the weakly almost periodic functions. -/
noncomputable def wapTranslation : Multiplicative ℤ →ₙ* (IntegerWap →L[ℂ] IntegerWap) :=
  wapVectorRepresentation translation

theorem translation_opNorm_le (a : Multiplicative ℤ) : ‖translation a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply lp.norm_le_of_forall_le (norm_nonneg f)
  intro t
  change ‖f (a.toAdd + t)‖ ≤ ‖f‖
  exact lp.norm_apply_le_norm (by simp) f _

instance : CompleteSpace IntegerWap :=
  (isClosed_wapVectorSubmodule translation translation_opNorm_le).completeSpace_coe

/-- Translation on the WAP space viewed as a unital group representation. -/
noncomputable def wapTranslationGroup : Multiplicative ℤ →* (IntegerWap →L[ℂ] IntegerWap) where
  toMulHom := wapTranslation
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    apply lp.ext
    funext t
    change f.val (0 + t) = f.val t
    rw [zero_add]

theorem wapTranslation_admissible : IsJdLGAdmissible wapTranslation := by
  apply admissible_of_commutative (compact_weakOperatorClosure_wapVectorRepresentation _
    translation_opNorm_le)
  intro a b
  rw [← map_mul, ← map_mul, mul_comm]

/-- The reversible part of the integer WAP translation space consists exactly
of the functions with norm-precompact orbit, namely the strongly almost
periodic functions. -/
theorem wapTranslation_reversible_iff_stronglyAlmostPeriodic (x : IntegerWap) :
    IsReversible (closureAction wapTranslation) x ↔ HasPrecompactOrbit wapTranslation x :=
  group_reversible_iff_precompactOrbit wapTranslationGroup wapTranslation_admissible x

/-- The actual perfect-powers indicator, regarded as a vector in `W(ℤ)`. -/
noncomputable def powersWapVector (k : ℕ) (hk : 2 ≤ k) : IntegerWap :=
  ⟨powersIndicator k, by
    change IsCompact (closure (Set.range (fun a : Multiplicative ℤ ↦ toWeakSpace ℂ W
      (translation a (powersIndicator k)))))
    exact powersIndicator_weakly_almost_periodic hk⟩

theorem powersWapVector_almost_weakly_stable (k : ℕ) (hk : 2 ≤ k) :
    IsAlmostWeaklyStable (closureAction wapTranslation) (powersWapVector k hk) := by
  apply (stable_iff_zero_mem_weakOrbitClosure wapTranslation_admissible.1 _).2
  let x := powersWapVector k hk
  have hi : Function.Injective (topDualPairing ℂ IntegerWap).flip := by
    intro x y h
    by_contra hne
    obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ) hne
    exact hf (LinearMap.congr_fun h f)
  have ht : Tendsto (fun a : ℤ ↦ toWeakSpace ℂ IntegerWap
      (wapTranslation (Multiplicative.ofAdd a) x)) atBot (𝓝 0) := by
    refine (WeakBilin.tendsto_iff_forall_eval_tendsto _ hi).2 fun f ↦ ?_
    obtain ⟨F, hF, -⟩ := exists_extension_norm_eq IntegerWap f
    have hcomp := (WeakBilin.eval_continuous (topDualPairing ℂ W).flip F).tendsto
      (0 : WeakSpace ℂ W)
    have hF' := hcomp.comp (translate_weakly_zero_atBot hk)
    change Tendsto (fun a : ℤ ↦ F (boundedIndicator (translateSupport k a))) atBot
      (𝓝 (F 0)) at hF'
    change Tendsto (fun a : ℤ ↦ f (wapTranslation (Multiplicative.ofAdd a) x)) atBot (𝓝 (f 0))
    rw [map_zero] at hF' ⊢
    exact hF'.congr' (Eventually.of_forall fun a ↦
      hF (wapTranslation (Multiplicative.ofAdd a) x))
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun a ↦
    ⟨Multiplicative.ofAdd a, rfl⟩)

/-- The unit coefficient at every positive polynomial time, inside the actual
WAP translation representation of Example 5.4. -/
theorem wap_polynomial_coefficient (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : 0 < n) :
    (wapTranslation (Multiplicative.ofAdd ((n : ℤ) ^ k)) (powersWapVector k hk)).val 0 = 1 :=
  polynomial_coefficient k n hn

end JdLG.PaperExamplesPowers
