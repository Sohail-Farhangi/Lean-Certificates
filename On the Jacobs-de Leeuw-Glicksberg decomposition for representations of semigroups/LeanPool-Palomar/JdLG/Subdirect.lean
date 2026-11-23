/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The reversible and stable factors of the operator semigroup

The group ideal and the operators restricted to the stable kernel give the
subdirect product in Theorem 2.3(v) of arXiv:2509.24003v3.
-/

@[expose] public section

namespace JdLG.GroupIdeal

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (K : GroupIdeal S) (ρ : S →ₙ* (E →L[𝕜] E))

/-- The action on the almost weakly stable kernel. -/
def stableAction : S →ₙ* ((LinearMap.ker (K.projection ρ).toLinearMap) →L[𝕜]
    (LinearMap.ker (K.projection ρ).toLinearMap)) where
  toFun s := (ρ s).restrict fun x hx ↦ by
    change K.projection ρ (ρ s x) = 0
    rw [K.projection_commutes]
    exact (congrArg (ρ s) (LinearMap.mem_ker.mp hx)).trans (map_zero (ρ s))
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (a * b) (x : E) = (ρ a * ρ b) (x : E)
    rw [map_mul]

private theorem stableAction_identity : K.stableAction ρ K.identity = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.mem_ker.mp x.2

/-- The joint action on the group ideal and the stable kernel, restricted to
the image on each factor. -/
noncomputable def subdirectHom : S →ₙ* (K.carrier × (K.stableAction ρ).srange) :=
  K.groupRetraction.prod (K.stableAction ρ).srangeRestrict

private theorem subdirectHom_injective (hρ : Function.Injective ρ) :
    Function.Injective (K.subdirectHom ρ) := by
  intro a b hab
  apply hρ
  apply ContinuousLinearMap.ext
  intro x
  have hgroup := congrArg (fun p : K.carrier × (K.stableAction ρ).srange ↦ ρ p.1.1 x) hab
  change ρ (K.identity * a) x = ρ (K.identity * b) x at hgroup
  rw [map_mul, map_mul] at hgroup
  change K.projection ρ (ρ a x) = K.projection ρ (ρ b x) at hgroup
  rw [K.projection_commutes, K.projection_commutes] at hgroup
  let y : LinearMap.ker (K.projection ρ).toLinearMap := ⟨x - K.projection ρ x, by
    change K.projection ρ (x - K.projection ρ x) = 0
    rw [map_sub, K.projection_apply_apply, sub_self]⟩
  have hstable := congrArg (fun p : K.carrier × (K.stableAction ρ).srange ↦ (p.2.1 y : E)) hab
  change ρ a (x - K.projection ρ x) = ρ b (x - K.projection ρ x) at hstable
  rw [map_sub, map_sub, hgroup] at hstable
  simpa only [sub_add_cancel] using congrArg (· + ρ b (K.projection ρ x)) hstable

/-- Theorem 2.3(v). The group factor and the action on the stable kernel both
have surjective coordinate maps. The second factor has a zero, so its smallest
nonempty two-sided ideal is the singleton consisting of that zero. -/
theorem subdirect_product (hρ : Function.Injective ρ) :
    Function.Injective (K.subdirectHom ρ) ∧
      Function.Surjective (fun a ↦ (K.subdirectHom ρ a).1) ∧
      Function.Surjective (fun a ↦ (K.subdirectHom ρ a).2) ∧
      ∃ z : (K.stableAction ρ).srange, ∀ r, z * r = z ∧ r * z = z := by
  refine ⟨K.subdirectHom_injective ρ hρ, K.groupRetraction_surjective,
    (K.stableAction ρ).srangeRestrict_surjective, ?_⟩
  refine ⟨(K.stableAction ρ).srangeRestrict K.identity, fun r ↦ ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    change K.stableAction ρ K.identity * r.1 = K.stableAction ρ K.identity
    rw [K.stableAction_identity, zero_mul]
  · apply Subtype.ext
    change r.1 * K.stableAction ρ K.identity = K.stableAction ρ K.identity
    rw [K.stableAction_identity, mul_zero]

end JdLG.GroupIdeal

namespace JdLG

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparatingDual 𝕜 E]

/-- The subdirect product description for the weak operator closure of a
JdLG-admissible representation. The second factor's absorbing element is
the restriction of the projection to its kernel. -/
theorem subdirect_product_of_admissible {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) :
    ∃ K : GroupIdeal (weakOperatorClosure π),
      Function.Injective (K.subdirectHom (closureAction π)) ∧
      Function.Surjective (fun a ↦ (K.subdirectHom (closureAction π) a).1) ∧
      Function.Surjective (fun a ↦ (K.subdirectHom (closureAction π) a).2) ∧
      ∃ z : (K.stableAction (closureAction π)).srange, ∀ r, z * r = z ∧ r * z = z := by
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  refine ⟨K, K.subdirect_product (closureAction π) ?_⟩
  intro a b hab
  exact Subtype.ext (ContinuousLinearMapWOT.toCLM_injective hab)

end JdLG
