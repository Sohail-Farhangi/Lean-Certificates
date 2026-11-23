/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Real weakly almost periodic tests

The weak topology is on the space of bounded continuous functions, and
weak almost periodicity is compactness of the weak closure of the
right-translation orbit. -/

@[expose] public section

open Set
open scoped BoundedContinuousFunction Topology

namespace JdLG

section WAP

variable {S : Type*} [Semigroup S] [TopologicalSpace S] [SeparatelyContinuousMul S]

local notation "BC" => S →ᵇ ℝ

/-- Right translation of a bounded continuous test. -/
def rightTranslateBC (f : BC) (s : S) : BC :=
  f.compContinuous ⟨(· * s), continuous_mul_const s⟩

/-- The bounded continuous tests with relatively weakly compact right
translation orbit. -/
def IsWeaklyAlmostPeriodic (f : BC) : Prop :=
  IsCompact (closure (range fun s ↦ toWeakSpace ℝ BC (rightTranslateBC f s)))

theorem isWap_zero : IsWeaklyAlmostPeriodic (0 : BC) := by
  have h₀ : range (fun s ↦ toWeakSpace ℝ BC (rightTranslateBC 0 s)) ⊆ {0} := by
    rintro _ ⟨s, rfl⟩
    have h : rightTranslateBC (0 : BC) s = 0 := BoundedContinuousFunction.ext fun _ ↦ rfl
    simp only [h, map_zero, mem_singleton_iff]
  exact isCompact_singleton.of_isClosed_subset isClosed_closure
    (closure_minimal h₀ isClosed_singleton)

theorem isWap_add {f g : BC} (hf : IsWeaklyAlmostPeriodic f)
    (hg : IsWeaklyAlmostPeriodic g) : IsWeaklyAlmostPeriodic (f + g) := by
  let F := closure (range fun s ↦ toWeakSpace ℝ BC (rightTranslateBC f s))
  let G := closure (range fun s ↦ toWeakSpace ℝ BC (rightTranslateBC g s))
  let add : WeakSpace ℝ BC × WeakSpace ℝ BC → WeakSpace ℝ BC := fun p ↦ p.1 + p.2
  have hK : IsCompact (add '' (F ×ˢ G)) :=
    (hf.prod hg).image (continuous_fst.add continuous_snd)
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨s, rfl⟩
  refine ⟨(toWeakSpace ℝ BC (rightTranslateBC f s), toWeakSpace ℝ BC (rightTranslateBC g s)),
    ⟨subset_closure (mem_range_self s), subset_closure (mem_range_self s)⟩, ?_⟩
  change toWeakSpace ℝ BC (rightTranslateBC f s) + toWeakSpace ℝ BC (rightTranslateBC g s) = _
  rw [← map_add]
  exact congrArg (toWeakSpace ℝ BC) (BoundedContinuousFunction.ext fun _ ↦ rfl)

theorem isWap_smul (r : ℝ) {f : BC} (hf : IsWeaklyAlmostPeriodic f) :
    IsWeaklyAlmostPeriodic (r • f) := by
  let F := closure (range fun s ↦ toWeakSpace ℝ BC (rightTranslateBC f s))
  have hK : IsCompact ((r • ·) '' F) := hf.image (continuous_id.const_smul r)
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨s, rfl⟩
  refine ⟨toWeakSpace ℝ BC (rightTranslateBC f s), subset_closure (mem_range_self s), ?_⟩
  change r • toWeakSpace ℝ BC (rightTranslateBC f s) = _
  rw [← map_smul]
  exact congrArg (toWeakSpace ℝ BC) (BoundedContinuousFunction.ext fun _ ↦ rfl)

/-- The real space of weakly almost periodic functions. -/
def weaklyAlmostPeriodicSubmodule : Submodule ℝ BC where
  carrier := {f | IsWeaklyAlmostPeriodic f}
  zero_mem' := isWap_zero
  add_mem' := isWap_add
  smul_mem' := isWap_smul

theorem isWap_one : IsWeaklyAlmostPeriodic (1 : BC) := by
  have h₁ : range (fun s ↦ toWeakSpace ℝ BC (rightTranslateBC 1 s)) ⊆ {toWeakSpace ℝ BC 1} := by
    rintro _ ⟨s, rfl⟩
    exact mem_singleton_iff.2 (congrArg (toWeakSpace ℝ BC)
      (BoundedContinuousFunction.ext fun _ ↦ rfl))
  exact isCompact_singleton.of_isClosed_subset isClosed_closure
    (closure_minimal h₁ isClosed_singleton)

/-- The right and left invariance clauses use the pointwise translation
formulas. The means have positive mass one on the constant function. -/
structure WapBiInvariantMean where
  functional : (weaklyAlmostPeriodicSubmodule (S := S)) →ₗ[ℝ] ℝ
  monotone' : ∀ f g, (∀ s : S, f.val s ≤ g.val s) → functional f ≤ functional g
  one' : functional ⟨1, isWap_one⟩ = 1
  left' : ∀ (s : S) (f g : weaklyAlmostPeriodicSubmodule (S := S)),
    (∀ t : S, g.val t = f.val (s * t)) → functional g = functional f
  right' : ∀ (s : S) (f g : weaklyAlmostPeriodicSubmodule (S := S)),
    (∀ t : S, g.val t = f.val (t * s)) → functional g = functional f

end WAP
end JdLG
