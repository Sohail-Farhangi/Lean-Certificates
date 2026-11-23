/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.CompactDenseGroup

/-! # Corollary 1.4 for representations of topological groups -/

@[expose] public section

open Set Filter
open scoped Topology

namespace JdLG

variable {G 𝕜 E : Type*} [Group G] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Corollary 1.4 for groups. A unital group representation with compact weak
operator closure is JdLG-admissible. The group may have any topology under
which it is a representation. The conclusion depends only on the compact
closure of its operator image. -/
theorem admissible_of_group (π : G →* (E →L[𝕜] E))
    (hCompact : IsCompact (weakOperatorClosure π.toMulHom : Set (E →WOT[𝕜] E))) :
    IsJdLGAdmissible π.toMulHom := by
  let T := weakOperatorClosure π.toMulHom
  have hMapOne : weakRepresentation π.toMulHom 1 = 1 := by
    change ContinuousLinearMapWOT.ringEquiv.symm (π 1) = 1
    rw [map_one, map_one]
  let M : Submonoid (E →WOT[𝕜] E) :=
    { T with
      one_mem' := hMapOne ▸ (show weakRepresentation π.toMulHom 1 ∈ T from subset_closure
        (mem_range_self 1)) }
  let : CompactSpace M := isCompact_iff_compactSpace.mp hCompact
  let i : G →* M :=
    { toFun := fun g ↦ closureInclusion π.toMulHom g
      map_one' := Subtype.ext hMapOne
      map_mul' := fun g h ↦ (closureInclusion π.toMulHom).map_mul g h }
  have hi : DenseRange i := denseRange_closureInclusion π.toMulHom
  exact ⟨hCompact, existsUnique_minimalIdempotent_of_denseGroup i hi⟩

/-- The final assertion of Corollary 1.4 in the group case. The semigroup
representation may have a different source if its weak operator closure
equals that of the group representation. -/
theorem admissible_of_same_group_weakOperatorClosure {S : Type*} [Semigroup S]
    (ρ : S →ₙ* (E →L[𝕜] E)) (π : G →* (E →L[𝕜] E))
    (hπ : IsCompact (weakOperatorClosure π.toMulHom : Set (E →WOT[𝕜] E)))
    (hEq : (weakOperatorClosure ρ : Set (E →WOT[𝕜] E)) =
      (weakOperatorClosure π.toMulHom : Set (E →WOT[𝕜] E))) :
    IsJdLGAdmissible ρ := by
  have hT : weakOperatorClosure ρ = weakOperatorClosure π.toMulHom :=
    SetLike.coe_injective hEq
  unfold IsJdLGAdmissible
  rw [hT]
  exact admissible_of_group π hπ

/-- Admissibility only depends on the weak operator closure. In particular
the final assertion of Corollary 1.4 also applies in the measured case. -/
theorem admissible_iff_of_equal_weakOperatorClosures {S T : Type*} [Semigroup S] [Semigroup T]
    (ρ : S →ₙ* (E →L[𝕜] E)) (π : T →ₙ* (E →L[𝕜] E))
    (hEq : (weakOperatorClosure ρ : Set (E →WOT[𝕜] E)) =
      (weakOperatorClosure π : Set (E →WOT[𝕜] E))) :
    IsJdLGAdmissible ρ ↔ IsJdLGAdmissible π := by
  have hT : weakOperatorClosure ρ = weakOperatorClosure π := SetLike.coe_injective hEq
  unfold IsJdLGAdmissible
  rw [hT]

end JdLG
