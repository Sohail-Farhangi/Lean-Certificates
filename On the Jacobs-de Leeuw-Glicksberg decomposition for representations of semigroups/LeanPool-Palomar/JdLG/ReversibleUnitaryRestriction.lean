/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-! # Invariant subspaces of unitary group actions -/

@[expose] public section

open Set Submodule
open scoped InnerProductSpace

namespace JdLG

section Restriction

variable {G 𝕜 H : Type*} [Group G] [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A subspace invariant under every element of a unitary group action. -/
def UnitaryInvariant (U : G →* (H ≃ₗᵢ[𝕜] H)) (V : Submodule 𝕜 H) : Prop :=
  ∀ g : G, ∀ x ∈ V, U g x ∈ V

theorem UnitaryInvariant.orthogonal {U : G →* (H ≃ₗᵢ[𝕜] H)} {V : Submodule 𝕜 H}
    (hV : UnitaryInvariant U V) : UnitaryInvariant U Vᗮ := by
  intro g x hx
  rw [V.mem_orthogonal] at hx ⊢
  intro y hy
  have hg (z : H) : U g (U g⁻¹ z) = z := by
    change (U g * U g⁻¹) z = z
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    inner 𝕜 y (U g x) = inner 𝕜 (U g (U g⁻¹ y)) (U g x) := by rw [hg]
    _ = inner 𝕜 (U g⁻¹ y) x := (U g).inner_map_map _ _
    _ = 0 := hx _ (hV _ _ hy)

theorem UnitaryInvariant.iSup {ι : Type*} {U : G →* (H ≃ₗᵢ[𝕜] H)}
    {V : ι → Submodule 𝕜 H} (hV : ∀ i, UnitaryInvariant U (V i)) :
    UnitaryInvariant U (⨆ i, V i) := by
  intro g
  let A := (U g).toLinearMap
  have hmap (i : ι) : Submodule.map A (V i) ≤ ⨆ j, V j := by
    exact (Submodule.map_le_iff_le_comap.2 (hV i g)).trans (le_iSup V i)
  have hle : Submodule.map A (⨆ i, V i) ≤ ⨆ i, V i := by
    rw [Submodule.map_iSup]
    exact iSup_le hmap
  exact Submodule.map_le_iff_le_comap.1 hle

/-- The restricted unitary group action on an invariant subspace. -/
def unitarySubmoduleAction (U : G →* (H ≃ₗᵢ[𝕜] H)) (V : Submodule 𝕜 H)
    (hV : UnitaryInvariant U V) : G →* (V ≃ₗᵢ[𝕜] V) where
  toFun g :=
    { toLinearEquiv :=
        { (U g).toLinearMap.restrict (hV g) with
          invFun := fun x ↦ ⟨U g⁻¹ x, hV g⁻¹ x x.2⟩
          left_inv := fun x ↦ Subtype.ext (show (U g⁻¹ * U g) x = x by
            rw [← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun x ↦ Subtype.ext (show (U g * U g⁻¹) x = x by
            rw [← map_mul, mul_inv_cancel, map_one]; rfl) }
      norm_map' := fun x ↦ (U g).norm_map x }
  map_one' := by
    ext x
    change U 1 x = (x : H)
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change U (g * h) x = U g (U h x)
    rw [map_mul]
    rfl

@[simp] theorem unitarySubmoduleAction_apply (U : G →* (H ≃ₗᵢ[𝕜] H)) (V : Submodule 𝕜 H)
    (hV : UnitaryInvariant U V) (g : G) (x : V) :
    (unitarySubmoduleAction U V hV g x : H) = U g x := rfl

end Restriction

end JdLG
