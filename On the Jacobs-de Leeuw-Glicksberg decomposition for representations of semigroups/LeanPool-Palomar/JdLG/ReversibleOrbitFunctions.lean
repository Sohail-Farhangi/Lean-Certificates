/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleRegular

/-! # Continuous orbit functions and Haar L² -/

@[expose] public section

open MeasureTheory Set

namespace JdLG

section OrbitFunctions

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The norm-continuous orbit functions of a uniformly bounded group action. -/
noncomputable def orbitFunctionMap (ρ : G →* (E →L[𝕜] E))
    (hρ : ∀ x, Continuous fun g ↦ ρ g x)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ g, ‖ρ g‖ ≤ C) : E →L[𝕜] C(G, E) :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨fun g ↦ ρ g x, hρ x⟩
      map_add' := by intro x y; ext g; exact map_add (ρ g) x y
      map_smul' := by intro a x; ext g; exact map_smul (ρ g) a x }
    C (fun x ↦ (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg x))).2
      fun g ↦ (ρ g).le_of_opNorm_le (hbound g) x)

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
@[simp] theorem orbitFunctionMap_apply (ρ : G →* (E →L[𝕜] E))
    (hρ : ∀ x, Continuous fun g ↦ ρ g x)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ g, ‖ρ g‖ ≤ C) (x : E) (g : G) :
    orbitFunctionMap ρ hρ C hC hbound x g = ρ g x := rfl

/-- Mapping a vector to its orbit function intertwines the original action with
the right regular action on Haar L². -/
theorem orbitFunctionMap_toLp_intertwines (ρ : G →* (E →L[𝕜] E))
    (hρ : ∀ x, Continuous fun g ↦ ρ g x)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ g, ‖ρ g‖ ≤ C) (x : E) (g : G) :
    haarRightTranslation (𝕜 := 𝕜) g
      (continuousToHaarL2 (𝕜 := 𝕜) (orbitFunctionMap ρ hρ C hC hbound x)) =
    continuousToHaarL2 (𝕜 := 𝕜) (orbitFunctionMap ρ hρ C hC hbound (ρ g x)) := by
  let P := continuousToHaarL2 (𝕜 := 𝕜) (G := G) (F := E)
  let O := orbitFunctionMap ρ hρ C hC hbound
  have h : rightTranslate g (O x) = O (ρ g x) := by
    apply ContinuousMap.ext
    intro t
    change ρ (t * g) x = ρ t (ρ g x)
    rw [map_mul]
    rfl
  exact (haarRightTranslation_toLp (𝕜 := 𝕜) g (O x)).trans (congrArg P h)

end OrbitFunctions

end JdLG
