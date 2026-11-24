/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mixing.SupportingJdLG.Core
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Norm-precompact orbits and reversibility

Under the norm-separation hypothesis of Theorem 3.1, a norm-precompact
orbit belongs to the reversible part. The argument applies the separation
hypothesis to the almost weakly stable component of the vector.
-/

@[expose] public section

namespace Mixing.JdLGBridge

open Set

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The orbit has a compact closure in the norm topology. -/
def HasPrecompactOrbit (π : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  IsCompact (closure (Set.range fun s ↦ π s x))

private theorem weakOperatorClosure_apply_mem_normOrbitClosure
    (π : S →ₙ* (E →L[𝕜] E)) (x : E) (hx : HasPrecompactOrbit π x)
    (A : weakOperatorClosure π) : A.1 x ∈ closure (Set.range fun s ↦ π s x) := by
  let C := closure (Set.range fun s ↦ π s x)
  let weak := toWeakSpaceCLM 𝕜 E
  have hclosed : IsClosed (weak '' C) := (hx.image weak.continuous).isClosed
  let evaluate : (E →WOT[𝕜] E) → WeakSpace 𝕜 E := fun T ↦ weak (T x)
  have heval : Continuous evaluate :=
    WeakBilin.continuous_of_continuous_eval _ fun f ↦
      ContinuousLinearMapWOT.continuous_dual_apply x f
  have hsub : ((weakRepresentation π).srange : Set (E →WOT[𝕜] E)) ⊆
      evaluate ⁻¹' (weak '' C) := by
    rintro _ ⟨s, rfl⟩
    exact ⟨π s x, subset_closure ⟨s, rfl⟩, rfl⟩
  have hA := closure_minimal hsub (hclosed.preimage heval) A.2
  obtain ⟨y, hy, heq⟩ := hA
  exact ((toWeakSpace 𝕜 E).injective heq) ▸ hy

/-- The precompact-orbit-to-reversible implication in Theorem 3.1. The uniform
positive lower bound for each nonzero precompact orbit excludes any nonzero
almost weakly stable component. -/
theorem reversible_of_precompactOrbit_of_separated
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (hseparated : ∀ y : E, y ≠ 0 → HasPrecompactOrbit π y →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : S, δ ≤ ‖π s y‖)
    (x : E) (hx : HasPrecompactOrbit π x) : IsReversible (closureAction π) x := by
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  let P := K.projection (closureAction π)
  let y := x - P x
  have hyzero : P y = 0 := by
    change P (x - P x) = 0
    rw [map_sub, K.projection_apply_apply (closureAction π) x, sub_self]
  let changeVector : E → E := fun z ↦ z - P z
  have hcont : Continuous changeVector := continuous_id.sub P.continuous
  have hcomm (s : S) : P (π s x) = π s (P x) := by
    let A : weakOperatorClosure π := ⟨weakRepresentation π s, subset_closure ⟨s, rfl⟩⟩
    exact K.projection_commutes (closureAction π) A x
  have hsub : Set.range (fun s ↦ π s y) ⊆
      changeVector '' closure (Set.range (fun s ↦ π s x)) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨π s x, subset_closure ⟨s, rfl⟩, ?_⟩
    change π s x - P (π s x) = π s (x - P x)
    rw [hcomm, map_sub]
  have hC := hx.image hcont
  have hy : HasPrecompactOrbit π y :=
    hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  have hzero : (0 : E) ∈ closure (Set.range fun s ↦ π s y) := by
    have hp := weakOperatorClosure_apply_mem_normOrbitClosure π y hy K.identity
    change P y ∈ closure (Set.range fun s ↦ π s y) at hp
    simpa only [hyzero] using hp
  apply (K.reversible_iff_fixed (closureAction π) x).2
  by_contra hfix
  have hne : y ≠ 0 := fun hy ↦ hfix ((sub_eq_zero.mp hy).symm)
  obtain ⟨δ, hδ, hlower⟩ := hseparated y hne hy
  have hclosed : IsClosed {z : E | δ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have hsubset : Set.range (fun s : S ↦ π s y) ⊆ {z : E | δ ≤ ‖z‖} := by
    rintro _ ⟨s, rfl⟩
    exact hlower s
  have hδzero : δ ≤ ‖(0 : E)‖ := closure_minimal hsubset hclosed hzero
  exact hδ.not_ge (by simpa using hδzero)

end Mixing.JdLGBridge
