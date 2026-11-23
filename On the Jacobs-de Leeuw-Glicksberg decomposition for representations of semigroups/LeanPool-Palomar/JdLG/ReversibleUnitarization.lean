/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleOrbitFunctions
public import JdLG.ReversibleSubspace
public import JdLG.ReversibleUnitaryRestriction
public import Mathlib.Analysis.Normed.Operator.Banach

/-! # Unitarizing a compact group action on a Hilbert space -/

@[expose] public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace JdLG

section Hilbert

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A bounded strongly continuous action of a compact group on a Hilbert space
is equivalent to a strongly continuous unitary action. The closed image of the
orbit-function map into Haar L² supplies the Hilbert space with the invariant norm. -/
theorem equivalent_unitary_of_compact_group
    (ρ : G →* (E →L[𝕜] E)) (hρ : ∀ x, Continuous fun g ↦ ρ g x)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ g, ‖ρ g‖ ≤ C) :
    ∃ V : Submodule 𝕜 (HaarL2 G E), IsClosed (V : Set (HaarL2 G E)) ∧
      ∃ (U : G →* (V ≃ₗᵢ[𝕜] V)) (J : E ≃L[𝕜] V),
        (∀ g x, U g (J x) = J (ρ g x)) ∧ ∀ v : V, Continuous fun g ↦ U g v := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let μ := normalizedHaar G
  let J : E →L[𝕜] HaarL2 G E :=
    (continuousToHaarL2 (𝕜 := 𝕜)).comp (orbitFunctionMap ρ hρ C hC.le hbound)
  have hj (g : G) (x : E) : haarRightTranslation (𝕜 := 𝕜) g (J x) = J (ρ g x) :=
    orbitFunctionMap_toLp_intertwines ρ hρ C hC.le hbound x g
  have hlower (x : E) (g : G) : ‖x‖ / C ≤ ‖ρ g x‖ := by
    apply (div_le_iff₀ hC).2
    have h := (ρ g⁻¹).le_of_opNorm_le (hbound g⁻¹) (ρ g x)
    have heq : ρ g⁻¹ (ρ g x) = x := by
      change (ρ g⁻¹ * ρ g) x = x
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    simpa only [heq, mul_comm C] using h
  have henergy (x : E) : ‖J x‖ ^ 2 = ∫ g, ‖ρ g x‖ ^ 2 ∂μ := by
    have heval : (J x : G → E) =ᵐ[μ] fun g ↦ ρ g x :=
      continuousToHaarL2_coeFn (𝕜 := 𝕜) (orbitFunctionMap ρ hρ C hC.le hbound x)
    calc
      ‖J x‖ ^ 2 = RCLike.re (inner 𝕜 (J x) (J x)) := norm_sq_eq_re_inner (J x)
      _ = RCLike.re (∫ g, inner 𝕜 (J x g) (J x g) ∂μ) :=
        congrArg RCLike.re (L2.inner_def (J x) (J x))
      _ = ∫ g, RCLike.re (inner 𝕜 (J x g) (J x g)) ∂μ :=
        (integral_re (L2.integrable_inner (𝕜 := 𝕜) (J x) (J x))).symm
      _ = ∫ g, ‖ρ g x‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [heval] with g hg
        simp only [hg, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  have hJ (x : E) : ‖x‖ ≤ C * ‖J x‖ := by
    have hfi : Integrable (fun g ↦ ‖ρ g x‖ ^ 2) μ :=
      ((hρ x).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h := integral_mono (integrable_const ((‖x‖ / C) ^ 2)) hfi
      (fun g ↦ pow_le_pow_left₀ (by positivity) (hlower x g) 2)
    have hsq : (‖x‖ / C) ^ 2 ≤ ‖J x‖ ^ 2 := by
      rw [henergy]
      simpa [integral_const] using h
    have hnorm : ‖x‖ / C ≤ ‖J x‖ :=
      le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq
    exact (div_le_iff₀ hC).1 hnorm |>.trans_eq (mul_comm _ _)
  have hanti : AntilipschitzWith ⟨C, hC.le⟩ J := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    change dist x y ≤ C * dist (J x) (J y)
    simpa only [dist_eq_norm, map_sub] using hJ (x - y)
  have hclosed : IsClosed (J.range : Set (HaarL2 G E)) := hanti.isClosed_range J.uniformContinuous
  have hinv : UnitaryInvariant (haarRightTranslation (𝕜 := 𝕜)) J.range := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨ρ g x, (hj g x).symm⟩
  let U := unitarySubmoduleAction (haarRightTranslation (𝕜 := 𝕜)) J.range hinv
  let e := J.equivRange hanti.injective hclosed
  have he (g : G) (x : E) : U g (e x) = e (ρ g x) := Subtype.ext (hj g x)
  refine ⟨J.range, hclosed, U, e, he, fun v ↦ ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective v
  simp_rw [he]
  exact e.continuous.comp (hρ x)

end Hilbert

section Reversible

universe u v

variable {S : Type u} {E : Type v} [Semigroup S] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] {π : S →ₙ* (E →L[ℂ] E)}
  (K : GroupIdeal (weakOperatorClosure π))

/-- The Hilbert-space equivalence assertion in Theorem 3.6. The original action
on the reversible subspace is intertwined by an invertible bounded linear map
with a unitary action of the same semigroup. -/
theorem GroupIdeal.reversibleAction_equivalent_unitary (hK : IsCompact K.carrier) :
    ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (U : S →ₙ* (H ≃ₗᵢ[ℂ] H))
      (J : K.reversibleSubmodule ≃L[ℂ] H),
      ∀ s x, U s (J x) = J (K.reversibleAction s x) := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  have hc := K.continuous_reversibleGroupAction_apply hK
  have hwot : Continuous fun g ↦ ContinuousLinearMapWOT.ofCLM (K.reversibleGroupAction g) :=
    ContinuousLinearMapWOT.continuous_of_dual_apply_continuous fun x f ↦ f.continuous.comp (hc x)
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot _ hwot
  obtain ⟨V, hV, U, J, hJ, _⟩ :=
    equivalent_unitary_of_compact_group K.reversibleGroupAction hc hC hbound
  let : CompleteSpace V := hV.completeSpace_coe
  refine ⟨V, inferInstance, inferInstance, inferInstance,
    U.toMulHom.comp (K.groupRetraction.comp (closureInclusion π)), J, ?_⟩
  intro s x
  have h := DFunLike.congr_fun (DFunLike.congr_fun K.reversibleAction_eq_comp s) x
  exact (hJ _ _).trans (congrArg J h.symm)

end Reversible


end JdLG
