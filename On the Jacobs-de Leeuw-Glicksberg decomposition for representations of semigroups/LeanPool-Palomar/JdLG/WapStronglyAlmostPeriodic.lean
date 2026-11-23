/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.WapTranslationDecomposition
public import JdLG.ReversibleBasis

/-!
# Strongly almost periodic functions on a monoid

The reversible summand of the WAP translation representation is the closed
linear span of matrix coefficients of continuous finite-dimensional unitary
representations. In one direction, these coefficients are obtained from the
finite unitary systems by evaluation at the monoid unit. In the other, a
limit of unitary matrices induces the ideal projection on the coefficient
space, where its idempotence forces it to act as the identity.
-/

@[expose] public section

open Filter Set
open scoped BoundedContinuousFunction Topology

namespace JdLG.WapTranslation

variable (S : Type*) [Monoid S] [TopologicalSpace S] [SeparatelyContinuousMul S]

local notation "BC" => S →ᵇ ℂ
local notation "W" => ComplexWap S
local notation "V[" n "]" => EuclideanSpace ℂ (Fin n)

/-- A matrix coefficient of a continuous finite-dimensional unitary representation. -/
def IsFiniteUnitaryCoefficient (f : W) : Prop :=
  ∃ (n : ℕ) (U : S →ₙ* (V[n] ≃ₗᵢ[ℂ] V[n])), (∀ x : V[n], Continuous fun s ↦ U s x) ∧
    ∃ (x : V[n]) (ℓ : StrongDual ℂ V[n]), ∀ s : S, f.val s = ℓ (U s x)

/-- The complex strongly almost periodic subspace. -/
noncomputable def stronglyAlmostPeriodicSubmodule : Submodule ℂ W :=
  (Submodule.span ℂ {f | IsFiniteUnitaryCoefficient S f}).topologicalClosure

private noncomputable def coefficientBC {n : ℕ} (U : S →ₙ* (V[n] ≃ₗᵢ[ℂ] V[n]))
    (hU : ∀ x : V[n], Continuous fun s ↦ U s x) (ℓ : StrongDual ℂ V[n]) (x : V[n]) : BC :=
  BoundedContinuousFunction.mkOfBound ⟨fun s ↦ ℓ (U s x), ℓ.continuous.comp (hU x)⟩
    (‖ℓ‖ * ‖x‖ + ‖ℓ‖ * ‖x‖) fun a b ↦ by
      simp only [ContinuousMap.coe_mk, dist_eq_norm]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · simpa only [(U a).norm_map] using ℓ.le_opNorm (U a x)
      · simpa only [(U b).norm_map] using ℓ.le_opNorm (U b x)

private noncomputable def coefficientMapBC {n : ℕ} (U : S →ₙ* (V[n] ≃ₗᵢ[ℂ] V[n]))
    (hU : ∀ x : V[n], Continuous fun s ↦ U s x) (ℓ : StrongDual ℂ V[n]) : V[n] →L[ℂ] BC :=
  ({ toFun := coefficientBC S U hU ℓ
     map_add' x y := BoundedContinuousFunction.ext fun s ↦ by
       change ℓ (U s (x + y)) = ℓ (U s x) + ℓ (U s y)
       rw [map_add, map_add]
     map_smul' c x := BoundedContinuousFunction.ext fun s ↦ by
       change ℓ (U s (c • x)) = c • ℓ (U s x)
       rw [map_smul, map_smul] } : V[n] →ₗ[ℂ] BC).mkContinuous ‖ℓ‖ fun x ↦ by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro s
    change ‖ℓ (U s x)‖ ≤ ‖ℓ‖ * ‖x‖
    simpa only [(U s).norm_map] using ℓ.le_opNorm (U s x)

private theorem coefficientMapBC_intertwines {n : ℕ} (U : S →ₙ* (V[n] ≃ₗᵢ[ℂ] V[n]))
    (hU : ∀ x : V[n], Continuous fun s ↦ U s x) (ℓ : StrongDual ℂ V[n]) (s : S) (x : V[n]) :
    translation S s (coefficientMapBC S U hU ℓ x) = coefficientMapBC S U hU ℓ (U s x) := by
  apply BoundedContinuousFunction.ext
  intro t
  change ℓ (U (t * s) x) = ℓ (U t (U s x))
  rw [map_mul]
  rfl

private theorem coefficientMapBC_mem_wap {n : ℕ} (U : S →ₙ* (V[n] ≃ₗᵢ[ℂ] V[n]))
    (hU : ∀ x : V[n], Continuous fun s ↦ U s x) (ℓ : StrongDual ℂ V[n]) (x : V[n]) :
    coefficientMapBC S U hU ℓ x ∈ ComplexWap S := by
  let J := coefficientMapBC S U hU ℓ
  let b := (toWeakSpace ℂ BC) ∘ J
  have hc : Continuous b := (toWeakSpaceCLM ℂ BC).continuous.comp J.continuous
  have hk : IsCompact (b '' Metric.sphere 0 ‖x‖) := (isCompact_sphere _ _).image hc
  refine hk.of_isClosed_subset isClosed_closure (closure_minimal ?_ hk.isClosed)
  rintro _ ⟨s, rfl⟩
  refine ⟨U s x, ?_, congrArg (toWeakSpace ℂ BC)
    (coefficientMapBC_intertwines S U hU ℓ s x).symm⟩
  simpa only [Metric.mem_sphere, dist_zero_right] using (U s).norm_map x

private noncomputable def coefficientMap {n : ℕ} (U : S →ₙ* (V[n] ≃ₗᵢ[ℂ] V[n]))
    (hU : ∀ x : V[n], Continuous fun s ↦ U s x) (ℓ : StrongDual ℂ V[n]) : V[n] →L[ℂ] W :=
  (coefficientMapBC S U hU ℓ).codRestrict (ComplexWap S) (coefficientMapBC_mem_wap S U hU ℓ)

private theorem intertwiner_on_closure_by_isometry {n : ℕ}
    (U : S →ₙ* (V[n] ≃ₗᵢ[ℂ] V[n])) (J : V[n] →L[ℂ] W)
    (hJ : ∀ s x, action S s (J x) = J (U s x)) (a : weakOperatorClosure (action S)) :
    ∃ A : V[n] →L[ℂ] V[n], Function.Surjective A ∧
      ∀ x, closureAction (action S) a (J x) = J (A x) := by
  let C : Set (V[n] →L[ℂ] V[n]) := {A | ∀ x, ‖A x‖ = ‖x‖}
  have hCC : IsClosed C := by
    have he : C = ⋂ x : V[n], {A | ‖A x‖ = ‖x‖} := by ext A; simp [C]
    rw [he]
    exact isClosed_iInter fun x ↦ isClosed_eq
      (ContinuousLinearMap.apply ℂ V[n] x).continuous.norm continuous_const
  have hCB : C ⊆ Metric.closedBall 0 1 := by
    intro A hA
    rw [Metric.mem_closedBall, dist_zero_right]
    exact A.opNorm_le_bound zero_le_one fun x ↦ (hA x).le.trans_eq (one_mul _).symm
  let : ProperSpace (V[n] →L[ℂ] V[n]) := FiniteDimensional.proper ℂ _
  have hC : IsCompact C := (isCompact_closedBall _ _).of_isClosed_subset hCC hCB
  let F (u : W →WOT[ℂ] W) (x : V[n]) := toWeakSpace ℂ W (u (J x))
  let G (A : V[n] →L[ℂ] V[n]) (x : V[n]) := toWeakSpace ℂ W (J (A x))
  have hF : Continuous F := continuous_pi fun x ↦ WeakBilin.continuous_of_continuous_eval _
    (ContinuousLinearMapWOT.continuous_dual_apply (J x))
  have hG : Continuous G := continuous_pi fun x ↦ (toWeakSpaceCLM ℂ W).continuous.comp
    (J.continuous.comp (ContinuousLinearMap.apply ℂ V[n] x).continuous)
  have himage : range (weakRepresentation (action S)) ⊆ F ⁻¹' (G '' C) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨(U s).toContinuousLinearEquiv.toContinuousLinearMap, (U s).norm_map, ?_⟩
    funext x
    exact congrArg (toWeakSpace ℂ W) (hJ s x).symm
  have ha : F a.val ∈ G '' C := closure_minimal himage ((hC.image hG).isClosed.preimage hF) a.2
  obtain ⟨A, hA, he⟩ := ha
  have hAi : Function.Injective A := (injective_iff_map_eq_zero A).2 fun x hx ↦
    norm_eq_zero.1 ((hA x).symm.trans (hx ▸ norm_zero))
  exact ⟨A, LinearMap.surjective_of_injective hAi, fun x ↦
    (toWeakSpace ℂ W).injective (congrFun he x).symm⟩

private theorem finiteUnitaryCoefficient_mem_reversible (K : GroupIdeal (weakOperatorClosure
    (action S))) {f : W} (hf : IsFiniteUnitaryCoefficient S f) : f ∈ K.reversibleSubmodule := by
  obtain ⟨n, U, hU, x, ℓ, h⟩ := hf
  let J := coefficientMap S U hU ℓ
  have hJ (s : S) (y : V[n]) : action S s (J y) = J (U s y) :=
    Subtype.ext (coefficientMapBC_intertwines S U hU ℓ s y)
  have hfx : J x = f := Subtype.ext (BoundedContinuousFunction.ext fun s ↦ (h s).symm)
  obtain ⟨A, hA, hPJ⟩ := intertwiner_on_closure_by_isometry S U J hJ K.identity
  let P := K.projection (closureAction (action S))
  apply (K.mem_reversibleSubmodule f).2
  obtain ⟨y, hy⟩ := hA x
  have hP : ∀ v, P (J v) = J (A v) := hPJ
  rw [← hfx, ← hy, ← hP y, K.projection_apply_apply]

private theorem finiteUnitarySystem_mem_coefficient {D : Submodule ℂ W}
    (hD : SpannedByIrreducibleUnitarySystem (action S) D) {f : W} (hf : f ∈ D) :
    IsFiniteUnitaryCoefficient S f := by
  obtain ⟨_, ⟨n, U, J, hJ, hJD, hinter⟩, _⟩ := hD
  rw [← hJD] at hf
  obtain ⟨x, rfl⟩ := hf
  refine ⟨n, U, ?_, x, (evaluation S 1).comp J, fun s ↦ ?_⟩
  · intro y
    let C := Metric.sphere (0 : V[n]) ‖y‖
    let : CompactSpace C := isCompact_iff_compactSpace.1 (isCompact_sphere _ _)
    let e (z : C) := toWeakSpace ℂ W (J z.val)
    have he : Continuous e := ((toWeakSpaceCLM ℂ W).continuous.comp J.continuous).comp
      continuous_subtype_val
    have hi : Function.Injective e := fun _ _ h ↦
      Subtype.ext (hJ ((toWeakSpace ℂ W).injective h))
    let u (s : S) : C := ⟨U s y, by
      change U s y ∈ Metric.sphere (0 : V[n]) ‖y‖
      simpa only [Metric.mem_sphere, dist_zero_right] using (U s).norm_map y⟩
    have hu : Continuous u := by
      apply (he.isClosedEmbedding hi).isEmbedding.continuous_iff.2
      change Continuous fun s ↦ toWeakSpace ℂ W (J (U s y))
      simp_rw [← hinter]
      exact (continuous_weakOrbit_closureAction (action S) (J y)).comp
        (continuous_closureInclusion S)
    exact continuous_subtype_val.comp hu
  · change (J x).val s = evaluation S 1 (J (U s x))
    rw [← hinter, evaluation_apply, action_apply, one_mul]

/-- The reversible vectors for the WAP right translations equal the
strongly almost periodic subspace. -/
theorem reversibleSubmodule_eq_stronglyAlmostPeriodic
    (K : GroupIdeal (weakOperatorClosure (action S))) (hK : IsCompact K.carrier) :
    K.reversibleSubmodule = stronglyAlmostPeriodicSubmodule S := by
  apply le_antisymm
  · rw [K.reversibleSubmodule_eq_irreducibleUnitarySystem_span hK]
    exact Submodule.topologicalClosure_mono (iSup_le fun D f hf ↦
      Submodule.subset_span (finiteUnitarySystem_mem_coefficient S D.2 hf))
  · have hb : Submodule.span ℂ {f | IsFiniteUnitaryCoefficient S f} ≤ K.reversibleSubmodule :=
      Submodule.span_le.2 fun _ hf ↦ finiteUnitaryCoefficient_mem_reversible S K hf
    exact closure_minimal hb K.isClosed_reversibleSubmodule

/-- The SAP summand and the functions of absolute mean zero are closed
complementary subspaces of the complex WAP functions. -/
theorem stronglyAlmostPeriodic_complement_of_biInvariantMean (m : WapBiInvariantMean (S := S)) :
    ∃ N : Submodule ℂ W, IsClosed (stronglyAlmostPeriodicSubmodule S : Set W) ∧
      IsClosed (N : Set W) ∧ IsCompl (stronglyAlmostPeriodicSubmodule S) N ∧
      ∀ f, f ∈ N ↔ m.functional (absolute S f) = 0 := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible (admissible S m)
  let π := closureAction (action S)
  let P := (K.projection π).toLinearMap
  rw [← reversibleSubmodule_eq_stronglyAlmostPeriodic S K hK, K.reversibleSubmodule_eq_range]
  exact ⟨P.ker, K.isClosed_range_projection π, K.isClosed_ker_projection π,
    K.range_isCompl_ker π, fun f ↦ (K.stable_iff_mem_ker π f).symm.trans
      (stable_iff_absolute_mean_eq_zero S m f)⟩

end JdLG.WapTranslation
