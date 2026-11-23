/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.RepresentationRenorm

/-! # Completeness for the orbit norm -/

@[expose] public section

namespace JdLG

variable {S E : Type*} [Monoid S] [gE : NormedAddCommGroup E] [sE : NormedSpace ℂ E]

/-- The normed additive group with the orbit norm. -/
@[instance_reducible]
noncomputable def orbitNormedAddCommGroup (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) : NormedAddCommGroup E :=
  (orbitNorm π hC).toNormedAddCommGroup

/-- The same complex vector space with the orbit norm. -/
@[instance_reducible]
noncomputable def orbitNormedSpace (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) :
    @NormedSpace ℂ E _ (orbitNormedAddCommGroup π hC).toSeminormedAddCommGroup :=
  @NormedSpace.mk ℂ E _ (orbitNormedAddCommGroup π hC).toSeminormedAddCommGroup
    sE.toModule (fun c x ↦ (orbitNorm_smul π hC c x).le)

/-- The two norms define uniformly equivalent metric structures. -/
noncomputable def orbitNorm_uniformEquiv (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) :
    @UniformEquiv E E gE.toUniformSpace (orbitNormedAddCommGroup π hC).toUniformSpace := by
  let d' := @dist E (orbitNormedAddCommGroup π hC).toDist
  have hd (x y : E) : d' x y = orbitNormFun π (x - y) := by
    change @dist E (orbitNormedAddCommGroup π hC).toDist x y = _
    rw [@dist_eq_norm E (orbitNormedAddCommGroup π hC).toSeminormedAddCommGroup]
    exact orbitNorm_apply π hC _
  let M := max 1 C
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  refine @UniformEquiv.mk E E gE.toUniformSpace
    (orbitNormedAddCommGroup π hC).toUniformSpace (Equiv.refl E) ?_ ?_
  · refine (@Metric.uniformContinuous_iff E E gE.toPseudoMetricSpace
      (orbitNormedAddCommGroup π hC).toPseudoMetricSpace id).2 ?_
    intro ε hε
    refine ⟨ε / M, div_pos hε hM, fun {a b} hab ↦ ?_⟩
    change d' a b < ε
    rw [hd]
    calc
      orbitNormFun π (a - b) ≤ C * ‖a - b‖ := orbitNormFun_le π hC _
      _ ≤ M * dist a b := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ < ε := (lt_div_iff₀' hM).1 hab
  · refine (@Metric.uniformContinuous_iff E E (orbitNormedAddCommGroup π hC).toPseudoMetricSpace
      gE.toPseudoMetricSpace id).2 ?_
    intro ε hε
    refine ⟨ε, hε, fun {a b} hab ↦ ?_⟩
    change d' a b < ε at hab
    rw [hd] at hab
    rw [dist_eq_norm]
    exact (norm_le_orbitNormFun π hC _).trans_lt hab

/-- The orbit norm is complete whenever the original norm is complete. -/
theorem orbitNorm_completeSpace (π : S →* (E →L[ℂ] E)) {C : ℝ}
    (hC : ∀ s, ‖π s‖ ≤ C) [CompleteSpace E] :
    @CompleteSpace E (orbitNormedAddCommGroup π hC).toUniformSpace :=
  (@UniformEquiv.completeSpace_iff E E gE.toUniformSpace
    (orbitNormedAddCommGroup π hC).toUniformSpace (orbitNorm_uniformEquiv π hC)).mp inferInstance

end JdLG
