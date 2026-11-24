/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroObservationLaw
public import Mixing.RudinShapiroMultiplicity

/-! # The L² pullback of the full dyadic phase -/

@[expose] public section
noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace Topology

namespace Mixing

variable (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)

theorem measurePreserving_rudinShapiroPhaseSequence :
    MeasurePreserving rudinShapiroPhaseSequence (rudinShapiroOrbitSystem p hp).measure (rudinShapiroPhaseLaw p) :=
  ⟨measurable_rudinShapiroPhaseSequence, rfl⟩

/-- The isometric L² pullback along all the dyadic phase observations. -/
def rudinShapiroPhasePullback : Lp ℂ 2 (rudinShapiroPhaseLaw p) →ₗᵢ[ℂ]
    Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure :=
  Lp.compMeasurePreservingₗᵢ ℂ rudinShapiroPhaseSequence (measurePreserving_rudinShapiroPhaseSequence p hp)

private def phaseWindowEvents : Set (Set RudinShapiroPhases) :=
  {D | ∃ N : ℕ, ∀ x y : RudinShapiroPhases, (∀ j, j ≤ N → x j = y j) → (x ∈ D ↔ y ∈ D)}

private theorem phaseWindowEvents_isPiSystem : IsPiSystem phaseWindowEvents := by
  rintro A ⟨a, ha⟩ B ⟨b, hb⟩ _
  refine ⟨max a b, fun x y hxy => ?_⟩
  exact and_congr (ha x y (fun j hj => hxy j (hj.trans (le_max_left _ _))))
    (hb x y (fun j hj => hxy j (hj.trans (le_max_right _ _))))

private theorem phaseWindowEvents_measurable {D : Set RudinShapiroPhases} (hD : D ∈ phaseWindowEvents) :
    MeasurableSet D := by
  obtain ⟨n, hn⟩ := hD
  let P : RudinShapiroPhases → (∀ i : Fin (n+1), Fin (2^i.val)) := fun x i => x i.val
  have hm : Measurable P := Measurable.of_eval fun i => measurable_pi_apply i.val
  have he : D = P ⁻¹' (P '' D) := by
    ext x
    constructor
    · exact fun hx => mem_image_of_mem _ hx
    · rintro ⟨y, hy, he⟩
      exact (hn y x (fun j hj => congrFun he ⟨j, Nat.lt_succ_of_le hj⟩)).mp hy
  rw [he]
  exact hm MeasurableSet.of_discrete

private theorem phaseWindowEvents_generate :
    (inferInstance : MeasurableSpace RudinShapiroPhases) = MeasurableSpace.generateFrom phaseWindowEvents := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le (fun _ => phaseWindowEvents_measurable))
  rw [MeasurableSpace.pi_eq_generateFrom_projections]
  apply MeasurableSpace.generateFrom_mono
  rintro _ ⟨i, C, hC, rfl⟩
  exact ⟨i, fun x y h => by change x i ∈ C ↔ y i ∈ C; rw [h i le_rfl]⟩

private def residueSpan : Submodule ℂ (Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure) :=
  (Submodule.span ℂ (range fun i : Σ k : ℕ, Fin (2^k) =>
    rudinShapiroResidueIndicator p hp i.1 i.2)).topologicalClosure

private theorem phaseWindow_pullback_mem_residueSpan {D : Set RudinShapiroPhases} (hD : D ∈ phaseWindowEvents) :
    rudinShapiroPhasePullback p hp (indicatorConstLp 2 (phaseWindowEvents_measurable hD)
      (measure_ne_top (rudinShapiroPhaseLaw p) D) (1:ℂ)) ∈ residueSpan p hp := by
  classical
  have hm := phaseWindowEvents_measurable hD
  obtain ⟨n, hn⟩ := hD
  let A : Finset (Fin (2^n)) := Finset.univ.filter fun a =>
    ∃ w ∈ rudinShapiroSubshift, rudinShapiroPhase n w = a ∧ rudinShapiroPhaseSequence w ∈ D
  have he (w : SignWords) (hw : w ∈ rudinShapiroSubshift) :
      rudinShapiroPhase n w ∈ A ↔ rudinShapiroPhaseSequence w ∈ D := by
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, v, hv, he, hD⟩
      exact (hn (rudinShapiroPhaseSequence v) (rudinShapiroPhaseSequence w)
        (fun j hj => rudinShapiroPhase_eq_of_le hv hw hj he)).mp hD
    · exact fun hD => ⟨Finset.mem_univ _, w, hw, rfl, hD⟩
  let e := indicatorConstLp 2 hm (measure_ne_top (rudinShapiroPhaseLaw p) D) (1:ℂ)
  have hPull : rudinShapiroPhasePullback p hp e =ᵐ[(rudinShapiroOrbitSystem p hp).measure]
      fun w => D.indicator (fun _ => (1:ℂ)) (rudinShapiroPhaseSequence w) :=
    (Lp.coeFn_compMeasurePreserving e (measurePreserving_rudinShapiroPhaseSequence p hp)).trans
      ((measurePreserving_rudinShapiroPhaseSequence p hp).quasiMeasurePreserving.ae_eq_comp
        (indicatorConstLp_coeFn (hs := hm)
          (hμs := measure_ne_top (rudinShapiroPhaseLaw p) D) (c := (1:ℂ))))
  have hSum := Lp.coeFn_finsetSum A (fun a => rudinShapiroResidueIndicator p hp n a)
  have hCoe : ∀ᵐ w ∂(rudinShapiroOrbitSystem p hp).measure, ∀ a : Fin (2^n),
      rudinShapiroResidueIndicator p hp n a w =
        ({w | rudinShapiroResidue n a w} : Set SignWords).indicator (fun _ => (1:ℂ)) w :=
    ae_all_iff.mpr (ae_rudinShapiroResidueIndicator p hp n)
  have hE : rudinShapiroPhasePullback p hp e = ∑ a ∈ A, rudinShapiroResidueIndicator p hp n a := by
    apply Lp.ext
    filter_upwards [hPull, hSum, hCoe, ae_mem_rudinShapiroSubshift p hp] with w h₁ h₂ h₃ hw
    rw [h₁, h₂]
    simp only [Finset.sum_apply, h₃, Set.indicator_apply, mem_ofPred_eq,
      ← rudinShapiroPhase_eq_iff hw n]
    rw [Finset.sum_ite_eq]
    by_cases h : rudinShapiroPhaseSequence w ∈ D
    · rw [ite_eq_left h, ite_eq_left ((he w hw).2 h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((he w hw).1 h'))]
  change rudinShapiroPhasePullback p hp e ∈ residueSpan p hp
  rw [hE]
  exact Submodule.sum_mem _ (fun a _ => Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨⟨n,a⟩, rfl⟩))

private theorem residueSpan_le_phasePullback_range :
    residueSpan p hp ≤ (rudinShapiroPhasePullback p hp).toLinearMap.range := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨n,a⟩, rfl⟩
    let D := {z : RudinShapiroPhases | z n = a}
    have hD : MeasurableSet D := by
      change MeasurableSet ((fun z : RudinShapiroPhases => z n) ⁻¹' {a})
      exact (measurable_pi_apply n) (measurableSet_singleton a)
    let e := indicatorConstLp 2 hD (measure_ne_top (rudinShapiroPhaseLaw p) D) (1:ℂ)
    refine ⟨e, ?_⟩
    change rudinShapiroPhasePullback p hp e = rudinShapiroResidueIndicator p hp n a
    apply Lp.ext
    have hPull : rudinShapiroPhasePullback p hp e =ᵐ[(rudinShapiroOrbitSystem p hp).measure]
        fun w => D.indicator (fun _ => (1:ℂ)) (rudinShapiroPhaseSequence w) :=
      (Lp.coeFn_compMeasurePreserving e (measurePreserving_rudinShapiroPhaseSequence p hp)).trans
        ((measurePreserving_rudinShapiroPhaseSequence p hp).quasiMeasurePreserving.ae_eq_comp
          (indicatorConstLp_coeFn (hs := hD) (hμs := measure_ne_top (rudinShapiroPhaseLaw p) D) (c := (1:ℂ))))
    filter_upwards [hPull, ae_rudinShapiroResidueIndicator p hp n a, ae_mem_rudinShapiroSubshift p hp]
      with w hw hA hS
    rw [hw, hA]
    have he : rudinShapiroPhaseSequence w ∈ D ↔ rudinShapiroResidue n a w :=
      rudinShapiroPhase_eq_iff hS n a
    by_cases hx : rudinShapiroPhaseSequence w ∈ D
    · rw [indicator_of_mem hx, indicator_of_mem (he.mp hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (he.mpr h))]
  · exact (rudinShapiroPhasePullback p hp).isometry.isClosedEmbedding.isClosed_range

/-- The L² range of the full phase map equals the closed span of the dyadic
residue indicators. A finite phase window reduces to its highest coordinate
on the conull set of words with coherent residues. -/
theorem rudinShapiroPhasePullback_range_eq_closedResidueSpan :
    (rudinShapiroPhasePullback p hp).toLinearMap.range =
      (Submodule.span ℂ (range fun i : Σ k : ℕ, Fin (2^k) =>
        rudinShapiroResidueIndicator p hp i.1 i.2)).topologicalClosure := by
  let R := residueSpan p hp
  let L := rudinShapiroPhasePullback p hp
  let W := R.comap L.toLinearMap
  have hWClosed : IsClosed (W : Set (Lp ℂ 2 (rudinShapiroPhaseLaw p))) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  let : CompleteSpace W := hWClosed.completeSpace_coe
  let : W.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W
  have hW : Wᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    let ν := rudinShapiroPhaseLaw p
    have hi : Integrable x ν := (Lp.memLp x).integrable (by norm_num)
    have hC (D : Set RudinShapiroPhases) (hD : D ∈ phaseWindowEvents) : (∫ z in D, x z ∂ν) = 0 := by
      let e := indicatorConstLp 2 (phaseWindowEvents_measurable hD) (measure_ne_top ν D) (1:ℂ)
      have he : e ∈ W := phaseWindow_pullback_mem_residueSpan p hp hD
      have hZero := hx e he
      change ⟪e, x⟫_ℂ = 0 at hZero
      rw [L2.inner_indicatorConstLp_one] at hZero
      exact hZero
    have hUniv : (∫ z, x z ∂ν) = 0 := by
      simpa only [Measure.restrict_univ] using hC univ ⟨0, fun _ _ _ => Iff.rfl⟩
    have hAll (D : Set RudinShapiroPhases) (hD : MeasurableSet D) : (∫ z in D, x z ∂ν) = 0 := by
      refine MeasurableSpace.induction_on_inter phaseWindowEvents_generate phaseWindowEvents_isPiSystem
        (by simp) hC ?_ ?_ D hD
      · intro D hD hZero
        rw [setIntegral_compl hD hi, hUniv, hZero, sub_zero]
      · intro D hDis hD hZero
        rw [integral_iUnion hD hDis hi.integrableOn]
        simp only [hZero, tsum_zero]
    apply Lp.ext
    exact (ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun _ _ _ => hi.integrableOn)
      (fun D hD _ => hAll D hD)).trans (Lp.coeFn_zero ℂ 2 ν).symm
  have hTop := Submodule.orthogonal_eq_bot_iff.mp hW
  change L.toLinearMap.range = R
  refine le_antisymm ?_ (residueSpan_le_phasePullback_range p hp)
  rintro _ ⟨x, rfl⟩
  exact show x ∈ W from hTop ▸ Submodule.mem_top

/-- The full dyadic phase realizes the Kronecker subspace of the actual orbit model. -/
theorem rudinShapiroPhasePullback_range_eq_purePointPart :
    (rudinShapiroPhasePullback p hp).toLinearMap.range =
      purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep := by
  rw [rudinShapiroPhasePullback_range_eq_closedResidueSpan]
  exact rudinShapiroResidueSpan_eq_purePointPart p hp

end Mixing
