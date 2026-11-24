/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationGeometryTower
public import Mixing.NilrotationKoopmanFibres
public import Mixing.NilrotationKoopmanVertical
public import Mixing.NilrotationVerticalDecay
public import Mixing.NilrotationVerticalMultiplicity
public import Mixing.NilrotationHaarComplement
public import Mixing.NilrotationBracketPhases
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
noncomputable section

namespace Mixing

open Function Filter MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped Nilrotation commutatorElement InnerProductSpace ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G]

omit [IsTopologicalGroup G] [SecondCountableTopology G] in
/-- The phase argument uses inverse time, since Koopman is pullback by positive time. -/
theorem nilrotation_dense_lifted_cosets_inv (a d : G) (L : Subgroup G)
    (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a^j*d*(γ:G) = x}) :
    Dense {x : G | ∃ (j : ℤ) (γ : L), (a⁻¹)^j*d*(γ:G) = x} := by
  apply hd.mono
  rintro _ ⟨j, γ, rfl⟩
  exact ⟨-j, γ, by rw [inv_zpow', neg_neg]⟩

omit [IsTopologicalGroup G] [SecondCountableTopology G] in
private theorem nilrotationQuotient_koopmanRep_eq {L : Subgroup G}
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ) :
    (nilrotationQuotientSystem L a μ hμ).koopmanRep =
      (inverseActionKoopmanRep μ hμ).comp (integerPowersHom a⁻¹) := by
  apply MonoidHom.ext
  intro g
  apply LinearIsometryEquiv.ext
  intro f
  change _ = inverseActionKoopmanRep μ hμ ((a⁻¹)^g.toAdd) f
  rw [inv_zpow']
  exact (inverseActionKoopmanRep_zpow_neg_apply
    (nilrotationQuotientSystem L a μ hμ) a hμ (fun _ _ ↦ rfl) g.toAdd f).symm

/-- The spectral conclusions carried through the closed lower-central tower. -/
structure NilrotationSpectralFacts {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) : Prop where
  haarAC : HasHaarAbsolutelyContinuousComplement U
  weakRange : ∀ p : Ultrafilter (Multiplicative ℤ), p ∈ freeUltrafilters (Multiplicative ℤ) →
    (ultrafilterOperator U p).range = purePointPart U

/-- The additional nontrivial connected stage supplies countably many mutually
orthogonal cyclic regular representations. -/
def HasCountableHaarOrbits {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∃ x : ℕ → H, (∀ j, dualVectorSpectralMeasure U (x j) = integerDualHaar) ∧
    ∀ ⦃j k : ℕ⦄, j ≠ k → ∀ g h : Multiplicative ℤ, ⟪U g (x j), U h (x k)⟫_ℂ = 0

set_option maxHeartbeats 1000000 in
/-- The abelian stage is pure point. A higher stage adds absolutely continuous
spectrum, with infinite multiplicity when its vertical action is nontrivial. -/
theorem nilrotationQuotient_vertical_spectralFacts (i : ℕ) (L : Subgroup G)
    [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (hC : ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G)⁆ ≤ L)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a^j*d*(γ:G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hBase : 0 < i → let C := (⊤ : Subgroup G).lowerCentralSeries i
      let h := nilrotation_lattice_le_verticalClosure C L
      let ν := μ.map (Subgroup.quotientMapOfLE h)
      letI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
        (nilrotationQuotientMap_continuous h).measurable.aemeasurable).mpr inferInstance
      let V := (nilrotationQuotientSystem _ a ν (nilrotationQuotient_map_preserves h μ hμ)).koopmanRep
      NilrotationSpectralFacts V) :
    let U := (nilrotationQuotientSystem L a μ hμ).koopmanRep
    NilrotationSpectralFacts U ∧
      (i = 0 → purePointPart U = ⊤) ∧
      (0 < i → ¬(⊤ : Subgroup G).lowerCentralSeries i ≤ L → HasCountableHaarOrbits U) := by
  let C := (⊤ : Subgroup G).lowerCentralSeries i
  let H := nilrotationVerticalClosure C L
  let h := nilrotation_lattice_le_verticalClosure C L
  let q : G ⧸ L → G ⧸ H := Subgroup.quotientMapOfLE h
  let ν := μ.map q
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    (nilrotationQuotientMap_continuous h).measurable.aemeasurable).mpr inferInstance
  let : IsClosed (L : Set G) := hL
  let : IsClosed (H : Set G) := Subgroup.isClosed_topologicalClosure _
  let : SecondCountableTopology (G ⧸ L) := QuotientGroup.instSecondCountableTopology L
  let : CompactSpace (G ⧸ H) := nilrotationQuotient_compactSpace h
  let : MetricSpace (G ⧸ L) := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (G ⧸ H) := TopologicalSpace.metrizableSpaceMetric _
  let E := nilrotationQuotientSystem L a μ hμ
  let B := nilrotationQuotientSystem H a ν (nilrotationQuotient_map_preserves h μ hμ)
  let π : FactorMap E B := ⟨q, ⟨(nilrotationQuotientMap_continuous h).measurable, rfl⟩,
    fun _ ↦ funext (nilrotationQuotientMap_smul h _)⟩
  let : (L.subgroupOf H).Normal := nilrotation_verticalLattice_normal_of_commutator_le C L hC hL
  let K := NilrotationVerticalGroup C L
  let : IsClosed ((L.subgroupOf H : Subgroup H) : Set H) := hL.preimage continuous_subtype_val
  let : CompactSpace K := nilrotation_verticalGroup_compactSpace C L
  let : T2Space K := QuotientGroup.instT2Space
  let : SecondCountableTopology H := Subtype.secondCountableTopology (H : Set G)
  let : SecondCountableTopology K := QuotientGroup.instSecondCountableTopology _
  let : CommGroup K := nilrotationVerticalCommGroup C L hC
  let : IsTopologicalGroup K := by dsimp [K]; infer_instance
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric _
  let : MulAction K (G ⧸ L) := nilrotationVerticalMulAction C L
  let : ContinuousSMul K (G ⧸ L) := ⟨nilrotation_continuous_verticalTranslate C L⟩
  let : MeasureTheory.IsSeparable μ := MeasureTheory.isSeparable_of_sigmaFinite μ
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let : SMulCommClass G K (G ⧸ L) := ⟨fun g k x ↦ (nilrotation_verticalTranslate_smul C L g k x).symm⟩
  let allPoints : PositiveCompacts K := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let m : Measure K := haarMeasure allPoints
  let : IsProbabilityMeasure m := ⟨haarMeasure_self (K₀ := allPoints)⟩
  let : IsMulRightInvariant m := isMulRightInvariant_of_haar_probability m
  let hK := nilrotationVerticalAction_measurePreserving C L hC μ hμ
  let R := inverseActionKoopmanRep μ hK
  let ρ := inverseActionKoopmanRep μ hμ
  let u : C →* K := nilrotation_verticalImage C L
  let ι (c : C) := (u c)⁻¹
  have hι (c : C) : R (ι c) = ρ (c : G) := by
    apply LinearIsometryEquiv.ext
    intro f
    exact (nilrotation_leftKoopman_central_eq_vertical C L hC μ hμ hK c f).symm
  have hR (f : Lp ℂ 2 μ) : Continuous fun k ↦ R k f :=
    continuous_inverseActionKoopmanRep μ hK f
  have hSpan := purePointPart_eq_top_of_compactAbelian m R hR
  change NilrotationSpectralFacts E.koopmanRep ∧ (i = 0 → purePointPart E.koopmanRep = ⊤) ∧
    (0 < i → ¬C ≤ L → HasCountableHaarOrbits E.koopmanRep)
  have hTime : E.koopmanRep = ρ.comp (integerPowersHom a⁻¹) :=
    nilrotationQuotient_koopmanRep_eq a μ hμ
  rcases i with _ | n
  · have hCtop : C = ⊤ := rfl
    let c : C := ⟨a⁻¹, hCtop.symm ▸ Subgroup.mem_top _⟩
    have hPowers : E.koopmanRep = R.comp (integerPowersHom (ι c)) := by
      rw [hTime]
      apply MonoidHom.ext
      intro g
      apply LinearIsometryEquiv.ext
      intro f
      change ρ ((a⁻¹)^g.toAdd) f = R ((ι c)^g.toAdd) f
      rw [map_zpow ρ, map_zpow R, hι]
    have hPure : purePointPart E.koopmanRep = ⊤ := by
      apply top_unique
      suffices hle : purePointPart R ≤ purePointPart E.koopmanRep from hSpan ▸ hle
      apply purePointPart_le_of_eigenvectors_le _ _ (isClosed_purePointPart _)
      rintro f ⟨χ,hχ⟩
      apply eigenvectors_le_purePointPart _
      exact ⟨χ.comp (integerPowersHom (ι c)), fun g ↦ hPowers.symm ▸ hχ _⟩
    refine ⟨⟨?_, ?_⟩, fun _ ↦ hPure, fun hi ↦ (Nat.not_lt_zero _ hi).elim⟩
    · rw [HasHaarAbsolutelyContinuousComplement, hPure, Submodule.top_orthogonal_eq_bot]
      exact bot_le
    · intro p _
      rw [hPure]
      apply top_unique
      intro x _
      exact ⟨(ultrafilterOperator E.koopmanRep p).adjoint x,
        (ultrafilterOperator_purePoint_inverse E.koopmanRep p (hPure.symm ▸ Submodule.mem_top)).1⟩
  · obtain ⟨s, hs, hsπ⟩ := exists_measurable_section_of_continuous_compact π.toFun
      (nilrotationQuotientMap_continuous h) (nilrotationQuotientMap_surjective h)
    obtain ⟨c, e, F, hFe, heπ, heK⟩ := principalExtension_exists_skewCoordinates E B π m s hs hsπ
      (nilrotationVerticalProjection_translate C L) (nilrotationVerticalTranslate_free C L)
      (fun _ _ ↦ nilrotationVerticalProjection_eq_iff C L |>.mp) hK
      (fun _ _ _ ↦ (nilrotation_verticalTranslate_smul C L _ _ _).symm)
    have he : MeasurePreserving e (ν.prod m) μ := hFe ▸ F.preserves
    have hFixed (x : Lp ℂ 2 μ) (hx : ∀ k, R k x = x) : ∃ v, π.pullback v = x :=
      (principalExtension_fixed_iff_pullback π m e he heπ heK hK x).mp hx
    have hComm (k : K) (g : G) : Commute (R k) (ρ g) :=
      (commute_inverseActionKoopmanRep μ hμ hK g k).symm
    have hModes (χ : K →* Circle) (x : Lp ℂ 2 μ) (hχ : χ ≠ 1)
        (hx : ∀ k, R k x = (χ k : ℂ) • x) (hx0 : x ≠ 0) :
        ∀ s : UnitAddCircle, ∃ (b : G) (c : C),
          ⁅a⁻¹,b⁆ = (c : G) ∧ χ (ι c) = AddCircle.toCircle s := by
      have hcχ := continuous_character_of_unitaryEigenvector R hx0 (hR x) χ hx
      let ψ : C →* Circle := (χ.comp u)⁻¹
      have hψ : Continuous ψ := (hcχ.comp (nilrotation_continuous_verticalImage C L)).inv
      have hχ' : ∃ k, χ k ≠ 1 := by
        by_contra! heq
        exact hχ (MonoidHom.ext heq)
      obtain ⟨c₀, hc₀⟩ := exists_nontrivial_character_of_denseRange u
        (nilrotation_denseRange_verticalImage C L) χ hcχ hχ'
      have hψ' : ∃ c : C, ψ c ≠ 1 := ⟨c₀, fun heq ↦ hc₀ (inv_eq_one.mp heq)⟩
      have hψL (c : C) (hc : (c : G) ∈ L) : ψ c = 1 := by
        have huc : u c = 1 := (QuotientGroup.eq_one_iff _).mpr hc
        change (χ (u c))⁻¹ = 1
        rw [huc, map_one, inv_one]
      have hPhase := nilrotation_bracket_full_time_phases n L hC a⁻¹ d
        (nilrotation_dense_lifted_cosets_inv a d L hd) (by simpa only [Subgroup.zpowers_inv])
        ψ hψ hψL hψ'
      intro s
      obtain ⟨b,c,hb,hc⟩ := hPhase s
      exact ⟨b,c,hb,(map_inv χ (u c)).trans hc⟩
    have hSpectral (χ : K →* Circle) (x : Lp ℂ 2 μ) (hχ : χ ≠ 1)
        (hx : ∀ k, R k x = (χ k : ℂ) • x) (hx0 : x ≠ 0) :=
      verticalPhase_dualVectorSpectralMeasure ρ R a⁻¹ hComm ι hι χ (hModes χ x hχ hx hx0) x hx hx0
    have hB := hBase (Nat.succ_pos _)
    refine ⟨⟨?_, ?_⟩, fun hn ↦ (Nat.succ_ne_zero _ hn).elim, ?_⟩
    · apply hasHaarAbsolutelyContinuousComplement_of_vertical B.koopmanRep E.koopmanRep R
        π.pullback π.intertwines_pullback hSpan hFixed hB.haarAC
      intro χ x hχ hx
      by_cases hx0 : x = 0
      · subst x
        exact (spectralAbsoluteContinuousSubmodule E.koopmanRep integerDualHaar).zero_mem
      rw [hTime]
      exact (hSpectral χ x hχ hx hx0).2 x hx
    · intro p hp
      apply ultrafilterOperator_range_eq_purePointPart_of_vertical B.koopmanRep E.koopmanRep R
        π.pullback.toContinuousLinearMap π.intertwines_pullback hSpan hFixed p (hB.weakRange p hp)
      intro χ x hχ hx
      by_cases hx0 : x = 0
      · simp [hx0]
      rw [hTime]
      exact ultrafilterOperator_zero_of_verticalPhase ρ R a⁻¹ hComm ι hι χ
        (hModes χ x hχ hx hx0) p hp x hx
    · intro _ hnontriv
      have hNontriv : Nontrivial K := by
        obtain ⟨c, hc, hnc⟩ : ∃ c, c ∈ C ∧ c ∉ L := by
          by_contra! heq
          exact hnontriv heq
        let z : H := ⟨c, nilrotation_centre_le_verticalClosure C L hc⟩
        refine ⟨⟨u ⟨c,hc⟩, 1, fun heq ↦ ?_⟩⟩
        change (QuotientGroup.mk z : K) = 1 at heq
        exact hnc ((QuotientGroup.eq_one_iff (N := L.subgroupOf H) z).mp heq)
      let : Nontrivial K := hNontriv
      let : ConnectedSpace C := connectedSpace_lowerCentralSeries_succ_of_component_sup_zpowers a hgen n
      let : PreconnectedSpace K := (nilrotation_denseRange_verticalImage C L).preconnectedSpace
        (nilrotation_continuous_verticalImage C L)
      let : ConnectedSpace K := { toNonempty := ⟨1⟩ }
      obtain ⟨η, hη, hη'⟩ := exists_nontrivial_continuousCharacter_of_compactAbelian m
      obtain ⟨χ, hχ, hX⟩ := exists_principalExtension_infinite_vertical_modes μ e heK hK η hη hη'
      have hY (j : ℕ) : ∃ y : Lp ℂ 2 μ, (∀ k, R k y = (χ j k : ℂ) • y) ∧
          dualVectorSpectralMeasure E.koopmanRep y = integerDualHaar := by
        obtain ⟨_, hne, x, hx0, hx⟩ := hX j
        have neOne : χ j ≠ 1 := fun heq ↦ by simp [heq] at hne
        rw [hTime]
        exact (hSpectral (χ j) x neOne hx hx0).1
      choose y hYchar hYhaar using hY
      refine ⟨y, hYhaar, ?_⟩
      intro j k hjk g h'
      have hYtime (i : ℕ) (t : Multiplicative ℤ) (k₀ : K) :
          R k₀ (E.koopmanRep t (y i)) = (χ i k₀ : ℂ) • E.koopmanRep t (y i) := by
        rw [hTime]
        change (R k₀ * ρ ((a⁻¹)^t.toAdd)) (y i) = _
        rw [(hComm k₀ _).eq]
        change ρ ((a⁻¹)^t.toAdd) (R k₀ (y i)) = _
        rw [hYchar, map_smul]
        rfl
      exact unitaryCharacter_inner_eq_zero_of_ne R (hχ.ne hjk) (hYtime j g) (hYtime k h')

end Mixing
