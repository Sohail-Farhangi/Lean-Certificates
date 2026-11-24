/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationGeometryReduction
public import Mixing.NilrotationGeometryTower
public import Mixing.NilrotationSpectralGluing

/-! # Spectral transport from the open component subgroup -/

@[expose] public section
noncomputable section

namespace Mixing

open Filter Function MeasureTheory Set TopologicalSpace
open scoped Nilrotation

section Transport

variable {G H K : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}

private theorem intertwines_isometryEquiv_symm {e : H ≃ₗᵢ[ℂ] K}
    (he : Intertwines U V e.toLinearIsometry.toContinuousLinearMap) :
    Intertwines V U e.symm.toLinearIsometry.toContinuousLinearMap := by
  intro g x
  apply e.injective
  change e (e.symm (V g x)) = e (U g (e.symm x))
  have h := he g (e.symm x)
  change e (U g (e.symm x)) = V g (e (e.symm x)) at h
  rw [h, e.apply_symm_apply, e.apply_symm_apply]

private theorem purePointPart_map_intertwining_equiv (e : H ≃ₗᵢ[ℂ] K)
    (he : Intertwines U V e.toLinearIsometry.toContinuousLinearMap) :
    (purePointPart U).map e.toLinearEquiv.toLinearMap = purePointPart V := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact he.mapsTo_purePointPart hx
  · intro x hx
    exact ⟨e.symm x, (intertwines_isometryEquiv_symm he).mapsTo_purePointPart hx, e.apply_symm_apply x⟩

/-- An equivariant Hilbert isometry equivalence preserves the pure point part. -/
theorem purePointPart_eq_top_of_intertwining_equiv (e : H ≃ₗᵢ[ℂ] K)
    (he : Intertwines U V e.toLinearIsometry.toContinuousLinearMap)
    (h : purePointPart U = ⊤) : purePointPart V = ⊤ := by
  rw [← purePointPart_map_intertwining_equiv e he, h, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- An equivariant Hilbert isometry equivalence transports a bilateral-shift
basis of the Lebesgue complement. -/
theorem HasLebesgueComplement.of_intertwining_equiv {I : Type*}
    (e : H ≃ₗᵢ[ℂ] K) (he : Intertwines U V e.toLinearIsometry.toContinuousLinearMap)
    (h : HasLebesgueComplement U I) : HasLebesgueComplement V I := by
  obtain ⟨b, hb⟩ := h
  let A := (purePointPart U)ᗮ
  let B := (purePointPart V)ᗮ
  have hAB : A.map e.toLinearEquiv.toLinearMap = B := by
    change (purePointPart U)ᗮ.map e.toLinearEquiv.toLinearMap = (purePointPart V)ᗮ
    rw [Submodule.map_orthogonal_equiv, purePointPart_map_intertwining_equiv e he]
  let e' : A ≃ₗᵢ[ℂ] B := (e.submoduleMap A).trans (LinearIsometryEquiv.ofEq _ _ hAB)
  let b' : HilbertBasis (I × G) ℂ B := HilbertBasis.ofRepr (e'.symm.trans b.repr)
  refine ⟨b', fun g i n ↦ ?_⟩
  have hval (p : I × G) : (b' p : K) = e (b p : H) := by
    change (e' (b p) : K) = _
    exact LinearIsometryEquiv.coe_ofEq_apply hAB _
  rw [hval, hval, ← show e (U g (b (i, n) : H)) = V g (e (b (i, n) : H)) from he g _,
    hb g i n]

/-- Equivariant Hilbert isometry equivalences transport the free-ultrafilter
range equality. -/
theorem ultrafilterOperator_range_eq_purePointPart_of_intertwining_equiv
    (e : H ≃ₗᵢ[ℂ] K) (he : Intertwines U V e.toLinearIsometry.toContinuousLinearMap)
    (p : Ultrafilter G) (h : (ultrafilterOperator U p).range = purePointPart U) :
    (ultrafilterOperator V p).range = purePointPart V := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    let y := e.symm x
    have hy : ultrafilterOperator U p y ∈ purePointPart U := h ▸ ⟨y, rfl⟩
    have hxy : e (ultrafilterOperator U p y) = ultrafilterOperator V p x := by
      have he' := he.ultrafilter p y
      change e (ultrafilterOperator U p y) = ultrafilterOperator V p (e y) at he'
      rwa [e.apply_symm_apply] at he'
    change ultrafilterOperator V p x ∈ purePointPart V
    rw [← hxy]
    exact he.mapsTo_purePointPart hy
  · intro x hx
    have hy := (intertwines_isometryEquiv_symm he).mapsTo_purePointPart hx
    rw [← h] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨e z, ?_⟩
    change ultrafilterOperator U p z = e.symm x at hz
    change ultrafilterOperator V p (e z) = x
    have he' := he.ultrafilter p z
    change e (ultrafilterOperator U p z) = ultrafilterOperator V p (e z) at he'
    rw [← he', hz]
    exact e.apply_symm_apply x

end Transport

section Reduction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyConnectedSpace G]

omit [LocallyConnectedSpace G] in
theorem nilrotationComponentSubgroup_lowerCentralSeries_eq_bot (a : G) (n : ℕ)
    (hn : (⊤ : Subgroup G).lowerCentralSeries n = ⊥) :
    (⊤ : Subgroup (nilrotationComponentSubgroup a)).lowerCentralSeries n = ⊥ := by
  let H := nilrotationComponentSubgroup a
  change (⊤ : Subgroup H).lowerCentralSeries n = ⊥
  rw [← Subgroup.map_subtype_inj, Subgroup.map_bot, Subgroup.top_subtype_lowerCentralSeries,
    eq_bot_iff, ← hn]
  exact H.lowerCentralSeries_mono n le_top

/-- The reduced acting subgroup retains a dense lifted time orbit. -/
theorem nilrotationComponentSubgroup_dense_lifted_cosets
    (L : Subgroup G) (a d : G)
    (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a ^ j * d * (γ : G) = x}) :
    let H := nilrotationComponentSubgroup a
    let t : H := ⟨a, nilrotationComponentSubgroup_contains_time a⟩
    let D := MulAction.stabilizer H (QuotientGroup.mk d : G ⧸ L)
    Dense {x : H | ∃ (j : ℤ) (γ : D), t ^ j * (γ : H) = x} := by
  let H := nilrotationComponentSubgroup a
  let t : H := ⟨a, nilrotationComponentSubgroup_contains_time a⟩
  let D := MulAction.stabilizer H (QuotientGroup.mk d : G ⧸ L)
  change Dense {x : H | ∃ (j : ℤ) (γ : D), t ^ j * (γ : H) = x}
  rw [dense_iff_inter_open]
  intro U hU hUn
  let R : H → G := fun h ↦ (h : G) * d
  have hR : IsOpenMap R := (Homeomorph.mulRight d).isOpenMap.comp
    (nilrotationComponentSubgroup_open a).isOpenEmbedding_subtypeVal.isOpenMap
  obtain ⟨_, ⟨j, γ, rfl⟩, u, hu, heu⟩ := hd.exists_mem_open (hR U hU) (hUn.image R)
  have hcos : (QuotientGroup.mk (a ^ j * d) : G ⧸ L) = QuotientGroup.mk ((u : G) * d) := by
    apply QuotientGroup.eq.mpr
    change (u : G) * d = a ^ j * d * (γ : G) at heu
    rw [heu, ← mul_assoc, inv_mul_cancel, one_mul]
    exact γ.2
  let δ : H := (t ^ j)⁻¹ * u
  have hδ : δ ∈ D := by
    change ((t ^ j)⁻¹ * u : H) • (QuotientGroup.mk d : G ⧸ L) = QuotientGroup.mk d
    rw [mul_smul]
    have he : (t ^ j) • (QuotientGroup.mk d : G ⧸ L) = u • (QuotientGroup.mk d : G ⧸ L) := by
      change (QuotientGroup.mk ((↑(t ^ j) : G) * d) : G ⧸ L) =
        QuotientGroup.mk ((u : G) * d)
      rwa [Subgroup.coe_zpow]
    rw [← he, inv_smul_smul]
  exact ⟨u, hu, ⟨j, ⟨δ, hδ⟩, by change t ^ j * ((t ^ j)⁻¹ * u) = u; group⟩⟩

private theorem nilrotation_lp_pullback_congr {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    {f g : X → Y} (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g μ ν)
    (h : f = g) (w : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving f hf w = Lp.compMeasurePreserving g hg w := by
  subst g
  rfl

/-- The spectral model of an ergodic homogeneous rotation can be taken on the
open subgroup generated by time and the identity component. -/
theorem nilrotationQuotient_exists_component_model [SecondCountableTopology G]
    (L : Subgroup G) [CompactSpace (G ⧸ L)] (hL : IsClosed (L : Set G))
    (a : G) (μ : Measure (G ⧸ L)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hErg : (nilrotationQuotientSystem L a μ hμ).IsErgodic) :
    let H := nilrotationComponentSubgroup a
    let t : H := ⟨a, nilrotationComponentSubgroup_contains_time a⟩
    ∃ (D : Subgroup H) (_ : IsClosed (D : Set H)) (_ : CompactSpace (H ⧸ D))
      (_ : Dense {x : H | ∃ (j : ℤ) (γ : D), t ^ j * (γ : H) = x})
      (ν : Measure (H ⧸ D)) (hProb : IsProbabilityMeasure ν)
      (hν : ∀ g : H, MeasurePreserving (fun x : H ⧸ D ↦ g • x) ν ν),
      letI : IsProbabilityMeasure ν := hProb
      let B := nilrotationQuotientSystem D t ν hν
      let E := nilrotationQuotientSystem L a μ hμ
      ∃ e : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
        Intertwines B.koopmanRep E.koopmanRep e.toLinearIsometry.toContinuousLinearMap := by
  let E := nilrotationQuotientSystem L a μ hμ
  obtain ⟨d, hd⟩ := nilrotation_exists_dense_lifted_cosets L a E hErg
    (nilrotationQuotientSystem_act L a μ hμ) hμ
  let H := nilrotationComponentSubgroup a
  let t : H := ⟨a, nilrotationComponentSubgroup_contains_time a⟩
  let x : G ⧸ L := QuotientGroup.mk d
  let D := MulAction.stabilizer H x
  let : IsClosed (L : Set G) := hL
  have hD : IsClosed (D : Set H) := by
    change IsClosed {g : H | (g : G) • x = x}
    exact isClosed_eq (continuous_smul.comp (continuous_subtype_val.prodMk continuous_const))
      continuous_const
  let e₀ := nilrotationComponentSubgroup_homeomorph L a d hd
  let e : H ⧸ D ≃ᵐ G ⧸ L := e₀.toMeasurableEquiv
  let ν := μ.map e.symm
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    e.symm.measurable.aemeasurable).mpr inferInstance
  have hE (g : H) (y : H ⧸ D) : e (g • y) = (g : G) • e y :=
    nilrotationComponentSubgroup_homeomorph_smul L a d hd g y
  have hν (g : H) : MeasurePreserving (fun y : H ⧸ D ↦ g • y) ν ν := by
    have hEq : (fun y : H ⧸ D ↦ g • y) ∘ e.symm =
        e.symm ∘ (fun y : G ⧸ L ↦ (g : G) • y) := by
      funext y
      apply e.injective
      change e (g • e.symm y) = e (e.symm ((g : G) • y))
      rw [hE, e.apply_symm_apply, e.apply_symm_apply]
    have hm : Measurable (fun y : H ⧸ D ↦ g • y) := (continuous_const_smul g).measurable
    refine ⟨hm, ?_⟩
    change (μ.map e.symm).map _ = μ.map e.symm
    rw [Measure.map_map hm e.symm.measurable, hEq,
      ← Measure.map_map e.symm.measurable (hμ g).measurable, (hμ g).map_eq]
  let B := nilrotationQuotientSystem D t ν hν
  have hmp : MeasurePreserving e.symm μ ν := ⟨e.symm.measurable, rfl⟩
  have hmpInv : MeasurePreserving e ν μ := by simpa only [MeasurableEquiv.symm_symm] using hmp.symm e.symm
  let F : FactorMap E B := ⟨e.symm, hmp, by
    intro g
    funext z
    apply e.injective
    change e (e.symm (a ^ g.toAdd • z)) = e (t ^ g.toAdd • e.symm z)
    rw [hE, e.apply_symm_apply, e.apply_symm_apply, Subgroup.coe_zpow]⟩
  have hsurj : Surjective F.pullback := by
    intro w
    change Lp ℂ 2 μ at w
    use Lp.compMeasurePreserving e hmpInv w
    change Lp.compMeasurePreserving e.symm hmp (Lp.compMeasurePreserving e hmpInv w) = w
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hEq : (e : H ⧸ D → G ⧸ L) ∘ e.symm = id := funext e.apply_symm_apply
    exact (nilrotation_lp_pullback_congr _ (MeasurePreserving.id μ) hEq w).trans
      (Lp.compMeasurePreserving_id_apply w)
  exact ⟨D, hD, e₀.symm.compactSpace, nilrotationComponentSubgroup_dense_lifted_cosets L a d hd,
    ν, inferInstance, hν, LinearIsometryEquiv.ofSurjective F.pullback hsurj, F.intertwines_pullback⟩

end Reduction

end Mixing
