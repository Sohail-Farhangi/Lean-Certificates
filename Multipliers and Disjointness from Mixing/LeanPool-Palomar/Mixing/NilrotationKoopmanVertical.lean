/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationKoopmanAction
public import Mixing.NilrotationGeometryVerticalGroup
public import Mixing.CompactRepresentationEigenvectors

/-! # Characters of the compact vertical Koopman action -/

@[expose] public section
noncomputable section

namespace Mixing

open MeasureTheory MeasureTheory.Measure
open scoped commutatorElement

/-- Equal inverse actions induce equal Koopman operators. -/
theorem inverseActionKoopmanRep_apply_eq_of_inverse_smul_eq
    {G K X : Type*} [Group G] [Group K] [MulAction G X] [MulAction K X]
    [MeasurableSpace X] (μ : Measure X)
    (hG : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (hK : ∀ k : K, MeasurePreserving (fun x : X ↦ k • x) μ μ)
    (g : G) (k : K) (hAct : ∀ x : X, g⁻¹ • x = k⁻¹ • x) (f : Lp ℂ 2 μ) :
    inverseActionKoopmanRep μ hG g f = inverseActionKoopmanRep μ hK k f := by
  apply Lp.ext
  filter_upwards [ae_inverseActionKoopmanRep_apply μ hG g f,
    ae_inverseActionKoopmanRep_apply μ hK k f] with x hg hk
  exact hg.trans ((congrArg (fun y : X ↦ f y) (hAct x)).trans hk.symm)

/-- On the dense image of the central group, vertical Koopman operators match
the left-group operators after inverting the vertical parameter. -/
theorem nilrotation_leftKoopman_central_eq_vertical
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (C L : Subgroup G) [(L.subgroupOf (nilrotationVerticalClosure C L)).Normal]
    [MeasurableSpace (G ⧸ L)] (hC : ⁅C, (⊤ : Subgroup G)⁆ ≤ L) (μ : Measure (G ⧸ L))
    (hG : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (hK : ∀ k : NilrotationVerticalGroup C L,
      MeasurePreserving (nilrotationVerticalTranslate C L k) μ μ)
    (c : C) :
    letI := nilrotationVerticalMulAction C L
    ∀ f : Lp ℂ 2 μ, inverseActionKoopmanRep μ hG (c : G) f =
      inverseActionKoopmanRep μ hK ((nilrotation_verticalImage C L c)⁻¹) f := by
  let := nilrotationVerticalMulAction C L
  intro f
  apply inverseActionKoopmanRep_apply_eq_of_inverse_smul_eq μ hG hK
  intro x
  rw [inv_inv]
  exact (nilrotation_verticalImage_translate_of_commutator_le C L hC c x).symm

/-- An element belonging to all conjugates of the stabilizer has trivial
Koopman operator on the homogeneous quotient. -/
theorem nilrotation_leftKoopman_eq_one_of_conjugates_mem
    {G : Type*} [Group G] (L : Subgroup G) [MeasurableSpace (G ⧸ L)] (μ : Measure (G ⧸ L))
    (hG : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ)
    (g : G) (h : ∀ x : G, x⁻¹ * g * x ∈ L) :
    inverseActionKoopmanRep μ hG g = 1 := by
  apply LinearIsometryEquiv.ext
  intro f
  have hAct (z : G ⧸ L) : g⁻¹ • z = z := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    apply QuotientGroup.eq.mpr
    change (g⁻¹ * x)⁻¹ * x ∈ L
    simpa only [mul_inv_rev, inv_inv] using h x
  change inverseActionKoopmanRep μ hG g f = f
  apply Lp.ext
  filter_upwards [ae_inverseActionKoopmanRep_apply μ hG g f] with x hx
  exact hx.trans (congrArg (fun y : G ⧸ L ↦ f y) (hAct x))

/-- The left representation on the homogeneous quotient factors through every
normal subgroup contained in the stabilizer. -/
theorem nilrotation_le_ker_leftKoopman
    {G : Type*} [Group G] (N L : Subgroup G) [N.Normal] (hN : N ≤ L)
    [MeasurableSpace (G ⧸ L)] (μ : Measure (G ⧸ L))
    (hG : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) μ μ) :
    N ≤ (inverseActionKoopmanRep μ hG).ker := by
  intro g hg
  show inverseActionKoopmanRep μ hG g = 1
  apply nilrotation_leftKoopman_eq_one_of_conjugates_mem
  intro x
  exact hN (Subgroup.Normal.conj_mem' (inferInstance : N.Normal) g hg x)

/-- A nontrivial continuous character stays nontrivial on any dense image. -/
theorem exists_nontrivial_character_of_denseRange
    {C K : Type*} [Group C] [Group K] [TopologicalSpace K]
    (i : C →* K) (hi : DenseRange i) (χ : K →* Circle) (hχ : Continuous χ)
    (hne : ∃ k, χ k ≠ 1) : ∃ c, (χ.comp i) c ≠ 1 := by
  by_contra! h
  obtain ⟨k, hk⟩ := hne
  exact hk (hi.induction_on k (isClosed_eq hχ continuous_const) h)

/-- A closed subspace of the Hilbert space of a compact abelian action is the
whole space if it contains the fixed subspace and every nontrivial character mode. -/
theorem eq_top_of_vertical_character_modes
    {K H : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ v, Continuous fun k ↦ ρ k v)
    (W : Submodule ℂ H) (hW : IsClosed (W : Set H))
    (hFixed : ∀ v : H, (∀ k, ρ k v = v) → v ∈ W)
    (hModes : ∀ (χ : K →* Circle), Continuous χ → (∃ k, χ k ≠ 1) →
      ∀ v : H, (∀ k, ρ k v = (χ k : ℂ) • v) → v ∈ W) :
    W = ⊤ := by
  apply top_unique
  rw [← purePointPart_eq_top_of_compactAbelian m ρ hρ]
  apply Submodule.topologicalClosure_minimal _ _ hW
  apply Submodule.span_le.mpr
  rintro v ⟨χ, hχ⟩
  by_cases hv : v = 0
  · subst v
    exact W.zero_mem
  by_cases hTrivial : ∀ k, χ k = 1
  · exact hFixed v fun k ↦ by simpa [hTrivial k] using hχ k
  exact hModes χ (continuous_character_of_unitaryEigenvector ρ hv (hρ v) χ hχ)
    (not_forall.mp hTrivial) v hχ

end Mixing
