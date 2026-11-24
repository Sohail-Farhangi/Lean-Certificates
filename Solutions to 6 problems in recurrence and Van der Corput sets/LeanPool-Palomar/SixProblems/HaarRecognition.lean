/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CompactRepresentationDensity
public import Mixing.NilrotationKoopmanAction
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Metrizable.Urysohn

/-! # Proposition 4.5: identifying Haar measure from matrix coefficients -/

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Mixing
open scoped InnerProductSpace

universe u

variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] in
/-- An irreducible unitary representation has nonzero underlying space and has
only the zero and full invariant subspaces. -/
def UnitaryIrreducible (ρ : K →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  IrreducibleInvariantSubmodule ρ ⊤

omit [Group K] [IsTopologicalGroup K] in
private theorem integrable_of_continuous_on_compact {E : Type*} [NormedAddCommGroup E]
    (ν : Measure K) [IsFiniteMeasure ν] {g : K → E} (hg : Continuous g) : Integrable g ν :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

section HaarMean

variable [CompleteSpace H]

/-- Haar averaging in a nontrivial irreducible unitary representation is zero. -/
theorem integral_orbit_haar_eq_zero
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (hIrred : UnitaryIrreducible ρ) (hNontriv : ∃ k, ρ k ≠ 1) (y : H) :
    (∫ k, ρ k y ∂m) = 0 := by
  let V : Submodule ℂ H :=
    { carrier := {x | ∀ a : K, ρ a x = x}
      zero_mem' := by simp
      add_mem' := by
        intro x z hx hz a
        rw [map_add, hx a, hz a]
      smul_mem' := by
        intro c x hx a
        rw [map_smul, hx a] }
  have hVI : IsInvariantSubmodule ρ V := fun a x hx ↦ (hx a).symm ▸ hx
  have hV : V = ⊥ := by
    rcases hIrred.2.2 V le_top hVI with hz | ht
    · exact hz
    · obtain ⟨a, ha⟩ := hNontriv
      exfalso
      apply ha
      apply LinearIsometryEquiv.ext
      intro x
      have hx : x ∈ V := ht.symm ▸ Submodule.mem_top
      exact hx a
  apply (Submodule.mem_bot ℂ).mp
  rw [← hV]
  intro a
  have hi := integrable_of_continuous_on_compact m (hρ y)
  calc
    ρ a (∫ k, ρ k y ∂m) = ∫ k, ρ a (ρ k y) ∂m :=
      ((ρ a).toLinearIsometry.toContinuousLinearMap.integral_comp_comm hi).symm
    _ = ∫ k, ρ (a * k) y ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k ↦ by
        change ρ a (ρ k y) = ρ (a * k) y
        rw [map_mul]
        rfl
    _ = ∫ k, ρ k y ∂m := integral_mul_left_eq_self (fun k ↦ ρ k y) a

/-- The matrix coefficients of a nontrivial irreducible unitary representation
have zero Haar integral. -/
theorem integral_coefficient_haar_eq_zero
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (hIrred : UnitaryIrreducible ρ) (hNontriv : ∃ k, ρ k ≠ 1) (x y : H) :
    (∫ k, ⟪x, ρ k y⟫_ℂ ∂m) = 0 := by
  change (∫ k, innerSL ℂ x (ρ k y) ∂m) = 0
  rw [(innerSL ℂ x).integral_comp_comm (integrable_of_continuous_on_compact m (hρ y)),
    integral_orbit_haar_eq_zero m ρ hρ hIrred hNontriv y, map_zero]

end HaarMean

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] in
private theorem restrict_irreducible (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (W : Submodule ℂ H)
    (hW : IrreducibleInvariantSubmodule ρ W) :
    UnitaryIrreducible (unitarySubmoduleAction ρ W hW.2.1) := by
  let σ := unitarySubmoduleAction ρ W hW.2.1
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1
  refine ⟨top_ne_bot, fun _ _ _ ↦ Submodule.mem_top, fun L _ hL ↦ ?_⟩
  have hinj := Submodule.map_injective_of_injective W.subtype_injective
  have hLW : L.map W.subtype ≤ W := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hLI : IsInvariantSubmodule ρ (L.map W.subtype) := by
    intro a _ hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    exact ⟨σ a x, hL a x hx, rfl⟩
  rcases hW.2.2 _ hLW hLI with hz | ht
  · exact Or.inl (hinj (hz.trans (Submodule.map_bot _).symm))
  · right
    apply hinj
    simpa only [Submodule.map_top, Submodule.range_subtype] using ht

omit [IsTopologicalGroup K] in
/-- Integration of an orbit of a strongly continuous unitary representation
defines a bounded linear operator. -/
def integratedUnitary (ν : Measure K) [IsProbabilityMeasure ν]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ∫ k, ρ k x ∂ν
      map_add' := fun x y ↦ by
        simp only [map_add]
        exact integral_add (integrable_of_continuous_on_compact ν (hρ x))
          (integrable_of_continuous_on_compact ν (hρ y))
      map_smul' := fun c x ↦ by simp only [map_smul, integral_smul, RingHom.id_apply] }
    1 fun x ↦ by
    change ‖∫ k, ρ k x ∂ν‖ ≤ 1 * ‖x‖
    simpa only [LinearIsometryEquiv.norm_map, integral_const, probReal_univ, one_smul, one_mul]
      using norm_integral_le_integral_norm (μ := ν) (fun k ↦ ρ k x)

omit [IsTopologicalGroup K] in
theorem integratedUnitary_apply (ν : Measure K) [IsProbabilityMeasure ν]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) (x : H) :
    integratedUnitary ν ρ hρ x = ∫ k, ρ k x ∂ν := rfl

/-- Vanishing of the nontrivial irreducible matrix coefficients of a measure. -/
def VanishesOnNontrivialIrreducibleCoefficients (ν : Measure K) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : K →* (E ≃ₗᵢ[ℂ] E)), (∀ x, Continuous fun k ↦ ρ k x) →
    UnitaryIrreducible ρ → (∃ k, ρ k ≠ 1) →
    ∀ x y, (∫ k, ⟪x, ρ k y⟫_ℂ ∂ν) = 0

private theorem integratedUnitary_eq_haar (m ν : Measure K)
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure] [IsProbabilityMeasure ν]
    (hν : VanishesOnNontrivialIrreducibleCoefficients ν)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (ρ : K →* (V ≃ₗᵢ[ℂ] V)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    integratedUnitary ν ρ hρ = integratedUnitary m ρ hρ := by
  let D := integratedUnitary ν ρ hρ - integratedUnitary m ρ hρ
  have hker : D.ker = ⊤ := by
    apply eq_top_of_contains_irreducibleInvariantSubmodules m ρ hρ D.ker D.isClosed_ker
    intro W hfin hW y hy
    let : FiniteDimensional ℂ W := hfin
    let : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    let σ := unitarySubmoduleAction ρ W hW.2.1
    have hσ (x : W) : Continuous fun k ↦ σ k x := (hρ x).subtype_mk _
    let z : W := ⟨y, hy⟩
    have hrestrict : ∀ (μ : Measure K) [IsProbabilityMeasure μ],
        W.subtypeL (∫ k, σ k z ∂μ) = integratedUnitary μ ρ hρ y := fun μ _ ↦
      (W.subtypeL.integral_comp_comm (integrable_of_continuous_on_compact μ (hσ z))).symm
    apply LinearMap.mem_ker.mpr
    change integratedUnitary ν ρ hρ y - integratedUnitary m ρ hρ y = 0
    apply sub_eq_zero.mpr
    rw [← hrestrict ν, ← hrestrict m]
    congr 1
    by_cases hnon : ∃ k, σ k ≠ 1
    · have hσI := restrict_irreducible ρ W hW
      rw [integral_orbit_haar_eq_zero m σ hσ hσI hnon z]
      apply ext_inner_left ℂ
      intro x
      change innerSL ℂ x (∫ k, σ k z ∂ν) = ⟪x, 0⟫_ℂ
      rw [← (innerSL ℂ x).integral_comp_comm (integrable_of_continuous_on_compact ν (hσ z)), inner_zero_right]
      exact hν W σ hσ hσI hnon x z
    · push Not at hnon
      have hz (k : K) : σ k z = z := by rw [hnon k]; rfl
      simp only [hz, integral_const, probReal_univ, one_smul]
  ext x
  have hx : x ∈ D.ker := hker.symm ▸ Submodule.mem_top
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp hx)

variable [SecondCountableTopology K] [T2Space K]

/-- **Proposition 4.5.** A probability on a compact metrizable group equals its
normalized Haar measure iff the indicated matrix coefficients have zero integral. -/
theorem proposition4_5 (m ν : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    [m.IsOpenPosMeasure] [IsProbabilityMeasure ν] :
    ν = m ↔ VanishesOnNontrivialIrreducibleCoefficients ν := by
  constructor
  · intro he
    subst ν
    intro E _ _ _ ρ hρ hIrred hNontriv x y
    let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
    exact integral_coefficient_haar_eq_zero m ρ hρ hIrred hNontriv x y
  · intro hν
    let hInv (k : K) : MeasurePreserving (fun x : K ↦ k • x) m m :=
      measurePreserving_mul_left m k
    let ρ := inverseActionKoopmanRep m hInv
    have hρ := continuous_inverseActionKoopmanRep m hInv
    have hA := integratedUnitary_eq_haar m ν hν ρ hρ
    have hComplex (f : C(K, ℂ)) : (∫ k, f k⁻¹ ∂ν) = ∫ k, f k⁻¹ ∂m := by
      let F (k : K) : C(K, ℂ) := ⟨fun x ↦ f (k⁻¹ * x),
        f.continuous.comp (continuous_const.mul continuous_id)⟩
      have hF : Continuous F := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact f.continuous.comp (continuous_fst.inv.mul continuous_snd)
      let J : C(K, ℂ) →L[ℂ] Lp ℂ 2 m := ContinuousMap.toLp 2 m ℂ
      have hJ (k : K) : J (F k) = ρ k (J f) := by
        apply Lp.ext
        refine (ContinuousMap.coeFn_toLp m (F k)).trans ?_
        refine Filter.EventuallyEq.trans ?_ (ae_inverseActionKoopmanRep_apply m hInv k (J f)).symm
        exact ((hInv k⁻¹).quasiMeasurePreserving.ae_eq_comp (ContinuousMap.coeFn_toLp m f)).symm
      have hIntegrals : (∫ k, F k ∂ν) = ∫ k, F k ∂m := by
        apply ContinuousMap.toLp_injective (𝕜 := ℂ) (p := 2) m
        rw [← J.integral_comp_comm (integrable_of_continuous_on_compact ν hF),
          ← J.integral_comp_comm (integrable_of_continuous_on_compact m hF)]
        simp_rw [hJ]
        exact DFunLike.congr_fun hA (J f)
      let ev := ContinuousMap.evalCLM ℂ (1 : K) (M := ℂ)
      simpa only [ev, ContinuousMap.evalCLM_apply, F, ContinuousMap.coe_mk, mul_one] using
        calc
          (∫ k, ev (F k) ∂ν) = ev (∫ k, F k ∂ν) :=
            ev.integral_comp_comm (integrable_of_continuous_on_compact ν hF)
          _ = ev (∫ k, F k ∂m) := congrArg ev hIntegrals
          _ = ∫ k, ev (F k) ∂m :=
            (ev.integral_comp_comm (integrable_of_continuous_on_compact m hF)).symm
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    let g : C(K, ℂ) := ⟨fun k ↦ (f k⁻¹ : ℂ), Complex.continuous_ofReal.comp (f.continuous.comp continuous_inv)⟩
    have hg := hComplex g
    have he : (∫ k, (f k : ℂ) ∂ν) = ∫ k, (f k : ℂ) ∂m := by
      simpa only [g, ContinuousMap.coe_mk, inv_inv] using hg
    exact Complex.ofReal_injective (by simpa only [integral_complex_ofReal] using he)

/-- **Proposition 4.5**, with the representation space written as `ℂᵈ` as in
the paper. The converse transfers the test through an orthonormal basis. -/
theorem proposition4_5_euclidean (m ν : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    [m.IsOpenPosMeasure] [IsProbabilityMeasure ν] :
    ν = m ↔ ∀ (d : ℕ) (ρ : K →* (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d))),
      (∀ x, Continuous fun k ↦ ρ k x) → UnitaryIrreducible ρ → (∃ k, ρ k ≠ 1) →
      ∀ x y, (∫ k, ⟪x, ρ k y⟫_ℂ ∂ν) = 0 := by
  constructor
  · intro he d ρ hρ hI hN x y
    subst ν
    exact integral_coefficient_haar_eq_zero m ρ hρ hI hN x y
  · intro hν
    apply (proposition4_5 m ν).mpr
    intro E _ _ _ ρ hρ hI hN x y
    let d := Module.finrank ℂ E
    let F := EuclideanSpace ℂ (Fin d)
    let e : E ≃ₗᵢ[ℂ] F := (stdOrthonormalBasis ℂ E).repr
    let σ : K →* (F ≃ₗᵢ[ℂ] F) :=
      { toFun := fun k ↦ (e.symm.trans (ρ k)).trans e
        map_one' := by
          apply LinearIsometryEquiv.ext
          intro v
          change e (ρ 1 (e.symm v)) = v
          rw [map_one]
          exact e.apply_symm_apply v
        map_mul' := by
          intro a b
          apply LinearIsometryEquiv.ext
          intro v
          change e (ρ (a * b) (e.symm v)) = e (ρ a (e.symm (e (ρ b (e.symm v)))))
          rw [map_mul, e.symm_apply_apply]
          rfl }
    have he (k : K) (v : E) : σ k (e v) = e (ρ k v) := by
      change e (ρ k (e.symm (e v))) = e (ρ k v)
      rw [e.symm_apply_apply]
    have hσ (v : F) : Continuous fun k ↦ σ k v := e.continuous.comp (hρ (e.symm v))
    have hσI : UnitaryIrreducible σ := by
      let : Nontrivial (⊤ : Submodule ℂ E) := Submodule.nontrivial_iff_ne_bot.mpr hI.1
      let : Nontrivial E := (⊤ : Submodule ℂ E).subtype_injective.nontrivial
      let : Nontrivial F := e.injective.nontrivial
      refine ⟨top_ne_bot, fun _ _ _ ↦ Submodule.mem_top, fun L _ hL ↦ ?_⟩
      let eL := e.toLinearEquiv.toLinearMap
      have hLI : IsInvariantSubmodule ρ (L.comap eL) := by
        intro a v hv
        change e v ∈ L at hv
        change e (ρ a v) ∈ L
        rw [← he]
        exact hL a _ hv
      have hinj := Submodule.comap_injective_of_surjective (f := eL) e.surjective
      rcases hI.2.2 _ le_top hLI with hz | ht
      · refine Or.inl (hinj ?_)
        rwa [Submodule.comap_bot, LinearMap.ker_eq_bot.mpr e.injective]
      · refine Or.inr (hinj ?_)
        rwa [Submodule.comap_top]
    have hσN : ∃ k, σ k ≠ 1 := by
      obtain ⟨k,hk⟩ := hN
      refine ⟨k, fun htriv ↦ hk ?_⟩
      apply LinearIsometryEquiv.ext
      intro v
      apply e.injective
      rw [← he, htriv]
      rfl
    have h := hν d σ hσ hσI hσN (e x) (e y)
    simpa only [he, e.inner_map_map] using h

end SixProblems
