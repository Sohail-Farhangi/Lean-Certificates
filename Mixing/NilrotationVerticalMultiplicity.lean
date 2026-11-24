/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationKoopmanVertical
public import Mixing.CentralCommutatorPhases
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Distinct nonzero character modes in a connected principal extension -/

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure Metric Set
open scoped ComplexConjugate InnerProductSpace

/-- Different common eigencharacters of a unitary representation have
orthogonal eigenspaces. -/
theorem unitaryCharacter_inner_eq_zero_of_ne
    {K H : Type*} [Group K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) {χ ψ : K →* Circle} (hne : χ ≠ ψ)
    {v w : H} (hv : ∀ k, ρ k v = (χ k : ℂ) • v) (hw : ∀ k, ρ k w = (ψ k : ℂ) • w) :
    ⟪v, w⟫_ℂ = 0 := by
  have hx : ∃ k, χ k ≠ ψ k := by
    by_contra! h
    exact hne (MonoidHom.ext h)
  obtain ⟨k, hk⟩ := hx
  have he := (ρ k).inner_map_map v w
  rw [hv k, hw k, inner_smul_left, inner_smul_right, ← mul_assoc] at he
  have hs : conj (χ k : ℂ) * (ψ k : ℂ) ≠ 1 := by
    intro h
    have hh : (χ k)⁻¹ * ψ k = 1 := Circle.coe_injective (by
      simpa only [Circle.coe_mul, Circle.coe_inv_eq_conj, Circle.coe_one] using h)
    exact hk (inv_mul_eq_one.mp hh)
  have hz : (conj (χ k : ℂ) * (ψ k : ℂ) - 1) * ⟪v, w⟫_ℂ = 0 := by
    rw [sub_mul, one_mul, he, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hs)

/-- A nonidentity left translation of a compact group with Haar probability
acts nontrivially on L². -/
private theorem exists_not_fixed_regularTranslation
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableMul₂ K]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (k : K) (hk : k ≠ 1) :
    ∃ f : Lp ℂ 2 m, inverseActionKoopmanRep m (measurePreserving_mul_left m) k f ≠ f := by
  have hk' : (1 : K) ≠ k⁻¹ := fun h ↦ hk (inv_eq_one.mp h.symm)
  obtain ⟨U, V, hU, hV, hOne, hkInv, hUV⟩ := t2_separation hk'
  let W := U ∩ (fun x : K ↦ k⁻¹ * x) ⁻¹' V
  have hW : IsOpen W := hU.inter (hV.preimage (continuous_const.mul continuous_id))
  have hOneW : (1 : K) ∈ W := ⟨hOne, by simpa only [mem_preimage, mul_one] using hkInv⟩
  let f : Lp ℂ 2 m := indicatorConstLp 2 hU.measurableSet (measure_ne_top m U) 1
  refine ⟨f, fun he ↦ ?_⟩
  have hEq := ae_inverseActionKoopmanRep_apply m (measurePreserving_mul_left m) k f
  rw [he] at hEq
  have hPos : ∀ᵐ x ∂m, x ∈ U → f x = 1 := indicatorConstLp_coeFn_mem
  have hZero : ∀ᵐ x ∂m, x ∉ U → f x = 0 := indicatorConstLp_coeFn_notMem
  have hEmpty : ∀ᵐ x ∂m, x ∉ W := by
    filter_upwards [hEq, hPos, (measurePreserving_mul_left m k⁻¹).quasiMeasurePreserving.ae hZero]
      with x he' hpx hzx
    intro hx
    have hu : x ∈ U := hx.1
    have hv : k⁻¹ * x ∈ V := hx.2
    have hn : k⁻¹ * x ∉ U := fun h ↦ Set.disjoint_left.mp hUV h hv
    exact one_ne_zero ((hpx hu).symm.trans (he'.trans (hzx hn)))
  have hmW : m W = 0 := by simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hEmpty
  exact (hW.measure_pos (μ := m) ⟨1, hOneW⟩).ne' hmW

/-- A nontrivial compact abelian group has a nontrivial continuous character.
Here this follows from the compact unitary decomposition of its regular action. -/
theorem exists_nontrivial_continuousCharacter_of_compactAbelian
    {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [Nontrivial K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableMul₂ K]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    [m.IsOpenPosMeasure] [m.InnerRegularCompactLTTop] :
    ∃ χ : K →* Circle, Continuous χ ∧ ∃ k, χ k ≠ 1 := by
  by_contra hNone
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  obtain ⟨v, hv⟩ := exists_not_fixed_regularTranslation m k hk
  let ρ := inverseActionKoopmanRep m (measurePreserving_mul_left m)
  let A := linearRepresentation ρ k - ContinuousLinearMap.id ℂ (Lp ℂ 2 m)
  have hρ (f : Lp ℂ 2 m) : Continuous (fun x ↦ ρ x f) :=
    continuous_inverseActionKoopmanRep m (measurePreserving_mul_left m) f
  have hTop : A.ker = ⊤ := by
    apply eq_top_of_vertical_character_modes m ρ hρ A.ker A.isClosed_ker
    · intro w hw
      change ρ k w - w = 0
      rw [hw k, sub_self]
    · intro χ hχ hne w _
      exact (hNone ⟨χ, hχ, hne⟩).elim
  have hvA : v ∈ A.ker := hTop.symm ▸ Submodule.mem_top
  exact hv (sub_eq_zero.mp (show ρ k v - v = 0 from hvA))

/-- The vertical coordinate of a principal extension realizes every measurable
circle character as a nonzero unitary eigenvector. -/
theorem exists_principalExtension_vertical_eigenvector
    {X Y K : Type*} [Group K] [MulAction K X]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e : Y × K ≃ᵐ X) (hE : ∀ y k r, e (y, k * r) = r⁻¹ • e (y, k))
    (hPres : ∀ k : K, MeasurePreserving (fun x : X ↦ k • x) μ μ)
    (χ : K →* Circle) (hχ : Measurable fun k ↦ (χ k : ℂ)) :
    ∃ v : Lp ℂ 2 μ, v ≠ 0 ∧ ∀ k, inverseActionKoopmanRep μ hPres k v = (χ k : ℂ) • v := by
  let f (x : X) : ℂ := χ (e.symm x).2
  have hM : Measurable f := hχ.comp (measurable_snd.comp e.symm.measurable)
  have hL : MemLp f 2 μ := MemLp.of_bound hM.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ (Circle.norm_coe (χ (e.symm x).2)).le)
  let v := hL.toLp f
  have hv : (v : X → ℂ) =ᵐ[μ] f := hL.coeFn_toLp
  refine ⟨v, ?_, ?_⟩
  · intro he
    obtain ⟨x, hx⟩ := ((Lp.eq_zero_iff_ae_eq_zero.mp he).symm.trans hv).exists
    exact (χ (e.symm x).2).coe_ne_zero hx.symm
  · intro k
    have he (x : X) : (e.symm (k⁻¹ • x)).2 = (e.symm x).2 * k := by
      obtain ⟨⟨y, r⟩, rfl⟩ := e.surjective x
      rw [← hE y r k, e.symm_apply_apply, e.symm_apply_apply]
    apply Lp.ext
    filter_upwards [ae_inverseActionKoopmanRep_apply μ hPres k v,
      (hPres k⁻¹).quasiMeasurePreserving.ae hv, Lp.coeFn_smul (χ k : ℂ) v, hv]
      with x h₁ h₂ h₃ h₄
    have hvalues : f (k⁻¹ • x) = (χ k : ℂ) • f x := by
      change (χ (e.symm (k⁻¹ • x)).2 : ℂ) = (χ k : ℂ) • (χ (e.symm x).2 : ℂ)
      rw [he, map_mul, Circle.coe_mul, smul_eq_mul, mul_comm]
    exact h₁.trans (h₂.trans (hvalues.trans
      ((congrArg (fun z : ℂ ↦ (χ k : ℂ) • z) h₄.symm).trans h₃.symm)))

/-- Powers of a nontrivial continuous character of a connected group are distinct. -/
theorem injective_pow_of_nontrivial_connected_circleCharacter
    {K : Type*} [Group K] [TopologicalSpace K] [ConnectedSpace K]
    (χ : K →* Circle) (hχ : Continuous χ) (hne : ∃ k, χ k ≠ 1) :
    Function.Injective (fun n : ℕ ↦ χ ^ n) := by
  intro n m he
  let d := max n m + 1
  have hd : d ≠ 0 := Nat.succ_ne_zero _
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
  have hz : IsPrimitiveRoot z d := Complex.isPrimitiveRoot_exp d hd
  let u : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr (hz.norm'_eq_one hd)⟩
  obtain ⟨k, hk⟩ := continuous_circle_hom_surjective_of_nontrivial χ hχ hne u
  apply hz.pow_inj (Nat.lt_succ_of_le (le_max_left n m)) (Nat.lt_succ_of_le (le_max_right n m))
  have h := congrArg (fun ψ : K →* Circle ↦ (ψ k : ℂ)) he
  simpa only [MonoidHom.pow_apply, hk, Circle.coe_pow] using h

/-- In principal coordinates, a nontrivial connected vertical character gives
countably many distinct nontrivial characters with nonzero eigenvectors. -/
theorem exists_principalExtension_infinite_vertical_modes
    {X Y K : Type*} [Group K] [MulAction K X] [TopologicalSpace K] [ConnectedSpace K]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace K] [BorelSpace K]
    [IsTopologicalGroup K] (μ : Measure X) [IsProbabilityMeasure μ]
    (e : Y × K ≃ᵐ X) (hE : ∀ y k r, e (y, k * r) = r⁻¹ • e (y, k))
    (hPres : ∀ k : K, MeasurePreserving (fun x : X ↦ k • x) μ μ)
    (χ : K →* Circle) (hχ : Continuous χ) (hne : ∃ k, χ k ≠ 1) :
    ∃ ψ : ℕ → K →* Circle, Function.Injective ψ ∧ ∀ n,
      Continuous (ψ n) ∧ (∃ k, ψ n k ≠ 1) ∧
      ∃ v : Lp ℂ 2 μ, v ≠ 0 ∧ ∀ k, inverseActionKoopmanRep μ hPres k v = (ψ n k : ℂ) • v := by
  let ψ (n : ℕ) : K →* Circle := χ ^ (n + 1)
  have hi := injective_pow_of_nontrivial_connected_circleCharacter χ hχ hne
  refine ⟨ψ, fun _ _ h ↦ Nat.succ.inj (hi h), ?_⟩
  intro n
  have hψ : Continuous (ψ n) := by
    change Continuous (fun k ↦ χ k ^ (n + 1))
    exact hχ.pow (n + 1)
  refine ⟨hψ, ?_, exists_principalExtension_vertical_eigenvector μ e hE hPres (ψ n)
    (continuous_subtype_val.comp hψ).measurable⟩
  by_contra! h
  have he : χ ^ (n + 1) = χ ^ 0 := MonoidHom.ext fun k ↦ by
    rw [pow_zero]
    exact h k
  exact Nat.succ_ne_zero n (hi he)

end Mixing
