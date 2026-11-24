/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactRepresentationAverage
public import Mixing.PurePointLebesgue
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure InnerProductSpace Module.End Set
open scoped ComplexConjugate InnerProductSpace

variable {K H : Type*} [CommGroup K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem exists_joint_unitary_scalar [FiniteDimensional ℂ H] [Nontrivial H]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) :
    ∃ x : H, x ≠ 0 ∧ ∀ k : K, ∃ z : ℂ, ρ k x = z • x := by
  classical
  let invariant (V : Submodule ℂ H) := ∀ k : K, ∀ x ∈ V, ρ k x ∈ V
  let P (n : ℕ) := ∃ V : Submodule ℂ H, V ≠ ⊥ ∧ Module.finrank ℂ V = n ∧ invariant V
  have hP : ∃ n, P n := ⟨_, ⊤, top_ne_bot, rfl, fun _ _ _ ↦ Submodule.mem_top⟩
  obtain ⟨V, hV, hDim, hInv⟩ := Nat.find_spec hP
  obtain ⟨x, hxV, hx⟩ : ∃ x ∈ V, x ≠ 0 := by
    by_contra! he
    exact hV ((Submodule.eq_bot_iff V).mpr he)
  let : Nontrivial V := ⟨⟨⟨x, hxV⟩, 0, fun h ↦ hx (congrArg Subtype.val h)⟩⟩
  let U := unitarySubmoduleAction ρ V hInv
  refine ⟨x, hx, fun a ↦ ?_⟩
  let T : Module.End ℂ V := (U a).toLinearMap
  obtain ⟨z,hz⟩ := T.exists_eigenvalue
  let W := T.eigenspace z
  let V' := W.map V.subtype
  have hV' : V' ≤ V := by
    rintro y ⟨v, hv, rfl⟩
    exact v.property
  have hW : W ≠ ⊥ := hasEigenvalue_iff.mp hz
  have hV'₀ : V' ≠ ⊥ := by
    intro he
    apply hW
    apply (Submodule.eq_bot_iff W).mpr
    intro y hy
    apply Subtype.ext
    have hh : V.subtype y ∈ (⊥ : Submodule ℂ H) :=
      he ▸ (Submodule.mem_map_of_mem hy : V.subtype y ∈ V')
    rw [Submodule.mem_bot] at hh
    change (y : H) = 0
    exact hh
  have hInv' : invariant V' := by
    intro b y hy
    obtain ⟨u, hu, rfl⟩ := hy
    have he : Commute T (U b).toLinearMap := by
      change T * (U b).toLinearMap = (U b).toLinearMap * T
      apply LinearMap.ext
      intro v
      change (U a) ((U b) v) = (U b) ((U a) v)
      change (U a * U b) v = (U b * U a) v
      rw [← map_mul, ← map_mul, mul_comm a b]
    have hv : U b u ∈ W := by
      have hu' := mem_eigenspace_iff.mp hu
      apply mem_eigenspace_iff.mpr
      change (T * (U b).toLinearMap) u = _
      rw [he.eq]
      change U b (T u) = _
      rw [hu', map_smul]
    exact Submodule.mem_map_of_mem hv
  have hEq : V' = V := by
    by_contra hn
    have hh : V' < V := lt_of_le_of_ne hV' hn
    have hl := Submodule.finrank_lt_finrank_of_lt hh
    exact (not_lt_of_ge (Nat.find_min' hP ⟨V', hV'₀, rfl, hInv'⟩)) (hDim ▸ hl)
  have hx' : x ∈ V' := hEq.symm ▸ hxV
  obtain ⟨u, hu, hux⟩ := hx'
  refine ⟨z, ?_⟩
  have he := congrArg Subtype.val (mem_eigenspace_iff.mp hu)
  change ρ a (V.subtype u) = z • V.subtype u at he
  rwa [hux] at he

theorem exists_unitaryCharacter_of_joint_scalars (ρ : K →* (H ≃ₗᵢ[ℂ] H))
    {x : H} (hx : x ≠ 0) (h : ∀ k, ∃ z : ℂ, ρ k x = z • x) :
    ∃ χ : K →* Circle, ∀ k, ρ k x = (χ k : ℂ) • x := by
  choose z hz using h
  have hn (k : K) : ‖z k‖ = 1 := by
    have he := congrArg norm (hz k)
    rw [LinearIsometryEquiv.norm_map, norm_smul] at he
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hx) (he.symm.trans (one_mul _).symm)
  have hS : Function.Injective (fun c : ℂ ↦ c • x) := fun a b hab ↦ by
    change a • x = b • x at hab
    have he : (a-b) • x = 0 := by rw [sub_smul, hab, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hx)
  let χ : K →* Circle :=
    { toFun := fun k ↦ ⟨z k, mem_sphere_zero_iff_norm.2 (hn k)⟩
      map_one' := by
        apply Subtype.ext
        change z 1 = 1
        apply hS
        change z 1 • x = (1 : ℂ) • x
        rw [← hz, map_one, one_smul]
        rfl
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        change z (a*b) = z a * z b
        apply hS
        change z (a*b) • x = (z a * z b) • x
        rw [← hz, map_mul]
        change ρ a (ρ b x) = _
        rw [hz b, map_smul, hz a, smul_smul, mul_comm] }
  exact ⟨χ,hz⟩

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [CompleteSpace H]

/-- Every nonzero compact abelian unitary representation has a joint eigenvector. -/
theorem exists_compactAbelian_unitaryEigenvector [Nontrivial H]
    (μ : Measure K) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ] [μ.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    ∃ x : H, x ≠ 0 ∧ x ∈ unitaryEigenvectors ρ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let A := compactRepresentationAverage μ ρ v
  have hA := isCompactOperator_compactRepresentationAverage μ ρ v (hρ v)
  have hSym := isSymmetric_compactRepresentationAverage μ ρ v (hρ v)
  have hne := compactRepresentationAverage_ne_zero μ ρ hv (hρ v)
  have he : ¬ ∀ z, HasEigenvalue A.toLinearMap z → z = 0 :=
    fun h ↦ hne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hA hSym).mp h)
  push Not at he
  obtain ⟨z, hz, hzero⟩ := he
  let W := eigenspace A.toLinearMap z
  let : FiniteDimensional ℂ W := ContinuousLinearMap.finite_dimensional_eigenspace hA z hzero
  have hW : W ≠ ⊥ := hasEigenvalue_iff.mp hz
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hInv (a : K) (w : H) (hw : w ∈ W) : ρ a w ∈ W := by
    have hv' := mem_eigenspace_iff.mp hw
    apply mem_eigenspace_iff.mpr
    change A (ρ a w) = z • ρ a w
    rw [← compactRepresentationAverage_commutes μ ρ v (hρ v), show A w = z • w from hv', map_smul]
  let U := unitarySubmoduleAction ρ W hInv
  obtain ⟨x, hx, h⟩ := exists_joint_unitary_scalar U
  refine ⟨x, ?_, exists_unitaryCharacter_of_joint_scalars ρ ?_ ?_⟩
  · exact fun he ↦ hx (Subtype.ext he)
  · exact fun he ↦ hx (Subtype.ext he)
  · intro k
    obtain ⟨c,hc⟩ := h k
    exact ⟨c, congrArg Subtype.val hc⟩

/-- Peter–Weyl in the abelian case, in the form needed for compact vertical
groups: the continuous unitary representation is spanned by characters. -/
theorem purePointPart_eq_top_of_compactAbelian
    (μ : Measure K) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ] [μ.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    purePointPart ρ = ⊤ := by
  let Q := purePointPart ρ
  let W := Qᗮ
  let : CompleteSpace (purePointPart ρ) := (isClosed_purePointPart ρ).completeSpace_coe
  have hInvQ (a : K) : Q ≤ Q.comap (ρ a).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro x ⟨χ,hx⟩
      have hMem : x ∈ Q := Submodule.le_topologicalClosure _
        (Submodule.subset_span (show x ∈ unitaryEigenvectors ρ from ⟨χ,hx⟩))
      change ρ a x ∈ Q
      rw [hx]
      exact Q.smul_mem _ hMem
    · exact (isClosed_purePointPart ρ).preimage (ρ a).continuous
  have hInv (a : K) (x : H) (hx : x ∈ W) : ρ a x ∈ W := by
    intro y hy
    have he : ρ a (ρ a⁻¹ y) = y := by
      change (ρ a * ρ a⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    calc
      ⟪y, ρ a x⟫_ℂ = ⟪ρ a (ρ a⁻¹ y),ρ a x⟫_ℂ :=
        congrArg (fun w ↦ ⟪w,ρ a x⟫_ℂ) he.symm
      _ = ⟪ρ a⁻¹ y,x⟫_ℂ := (ρ a).inner_map_map _ _
      _ = 0 := hx _ (hInvQ a⁻¹ hy)
  apply Submodule.orthogonal_eq_bot_iff.mp
  by_contra hW
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let U := unitarySubmoduleAction ρ W hInv
  have hUC (x : W) : Continuous fun k ↦ U k x :=
    (hρ x).subtype_mk _
  obtain ⟨x,hx,χ,hχ⟩ := exists_compactAbelian_unitaryEigenvector μ U hUC
  have hxQ : (x : H) ∈ Q := Submodule.le_topologicalClosure _
    (Submodule.subset_span (show (x : H) ∈ unitaryEigenvectors ρ from
      ⟨χ,fun k ↦ congrArg Subtype.val (hχ k)⟩))
  exact hx (Subtype.ext (inner_self_eq_zero.mp (x.property _ hxQ)))

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [CompleteSpace H] in
/-- The character of a nonzero joint eigenvector is continuous in a strongly
continuous representation. -/
theorem continuous_character_of_unitaryEigenvector (ρ : K →* (H ≃ₗᵢ[ℂ] H))
    {x : H} (hx : x ≠ 0) (hρ : Continuous fun k ↦ ρ k x)
    (χ : K →* Circle) (hχ : ∀ k, ρ k x = (χ k : ℂ) • x) : Continuous χ := by
  have h : Continuous (fun k ↦ (χ k : ℂ)) := by
    have he (k : K) : (χ k : ℂ) = ⟪x,ρ k x⟫_ℂ / ⟪x,x⟫_ℂ := by
      rw [hχ, inner_smul_right, div_eq_mul_inv, mul_assoc,
        mul_inv_cancel₀ (fun h ↦ hx (inner_self_eq_zero.mp h)), mul_one]
    simp_rw [he]
    exact (continuous_const.inner hρ).div_const _
  exact continuous_induced_rng.mpr h

end Mixing
