/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.MixingFamilies

/-! # The dual of ultrafilter mixing -/

@[expose] public section

open Filter Set
open scoped InnerProductSpace Mixing Topology

namespace Mixing

universe u v

variable {G : Type*} [Group G]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded linear map intertwines two unitary actions if it respects every group element. -/
def Intertwines (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K))
    (J : H →L[ℂ] K) : Prop :=
  ∀ g x, J (U g x) = V g (J x)

/-- Spectral disjointness is vanishing of all bounded linear intertwiners. -/
def SpectrallyDisjoint (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K)) : Prop :=
  ∀ J : K →L[ℂ] H, Intertwines V U J → J = 0

/-- Intertwining extends from the original action to all ultrafilter operators. -/
theorem Intertwines.ultrafilter {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}
    {J : H →L[ℂ] K} (hJ : Intertwines U V J) (p : Ultrafilter G) (x : H) :
    J (ultrafilterOperator U p x) = ultrafilterOperator V p (J x) := by
  apply ext_inner_left ℂ
  intro y
  rw [← J.adjoint_inner_left]
  apply tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p (J.adjoint y) x)
  convert tendsto_ultrafilterOperator_coeff V p y (J x) using 1
  funext g
  rw [J.adjoint_inner_left, hJ g x]

theorem Intertwines.adjoint {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}
    {J : H →L[ℂ] K} (hJ : Intertwines U V J) :
    Intertwines V U J.adjoint := by
  intro g y
  apply ext_inner_left ℂ
  intro x
  have hU : ((U g : H →L[ℂ] H).adjoint) x = U g⁻¹ x := by
    rw [LinearIsometryEquiv.adjoint_eq_symm, map_inv]
    rfl
  have hV : ∀ z, ((V g : K →L[ℂ] K).adjoint) z = V g⁻¹ z := by
    intro z
    rw [LinearIsometryEquiv.adjoint_eq_symm, map_inv]
    rfl
  calc
    ⟪x, J.adjoint (V g y)⟫_ℂ = ⟪J x, V g y⟫_ℂ := J.adjoint_inner_right _ _
    _ = ⟪V g⁻¹ (J x), y⟫_ℂ := by rw [← hV]; exact ((V g : K →L[ℂ] K).adjoint_inner_left _ _).symm
    _ = ⟪J (U g⁻¹ x), y⟫_ℂ := by rw [hJ]
    _ = ⟪U g⁻¹ x, J.adjoint y⟫_ℂ := (J.adjoint_inner_right _ _).symm
    _ = ⟪x, U g (J.adjoint y)⟫_ℂ := by rw [← hU]; exact (U g : H →L[ℂ] H).adjoint_inner_left _ _

theorem SpectrallyDisjoint.symm {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}
    (h : SpectrallyDisjoint U V) : SpectrallyDisjoint V U := by
  intro J hJ
  have he := h _ hJ.adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint, map_zero] using
    congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ)) he

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (P : Set (Ultrafilter G))

/-- The common kernel in equations (6) and (7). -/
noncomputable def mixingSubspace : Submodule ℂ H := ⨅ p : P, (ultrafilterOperator U p).ker

omit [CompleteSpace H] in
theorem mixingSubspace_isClosed : IsClosed (mixingSubspace U P : Set H) := by
  change IsClosed ((⨅ p : P, (ultrafilterOperator U p).ker : Submodule ℂ H) : Set H)
  simp only [Submodule.coe_iInf]
  exact isClosed_iInter fun p => (ultrafilterOperator U p).isClosed_ker

/-- Equation (7), the family generates the Hilbert space if its images have dense linear span. -/
def IsUGenerated : Prop :=
  (Submodule.span ℂ (⋃ p : P, ((ultrafilterOperator U p).range : Set H))).topologicalClosure = ⊤

theorem isUGenerated_iff [IsMulCommutative G] : IsUGenerated U P ↔ mixingSubspace U P = ⊥ := by
  unfold IsUGenerated mixingSubspace
  rw [← normal_iInf_ker_orthogonal_eq_span _ (fun p : P => ultrafilterOperator_normal U p),
    Submodule.orthogonal_eq_top_iff]

/-- `V` is annihilated relative to `(P,U)` when the kernels of all indices sharing
the same ultrafilter operator on `U` span densely, for each index in `P`. -/
def IsUAnnihilated (V : G →* (K ≃ₗᵢ[ℂ] K)) : Prop :=
  ∀ p : P, (⨆ q : {q : Ultrafilter G // ultrafilterOperator U q = ultrafilterOperator U p},
    (ultrafilterOperator V q).ker).topologicalClosure = ⊤

omit [CompleteSpace H] [CompleteSpace K] in
theorem isUAnnihilated_of_isUMixing {V : G →* (K ≃ₗᵢ[ℂ] K)} (h : IsUMixing V P) :
    IsUAnnihilated U P V := by
  intro p
  apply top_unique
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  have hle := le_iSup (fun q : {q : Ultrafilter G //
    ultrafilterOperator U q = ultrafilterOperator U p} => (ultrafilterOperator V q).ker) ⟨p, rfl⟩
  change (ultrafilterOperator V p).ker ≤ _ at hle
  rw [h p p.property] at hle
  simpa only [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero] using hle

/-- Restriction of a unitary group action to an invariant subspace. -/
noncomputable def unitarySubmoduleAction (W : Submodule ℂ H)
    (hW : ∀ g x, x ∈ W → U g x ∈ W) : G →* (W ≃ₗᵢ[ℂ] W) where
  toFun g :=
    { toLinearEquiv :=
        { (U g).toLinearMap.restrict (hW g) with
          invFun := fun x => ⟨U g⁻¹ x, hW g⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (show (U g⁻¹ * U g) x = x by
            rw [← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun x => Subtype.ext (show (U g * U g⁻¹) x = x by
            rw [← map_mul, mul_inv_cancel, map_one]; rfl) }
      norm_map' := fun x => (U g).norm_map x }
  map_one' := by
    ext x
    change U 1 x = (x : H)
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change U (g * h) x = U g (U h x)
    rw [map_mul]
    rfl

omit [CompleteSpace H] in
theorem intertwines_unitarySubmoduleAction (W : Submodule ℂ H)
    (hW : ∀ g x, x ∈ W → U g x ∈ W) :
    Intertwines (unitarySubmoduleAction U W hW) U W.subtypeL :=
  fun _ _ => rfl

/-- The ultrafilter operators commute with the original operators for an abelian group. -/
theorem ultrafilterOperator_commute [IsMulCommutative G] (p : Ultrafilter G) (g : G) (x : H) :
    U g (ultrafilterOperator U p x) = ultrafilterOperator U p (U g x) := by
  apply Intertwines.ultrafilter (J := (U g : H →L[ℂ] H)) (U := U) (V := U) ?_ p x
  intro a y
  change (U g * U a) y = (U a * U g) y
  rw [← map_mul, ← map_mul, mul_comm' g a]

theorem mixingSubspace_invariant [IsMulCommutative G] (g : G) (x : H)
    (hx : x ∈ mixingSubspace U P) : U g x ∈ mixingSubspace U P := by
  simp only [mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe] at hx ⊢
  intro p
  rw [← ultrafilterOperator_commute U p, hx, map_zero]

theorem mixingSubspace_orthogonal_invariant [IsMulCommutative G] (g : G) (x : H)
    (hx : x ∈ (mixingSubspace U P)ᗮ) : U g x ∈ (mixingSubspace U P)ᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hg : U g (U g⁻¹ y) = y := by
    change (U g * U g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    ⟪y, U g x⟫_ℂ = ⟪U g (U g⁻¹ y), U g x⟫_ℂ := by rw [hg]
    _ = ⟪U g⁻¹ y, x⟫_ℂ := (U g).inner_map_map _ _
    _ = 0 := hx _ (mixingSubspace_invariant U P _ _ hy)

variable [IsMulCommutative G]

omit [IsMulCommutative G] in
/-- A map from an annihilated action has image in the common kernel. -/
theorem intertwiner_mem_mixingSubspace {V : G →* (K ≃ₗᵢ[ℂ] K)} {J : K →L[ℂ] H}
    (hJ : Intertwines V U J) (hV : IsUAnnihilated U P V) (x : K) :
    J x ∈ mixingSubspace U P := by
  simp only [mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  intro p
  let A := (ultrafilterOperator U p).comp J
  have hle : (⨆ q : {q : Ultrafilter G // ultrafilterOperator U q = ultrafilterOperator U p},
    (ultrafilterOperator V q).ker) ≤ A.ker := by
    apply iSup_le
    intro q y hy
    change ultrafilterOperator U p (J y) = 0
    rw [← q.property, ← hJ.ultrafilter q, show ultrafilterOperator V q y = 0 from hy, map_zero]
  have ht := Submodule.topologicalClosure_minimal _ hle A.isClosed_ker
  rw [hV p] at ht
  exact ht (Submodule.mem_top (x := x))

/-- Theorem 3.1, (iii) implies (i). -/
theorem spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated
    {V : G →* (K ≃ₗᵢ[ℂ] K)} (hU : IsUGenerated U P) (hV : IsUAnnihilated U P V) :
    SpectrallyDisjoint U V := by
  intro J hJ
  apply ContinuousLinearMap.ext
  intro x
  have hx := intertwiner_mem_mixingSubspace U P hJ hV x
  rw [(isUGenerated_iff U P).mp hU, Submodule.mem_bot] at hx
  exact hx

/-- Theorem 3.1, (ii) implies (iii). The restricted action on the common
kernel is itself a mixing action, and its inclusion is an intertwiner. -/
theorem isUGenerated_of_spectrallyDisjoint_all_mixing
    (h : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUMixing V P → SpectrallyDisjoint U V) :
    IsUGenerated U P := by
  let W := mixingSubspace U P
  let _ : CompleteSpace W := (mixingSubspace_isClosed U P).completeSpace_coe
  let V := unitarySubmoduleAction U W (mixingSubspace_invariant U P)
  have hJ : Intertwines V U W.subtypeL :=
    intertwines_unitarySubmoduleAction U W (mixingSubspace_invariant U P)
  have hV : IsUMixing V P := by
    intro p hp
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change W.subtypeL (ultrafilterOperator V p x) = 0
    rw [hJ.ultrafilter]
    have hx := x.property
    simp only [W, mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] at hx
    exact hx ⟨p, hp⟩
  have hz := @h W _ _ _ V hV W.subtypeL hJ
  rw [isUGenerated_iff]
  apply le_antisymm _ bot_le
  intro x hx
  exact congrArg (fun J : W →L[ℂ] H => J ⟨x, hx⟩) hz

/-- Theorem 3.1. The generation criterion is equivalent to disjointness from
every annihilated action and to disjointness from every mixing action. -/
theorem theorem3_1 :
    (IsUGenerated U P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUAnnihilated U P V → SpectrallyDisjoint U V) ∧
    (IsUGenerated U P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUMixing V P → SpectrallyDisjoint U V) := by
  constructor
  · constructor
    · exact fun h _ _ _ _ _ hV => spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated U P h hV
    · intro h
      apply isUGenerated_of_spectrallyDisjoint_all_mixing U P
      intro K _ _ _ V hV
      exact @h K _ _ _ V (isUAnnihilated_of_isUMixing U P hV)
  · constructor
    · exact fun h _ _ _ _ _ hV =>
        spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated U P h (isUAnnihilated_of_isUMixing U P hV)
    · exact isUGenerated_of_spectrallyDisjoint_all_mixing U P

/-- Corollary 3, also the Hilbert-space equivalence behind Theorem 1.3(i).
Apply this to the mean-zero Koopman representation to test operator mixing
using disjointness from every generated action. -/
theorem corollary3 :
    IsUMixing U P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUGenerated V P → SpectrallyDisjoint U V := by
  constructor
  · intro h K _ _ _ V hV
    exact (spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated V P hV
      (isUAnnihilated_of_isUMixing V P h)).symm
  · intro h
    let W := (mixingSubspace U P)ᗮ
    let _ : CompleteSpace W := (Submodule.isClosed_orthogonal _).completeSpace_coe
    let V := unitarySubmoduleAction U W (mixingSubspace_orthogonal_invariant U P)
    have hJ : Intertwines V U W.subtypeL :=
      intertwines_unitarySubmoduleAction U W (mixingSubspace_orthogonal_invariant U P)
    have hV : IsUGenerated V P := by
      rw [isUGenerated_iff]
      apply le_antisymm _ bot_le
      intro x hx
      have hx' : (x : H) ∈ mixingSubspace U P := by
        simp only [mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
          ContinuousLinearMap.coe_coe] at hx ⊢
        intro p
        change ultrafilterOperator U p (W.subtypeL x) = 0
        rw [← hJ.ultrafilter p x, hx, map_zero]
      rw [Submodule.mem_bot]
      apply Subtype.ext
      exact (Submodule.disjoint_def.mp (mixingSubspace U P).orthogonal_disjoint) x hx' x.property
    have hz := @h W _ _ _ V hV W.subtypeL hJ
    have hW : (mixingSubspace U P)ᗮ = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact congrArg (fun J : W →L[ℂ] H => J ⟨x, hx⟩) hz
    rw [isUMixing_iff_iInf_ker_eq_top]
    change mixingSubspace U P = ⊤
    have heq := congrArg Submodule.orthogonal hW
    rwa [Submodule.orthogonal_orthogonal_eq_closure, Submodule.bot_orthogonal_eq_top,
      (mixingSubspace_isClosed U P).submodule_topologicalClosure_eq] at heq

end Mixing
