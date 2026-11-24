/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NormalOperator
public import Mixing.UltrafilterAction
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Finsupp.Span

/-! # Orthogonal series from families of commuting normal operators -/

@[expose] public section

open ContinuousLinearMap Filter
open scoped InnerProductSpace

namespace Mixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem exists_nat_subfamily_of_mem_closure_iSup {ι : Type*} [Nonempty ι]
    (K : ι → Submodule ℂ H) {x : H} (hx : x ∈ (⨆ i, K i).topologicalClosure) :
    ∃ f : ℕ → ι, x ∈ (⨆ n, K (f n)).topologicalClosure := by
  classical
  have hx' : x ∈ closure (↑(⨆ i, K i) : Set H) := by
    rwa [← Submodule.topologicalClosure_coe]
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hx'
  choose s hs using fun n ↦ Submodule.exists_finset_of_mem_iSup K (hu n)
  let i₀ : ι := Classical.choice inferInstance
  let C := insert i₀ (⋃ n, (s n : Set ι))
  have hC : C.Countable := (Set.countable_iUnion fun n ↦ (s n).finite_toSet.countable).insert i₀
  obtain ⟨f, hf⟩ := hC.exists_eq_range (by simp [C])
  refine ⟨f, ?_⟩
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto hlim (.of_forall fun n ↦ ?_)
  have hle : (⨆ i ∈ s n, K i) ≤ ⨆ j, K (f j) := by
    refine iSup₂_le fun i hi ↦ ?_
    have hiC : i ∈ C := Set.mem_insert_of_mem _ (Set.mem_iUnion.mpr ⟨n, hi⟩)
    rw [hf] at hiC
    obtain ⟨j, rfl⟩ := hiC
    exact le_iSup (fun j ↦ K (f j)) j
  exact hle (hs n)

private theorem commute_starProjection_of_mapsTo (K : Submodule ℂ H)
    [K.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (hA : Set.MapsTo A (K : Set H) (K : Set H))
    (hAdj : Set.MapsTo A.adjoint (K : Set H) (K : Set H)) :
    Commute A K.starProjection := by
  have ho : Set.MapsTo A (Kᗮ : Set H) (Kᗮ : Set H) := by
    intro y hy z hz
    rw [← A.adjoint_inner_left]
    exact hy _ (hAdj hz)
  show A * K.starProjection = K.starProjection * A
  ext y
  change A (K.starProjection y) = K.starProjection (A y)
  symm
  refine Submodule.eq_starProjection_of_mem_orthogonal (hA (K.starProjection_apply_mem y)) ?_
  rw [← map_sub]
  exact ho (K.sub_starProjection_mem_orthogonal y)

private theorem starProjection_ker_mapsTo_ker {A B : H →L[ℂ] H}
    [A.ker.HasOrthogonalProjection] (h : Commute A B) (hAdj : Commute A B.adjoint) :
    Set.MapsTo A.ker.starProjection (B.ker : Set H) (B.ker : Set H) := by
  have hMaps {C : H →L[ℂ] H} (hc : Commute A C) :
      Set.MapsTo C (A.ker : Set H) (A.ker : Set H) := by
    intro y hy
    change A y = 0 at hy
    change A (C y) = 0
    rw [show A (C y) = C (A y) from DFunLike.congr_fun hc.eq y, hy, map_zero]
  have hComm := commute_starProjection_of_mapsTo A.ker B (hMaps h) (hMaps hAdj)
  intro y hy
  change B y = 0 at hy
  change B (A.ker.starProjection y) = 0
  rw [show B (A.ker.starProjection y) = A.ker.starProjection (B y) from
    DFunLike.congr_fun hComm.eq y, hy, map_zero]

private theorem exists_hasSum_rangeClosure_ker_of_nat (T : ℕ → (H →L[ℂ] H))
    (hT : ∀ n, IsStarNormal (T n)) (hComm : ∀ i j, Commute (T i) (T j))
    (hAdjComm : ∀ i j, Commute (T i) (T j).adjoint)
    {x : H} (hx : x ∈ (⨆ n, (T n).range).topologicalClosure) :
    ∃ ξ : ℕ → H, HasSum ξ x ∧
      ∀ n, ξ n ∈ (T n).range.topologicalClosure ∧ ∀ j < n, ξ n ∈ (T j).ker := by
  let K : ℕ → Submodule ℂ H := fun n ↦ ⨅ j : Fin n, (T j).ker
  let D : ℕ → Submodule ℂ H := fun n ↦ K n ⊓ (T n).kerᗮ
  have hK (n : ℕ) (y : H) : y ∈ K n ↔ ∀ j < n, y ∈ (T j).ker := by
    simp only [K, Submodule.mem_iInf]
    exact ⟨fun h j hj ↦ h ⟨j, hj⟩, fun h j ↦ h j j.isLt⟩
  have hKClosed (n : ℕ) : IsClosed (K n : Set H) := by
    rw [show (K n : Set H) = ⋂ j : Fin n, ((T j).ker : Set H) from Submodule.coe_iInf _]
    exact isClosed_iInter fun j ↦ (T j).isClosed_ker
  let _ (n : ℕ) : CompleteSpace (D n) :=
    ((hKClosed n).inter ((T n).ker.isClosed_orthogonal)).completeSpace_coe
  have hOrtho (i j : ℕ) (hij : i < j) : D i ⟂ D j := by
    rw [Submodule.isOrtho_iff_inner_eq]
    intro a ha b hb
    exact Submodule.inner_left_of_mem_orthogonal ((hK j b).mp hb.1 i hij) ha.2
  have hKer : (⨆ n, D n)ᗮ ≤ ⨅ n, (T n).ker := by
    intro y hy
    have hPast (n : ℕ) : y ∈ K n := by
      induction n with
      | zero =>
        exact (hK 0 y).mpr fun j hj ↦ (Nat.not_lt_zero j hj).elim
      | succ n ih =>
        let _ : CompleteSpace (T n).ker := (T n).isClosed_ker.completeSpace_coe
        let p := (T n).ker.starProjection y
        have hp : p ∈ (T n).ker := (T n).ker.starProjection_apply_mem y
        have hpPast : p ∈ K n := (hK n p).mpr fun j hj ↦
          starProjection_ker_mapsTo_ker (hComm n j) (hAdjComm n j) ((hK n y).mp ih j hj)
        have hr : y - p ∈ D n :=
          ⟨(K n).sub_mem ih hpPast, (T n).ker.sub_starProjection_mem_orthogonal y⟩
        have hyhr : ⟪y - p, y⟫_ℂ = 0 := hy _ (Submodule.mem_iSup_of_mem n hr)
        have hphr : ⟪y - p, p⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hp hr.2
        have heq : y - p = 0 :=
          (inner_self_eq_zero (𝕜 := ℂ)).mp (by rw [inner_sub_right, hyhr, hphr, sub_zero])
        have hyKernel : y ∈ (T n).ker := by rwa [sub_eq_zero.mp heq]
        refine (hK _ _).mpr fun j hj ↦ ?_
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact (hK _ _).mp ih j h
        · exact hyKernel
    exact (Submodule.mem_iInf _).mpr fun n ↦ (hK (n + 1) y).mp (hPast _) n (Nat.lt_succ_self n)
  have hxD : x ∈ (⨆ n, D n).topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.orthogonal_le hKer (by rwa [normal_iInf_ker_orthogonal T hT])
  let V : ∀ n, D n →ₗᵢ[ℂ] H := fun n ↦ (D n).subtypeₗᵢ
  have hV : OrthogonalFamily ℂ (fun n ↦ D n) V := .of_pairwise fun i j hij ↦ by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hOrtho i j h
    · exact (hOrtho j i h).symm
  have hrange (n : ℕ) : LinearMap.range (V n).toLinearMap = D n := Submodule.range_subtype _
  rw [← show LinearMap.range hV.linearIsometry.toLinearMap = (⨆ n, D n).topologicalClosure by
    rw [hV.range_linearIsometry]
    simp only [hrange]] at hxD
  obtain ⟨a, rfl⟩ := hxD
  refine ⟨fun n ↦ a n, hV.hasSum_linearIsometry a, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [← Submodule.orthogonal_orthogonal_eq_closure, normal_range_orthogonal (T n) (hT n)]
    exact (a n).property.2
  · exact (hK n _).mp (a n).property.1

/-- The Hilbert-space assertion in Remark 5. Each vector in the closed span of the ranges of
a nonempty star-commuting family is the sum of a sequence of orthogonal pieces. The piece
at index `n` is in the closed range of the operator chosen at that index and in the kernels of
the operators chosen at all earlier indices. -/
theorem mem_closure_iSup_range_iff_exists_hasSum_rangeClosure_ker {ι : Type*} [Nonempty ι]
    (T : ι → (H →L[ℂ] H)) (hT : ∀ i, IsStarNormal (T i))
    (hComm : ∀ i j, Commute (T i) (T j)) (hAdjComm : ∀ i j, Commute (T i) (T j).adjoint)
    (x : H) :
    x ∈ (⨆ i, (T i).range).topologicalClosure ↔
      ∃ (f : ℕ → ι) (ξ : ℕ → H), HasSum ξ x ∧
        ∀ n, ξ n ∈ (T (f n)).range.topologicalClosure ∧ ∀ j < n, ξ n ∈ (T (f j)).ker := by
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := exists_nat_subfamily_of_mem_closure_iSup (fun i ↦ (T i).range) hx
    obtain ⟨ξ, hsum, hξ⟩ :=
      exists_hasSum_rangeClosure_ker_of_nat (fun n ↦ T (f n)) (fun n ↦ hT (f n))
        (fun i j ↦ hComm (f i) (f j)) (fun i j ↦ hAdjComm (f i) (f j)) hf
    exact ⟨f, ξ, hsum, hξ⟩
  · rintro ⟨f, ξ, hsum, hξ⟩
    refine (⨆ i, (T i).range).isClosed_topologicalClosure.mem_of_tendsto hsum
      (.of_forall fun s ↦ Submodule.sum_mem _ ?_)
    intro n _
    exact Submodule.topologicalClosure_mono (le_iSup (fun i ↦ (T i).range) (f n)) (hξ n).1


/-- Remark 5 for the actual ultrafilter operators of the representation. The zero-based
indexing has no earlier-kernel condition on the first summand. -/
theorem ultrafilter_mem_closure_iSup_range_iff_exists_hasSum
    {G : Type*} [Group G] [IsMulCommutative G] (U : G →* (H ≃ₗᵢ[ℂ] H))
    (P : Set (Ultrafilter G)) (hP : P.Nonempty) (x : H) :
    x ∈ (⨆ p : P, (ultrafilterOperator U p).range).topologicalClosure ↔
      ∃ (p : ℕ → P) (ξ : ℕ → H), HasSum ξ x ∧
        ∀ n, ξ n ∈ (ultrafilterOperator U (p n)).range.topologicalClosure ∧
          ∀ j < n, ξ n ∈ (ultrafilterOperator U (p j)).ker := by
  let _ : Nonempty P := hP.to_subtype
  refine mem_closure_iSup_range_iff_exists_hasSum_rangeClosure_ker
    (fun p : P ↦ ultrafilterOperator U p) (fun p ↦ ultrafilterOperator_normal U p)
    (fun p q ↦ ultrafilterOperator_commute_pair U p q) (fun p q ↦ ?_) x
  rw [← ultrafilterOperator_inverse U q]
  exact ultrafilterOperator_commute_pair U p (inverseUltrafilter q)

end Mixing
