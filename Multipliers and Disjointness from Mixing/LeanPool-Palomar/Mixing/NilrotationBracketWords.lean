/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationGeometryConnectivity
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section
noncomputable section

namespace Mixing

open scoped commutatorElement

variable {G H : Type*} [Group G] [Group H]

/-- The right-nested commutator of an ordered tuple of `n + 1` elements. -/
def nilrotationBracketWord : (n : ℕ) → (Fin (n+1) → G) → G
  | 0, u => u 0
  | n+1, u => ⁅u 0, nilrotationBracketWord n (Fin.tail u)⁆

theorem map_nilrotationBracketWord (f : G →* H) (n : ℕ) (u : Fin (n+1) → G) :
    f (nilrotationBracketWord n u) = nilrotationBracketWord n (f ∘ u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nilrotationBracketWord, nilrotationBracketWord, map_commutatorElement, ih]
    rfl

theorem nilrotationBracketWord_mem_lowerCentral (n : ℕ) (u : Fin (n+1) → G) :
    nilrotationBracketWord n u ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [nilrotationBracketWord, Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (ih (Fin.tail u))

theorem nilrotationBracketWord_mem_subgroup (L : Subgroup G) (n : ℕ) (u : Fin (n+1) → G)
    (hu : ∀ i, u i ∈ L) : nilrotationBracketWord n u ∈ L := by
  induction n with
  | zero => exact hu 0
  | succ n ih =>
    rw [nilrotationBracketWord, commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem (hu 0) (ih _ fun i ↦ hu i.succ)) (L.inv_mem (hu 0)))
      (L.inv_mem (ih _ fun i ↦ hu i.succ))

/-- Iterated commutator words generate their term of the lower central series. -/
theorem closure_range_nilrotationBracketWord (n : ℕ) :
    Subgroup.closure (Set.range (nilrotationBracketWord (G := G) n)) =
      (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    have h : Set.range (nilrotationBracketWord (G := G) 0) = Set.univ :=
      Set.eq_univ_of_forall fun g ↦ ⟨fun _ ↦ g, rfl⟩
    rw [h, Subgroup.closure_univ, Subgroup.lowerCentralSeries_zero]
  | succ n ih =>
    let D := Subgroup.closure (Set.range (nilrotationBracketWord (G := G) (n+1)))
    have hD : D.Normal := ⟨fun g hg x ↦ by
      have hle : D ≤ D.comap (MulAut.conj x).toMonoidHom := by
        apply (Subgroup.closure_le _).mpr
        rintro _ ⟨u, rfl⟩
        change (MulAut.conj x).toMonoidHom (nilrotationBracketWord (n+1) u) ∈ D
        rw [map_nilrotationBracketWord (MulAut.conj x).toMonoidHom]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      exact hle hg⟩
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr
        (Set.range_subset_iff.mpr (nilrotationBracketWord_mem_lowerCentral (n+1)))
    · rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm, ← ih]
      apply Subgroup.commutator_le.mpr
      intro a _ b hb
      let q := QuotientGroup.mk' D
      have hc : Subgroup.closure (Set.range (nilrotationBracketWord (G := G) n)) ≤
          (Subgroup.centralizer {q a}).comap q := by
        apply (Subgroup.closure_le _).mpr
        rintro _ ⟨u, rfl⟩
        change q (nilrotationBracketWord n u) ∈ Subgroup.centralizer {q a}
        rw [Subgroup.mem_centralizer_iff, Set.forall_mem_singleton]
        apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        apply (QuotientGroup.eq_one_iff _).mpr
        exact Subgroup.subset_closure ⟨Fin.cons a u, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mp
      change q ⁅a,b⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have he := Subgroup.mem_centralizer_iff.mp (hc hb)
      exact he (q a) (Set.mem_singleton _)

/-- The last lower-central subgroup in a terminating series is central. -/
theorem nilrotation_last_lowerCentral_le_center (n : ℕ)
    (hn : (⊤ : Subgroup G).lowerCentralSeries (n+1) = ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries n ≤ Subgroup.center G := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hh := Subgroup.lowerCentralSeries_isDescendingCentralSeries.2 x n hx g
  rw [hn, Subgroup.mem_bot] at hh
  exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm

private theorem nilrotationBracketWord_update_zero (n : ℕ) (u : Fin (n+2) → G) (x : G) :
    nilrotationBracketWord (n+1) (Function.update u 0 x) =
      ⁅x, nilrotationBracketWord n (Fin.tail u)⁆ := by
  classical
  rw [nilrotationBracketWord, Function.update_self]
  congr 2

private theorem nilrotationBracketWord_update_succ (n : ℕ) (u : Fin (n+2) → G)
    (i : Fin (n+1)) (x : G) :
    nilrotationBracketWord (n+1) (Function.update u i.succ x) =
      ⁅u 0, nilrotationBracketWord n (Function.update (Fin.tail u) i x)⁆ := by
  classical
  rw [nilrotationBracketWord, Function.update_of_ne (Fin.succ_ne_zero i).symm]
  congr 2
  funext j
  simp [Fin.tail, Function.update, Fin.succ_inj]

/-- At the last layer, the top commutator word is a homomorphism in each slot. -/
theorem nilrotationBracketWord_update_mul (n : ℕ) {G : Type*} [Group G]
    (hn : (⊤ : Subgroup G).lowerCentralSeries (n+1) = ⊥)
    (u : Fin (n+1) → G) (i : Fin (n+1)) (x y : G) :
    nilrotationBracketWord n (Function.update u i (x*y)) =
      nilrotationBracketWord n (Function.update u i x) *
        nilrotationBracketWord n (Function.update u i y) := by
  induction n generalizing G with
  | zero =>
    rw [Fin.eq_zero i]
    simp only [nilrotationBracketWord, Function.update_self]
  | succ n ih =>
    let C := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    have hC : C ≤ Subgroup.center G := nilrotation_last_lowerCentral_le_center (n+1) hn
    have hcom (g : G) (b : (⊤ : Subgroup G).lowerCentralSeries n) : ⁅g, (b : G)⁆ ∈ C := by
      change ⁅g, (b : G)⁆ ∈ ⁅(⊤ : Subgroup G).lowerCentralSeries n, (⊤ : Subgroup G)⁆
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.2
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [nilrotationBracketWord_update_zero]
      let b : (⊤ : Subgroup G).lowerCentralSeries n :=
        ⟨nilrotationBracketWord n (Fin.tail u), nilrotationBracketWord_mem_lowerCentral n _⟩
      rw [commutatorElement_mul_left_eq_conj_mul]
      have he := (Subgroup.mem_center_iff.mp (hC (hcom y b))) x
      change x * ⁅y, (b : G)⁆ = ⁅y, (b : G)⁆ * x at he
      change MulAut.conj x ⁅y, (b : G)⁆ * ⁅x, (b : G)⁆ = _
      rw [MulAut.conj_apply, he, mul_assoc _ x, mul_inv_cancel, mul_one]
      exact Subgroup.mem_center_iff.mp (hC (hcom x b)) _
    · simp only [nilrotationBracketWord_update_succ]
      let q := QuotientGroup.mk' C
      have hq : (⊤ : Subgroup (G ⧸ C)).lowerCentralSeries (n+1) = ⊥ := by
        have ht : (⊤ : Subgroup G).map q = ⊤ :=
          Subgroup.map_top_of_surjective q QuotientGroup.mk_surjective
        rw [← ht, ← Subgroup.map_lowerCentralSeries]
        exact le_antisymm (Subgroup.map_le_iff_le_comap.mpr fun b hb ↦
          Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hb)) bot_le
      have hupdate (z : G) : q ∘ Function.update (Fin.tail u) j z =
          Function.update (q ∘ Fin.tail u) j (q z) := by
        funext v
        by_cases hv : v = j
        · subst v; simp
        · simp [Function.update_of_ne hv]
      let w (z : G) := nilrotationBracketWord n (Function.update (Fin.tail u) j z)
      have hw : q (w (x*y)) = q (w x * w y) := by
        simp only [w, map_mul, map_nilrotationBracketWord, hupdate]
        exact ih hq (q ∘ Fin.tail u) j (q x) (q y)
      let c := (w x * w y)⁻¹ * w (x*y)
      have hc : c ∈ C := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q ((w x * w y)⁻¹ * w (x*y)) = 1
        rw [map_mul, map_inv, hw, inv_mul_cancel]
      have he : w (x*y) = (w x * w y) * c := by
        unfold c
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      have hcc : ⁅u 0, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_center_iff.mp (hC hc)) (u 0))
      change ⁅u 0, w (x*y)⁆ = ⁅u 0, w x⁆ * ⁅u 0, w y⁆
      have he' : ⁅u 0, w (x*y)⁆ = ⁅u 0, w x * w y⁆ := by
        rw [he, commutatorElement_mul_right_eq_mul_conj, hcc, mul_one, mul_assoc,
          mul_inv_cancel, mul_one]
      rw [he', commutatorElement_mul_right_eq_mul_conj]
      have hb := hcom (u 0) ⟨w y, nilrotationBracketWord_mem_lowerCentral n _⟩
      rw [mul_assoc _ (w x), Subgroup.mem_center_iff.mp (hC hb) (w x)]
      change ⁅u 0, w x⁆ * (⁅u 0, w y⁆ * w x) * (w x)⁻¹ = _
      simp only [mul_assoc, mul_inv_cancel, mul_one]

end Mixing
