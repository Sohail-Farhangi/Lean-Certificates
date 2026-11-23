/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRigid
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Int.Interval

/-!
# The lower-density obstruction in Example 4.6

Arbitrarily long gaps provide a Følner sequence with density zero,
contradicting lower Banach density one. Consequently the bounded-gaps
obstruction applies to any strongly rigid nonzero vector.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter
open scoped Topology

/-- The integer interval from `a` through `a + n`, inclusive. -/
def window (a : ℤ) (n : ℕ) : Finset ℤ := Finset.Icc a (a + (n : ℤ))

@[simp] theorem window_card (a : ℤ) (n : ℕ) : (window a n).card = n + 1 := by
  rw [window, Int.card_Icc]
  have heq : a + (n : ℤ) + 1 - a = (n + 1 : ℕ) := by omega
  rw [heq]
  rfl

theorem image_window (a z : ℤ) (n : ℕ) :
    (window a n).image (z + ·) = window (z + a) n := by
  ext x
  simp only [window, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    constructor <;> omega
  · rintro ⟨hx, hx'⟩
    exact ⟨x - z, ⟨by omega, by omega⟩, by omega⟩

theorem window_deficit (a z : ℤ) (n : ℕ) :
    (window a n \ (window a n).image (z + ·)).card ≤ z.natAbs := by
  rw [image_window, Finset.card_sdiff, Finset.inter_comm, window_card]
  have hlow : n + 1 - z.natAbs ≤ ((window a n) ∩ (window (z + a) n)).card := by
    let core := Finset.Icc (max a (z + a)) (min (a + (n : ℤ)) (z + a + (n : ℤ)))
    have hsub : core ⊆ window a n ∩ window (z + a) n := by
      intro x hx
      have hx' := Finset.mem_Icc.1 hx
      exact Finset.mem_inter.2 ⟨Finset.mem_Icc.2
        ⟨(le_max_left _ _).trans hx'.1, hx'.2.trans (min_le_left _ _)⟩,
        Finset.mem_Icc.2 ⟨(le_max_right _ _).trans hx'.1, hx'.2.trans (min_le_right _ _)⟩⟩
    apply le_trans ?_ (Finset.card_mono hsub)
    simp only [core, Int.card_Icc]
    by_cases h : 0 ≤ z
    · rw [max_eq_right (by omega), min_eq_left (by omega)]
      omega
    · rw [max_eq_left (by omega), min_eq_right (by omega)]
      omega
  omega

/-- A strong left Følner sequence of finite nonempty subsets of the integers.
Translations are bijections, so the one-sided deficit also bounds the
symmetric difference. -/
def IntegerFolner (F : ℕ → Finset ℤ) : Prop :=
  (∀ n, (F n).Nonempty) ∧ ∀ z : ℤ,
    Tendsto (fun n ↦ ((F n \ (F n).image (z + ·)).card : ℝ) / (F n).card) atTop (𝓝 0)

theorem window_integerFolner (a : ℕ → ℤ) : IntegerFolner (fun n ↦ window (a n) n) := by
  refine ⟨fun n ↦ ⟨a n, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩, fun z ↦ ?_⟩
  have hshift : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have htop := (tendsto_const_div_atTop_nhds_zero_nat (z.natAbs : ℝ)).comp hshift
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Eventually.of_forall fun _ ↦ div_nonneg (by positivity) (by positivity)) ?_
  refine Eventually.of_forall fun n ↦ ?_
  dsimp only [Function.comp_apply]
  rw [window_card]
  exact div_le_div_of_nonneg_right (by exact_mod_cast window_deficit (a n) z n) (by positivity)

open Classical in
/-- Proportion of a set in a finite counting sample. -/
noncomputable def sampleDensity (A : Set ℤ) (F : Finset ℤ) : ℝ :=
  (F.filter fun x ↦ x ∈ A).card / (F.card : ℝ)

/-- Density one along every left Følner sequence is enough to force bounded
gaps. Lower Banach density one in the paper entails this hypothesis. -/
theorem boundedGaps_of_density_one_on_every_Folner (A : Set ℤ)
    (hA : ∀ F : ℕ → Finset ℤ, IntegerFolner F →
      Tendsto (fun n ↦ sampleDensity A (F n)) atTop (𝓝 1)) : BoundedGaps A := by
  classical
  by_contra hG
  unfold BoundedGaps at hG
  push Not at hG
  choose a ha using hG
  have hzero (n : ℕ) : sampleDensity A (window (a n) n) = 0 := by
    have hfilter : ((window (a n) n).filter fun x ↦ x ∈ A) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro x hx
      obtain ⟨hx', hxA⟩ := Finset.mem_filter.1 hx
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.1 hx'
      have habs : (((x - a n).toNat : ℕ) : ℤ) = x - a n := Int.toNat_of_nonneg (by omega)
      let l : Fin (n + 1) := ⟨(x - a n).toNat, by omega⟩
      have heq : a n + (l.val : ℤ) = x := by dsimp [l]; omega
      exact ha n l (heq ▸ hxA)
    simp [sampleDensity, hfilter]
  have hlim := hA _ (window_integerFolner a)
  simp only [hzero] at hlim
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- The density-one conclusion of Example 4.6, conditional on the strong
rigidity hypothesis of the given unitary family. -/
theorem not_weakDecayOn_of_rigid_lowerBanachDensityOne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (V : ℤ → E ≃ₗᵢ[ℂ] E) (hmul : ∀ a b, V (a + b) = (V b).trans (V a))
    (ξ : E) (hξ : ξ ≠ 0) (u : ℕ → ℤ) (hu : Tendsto u atTop cofinite)
    (hstrong : Tendsto (fun k ↦ V (u k) ξ) atTop (𝓝 ξ))
    (A : Set ℤ) (hA : ∀ F : ℕ → Finset ℤ, IntegerFolner F →
      Tendsto (fun n ↦ sampleDensity A (F n)) atTop (𝓝 1)) :
    ¬ WeakDecayOn (fun s ↦ V s ξ) A :=
  not_weakDecayOn_of_rigid_boundedGaps V hmul ξ hξ u hu hstrong A
    (boundedGaps_of_density_one_on_every_Folner A hA)

end JdLG.PaperExamplesRigid
