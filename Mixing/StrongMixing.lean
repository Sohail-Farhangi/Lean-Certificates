/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralDisjointness

/-! # Strong mixing and its spectral disjointness criterion -/

@[expose] public section

open Filter Set
open scoped Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The free ultrafilters, written `G*` in the paper. -/
def freeUltrafilters (G : Type*) : Set (Ultrafilter G) := {p | (p : Filter G) ≤ cofinite}

/-- The weak coefficients converge to zero along every sequence escaping finite sets. -/
def IsStronglyMixing : Prop :=
  ∀ g : ℕ → G, Tendsto g atTop cofinite → ∀ x y : H,
    Tendsto (fun n => inner ℂ x (U (g n) y)) atTop (𝓝 0)

/-- Testing a cofinite limit on sequences escaping finite sets. -/
theorem tendsto_cofinite_iff_forall_escaping_sequences {G X : Type*} [TopologicalSpace X]
    (f : G → X) (x : X) :
    Tendsto f cofinite (𝓝 x) ↔ ∀ g : ℕ → G, Tendsto g atTop cofinite →
      Tendsto (f ∘ g) atTop (𝓝 x) := by
  constructor
  · intro h g hg
    exact h.comp hg
  · intro h
    by_contra hn
    obtain ⟨S, hS, hbad⟩ := not_tendsto_iff_exists_frequently_notMem.mp hn
    have hInf : {g | f g ∉ S}.Infinite := frequently_cofinite_iff_infinite.mp hbad
    let e := Set.Infinite.natEmbedding _ hInf
    let g : ℕ → G := fun n => (e n : G)
    have hg : Function.Injective g := Subtype.val_injective.comp e.injective
    have hlim := h g (Nat.cofinite_eq_atTop ▸ hg.tendsto_cofinite)
    have hEv : ∀ᶠ n in atTop, f (g n) ∈ S := hlim.eventually hS
    obtain ⟨n, hn⟩ := hEv.exists
    exact (e n).property hn

theorem isStronglyMixing_iff_isUMixing_free :
    IsStronglyMixing U ↔ IsUMixing U (freeUltrafilters G) := by
  constructor
  · intro h p hp
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro x
    have hC := (tendsto_cofinite_iff_forall_escaping_sequences
      (fun g => inner ℂ x (U g y)) 0).mpr fun g hg => h g hg x y
    simpa only [zero_apply, inner_zero_right] using
      tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p x y) (hC.mono_left hp)
  · intro h g hg x y
    have hC : Tendsto (fun a => inner ℂ x (U a y)) cofinite (𝓝 0) := by
      apply (Filter.tendsto_iff_ultrafilter _ _ _).mpr
      intro p hp
      have hlim := tendsto_ultrafilterOperator_coeff U p x y
      rw [h p hp, zero_apply, inner_zero_right] at hlim
      exact hlim
    exact hC.comp hg

/-- The iterates `Δ^n` in Proposition 6(i). -/
def ultrafilterDeltaIterate (P : Set (Ultrafilter G)) : ℕ → Set (Ultrafilter G)
  | 0 => P
  | n + 1 => ultrafilterDelta (ultrafilterDeltaIterate P n)

/-- Proposition 6(i), strong mixing can be tested using any iterate of Δ. -/
theorem isStronglyMixing_iff_isUMixing_deltaIterate (n : ℕ) :
    IsStronglyMixing U ↔ IsUMixing U (ultrafilterDeltaIterate (freeUltrafilters G) n) := by
  induction n with
  | zero => exact isStronglyMixing_iff_isUMixing_free U
  | succ n ih => exact ih.trans (isUMixing_iff_ultrafilterDelta U _)

variable [IsMulCommutative G]

/-- Proposition 6(ii), strong mixing can be tested on products of any fixed
positive number `n+1` of free ultrafilters. -/
theorem isStronglyMixing_iff_isUMixing_freeProducts (n : ℕ) :
    IsStronglyMixing U ↔ IsUMixing U (ultrafilterProductsSucc (freeUltrafilters G) n) :=
  (isStronglyMixing_iff_isUMixing_free U).trans (isUMixing_iff_ultrafilterProductsSucc U _ n)

universe u

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable (U₁ : G →* (H₁ ≃ₗᵢ[ℂ] H₁))

/-- Corollary 5(i). Generation by the free ultrafilters is equivalent to
spectral disjointness from all strongly mixing actions. -/
theorem generated_free_iff_spectrallyDisjoint_all_stronglyMixing :
    IsUGenerated U₁ (freeUltrafilters G) ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsStronglyMixing V → SpectrallyDisjoint U₁ V := by
  constructor
  · intro h K _ _ _ V hV
    have hd := (theorem3_1 U₁ (freeUltrafilters G)).2.mp h
    exact @hd K _ _ _ V ((isStronglyMixing_iff_isUMixing_free V).mp hV)
  · intro h
    apply (theorem3_1 U₁ (freeUltrafilters G)).2.mpr
    intro K _ _ _ V hV
    exact @h K _ _ _ V ((isStronglyMixing_iff_isUMixing_free V).mpr hV)

omit [IsMulCommutative G] in
/-- Corollary 5(ii). An injective ultrafilter operator is a sufficient condition
for disjointness from every action mixing along that ultrafilter. -/
theorem spectrallyDisjoint_of_ultrafilterOperator_injective {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : G →* (K ≃ₗᵢ[ℂ] K)) (p : Ultrafilter G)
    (hU : Function.Injective (ultrafilterOperator U p)) (hV : ultrafilterOperator V p = 0) :
    SpectrallyDisjoint U V := by
  intro J hJ
  apply ContinuousLinearMap.ext
  intro x
  apply hU
  rw [← hJ.ultrafilter, hV, zero_apply, map_zero, zero_apply, map_zero]

end Mixing
