/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconScaleDecomposition
public import Mixing.ChaconAllHeightLimits

/-! # Reduction of free power limits to normalized natural times -/

@[expose] public section

open Filter Set
open scoped Topology

namespace Mixing

/-- Embed a natural time in the integer time group. -/
def chaconNaturalTime (j : ℕ) : Multiplicative ℤ := Multiplicative.ofAdd (j : ℤ)

theorem chaconNaturalTime_tendsto_cofinite : Tendsto chaconNaturalTime atTop cofinite := by
  have h : Function.Injective chaconNaturalTime := by
    intro i j hij
    exact Int.ofNat_inj.mp (congrArg Multiplicative.toAdd hij)
  simpa only [Nat.cofinite_eq_atTop] using h.tendsto_cofinite

/-- A free ultrafilter concentrated on nonnegative times is the image of a
free ultrafilter on the natural numbers. -/
theorem chaconNaturalTime_lift (p : Ultrafilter (Multiplicative ℤ))
    (hp : p ∈ freeUltrafilters (Multiplicative ℤ))
    (hpos : {g : Multiplicative ℤ | 0 ≤ g.toAdd} ∈ p) :
    ∃ q : Ultrafilter ℕ, (q : Filter ℕ) ≤ atTop ∧ q.map chaconNaturalTime = p := by
  let t (g : Multiplicative ℤ) := g.toAdd.toNat
  let q := p.map t
  refine ⟨q, ?_, ?_⟩
  · change Tendsto t (p : Filter (Multiplicative ℤ)) atTop
    refine tendsto_atTop.2 (fun n ↦ ?_)
    have hinj : Function.Injective (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      fun _ _ h ↦ Multiplicative.ext h
    have hB : (Multiplicative.toAdd ⁻¹' Icc (0 : ℤ) (n : ℤ)).Finite :=
      (Set.finite_Icc _ _).preimage hinj.injOn
    filter_upwards [hpos, hp hB.compl_mem_cofinite] with g hg hng
    change 0 ≤ g.toAdd at hg
    have hng' : ¬(0 ≤ g.toAdd ∧ g.toAdd ≤ (n : ℤ)) := hng
    have hcast : (t g : ℤ) = g.toAdd := Int.toNat_of_nonneg hg
    omega
  · apply Ultrafilter.coe_inj.mp
    rw [Ultrafilter.coe_map, Ultrafilter.coe_map, Filter.map_map]
    have h : chaconNaturalTime ∘ t =ᶠ[(p : Filter (Multiplicative ℤ))] id := by
      filter_upwards [hpos] with g h
      exact Multiplicative.ext (Int.toNat_of_nonneg h)
    rw [Filter.map_congr h, Filter.map_id]

/-- Up to inversion, free integer time ultrafilters are lifted from
natural times. -/
theorem chaconNaturalTime_lift_or_inverse (p : Ultrafilter (Multiplicative ℤ))
    (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    ∃ q : Ultrafilter ℕ, (q : Filter ℕ) ≤ atTop ∧
      (q.map chaconNaturalTime = p ∨ q.map chaconNaturalTime = inverseUltrafilter p) := by
  let S : Set (Multiplicative ℤ) := {g | 0 ≤ g.toAdd}
  rcases p.mem_or_compl_mem S with h | h
  · obtain ⟨q, hq, he⟩ := chaconNaturalTime_lift p hp h
    exact ⟨q, hq, Or.inl he⟩
  · have hInv : Function.Injective (Inv.inv : Multiplicative ℤ → Multiplicative ℤ) :=
      inv_injective
    have hp' : inverseUltrafilter p ∈ freeUltrafilters (Multiplicative ℤ) :=
      hInv.tendsto_cofinite.mono_left hp
    have h' : S ∈ inverseUltrafilter p := by
      change Inv.inv ⁻¹' S ∈ (p : Filter (Multiplicative ℤ))
      refine mem_of_superset h fun g hg ↦ ?_
      change ¬(0 ≤ g.toAdd) at hg
      change 0 ≤ -g.toAdd
      omega
    obtain ⟨q, hq, he⟩ := chaconNaturalTime_lift (inverseUltrafilter p) hp' h'
    exact ⟨q, hq, Or.inr he⟩

/-- The scale at a fixed depth below the largest Chacon tower height
smaller than the time. -/
noncomputable def chaconScaleLevel (r j : ℕ) : ℕ := chaconHeightScale j - r

/-- In the integral branch there is a fixed positive height multiple and
a signed sub-height error. In the other branch the successive quotient
coefficients are the ternary prefixes of a nonintegral limiting ratio. -/
theorem chaconNaturalTime_scale_dichotomy (q : Ultrafilter ℕ) (hq : (q : Filter ℕ) ≤ atTop) :
    (∃ (m : ℕ) (n : ℕ → ℕ) (s : ℕ → ℤ), 0 < m ∧ Tendsto n q atTop ∧
      Tendsto (fun j ↦ ((s j).natAbs : ℝ) / chaconTowerHeight (n j)) q (𝓝 0) ∧
      ∀ j : ℕ, (j : ℤ) = (m * chaconTowerHeight (n j) : ℕ) + s j) ∨
    (∃ τ ∈ Icc (1 : ℝ) 3, (∀ r m : ℕ, τ * 3 ^ r ≠ (m : ℝ)) ∧
      ∀ r : ℕ, Tendsto (chaconScaleLevel r) q atTop ∧
        ∀ᶠ j in (q : Filter ℕ), j / chaconTowerHeight (chaconScaleLevel r j) =
          chaconScaleCoefficient τ r) := by
  have hid : Tendsto (fun j : ℕ ↦ j) q atTop := hq
  obtain ⟨τ, hτ, hlim⟩ := exists_chaconScaleRatio_tendsto q hid
  by_cases hInt : ∃ r m : ℕ, τ * 3 ^ r = (m : ℝ)
  · obtain ⟨r, m, hm⟩ := hInt
    have hp : m = chaconScaleCoefficient τ r := by
      rw [chaconScaleCoefficient, hm, Nat.floor_natCast]
    left
    refine ⟨m, chaconScaleLevel r, fun j ↦ (j : ℤ) - (m * chaconTowerHeight
      (chaconScaleLevel r j) : ℕ), ?_, tendsto_chaconScale_index_sub hid r, ?_, ?_⟩
    · rw [hp]
      exact chaconScaleCoefficient_pos hτ.1 r
    · simpa only [chaconScaleLevel, Nat.cast_mul] using
        tendsto_chaconHeight_relative_remainder hid hlim hm
    · intro j
      ring
  · right
    have hNon : ∀ r m : ℕ, τ * 3 ^ r ≠ (m : ℝ) :=
      fun r m h ↦ hInt ⟨r, m, h⟩
    refine ⟨τ, hτ, hNon, fun r ↦ ⟨tendsto_chaconScale_index_sub hid r, ?_⟩⟩
    exact eventually_chaconHeight_div_eq_floor hid (zero_le_one.trans hτ.1) hlim r (hNon r)

end Mixing
