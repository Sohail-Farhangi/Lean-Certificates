/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationSpectralGluing
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

@[expose] public section
noncomputable section
namespace Mixing

open MeasureTheory
open scoped commutatorElement

variable {G K H : Type*} [Group G] [Group K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SecondCountableTopology H]

private theorem verticalPhase_analysis
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (R : K →* (H ≃ₗᵢ[ℂ] H)) (a : G)
    (hComm : ∀ (k : K) (g : G), Commute (R k) (ρ g))
    {C : Subgroup G} (ι : C → K) (hι : ∀ c : C, R (ι c) = ρ (c : G))
    (χ : K →* Circle)
    (hPhase : ∀ s : UnitAddCircle, ∃ (b : G) (c : C),
      ⁅a, b⁆ = (c : G) ∧ χ (ι c) = AddCircle.toCircle s)
    (x : H) (hx : ∀ k, R k x = (χ k : ℂ) • x) (hx0 : x ≠ 0) :
    ((∃ y : H, (∀ k, R k y = (χ k : ℂ) • y) ∧
        dualVectorSpectralMeasure (ρ.comp (integerPowersHom a)) y = integerDualHaar) ∧
      ∀ z : H, (∀ k, R k z = (χ k : ℂ) • z) →
        dualVectorSpectralMeasure (ρ.comp (integerPowersHom a)) z ≪ integerDualHaar) ∧
    (∀ p ∈ freeUltrafilters (Multiplicative ℤ),
      ultrafilterOperator (ρ.comp (integerPowersHom a)) p x = 0) := by
  let χ' := χ.comp (⊤ : Subgroup K).subtype
  let W := centralCharacterSubmodule R χ'
  have hW : IsInvariantSubmodule ρ W := by
    intro g y hy k
    change R (k : K) (ρ g y) = (χ (k : K) : ℂ) • ρ g y
    change (R (k : K) * ρ g) y = _
    rw [(hComm k g).eq]
    change ρ g (R (k : K) y) = _
    rw [show R (k : K) y = (χ (k : K) : ℂ) • y from hy k, map_smul]
  let T := unitarySubmoduleAction ρ W hW
  let U := T.comp (integerPowersHom a)
  let y : W := ⟨x, fun k ↦ hx k⟩
  let : CompleteSpace W := (centralCharacterSubmodule_isClosed R χ').completeSpace_coe
  let : Nontrivial W := ⟨⟨y, 0, fun h ↦ hx0 (congrArg Subtype.val h)⟩⟩
  have hMod (s : UnitAddCircle) : ∃ B : W ≃ₗᵢ[ℂ] W, ∀ (n : ℤ) (w : W),
      U (Multiplicative.ofAdd n) (B w) =
        fourier n s • B (U (Multiplicative.ofAdd n) w) := by
    obtain ⟨b, c, hc, hcχ⟩ := hPhase s
    refine ⟨T b, fun n w ↦ ?_⟩
    apply Subtype.ext
    change ρ (a^n) (ρ b w) = fourier n s • ρ b (ρ (a^n) w)
    have hab : a*b = (c : G)*(b*a) := by rw [← hc, commutatorElement_def]; group
    have h₁ : ρ a * ρ b = ρ b * ρ a * ρ (c : G) := by
      calc
        ρ a * ρ b = ρ (a*b) := (map_mul ρ _ _).symm
        _ = ρ (c : G) * (ρ b * ρ a) := by rw [hab, map_mul, map_mul]
        _ = ρ b * ρ a * ρ (c : G) := by
          rw [← hι c]
          exact ((hComm (ι c) b).mul_right (hComm (ι c) a)).eq
    have h₂ := mul_eq_mul_commuting_of_zpow
      (show Commute (ρ a) (ρ (c : G)) from hι c ▸ (hComm (ι c) a).symm) h₁ n
    rw [← map_zpow ρ a n, ← map_zpow ρ (c : G) n] at h₂
    have h₃ : ρ ((c : G)^n) w = fourier n s • (w : H) := by
      have hh := w.property (⟨(ι c)^n, Subgroup.mem_top _⟩ : (⊤ : Subgroup K))
      change R ((ι c)^n) w = ((χ ((ι c)^n) : Circle) : ℂ) • (w : H) at hh
      rw [map_zpow R, hι c, ← map_zpow ρ, map_zpow χ, hcχ] at hh
      rw [fourier_apply, AddCircle.toCircle_zsmul]
      exact hh
    calc
      _ = (ρ (a^n) * ρ b) w := rfl
      _ = (ρ b * ρ (a^n) * ρ ((c : G)^n)) w := congrArg (fun V : H ≃ₗᵢ[ℂ] H ↦ V w) h₂
      _ = _ := by
        change ρ b (ρ (a^n) (ρ ((c : G)^n) w)) = _
        rw [h₃, map_smul, map_smul]
  constructor
  · obtain ⟨v, hvMax, hv⟩ := exists_haar_maximal_spectral_vector U hMod
    have hLift (w : W) : dualVectorSpectralMeasure (ρ.comp (integerPowersHom a)) (w : H) =
        dualVectorSpectralMeasure U w :=
      dualVectorSpectralMeasure_eq_of_isometric_intertwiner U (ρ.comp (integerPowersHom a))
        W.subtypeₗᵢ (fun _ _ ↦ rfl) w
    refine ⟨⟨v, fun k ↦ v.2 ⟨k, Subgroup.mem_top _⟩, (hLift v).trans hv⟩, ?_⟩
    intro z hz
    let w : W := ⟨z, fun k ↦ hz k⟩
    change dualVectorSpectralMeasure (ρ.comp (integerPowersHom a)) (w : H) ≪ integerDualHaar
    rw [hLift, ← hv]
    exact hvMax w
  · intro p hp
    have hZero := (isStronglyMixing_iff_isUMixing_free U).mp
      (isStronglyMixing_of_full_modulations U hMod) p hp
    have hIn : Intertwines U (ρ.comp (integerPowersHom a)) W.subtypeL := fun _ _ ↦ rfl
    have he := hIn.ultrafilter p y
    rw [hZero, zero_apply, map_zero] at he
    exact he.symm

/-- A nonzero vertical character space with full time-commutator phases realizes
Haar as a vector spectral measure. Every vector in the character space has
spectral measure absolutely continuous with respect to the same Haar measure. -/
theorem verticalPhase_dualVectorSpectralMeasure
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (R : K →* (H ≃ₗᵢ[ℂ] H)) (a : G)
    (hComm : ∀ (k : K) (g : G), Commute (R k) (ρ g))
    {C : Subgroup G} (ι : C → K) (hι : ∀ c : C, R (ι c) = ρ (c : G))
    (χ : K →* Circle)
    (hPhase : ∀ s : UnitAddCircle, ∃ (b : G) (c : C),
      ⁅a, b⁆ = (c : G) ∧ χ (ι c) = AddCircle.toCircle s)
    (x : H) (hx : ∀ k, R k x = (χ k : ℂ) • x) (hx0 : x ≠ 0) :
    (∃ y : H, (∀ k, R k y = (χ k : ℂ) • y) ∧
      dualVectorSpectralMeasure (ρ.comp (integerPowersHom a)) y = integerDualHaar) ∧
    ∀ z : H, (∀ k, R k z = (χ k : ℂ) • z) →
      dualVectorSpectralMeasure (ρ.comp (integerPowersHom a)) z ≪ integerDualHaar :=
  (verticalPhase_analysis ρ R a hComm ι hι χ hPhase x hx hx0).1

/-- A vertical character space has weak decay when every circle phase is
realized by a time commutator. Commuting actions suffice at a quotient stage. -/
theorem ultrafilterOperator_zero_of_verticalPhase
    (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (R : K →* (H ≃ₗᵢ[ℂ] H)) (a : G)
    (hComm : ∀ (k : K) (g : G), Commute (R k) (ρ g))
    {C : Subgroup G} (ι : C → K) (hι : ∀ c : C, R (ι c) = ρ (c : G))
    (χ : K →* Circle)
    (hPhase : ∀ s : UnitAddCircle, ∃ (b : G) (c : C),
      ⁅a, b⁆ = (c : G) ∧ χ (ι c) = AddCircle.toCircle s)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : p ∈ freeUltrafilters (Multiplicative ℤ))
    (x : H) (hx : ∀ k, R k x = (χ k : ℂ) • x) :
    ultrafilterOperator (ρ.comp (integerPowersHom a)) p x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · exact (verticalPhase_analysis ρ R a hComm ι hι χ hPhase x hx hx0).2 p hp

end Mixing
