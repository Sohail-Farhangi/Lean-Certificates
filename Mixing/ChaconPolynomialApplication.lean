/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconWeakMixing
public import Mixing.PolynomialLimits
public import Mixing.InjectiveLimits

/-! # Example 2, applied to the concrete Chacon tower -/

@[expose] public section

open MeasureTheory Filter Set Polynomial
open scoped Classical Topology InnerProductSpace

namespace Mixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem power_eigenvector (E : H ≃ₗᵢ[ℂ] H) (v : H) (z : ℂ) (h : E v = z • v) :
    ∀ n : ℕ, (E^n) v = z^n • v := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change E ((E^n) v) = _
    rw [ih, map_smul, h, smul_smul, pow_succ]

/-- Weak mixing of an integer action rules out eigenvectors of its generator. -/
theorem generator_sub_scalar_injective_of_weaklyMixing
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) (hWeak : IsWeaklyMixing U) (z : ℂ) :
    Function.Injective ((U (Multiplicative.ofAdd 1) : H →L[ℂ] H) -
      algebraMap ℂ (H →L[ℂ] H) z) := by
  let : Countable (Multiplicative ℤ) := by change Countable ℤ; infer_instance
  let r := Multiplicative.ofAdd (1 : ℤ)
  let E := U r
  let A : H →L[ℂ] H := (E : H →L[ℂ] H) - algebraMap ℂ (H →L[ℂ] H) z
  intro x y hxy
  let v := x - y
  have hvA : A v = 0 := by
    change A (x-y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hvE : E v = z • v := sub_eq_zero.mp hvA
  by_contra hne
  have hvne : v ≠ 0 := sub_ne_zero.mpr hne
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hz : ‖z‖ = 1 := by
    have h := congrArg norm hvE
    rw [E.norm_map, norm_smul] at h
    exact mul_right_cancel₀ hvpos.ne' (by simpa only [one_mul] using h.symm)
  have hnz : z ≠ 0 := fun h ↦ by simp [h] at hz
  have hvInv : E⁻¹ v = z⁻¹ • v := by
    apply E.injective
    change E (E.symm v) = E (z⁻¹ • v)
    rw [E.apply_symm_apply, map_smul, hvE, smul_smul, inv_mul_cancel₀ hnz, one_smul]
  have hg (g : Multiplicative ℤ) : U g v = z^g.toAdd • v := by
    have he : r ^ g.toAdd = g := by
      change g.toAdd • (1 : ℤ) = g.toAdd
      simp
    have hg (n : ℤ) : (E^n) v = z^n • v := by
      cases n with
      | ofNat n =>
        simpa only [Int.ofNat_eq_natCast, zpow_natCast] using power_eigenvector E v z hvE n
      | negSucc n =>
        have hn : (Int.negSucc n : ℤ) = -((n+1 : ℕ) : ℤ) := by omega
        rw [hn, zpow_neg, zpow_natCast, ← inv_pow, zpow_neg, zpow_natCast, ← inv_pow]
        exact power_eigenvector E⁻¹ v z⁻¹ hvInv _
    calc
      U g v = U (r ^ g.toAdd) v := congrArg (fun t ↦ U t v) he.symm
      _ = (E ^ g.toAdd) v := by rw [map_zpow]
      _ = z^g.toAdd • v := hg _
  have hcoeff (g : Multiplicative ℤ) : ‖⟪v, U g v⟫_ℂ‖ = ‖v‖^2 := by
    rw [hg, inner_smul_right, norm_mul, norm_zpow, hz, one_zpow, one_mul,
      inner_self_eq_norm_sq_to_K]
    rw [norm_pow]
    change ‖((‖v‖ : ℝ) : ℂ)‖ ^ 2 = ‖v‖ ^ 2
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v)]
  obtain ⟨F, hF⟩ := exists_isFolnerSequence (G := Multiplicative ℤ)
  have havg := hWeak v F hF
  have hconst (n : ℕ) : (∑ g ∈ F n, ‖⟪v, U g v⟫_ℂ‖) / (F n).card = ‖v‖^2 := by
    simp only [hcoeff, Finset.sum_const, nsmul_eq_mul]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast (hF.1 n).card_ne_zero)
  simp_rw [hconst] at havg
  have hzero := tendsto_nhds_unique havg tendsto_const_nhds
  exact (pow_ne_zero _ hvpos.ne') hzero.symm

/-- The weak-limit classification stated in Example 2, restricted to the
mean-zero space and with Laurent monomials factored off. This is the cited
classification input, rather than a theorem of this module. -/
def HasChaconPolynomialLimits : Prop :=
  let U := chaconTowerSystem.koopmanZeroRep
  ∀ p : Ultrafilter (Multiplicative ℤ), p ∈ freeUltrafilters (Multiplicative ℤ) →
    ultrafilterOperator U p = 0 ∨
      ∃ (b : ℤ) (Q : ℂ[X]), Q ≠ 0 ∧ ultrafilterOperator U p =
        (U (Multiplicative.ofAdd b) : _ →L[ℂ] _) *
          aeval (U (Multiplicative.ofAdd 1) : _ →L[ℂ] _) Q

/-- The mixing-or-generation conclusion of Example 2 for the concrete tower.
Only the weak-limit classification is supplied as an input. -/
theorem example2_chaconTower_of_polynomial_classification
    (hClass : HasChaconPolynomialLimits) (p : Ultrafilter (Multiplicative ℤ))
    (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    chaconTowerSystem.IsUMixing {p} ∨
      (chaconTowerSystem.generatedSigma {p} = (inferInstance : MeasurableSpace (ChaconOdometer × Bool)) ∧
        ∀ {Y : Type*} [MeasurableSpace Y] (T : System (Multiplicative ℤ) Y), T.IsUMixing {p} →
          SpectrallyDisjoint chaconTowerSystem.koopmanZeroRep T.koopmanZeroRep) := by
  let U := chaconTowerSystem.koopmanZeroRep
  rcases hClass p hp with h | ⟨b, Q, hQ, hlim⟩
  · left
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact h
  · right
    have hinj : Function.Injective (ultrafilterOperator U p) := by
      rw [hlim]
      exact (U (Multiplicative.ofAdd b)).injective.comp
        (aeval_injective_of_no_eigenvectors _ (generator_sub_scalar_injective_of_weaklyMixing U
          chaconTower_isWeaklyMixing) hQ)
    exact chaconTowerSystem.generated_and_spectrallyDisjoint_of_injective_limit p hinj

end Mixing
