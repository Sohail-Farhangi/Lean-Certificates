/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconAllHeightLimits
public import Mixing.ChaconDecayDigits
public import Mixing.ChaconDecayFunctionalCalculus

/-! # Chacon polynomial decay on the mean-zero Koopman space -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

local notation "𝓗" => meanZero chaconTowerSystem.measure
local notation "𝓤" => chaconTowerSystem.koopmanZeroRep

/-- The same height polynomial for positive and negative height limits.
The Boolean flag reverses the direction by taking the adjoint. -/
noncomputable def chaconDecayOperator (reverse : Bool) (m : ℕ) : 𝓗 →L[ℂ] 𝓗 :=
  if reverse then star (chaconHeightPolynomialOperatorZero m)
  else chaconHeightPolynomialOperatorZero m

section SpectralPolynomials

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))

local notation "Σᵁ" => RepresentationSpectrum U

private noncomputable def chaconDecaySpectralPositive (m : ℕ) : C(Σᵁ, ℂ) :=
  Polynomial.aeval (chaconDecayParameter U) ((chaconPolynomial m).map (algebraMap ℝ ℂ))

private theorem chaconDecaySpectralPositive_apply (m : ℕ) (z : Σᵁ) :
    chaconDecaySpectralPositive U m z = chaconDecayValue (chaconDecayParameter U z) m := by
  change (ContinuousMap.evalStarAlgHom ℂ ℂ z).toAlgHom (chaconDecaySpectralPositive U m) = _
  rw [chaconDecaySpectralPositive,
    ← Polynomial.aeval_algHom_apply (ContinuousMap.evalStarAlgHom ℂ ℂ z).toAlgHom,
    Polynomial.aeval_def, Polynomial.eval₂_map]
  rfl

private theorem spectralCalculus_chaconDecaySpectralPositive (m : ℕ) :
    spectralCalculus U (chaconDecaySpectralPositive U m) =
      Polynomial.aeval (linearRepresentation U (Multiplicative.ofAdd (-1)))
        ((chaconPolynomial m).map (algebraMap ℝ ℂ)) := by
  change (spectralCalculus U).toAlgHom (Polynomial.aeval (chaconDecayParameter U)
    ((chaconPolynomial m).map (algebraMap ℝ ℂ))) = _
  rw [← Polynomial.aeval_algHom_apply (spectralCalculus U).toAlgHom, chaconDecayParameter]
  change Polynomial.aeval (spectralCalculus U (spectralCoefficient U (Multiplicative.ofAdd (-1))))
    _ = _
  rw [spectralCalculus_spectralCoefficient]

private noncomputable def chaconDecaySpectral (reverse : Bool) (m : ℕ) : C(Σᵁ, ℂ) :=
  if reverse then star (chaconDecaySpectralPositive U m) else chaconDecaySpectralPositive U m

private theorem chaconDecaySpectral_norm_apply (reverse : Bool) (m : ℕ) (z : Σᵁ) :
    ‖chaconDecaySpectral U reverse m z‖ = ‖chaconDecayValue (chaconDecayParameter U z) m‖ := by
  cases reverse <;> simp [chaconDecaySpectral, chaconDecaySpectralPositive_apply, ContinuousMap.star_apply]

private theorem tendsto_spectral_ternary_prefix_zero (hWeak : IsWeaklyMixing U)
    (m : ℕ → ℕ) (d : ℕ → Fin 3)
    (hm : ∀ n, m (n+1) = 3 * m n + (d n).val)
    (hNoZeroTail : ¬ ∃ N, ∀ n ≥ N, d n = 0)
    (hNoTwoTail : ¬ ∃ N, ∀ n ≥ N, d n = 2)
    (adjacent reverse : Bool) (x : H) :
    Tendsto (fun n ↦ spectralCalculus U (chaconDecaySpectral U reverse
      (if adjacent then m n + 1 else m n)) x) atTop (𝓝 0) := by
  let f n := chaconDecaySpectral U reverse (if adjacent then m n + 1 else m n)
  have hnorm (n : ℕ) (z : Σᵁ) : ‖f n z‖ ≤ chaconDecayPair (chaconDecayParameter U z) (m n) := by
    dsimp only [f]
    rw [chaconDecaySpectral_norm_apply]
    cases adjacent
    · exact le_max_left ..
    · exact le_max_right ..
  exact tendsto_chaconDecaySpectralCalculus_zero U hWeak x f
    (fun n z ↦ (hnorm n z).trans (chaconDecayPair_le_one (chaconDecayParameter_norm U z) (m n)))
    (fun z hz ↦ by
      have hh := tendsto_chaconDecayPair_ternary_prefix_zero (chaconDecayParameter_norm U z) hz
        m d hm hNoZeroTail hNoTwoTail
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simp only [sub_zero]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
        (fun _ ↦ norm_nonneg _) (fun n ↦ hnorm n z))

private noncomputable def chaconDecaySpectralProduct (indices : List (Bool × ℕ)) :
    C(Σᵁ, ℂ) :=
  (indices.map fun j ↦ chaconDecaySpectral U j.1 j.2).prod

private theorem chaconDecaySpectralProduct_norm (indices : List (Bool × ℕ))
    (hpos : ∀ j ∈ indices, 0 < j.2) (z : Σᵁ) :
    ‖chaconDecaySpectralProduct U indices z‖ ≤
      (chaconDecayRatio (chaconDecayParameter U z)) ^ indices.length := by
  induction indices with
  | nil => simp [chaconDecaySpectralProduct, ContinuousMap.one_apply]
  | cons j js ih =>
    have hj := chaconDecayValue_norm_le_ratio (chaconDecayParameter_norm U z) _
      (hpos j (List.mem_cons_self ..))
    have hjs := ih (fun k hk ↦ hpos k (List.mem_cons_of_mem _ hk))
    change ‖(chaconDecaySpectral U j.1 j.2 * chaconDecaySpectralProduct U js) z‖ ≤ _
    rw [ContinuousMap.mul_apply, norm_mul, chaconDecaySpectral_norm_apply, List.length_cons, pow_succ']
    exact mul_le_mul hj hjs (norm_nonneg _) (chaconDecayRatio_nonneg _)

private theorem tendsto_spectralProduct_star_zero (hWeak : IsWeaklyMixing U)
    (indices : ℕ → List (Bool × ℕ)) (hpos : ∀ n j, j ∈ indices n → 0 < j.2)
    (hLength : Tendsto (fun n ↦ (indices n).length) atTop atTop) (x : H) :
    Tendsto (fun n ↦ spectralCalculus U (star (chaconDecaySpectralProduct U (indices n))) x) atTop (𝓝 0) := by
  let f n := star (chaconDecaySpectralProduct U (indices n))
  have hb (n : ℕ) (z : Σᵁ) :
      ‖f n z‖ ≤ (chaconDecayRatio (chaconDecayParameter U z)) ^ (indices n).length := by
    simpa only [f, ContinuousMap.star_apply, Complex.star_def, Complex.norm_conj] using
      chaconDecaySpectralProduct_norm U (indices n) (hpos n) z
  exact tendsto_chaconDecaySpectralCalculus_zero U hWeak x f
    (fun n z ↦ (hb n z).trans (pow_le_one₀ (chaconDecayRatio_nonneg _)
      (chaconDecayRatio_le_one (chaconDecayParameter_norm U z))))
    (fun z hz ↦ by
      have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (chaconDecayRatio_nonneg _)
        (chaconDecayRatio_lt_one (chaconDecayParameter_norm U z) hz)).comp hLength
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simp only [sub_zero]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp
        (fun _ ↦ norm_nonneg _) (fun n ↦ hb n z))

end SpectralPolynomials

private theorem spectralCalculus_chaconDecaySpectral (reverse : Bool) (m : ℕ) :
    spectralCalculus 𝓤 (chaconDecaySpectral 𝓤 reverse m) = chaconDecayOperator reverse m := by
  have h : spectralCalculus 𝓤 (chaconDecaySpectralPositive 𝓤 m) =
      chaconHeightPolynomialOperatorZero m :=
    (spectralCalculus_chaconDecaySpectralPositive 𝓤 m).trans
      (chaconHeightPolynomialOperatorZero_eq_aeval m).symm
  cases reverse
  · exact h
  · change spectralCalculus 𝓤 (star (chaconDecaySpectralPositive 𝓤 m)) =
      star (chaconHeightPolynomialOperatorZero m)
    rw [map_star, h]

/-- Both of the neighboring Chacon polynomials act strongly as zero along
prefixes that do not end in either type of constant ternary tail. -/
theorem tendsto_chaconDecayOperator_ternary_prefix_zero (m : ℕ → ℕ) (d : ℕ → Fin 3)
    (hm : ∀ n, m (n+1) = 3 * m n + (d n).val)
    (hNoZeroTail : ¬ ∃ N, ∀ n ≥ N, d n = 0)
    (hNoTwoTail : ¬ ∃ N, ∀ n ≥ N, d n = 2)
    (adjacent reverse : Bool) (x : 𝓗) :
    Tendsto (fun n ↦ chaconDecayOperator reverse (if adjacent then m n + 1 else m n) x) atTop
      (𝓝 0) := by
  simpa only [spectralCalculus_chaconDecaySpectral] using
    tendsto_spectral_ternary_prefix_zero 𝓤 chaconTower_isWeaklyMixing m d hm hNoZeroTail hNoTwoTail
      adjacent reverse x

/-- A product of specified positive-height polynomials or their adjoints. -/
noncomputable def chaconDecayProduct (indices : List (Bool × ℕ)) : 𝓗 →L[ℂ] 𝓗 :=
  (indices.map fun j ↦ chaconDecayOperator j.1 j.2).prod

private theorem spectralCalculus_chaconDecaySpectralProduct (indices : List (Bool × ℕ)) :
    spectralCalculus 𝓤 (chaconDecaySpectralProduct 𝓤 indices) = chaconDecayProduct indices := by
  induction indices with
  | nil => simp [chaconDecaySpectralProduct, chaconDecayProduct]
  | cons j js ih =>
    simp only [chaconDecaySpectralProduct, chaconDecayProduct, List.map_cons, List.prod_cons,
      map_mul, spectralCalculus_chaconDecaySpectral] at ih ⊢
    rw [ih]

/-- Long products of signed positive-height polynomials have adjoints tending
strongly to zero on the mean-zero Koopman space, uniformly in the choices
of their degrees and signs. -/
theorem tendsto_chaconDecayProduct_adjoint_zero (indices : ℕ → List (Bool × ℕ))
    (hpos : ∀ n j, j ∈ indices n → 0 < j.2)
    (hLength : Tendsto (fun n ↦ (indices n).length) atTop atTop) (x : 𝓗) :
    Tendsto (fun n ↦ (star (chaconDecayProduct (indices n))) x) atTop (𝓝 0) := by
  simpa only [map_star, spectralCalculus_chaconDecaySpectralProduct] using
    tendsto_spectralProduct_star_zero 𝓤 chaconTower_isWeaklyMixing indices hpos hLength x

end Mixing
