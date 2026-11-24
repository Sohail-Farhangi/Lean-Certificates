module

public import Mixing.StrongMixing
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

namespace Mixing

open Polynomial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The polynomial step in Example 2. If the generator has no eigenvectors,
then every nonzero polynomial in it is injective. -/
theorem aeval_injective_of_no_eigenvectors (A : H →L[ℂ] H)
    (hA : ∀ z : ℂ, Function.Injective (A - algebraMap ℂ (H →L[ℂ] H) z))
    {Q : ℂ[X]} (hQ : Q ≠ 0) : Function.Injective (aeval A Q) := by
  have hmul (B C : H →L[ℂ] H) (hB : Function.Injective B) (hC : Function.Injective C) :
      Function.Injective (B * C) := by
    intro x y he
    exact hC (hB he)
  have hroots (s : Multiset ℂ) :
      Function.Injective (aeval A (s.map (fun a ↦ X - C a)).prod) := by
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, map_one]
      exact fun _ _ he ↦ he
    | cons a s hs =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul]
      apply hmul _ _ _ hs
      simpa only [map_sub, aeval_X, aeval_C] using hA a
  have hlead : Function.Injective (algebraMap ℂ (H →L[ℂ] H) Q.leadingCoeff) :=
    smul_right_injective H (leadingCoeff_ne_zero.mpr hQ)
  rw [(IsAlgClosed.splits Q).eq_prod_roots, map_mul, aeval_C]
  exact hmul _ _ hlead (hroots Q.roots)

/-- The spectral conclusion of the polynomial case of Example 2, conditional on
the polynomial form of the weak limit supplied by the Chacon classification. -/
theorem example2_spectrallyDisjoint_of_polynomial_limit
    [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H))
    (V : Multiplicative ℤ →* (K ≃ₗᵢ[ℂ] K)) (p : Ultrafilter (Multiplicative ℤ))
    (hA : ∀ z : ℂ,
      Function.Injective ((U (Multiplicative.ofAdd 1) : H →L[ℂ] H) -
        algebraMap ℂ (H →L[ℂ] H) z))
    {Q : ℂ[X]} (hQ : Q ≠ 0)
    (hlim : ultrafilterOperator U p = aeval (U (Multiplicative.ofAdd 1) : H →L[ℂ] H) Q)
    (hmix : ultrafilterOperator V p = 0) : SpectrallyDisjoint U V := by
  apply spectrallyDisjoint_of_ultrafilterOperator_injective U V p _ hmix
  rw [hlim]
  exact aeval_injective_of_no_eigenvectors _ hA hQ

end Mixing
