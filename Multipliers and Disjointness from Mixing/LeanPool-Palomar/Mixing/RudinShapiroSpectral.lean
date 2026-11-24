/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroOrbit
public import Mixing.CantorLebesgueSpectrum

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology

theorem integral_rudinShapiro_pairSign_int (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) (k : ℤ) :
    (∫ w, signValue (w 0) * signValue (w k) ∂(rudinShapiroOrbitLaw p : Measure SignWords)) =
      if k = 0 then 1 else 0 := by
  have hPos (k : ℤ) (hk : 0 ≤ k) :
      (∫ w, signValue (w 0) * signValue (w k) ∂(rudinShapiroOrbitLaw p : Measure SignWords)) =
        if k = 0 then 1 else 0 := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simpa using integral_rudinShapiro_pairSign p hp n
  by_cases hk : 0 ≤ k
  · exact hPos k hk
  let ν := (rudinShapiroOrbitLaw p : Measure SignWords)
  let f (w : SignWords) := signValue (w 0) * signValue (w k)
  have hf : Continuous f := by
    have h : Continuous signValue := continuous_of_discreteTopology
    exact (h.comp (continuous_apply 0)).mul (h.comp (continuous_apply k))
  have hm : MeasurePreserving (signWordShift (-k)) ν ν :=
    rudinShapiroOrbitLaw_preserving p hp (-k)
  have hInv : (∫ w, f (signWordShift (-k) w) ∂ν) = ∫ w, f w ∂ν := by
    calc
      _ = ∫ w, f w ∂ν.map (signWordShift (-k)) :=
        (integral_map hm.measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [hm.map_eq]
  have he (w : SignWords) : f (signWordShift (-k) w) = signValue (w 0) * signValue (w (-k)) := by
    simp [f, signWordShift, mul_comm]
  simp_rw [he] at hInv
  rw [← hInv, hPos (-k) (neg_nonneg.mpr (le_of_not_ge hk))]
  simp only [neg_eq_zero]

/-- The coordinate sign in the Rudin–Shapiro orbit, realized as a continuous
complex-valued function. -/
def rudinShapiroSignContinuous : C(SignWords, ℂ) where
  toFun w := (signValue (w 0) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply 0))

/-- The coordinate sign as a vector in the Koopman space. -/
def rudinShapiroSignLp (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure :=
  ContinuousMap.toLp 2 (rudinShapiroOrbitSystem p hp).measure ℂ rudinShapiroSignContinuous

theorem rudinShapiroSignLp_autocorrelation (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) (n : ℤ) :
    ⟪rudinShapiroSignLp p hp,
      (rudinShapiroOrbitSystem p hp).koopmanRep (Multiplicative.ofAdd n) (rudinShapiroSignLp p hp)⟫_ℂ =
      if n = 0 then 1 else 0 := by
  let S := rudinShapiroOrbitSystem p hp
  let g := Multiplicative.ofAdd n
  have hf : rudinShapiroSignLp p hp =ᵐ[S.measure] rudinShapiroSignContinuous :=
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) _ rudinShapiroSignContinuous
  have hAction : S.koopmanRep g (rudinShapiroSignLp p hp) =ᵐ[S.measure]
      fun w ↦ rudinShapiroSignContinuous (S.act g w) :=
    (Lp.coeFn_compMeasurePreserving _ (S.preserves g)).trans
      ((S.preserves g).quasiMeasurePreserving.ae_eq_comp hf)
  rw [L2.inner_def]
  calc
    _ = ∫ w, (↑(signValue (w 0) * signValue (w n)) : ℂ) ∂S.measure := by
      apply integral_congr_ae
      filter_upwards [hf, hAction] with w hw hAw
      change inner ℂ (rudinShapiroSignLp p hp w) (S.koopmanRep g (rudinShapiroSignLp p hp) w) = _
      rw [hw, hAw, RCLike.inner_apply']
      change conj (signValue (w 0) : ℂ) * (signValue (w (0 + n)) : ℂ) = _
      simp
    _ = _ := by
      rw [integral_complex_ofReal]
      change (↑(∫ w, signValue (w 0) * signValue (w n) ∂(rudinShapiroOrbitLaw p : Measure SignWords)) : ℂ) = _
      rw [integral_rudinShapiro_pairSign_int p hp n]
      split_ifs <;> simp

/-- The coordinate sign of the measured Rudin–Shapiro orbit has normalized
Lebesgue spectral measure. This is a single cyclic Lebesgue subspace. -/
theorem rudinShapiroSignLp_spectrum_haar (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) :
    integerVectorSpectralMeasure (rudinShapiroOrbitSystem p hp).koopmanRep
      (rudinShapiroSignLp p hp) = (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  apply circleMeasure_eq_of_fourier_eq
  intro n
  rw [integral_fourier_integerVectorSpectralMeasure, rudinShapiroSignLp_autocorrelation p hp n]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [ite_eq_right hn, integral_haar_fourier_zero n hn]

end Mixing
