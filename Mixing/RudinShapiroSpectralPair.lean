/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroParity

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory
open scoped ComplexConjugate InnerProductSpace Topology

private theorem phase_ae_shift (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) (k : ℤ) :
    ∀ᵐ w ∂(rudinShapiroOrbitLaw p : Measure SignWords),
      rudinShapiroParity (signWordShift k w) = (-1 : ℝ) ^ k * rudinShapiroParity w :=
  (ae_mem_rudinShapiroSubshift p hp).mono fun _ hw ↦ rudinShapiroParity_shift_of_mem hw k

theorem integral_rudinShapiro_signedPair_int (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (k : ℤ) : (∫ w, rudinShapiroParity w * (signValue (w 0) * signValue (w k))
      ∂(rudinShapiroOrbitLaw p : Measure SignWords)) = 0 := by
  have hPos (k : ℤ) (hk : 0 ≤ k) : (∫ w, rudinShapiroParity w *
      (signValue (w 0) * signValue (w k)) ∂(rudinShapiroOrbitLaw p : Measure SignWords)) = 0 := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact integral_rudinShapiro_signedPair p hp n
  by_cases hk : 0 ≤ k
  · exact hPos k hk
  let ν := (rudinShapiroOrbitLaw p : Measure SignWords)
  let f (w : SignWords) := rudinShapiroParity w * (signValue (w 0) * signValue (w (-k)))
  have hf : Continuous f := by
    have h : Continuous signValue := continuous_of_discreteTopology
    exact rudinShapiroParity.continuous.mul ((h.comp (continuous_apply 0)).mul
      (h.comp (continuous_apply (-k))))
  have hm := rudinShapiroOrbitLaw_preserving p hp k
  have hInv : (∫ w, f (signWordShift k w) ∂ν) = 0 := by
    calc
      _ = ∫ w, f w ∂ν.map (signWordShift k) :=
        (integral_map hm.measurable.aemeasurable hf.aestronglyMeasurable).symm
      _ = 0 := by
        rw [hm.map_eq]
        exact hPos (-k) (neg_nonneg.mpr (le_of_not_ge hk))
  have he : (∫ w, f (signWordShift k w) ∂ν) =
      ∫ w, (-1 : ℝ) ^ k * (rudinShapiroParity w * (signValue (w 0) * signValue (w k))) ∂ν := by
    apply integral_congr_ae
    filter_upwards [phase_ae_shift p hp k] with w hw
    unfold f
    rw [hw]
    simp only [signWordShift, zero_add, neg_add_cancel]
    ring
  rw [he, integral_const_mul] at hInv
  exact (mul_eq_zero.mp hInv).resolve_left (zpow_ne_zero _ (by norm_num))

def rudinShapiroCompanionContinuous : C(SignWords, ℂ) where
  toFun w := ((rudinShapiroParity w * signValue (w 0) : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp (rudinShapiroParity.continuous.mul
    ((continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply 0)))

/-- The two Rudin–Shapiro vectors. The companion is the coordinate sign
multiplied by the intrinsic parity eigenfunction. -/
def rudinShapiroPairLp (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) (b : Bool) :
    Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure :=
  if b then ContinuousMap.toLp 2 (rudinShapiroOrbitSystem p hp).measure ℂ
    rudinShapiroCompanionContinuous else rudinShapiroSignLp p hp

theorem coe_rudinShapiroPairLp (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) (b : Bool) :
    rudinShapiroPairLp p hp b =ᵐ[(rudinShapiroOrbitSystem p hp).measure] fun w ↦
      ((if b then rudinShapiroParity w * signValue (w 0) else signValue (w 0) : ℝ) : ℂ) := by
  cases b
  · exact ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) _ rudinShapiroSignContinuous
  · exact ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) _ rudinShapiroCompanionContinuous

/-- All mixed correlations of the two vectors vanish. Each has Haar
autocorrelations, so they supply two orthogonal cyclic Lebesgue subspaces. -/
theorem rudinShapiroPairLp_correlation (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (a b : Bool) (k : ℤ) :
    ⟪rudinShapiroPairLp p hp a,
      (rudinShapiroOrbitSystem p hp).koopmanRep (Multiplicative.ofAdd k) (rudinShapiroPairLp p hp b)⟫_ℂ =
        if a = b ∧ k = 0 then 1 else 0 := by
  let S := rudinShapiroOrbitSystem p hp
  let g := Multiplicative.ofAdd k
  let f (b : Bool) (w : SignWords) :=
    if b then rudinShapiroParity w * signValue (w 0) else signValue (w 0)
  have h := Lp.coeFn_compMeasurePreserving (rudinShapiroPairLp p hp b) (S.preserves g)
  have h' := (S.preserves g).quasiMeasurePreserving.ae_eq_comp (coe_rudinShapiroPairLp p hp b)
  have he : (∫ w, inner ℂ (rudinShapiroPairLp p hp a w)
      ((S.koopmanRep g (rudinShapiroPairLp p hp b)) w) ∂S.measure) =
      (↑(∫ w, f a w * f b (signWordShift k w) ∂S.measure) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [coe_rudinShapiroPairLp p hp a, h.trans h'] with w ha hb
    change rudinShapiroPairLp p hp a w = (f a w : ℂ) at ha
    change (S.koopmanRep g (rudinShapiroPairLp p hp b)) w =
      (f b (signWordShift k w) : ℂ) at hb
    rw [ha, hb, RCLike.inner_apply']
    simp
  rw [L2.inner_def, he]
  have hU := integral_rudinShapiro_pairSign_int p hp k
  have hS : (∫ w, rudinShapiroParity w * (signValue (w 0) * signValue (w k)) ∂S.measure) = 0 :=
    integral_rudinShapiro_signedPair_int p hp k
  cases a <;> cases b
  · have he' : (∫ w, f false w * f false (signWordShift k w) ∂S.measure) =
        ∫ w, signValue (w 0) * signValue (w k)
          ∂(rudinShapiroOrbitLaw p : Measure SignWords) := by
      simp only [f, Bool.false_eq_true, ite_false, signWordShift, zero_add]
      rfl
    rw [he', hU]
    by_cases hk : k = 0 <;> simp [hk]
  · have he' : (∫ w, f false w * f true (signWordShift k w) ∂S.measure) =
        ∫ w, (-1 : ℝ) ^ k * (rudinShapiroParity w * (signValue (w 0) * signValue (w k)))
          ∂S.measure := by
      apply integral_congr_ae
      filter_upwards [phase_ae_shift p hp k] with w hw
      simp only [f, Bool.false_eq_true, ite_false, ite_true, hw]
      simp only [signWordShift, zero_add]
      ring
    rw [he', integral_const_mul, hS]
    simp
  · have he' (w : SignWords) : f true w * f false (signWordShift k w) =
        rudinShapiroParity w * (signValue (w 0) * signValue (w k)) := by
      simp only [f, ite_true, ite_false, Bool.false_eq_true, signWordShift, zero_add]
      ring
    simp_rw [he']
    rw [hS]
    simp
  · have he' : (∫ w, f true w * f true (signWordShift k w) ∂S.measure) =
        ∫ w, (-1 : ℝ) ^ k * (signValue (w 0) * signValue (w k)) ∂S.measure := by
      apply integral_congr_ae
      filter_upwards [phase_ae_shift p hp k] with w hw
      simp only [f, ite_true, hw]
      simp only [signWordShift, zero_add]
      linear_combination ((-1 : ℝ) ^ k * (signValue (w 0) * signValue (w k))) * rudinShapiroParity_sq w
    rw [he', integral_const_mul]
    change (↑((-1 : ℝ) ^ k * (∫ w, signValue (w 0) * signValue (w k)
      ∂(rudinShapiroOrbitLaw p : Measure SignWords))) : ℂ) = _
    rw [hU]
    by_cases hk : k = 0 <;> simp [hk]

theorem rudinShapiroPairLp_spectrum_haar (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (b : Bool) :
    integerVectorSpectralMeasure (rudinShapiroOrbitSystem p hp).koopmanRep
      (rudinShapiroPairLp p hp b) = (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  apply circleMeasure_eq_of_fourier_eq
  intro n
  rw [integral_fourier_integerVectorSpectralMeasure, rudinShapiroPairLp_correlation p hp b b n]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [integral_haar_fourier_zero n hn]
    simp [hn]

end Mixing
