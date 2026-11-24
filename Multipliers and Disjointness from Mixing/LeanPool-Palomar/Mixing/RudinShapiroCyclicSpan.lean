/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroCutoffs
public import Mixing.RudinShapiroSpectralPair
public import Mixing.GeneratedClosure

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped Classical InnerProductSpace

private theorem abs_signValue (b : Bool) : |signValue b| = 1 := by
  cases b <;> simp [signValue]

theorem measurable_rudinShapiro_centreSign : Measurable (fun w : SignWords ↦ signValue (w 0)) :=
  ((continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply 0)).measurable

theorem measurable_rudinShapiroZeroCutoff (k : ℕ) : Measurable (rudinShapiroZeroCutoff k) :=
  measurable_rudinShapiro_centreSign.ite (measurableSet_rudinShapiroZeroPhase k) measurable_const

theorem measurable_rudinShapiroSignedZeroCutoff (k : ℕ) :
    Measurable (rudinShapiroSignedZeroCutoff k) :=
  (measurable_rudinShapiroZeroCutoff k).ite (measurableSet_rudinShapiroZeroPhase (k + 1))
    (measurable_rudinShapiroZeroCutoff k).neg

/-- The two zero-class cutoffs as bounded complex observables. -/
def rudinShapiroZeroCutoffObservable (k : ℕ) (b : Bool) : BoundedObservable SignWords where
  toFun w := ((if b then rudinShapiroSignedZeroCutoff k w else rudinShapiroZeroCutoff k w : ℝ) : ℂ)
  measurable := Complex.continuous_ofReal.measurable.comp (by
    cases b
    · exact measurable_rudinShapiroZeroCutoff k
    · exact measurable_rudinShapiroSignedZeroCutoff k)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le w := by
    cases b <;> by_cases hk : rudinShapiroZeroPhase k w <;>
      by_cases hk' : rudinShapiroZeroPhase (k + 1) w <;>
        simp [rudinShapiroZeroCutoff, rudinShapiroSignedZeroCutoff, hk, hk', abs_signValue]

/-- The sign-residue product as a bounded complex observable. -/
def rudinShapiroResidueCutoffObservable (k a : ℕ) : BoundedObservable SignWords where
  toFun w := (rudinShapiroResidueCutoff k a w : ℂ)
  measurable := Complex.continuous_ofReal.measurable.comp
    (measurable_rudinShapiro_centreSign.ite (measurableSet_rudinShapiroResidue k a) measurable_const)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le w := by
    by_cases h : rudinShapiroResidue k a w <;>
      simp [rudinShapiroResidueCutoff, h, abs_signValue]

variable (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)

/-- The algebraic span of the translates of the two Haar spectral vectors. -/
def rudinShapiroPairSpan :
    Submodule ℂ (Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure) :=
  Submodule.span ℂ (range fun (i : Bool × Multiplicative ℤ) ↦
    (rudinShapiroOrbitSystem p hp).koopmanRep i.2 (rudinShapiroPairLp p hp i.1))

theorem rudinShapiroPairSpan_invariant (g : Multiplicative ℤ)
    {v : Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure}
    (hv : v ∈ rudinShapiroPairSpan p hp) :
    (rudinShapiroOrbitSystem p hp).koopmanRep g v ∈ rudinShapiroPairSpan p hp := by
  let U := (rudinShapiroOrbitSystem p hp).koopmanRep
  have hIncl : rudinShapiroPairSpan p hp ≤
      (rudinShapiroPairSpan p hp).comap (U g).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b, n⟩, rfl⟩
    change (U g * U n) (rudinShapiroPairLp p hp b) ∈ rudinShapiroPairSpan p hp
    rw [← map_mul]
    exact Submodule.subset_span ⟨(b, g * n), rfl⟩
  exact hIncl hv

private theorem ae_koopman_rudinShapiro_obs (v : BoundedObservable SignWords) (n : ℤ) :
    ((rudinShapiroOrbitSystem p hp).koopmanRep (Multiplicative.ofAdd n)
      (v.l2 (rudinShapiroOrbitSystem p hp).measure)) =ᵐ[(rudinShapiroOrbitSystem p hp).measure]
        fun w ↦ v (signWordShift n w) := by
  let S := rudinShapiroOrbitSystem p hp
  let μ := S.measure
  let g := Multiplicative.ofAdd n
  exact (Lp.coeFn_compMeasurePreserving (v.l2 μ) (S.preserves g)).trans
    ((S.preserves g).quasiMeasurePreserving.ae_eq_comp (v.coe_l2 μ))

private theorem zeroCutoffObservable_l2_zero (b : Bool) :
    (rudinShapiroZeroCutoffObservable 0 b).l2 (rudinShapiroOrbitSystem p hp).measure =
      rudinShapiroPairLp p hp b := by
  apply Lp.ext
  filter_upwards [(rudinShapiroZeroCutoffObservable 0 b).coe_l2 (rudinShapiroOrbitSystem p hp).measure,
    coe_rudinShapiroPairLp p hp b] with w h₁ h₂
  rw [h₁, h₂]
  have hParity (w : SignWords) : rudinShapiroParity w = 1 ∨ rudinShapiroParity w = -1 := by
    have he := rudinShapiroParity_sq w
    exact sq_eq_one_iff.mp he
  cases b
  · simp [rudinShapiroZeroCutoffObservable, rudinShapiroZeroCutoff, rudinShapiroZeroPhase]
  · rcases hParity w with h | h <;>
      norm_num [rudinShapiroZeroCutoffObservable, rudinShapiroZeroCutoff, rudinShapiroSignedZeroCutoff,
        rudinShapiroZeroPhase, h]

private theorem zeroCutoffObservable_l2_recursion (k : ℕ) :
    let S := rudinShapiroOrbitSystem p hp
    let f b := (rudinShapiroZeroCutoffObservable k b).l2 S.measure
    let g b := (rudinShapiroZeroCutoffObservable (k + 1) b).l2 S.measure
    let time := Multiplicative.ofAdd (((2 : ℕ) ^ k : ℕ) : ℤ)
    (2 : ℂ) • g false = f false + f true ∧
      (2 : ℂ) • g true = S.koopmanRep time (f false) - S.koopmanRep time (f true) := by
  let S := rudinShapiroOrbitSystem p hp
  let μ := S.measure
  let f (b : Bool) := (rudinShapiroZeroCutoffObservable k b).l2 μ
  let g (b : Bool) := (rudinShapiroZeroCutoffObservable (k + 1) b).l2 μ
  let n : ℤ := ((2 : ℕ) ^ k : ℕ)
  let U := S.koopmanRep (Multiplicative.ofAdd n)
  change (2 : ℂ) • g false = f false + f true ∧ (2 : ℂ) • g true = U (f false) - U (f true)
  constructor
  · apply Lp.ext
    filter_upwards [Lp.coeFn_smul (2 : ℂ) (g false), Lp.coeFn_add (f false) (f true),
      (rudinShapiroZeroCutoffObservable (k + 1) false).coe_l2 μ,
      (rudinShapiroZeroCutoffObservable k false).coe_l2 μ,
      (rudinShapiroZeroCutoffObservable k true).coe_l2 μ] with w hG hF hg hf₁ hf₂
    change g false w = _ at hg
    change f false w = _ at hf₁
    change f true w = _ at hf₂
    rw [hG, hF, Pi.smul_apply, Pi.add_apply, hg, hf₁, hf₂, smul_eq_mul]
    change (2 : ℂ) * (rudinShapiroZeroCutoff (k + 1) w : ℂ) =
      (rudinShapiroZeroCutoff k w : ℂ) + (rudinShapiroSignedZeroCutoff k w : ℂ)
    exact_mod_cast rudinShapiroZeroCutoff_succ k w
  · apply Lp.ext
    filter_upwards [Lp.coeFn_smul (2 : ℂ) (g true), Lp.coeFn_sub (U (f false)) (U (f true)),
      (rudinShapiroZeroCutoffObservable (k + 1) true).coe_l2 μ,
      ae_koopman_rudinShapiro_obs p hp (rudinShapiroZeroCutoffObservable k false) n,
      ae_koopman_rudinShapiro_obs p hp (rudinShapiroZeroCutoffObservable k true) n,
      ae_mem_rudinShapiroSubshift p hp] with w hG hF hg hf₁ hf₂ hw
    change g true w = _ at hg
    change U (f false) w = _ at hf₁
    change U (f true) w = _ at hf₂
    rw [hG, hF, Pi.smul_apply, Pi.sub_apply, hg, hf₁, hf₂, smul_eq_mul]
    change (2 : ℂ) * (rudinShapiroSignedZeroCutoff (k + 1) w : ℂ) =
      (rudinShapiroZeroCutoff k (signWordShift n w) : ℂ) -
        (rudinShapiroSignedZeroCutoff k (signWordShift n w) : ℂ)
    exact_mod_cast rudinShapiroSignedZeroCutoff_succ hw k

theorem rudinShapiroZeroCutoffObservable_mem_span (k : ℕ) (b : Bool) :
    (rudinShapiroZeroCutoffObservable k b).l2 (rudinShapiroOrbitSystem p hp).measure ∈
      rudinShapiroPairSpan p hp := by
  induction k generalizing b with
  | zero =>
    rw [zeroCutoffObservable_l2_zero p hp b]
    exact Submodule.subset_span ⟨(b, 1), by simp⟩
  | succ k ih =>
    let S := rudinShapiroOrbitSystem p hp
    let Q := rudinShapiroPairSpan p hp
    have h := zeroCutoffObservable_l2_recursion p hp k
    suffices (2 : ℂ) • (rudinShapiroZeroCutoffObservable (k + 1) b).l2 S.measure ∈ Q by
      simpa [smul_smul] using Q.smul_mem (2 : ℂ)⁻¹ this
    cases b
    · rw [h.1]
      exact Q.add_mem (ih false) (ih true)
    · rw [h.2]
      exact Q.sub_mem (rudinShapiroPairSpan_invariant p hp _ (ih false))
        (rudinShapiroPairSpan_invariant p hp _ (ih true))

theorem rudinShapiroResidueCutoffObservable_mem_span (k a : ℕ) (ha : a < 2 ^ (k + 1)) :
    (rudinShapiroResidueCutoffObservable (k + 1) a).l2 (rudinShapiroOrbitSystem p hp).measure ∈
      rudinShapiroPairSpan p hp := by
  let b : Bool := decide (a / 2 ^ k ≠ 0)
  let f := rudinShapiroZeroCutoffObservable (k + 1) b
  let O := rudinShapiroResidueCutoffObservable (k + 1) a
  let S := rudinShapiroOrbitSystem p hp
  let U := S.koopmanRep (Multiplicative.ofAdd (-(a : ℤ)))
  have he : O.l2 S.measure = (rudinShapiro a : ℂ) • U (f.l2 S.measure) := by
    apply Lp.ext
    filter_upwards [O.coe_l2 S.measure, Lp.coeFn_smul (rudinShapiro a : ℂ) (U (f.l2 S.measure)),
      ae_koopman_rudinShapiro_obs p hp f (-(a : ℤ)), ae_mem_rudinShapiroSubshift p hp] with w hO hU hf hw
    change U (f.l2 S.measure) w = _ at hf
    rw [hO, hU, Pi.smul_apply, hf, smul_eq_mul]
    have hh := rudinShapiroResidueCutoff_eq_translate hw k a ha
    by_cases h : a / 2 ^ k = 0 <;> simpa [O, f, b, h, rudinShapiroResidueCutoffObservable,
      rudinShapiroZeroCutoffObservable] using congrArg Complex.ofReal hh
  rw [he]
  exact (rudinShapiroPairSpan p hp).smul_mem _ (rudinShapiroPairSpan_invariant p hp _
    (rudinShapiroZeroCutoffObservable_mem_span p hp (k + 1) b))

end Mixing
