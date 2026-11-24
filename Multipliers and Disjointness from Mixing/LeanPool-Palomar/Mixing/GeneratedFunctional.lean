module

public import Mixing.GeneratedClosure
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-! # Bounded function calculus in the generated product span -/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Topology

namespace Mixing

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- A function has a bounded representative in the product span closure. -/
def HasGeneratedRepresentative (T : System G X) (U : Set (Ultrafilter G)) (f : X → ℂ) : Prop :=
  ∃ b : BoundedObservable X, (b : X → ℂ) = f ∧ b.l2 T.measure ∈ T.generatedProductsClosure U

namespace HasGeneratedRepresentative

variable {T : System G X} {U : Set (Ultrafilter G)} {f g : X → ℂ}

theorem of_observable (b : BoundedObservable X) (h : b.l2 T.measure ∈ T.generatedProductsClosure U) :
    HasGeneratedRepresentative T U b :=
  ⟨b, rfl, h⟩

theorem const (c : ℂ) : HasGeneratedRepresentative T U (fun _ => c) :=
  ⟨BoundedObservable.const c, rfl, T.const_mem_generatedProductsClosure U c⟩

theorem add (hf : HasGeneratedRepresentative T U f) (hg : HasGeneratedRepresentative T U g) :
    HasGeneratedRepresentative T U (fun x => f x + g x) := by
  obtain ⟨u, hu, hU⟩ := hf
  obtain ⟨v, hv, hV⟩ := hg
  refine ⟨u.add v, ?_, ?_⟩
  · funext x
    change u x + v x = _
    rw [congrFun hu x, congrFun hv x]
  · rw [BoundedObservable.l2_add]
    exact (T.generatedProductsClosure U).add_mem hU hV

theorem sub (hf : HasGeneratedRepresentative T U f) (hg : HasGeneratedRepresentative T U g) :
    HasGeneratedRepresentative T U (fun x => f x - g x) := by
  obtain ⟨u, hu, hU⟩ := hf
  obtain ⟨v, hv, hV⟩ := hg
  refine ⟨u.sub v, ?_, ?_⟩
  · funext x
    change u x - v x = _
    rw [congrFun hu x, congrFun hv x]
  · rw [BoundedObservable.l2_sub]
    exact (T.generatedProductsClosure U).sub_mem hU hV

theorem mul (hf : HasGeneratedRepresentative T U f) (hg : HasGeneratedRepresentative T U g) :
    HasGeneratedRepresentative T U (fun x => f x * g x) := by
  obtain ⟨u, hu, hU⟩ := hf
  obtain ⟨v, hv, hV⟩ := hg
  refine ⟨u.mul v, ?_, T.mul_mem_generatedProductsClosure U u v hU hV⟩
  funext x
  change u x * v x = _
  rw [congrFun hu x, congrFun hv x]

theorem pow (hf : HasGeneratedRepresentative T U f) (n : ℕ) :
    HasGeneratedRepresentative T U (fun x => f x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (const (T := T) (U := U) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem ae_eq (hf : HasGeneratedRepresentative T U f) (g : BoundedObservable X)
    (he : f =ᵐ[T.measure] g) : HasGeneratedRepresentative T U g := by
  obtain ⟨b, hb, hm⟩ := hf
  refine ⟨g, rfl, ?_⟩
  rw [← BoundedObservable.l2_eq_of_ae_eq (show (b : X → ℂ) =ᵐ[T.measure] g from hb ▸ he)]
  exact hm

/-- A uniformly bounded a.e. limit stays in the span closure. -/
theorem of_ae_tendsto {f : ℕ → X → ℂ} (g : BoundedObservable X)
    (hf : ∀ n, HasGeneratedRepresentative T U (f n)) {C : ℝ}
    (hC : ∀ n x, ‖f n x‖ ≤ C)
    (hLim : ∀ᵐ x ∂T.measure, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    HasGeneratedRepresentative T U g := by
  choose b hb hMem using hf
  have hBound (n : ℕ) (x : X) : ‖b n x‖ ≤ C := by simpa only [hb n] using hC n x
  have hTendsto : ∀ᵐ x ∂T.measure, Tendsto (fun n => b n x) atTop (𝓝 (g x)) := by
    simpa only [hb] using hLim
  exact of_observable g <| (T.isClosed_generatedProductsClosure U).mem_of_tendsto
    (BoundedObservable.tendsto_l2_of_ae_tendsto T.measure b g hBound hTendsto)
    (Eventually.of_forall hMem)

theorem eval_polynomial {u : X → ℝ}
    (hu : HasGeneratedRepresentative T U (fun x => (u x : ℂ))) (p : Polynomial ℝ) :
    HasGeneratedRepresentative T U (fun x => Complex.ofReal (p.eval (u x))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add, Complex.ofReal_add] using hp.add hq
  | monomial n c =>
    simpa only [Polynomial.eval_monomial, Complex.ofReal_mul, Complex.ofReal_pow] using
      (const (T := T) (U := U) (c : ℂ)).mul (hu.pow n)

/-- Applying a bounded continuous real function to a bounded real observable preserves
membership in the product span closure. -/
theorem continuous_real {u : X → ℝ}
    (hu : HasGeneratedRepresentative T U (fun x => (u x : ℂ)))
    (huMeas : Measurable u) {M : ℝ} (huBound : ∀ x, |u x| ≤ M)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC₀ : 0 ≤ C) (hC : ∀ k, |ψ k| ≤ C) :
    HasGeneratedRepresentative T U (fun x => (ψ (u x) : ℂ)) := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  choose p hp using fun n => exists_polynomial_near_of_continuousOn (-M) M ψ
    hψ.continuousOn (ε n) (hεpos n)
  let v (n : ℕ) (x : X) : ℂ := Complex.ofReal ((p n).eval (u x))
  let b : BoundedObservable X :=
    ⟨fun x => ψ (u x), Complex.continuous_ofReal.measurable.comp (hψ.measurable.comp huMeas),
      C, hC₀, fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC (u x)⟩
  have hApprox (n : ℕ) (x : X) : |(p n).eval (u x) - ψ (u x)| < ε n :=
    hp n (u x) (abs_le.mp (huBound x))
  have hBound (n : ℕ) (x : X) : ‖v n x‖ ≤ C + 1 := by
    change ‖Complex.ofReal ((p n).eval (u x))‖ ≤ C + 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      _ = |(p n).eval (u x) - ψ (u x) + ψ (u x)| := by rw [sub_add_cancel]
      _ ≤ |(p n).eval (u x) - ψ (u x)| + |ψ (u x)| := abs_add_le _ _
      _ ≤ C + 1 := by linarith [hApprox n x, hεle n, hC (u x)]
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hPoint (x : X) : Tendsto (fun n => v n x) atTop (𝓝 (b x)) := by
    have hReal : Tendsto (fun n => (p n).eval (u x)) atTop (𝓝 (ψ (u x))) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hε
      simpa only [Real.norm_eq_abs] using (hApprox n x).le
    exact (Complex.continuous_ofReal.tendsto _).comp hReal
  exact of_ae_tendsto b (fun n => eval_polynomial hu (p n)) hBound (Eventually.of_forall hPoint)

end HasGeneratedRepresentative

namespace System

theorem hasGeneratedRepresentative_ultrafilterTranslate_re (T : System G X)
    (U : Set (Ultrafilter G)) {p : Ultrafilter G} (hp : p ∈ U) (f : BoundedObservable X) :
    HasGeneratedRepresentative T U (fun x => ((T.ultrafilterTranslate p f x).re : ℂ)) := by
  let o := T.ultrafilterTranslate p f
  have ho : HasGeneratedRepresentative T U o :=
    .of_observable o (T.ultrafilterTranslate_mem_generatedProductsClosure U hp f)
  have hoc : HasGeneratedRepresentative T U (T.ultrafilterTranslate p f.conjugate) :=
    .of_observable _ (T.ultrafilterTranslate_mem_generatedProductsClosure U hp f.conjugate)
  have hconj := hoc.ae_eq o.conjugate (T.ultrafilterTranslate_conjugate_ae p f)
  have h := (HasGeneratedRepresentative.const (T := T) (U := U) (2 : ℂ)⁻¹).mul (ho.add hconj)
  simpa only [o, BoundedObservable.conjugate_apply, mul_comm (2 : ℂ)⁻¹, ← div_eq_mul_inv,
    ← Complex.re_eq_add_conj] using h

theorem hasGeneratedRepresentative_ultrafilterTranslate_im (T : System G X)
    (U : Set (Ultrafilter G)) {p : Ultrafilter G} (hp : p ∈ U) (f : BoundedObservable X) :
    HasGeneratedRepresentative T U (fun x => ((T.ultrafilterTranslate p f x).im : ℂ)) := by
  let o := T.ultrafilterTranslate p f
  have ho : HasGeneratedRepresentative T U o :=
    .of_observable o (T.ultrafilterTranslate_mem_generatedProductsClosure U hp f)
  have hoc : HasGeneratedRepresentative T U (T.ultrafilterTranslate p f.conjugate) :=
    .of_observable _ (T.ultrafilterTranslate_mem_generatedProductsClosure U hp f.conjugate)
  have hconj := hoc.ae_eq o.conjugate (T.ultrafilterTranslate_conjugate_ae p f)
  have h := (ho.sub hconj).mul (HasGeneratedRepresentative.const (T := T) (U := U)
    ((2 : ℂ) * Complex.I)⁻¹)
  simpa only [o, BoundedObservable.conjugate_apply, ← div_eq_mul_inv,
    ← Complex.im_eq_sub_conj] using h

end System

end Mixing
