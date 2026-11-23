/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.ErgodicExamples
public import Mathlib.Dynamics.Ergodic.Function
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Ergodic Discrete -/

@[expose] public section

open Filter Finset Function MeasureTheory Set
open scoped Topology BigOperators InnerProductSpace ENNReal

namespace VdC

section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- Koopman eigenvectors in the actual Mathlib L² space. -/
def koopmanLpEigenvectors (hT : MeasurePreserving T μ μ) : Set (Lp ℂ 2 μ) :=
  {v | ∃ c : ℂ, Lp.compMeasurePreserving T hT v = c • v}

/-- The usual discrete-spectrum condition that the Koopman eigenvectors span a
dense subspace of L². -/
def KoopmanDiscreteSpectrumLp (hT : MeasurePreserving T μ μ) : Prop :=
  Dense (↑(Submodule.span ℂ (koopmanLpEigenvectors hT)) : Set (Lp ℂ 2 μ))

private theorem eigenvector_unit_modulus (hT : MeasurePreserving T μ μ) {v : Lp ℂ 2 μ}
    (hv : v ∈ koopmanLpEigenvectors hT) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ Lp.compMeasurePreserving T hT v = c • v := by
  by_cases h : v = 0
  · subst v
    exact ⟨1, norm_one, by simp⟩
  obtain ⟨c, hc⟩ := hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr h
  have he : ‖v‖ = ‖c‖ * ‖v‖ :=
    (Lp.norm_compMeasurePreserving v hT).symm.trans ((congrArg norm hc).trans (norm_smul _ _))
  have hh : ‖c‖ * ‖v‖ = 1 * ‖v‖ := he.symm.trans (one_mul _).symm
  exact ⟨c, mul_right_cancel₀ hn.ne' hh, hc⟩

private theorem exists_bounded_eigen_representative (hT : Ergodic T μ) {v : Lp ℂ 2 μ}
    (hv : v ∈ koopmanLpEigenvectors hT.toMeasurePreserving) :
    ∃ e : BoundedKoopmanEigenfunction μ T, (e.value : X → ℂ) =ᵐ[μ] v := by
  classical
  obtain ⟨c, hc, hcv⟩ := eigenvector_unit_modulus hT.toMeasurePreserving hv
  let u : X → ℂ := (Lp.aestronglyMeasurable v).mk v
  have hu : Measurable u := (Lp.aestronglyMeasurable v).stronglyMeasurable_mk.measurable
  have hvu : (v : X → ℂ) =ᵐ[μ] u := (Lp.aestronglyMeasurable v).ae_eq_mk
  have hvT := Lp.coeFn_compMeasurePreserving v hT.toMeasurePreserving
  rw [hcv] at hvT
  have hEq : ∀ᵐ x ∂μ, u (T x) = c*u x := by
    filter_upwards [hvT, Lp.coeFn_smul c v, hvu,
      hT.toMeasurePreserving.quasiMeasurePreserving.ae_eq_comp hvu] with x hcomp hsmul hx hx'
    change v (T x) = u (T x) at hx'
    change (c • v) x = v (T x) at hcomp
    have hh : (c • v) x = c * v x := hsmul
    rw [← hx', ← hcomp, hh, hx]
  have hInv : (fun x => ‖u x‖) ∘ T =ᵐ[μ] (fun x => ‖u x‖) := by
    filter_upwards [hEq] with x hx
    change ‖u (T x)‖ = ‖u x‖
    rw [hx, norm_mul, hc, one_mul]
  obtain ⟨C, hC⟩ := hT.ae_eq_const_of_ae_eq_comp₀ hu.norm.nullMeasurable hInv
  let B : Set X := {x | ‖u x‖ = C}
  have hB : MeasurableSet B := measurableSet_eq_fun hu.norm measurable_const
  let g := B.indicator u
  have hgu : (g : X → ℂ) =ᵐ[μ] u := by
    filter_upwards [hC] with x hx
    exact Set.indicator_of_mem hx _
  let D := max 0 C
  have hg : BoundedObservable g := by
    refine ⟨hu.indicator hB, D, le_max_left _ _, fun x => ?_⟩
    change ‖B.indicator u x‖ ≤ D
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, show ‖u x‖ = C from hx]
      exact le_max_right _ _
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact le_max_left _ _
  have he : ∀ᵐ x ∂μ, g (T x) = c*g x := by
    filter_upwards [hEq, hgu, hT.toMeasurePreserving.quasiMeasurePreserving.ae_eq_comp hgu] with x h hx hx'
    change g (T x) = u (T x) at hx'
    rw [hx', hx, h]
  exact ⟨⟨g, hg, c, hc, he⟩, hgu.trans hvu.symm⟩

private theorem eigen_fin_sum_of_mem_span (hT : MeasurePreserving T μ μ) {v : Lp ℂ 2 μ}
    (hv : v ∈ Submodule.span ℂ (koopmanLpEigenvectors hT)) :
    ∃ (k : ℕ) (e : Fin k → Lp ℂ 2 μ), (∀ i, e i ∈ koopmanLpEigenvectors hT) ∧
      (∑ i, e i) = v := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, fun _ => v, fun _ => hv, by simp⟩
  | zero => exact ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨n, e, he, hE⟩ := hv
    obtain ⟨m, f, hf, hF⟩ := hw
    refine ⟨n+m, Fin.addCases e f, ?_, ?_⟩
    · apply Fin.addCases
      · intro i
        simpa only [Fin.addCases_left] using he i
      · intro i
        simpa only [Fin.addCases_right] using hf i
    · rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, hE, hF]
  | smul c v _ hv =>
    obtain ⟨n, e, he, hE⟩ := hv
    refine ⟨n, fun i => c • e i, fun i => ?_, ?_⟩
    · obtain ⟨d, hd⟩ := he i
      refine ⟨d, ?_⟩
      have h := (Lp.compMeasurePreservingₗ (E := ℂ) (p := 2) ℂ T hT).map_smul c (e i)
      change Lp.compMeasurePreserving T hT (c • e i) = c • Lp.compMeasurePreserving T hT (e i) at h
      rw [h, hd, smul_comm]
    · rw [← Finset.smul_sum, hE]

private theorem norm_sq_L2_eq_integral (v : Lp ℂ 2 μ) : ‖v‖^2 = ∫ x, ‖v x‖^2 ∂μ := by
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (‖v‖^2) = ⟪v, v⟫_ℂ := by
      rw [Complex.ofReal_pow]
      exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v).symm
    _ = ∫ x, ⟪v x, v x⟫_ℂ ∂μ := L2.inner_def v v
    _ = _ := by
      have h (x : X) : ⟪v x, v x⟫_ℂ = Complex.ofReal (‖v x‖^2) := by
        rw [Complex.ofReal_pow]
        exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (v x)
      simp_rw [h]
      exact integral_complex_ofReal

/-- From the standard dense L² eigenvector-span condition, obtain the bounded
measurable eigenfunction approximation hypothesis used for the orbit examples. -/
theorem koopmanDiscreteSpectrum_of_Lp [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (hd : KoopmanDiscreteSpectrumLp hT.toMeasurePreserving) : KoopmanDiscreteSpectrum μ T := by
  classical
  intro f hf ε hε
  obtain ⟨C, hC, hb⟩ := hf.2
  have hfp : MemLp f 2 μ := MemLp.of_bound hf.1.aestronglyMeasurable C (Eventually.of_forall hb)
  let F := hfp.toLp f
  obtain ⟨v, hv, hvDist⟩ := Metric.mem_closure_iff.mp (hd F) (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨k, u, hu, huSum⟩ := eigen_fin_sum_of_mem_span hT.toMeasurePreserving hv
  choose e he using fun i => exists_bounded_eigen_representative hT (hu i)
  let U : Lp ℂ 2 μ := ∑ i, u i
  have hcoe : (U : X → ℂ) =ᵐ[μ] fun x => ∑ i, (e i).value x := by
    refine (Lp.coeFn_fun_finsetSum univ u).trans ?_
    filter_upwards [ae_all_iff.mpr he] with x hx
    exact Finset.sum_congr rfl (fun i _ => (hx i).symm)
  have hEq : ∀ᵐ x ∂μ, (F-U) x = f x - ∑ i, (e i).value x := by
    filter_upwards [Lp.coeFn_sub F U, hfp.coeFn_toLp, hcoe] with x hsub hf' hu'
    rw [hsub]
    change F x = f x at hf'
    change F x - U x = _
    rw [hf', hu']
  refine ⟨k, e, ?_⟩
  have hcalc : (∫ x, ‖f x - ∑ i, (e i).value x‖^2 ∂μ) = ‖F - U‖^2 :=
    (integral_congr_ae (hEq.mono fun x hx => by rw [hx])).symm.trans (norm_sq_L2_eq_integral _).symm
  rw [hcalc, show U = v from huSum, ← Real.sq_sqrt hε.le]
  rw [dist_eq_norm] at hvDist
  exact pow_lt_pow_left₀ hvDist (norm_nonneg _) (by decide)

end
end VdC
