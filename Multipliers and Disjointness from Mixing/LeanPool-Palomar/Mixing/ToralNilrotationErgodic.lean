/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ToralNilrotationBasis
public import Mixing.ErgodicBarycenters
public import Mathlib.NumberTheory.Real.Irrational

/-! # Ergodicity of an irrational toral nilrotation -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing.ToralNilrotation

variable (α : UnitAddCircle)

private theorem phase_horizontal_one_step (k : ℤ) :
    phase α (Multiplicative.ofAdd 1) (k, 0) = (AddCircle.toCircle (k • α) : ℂ) := by
  simp only [phase, toAdd_ofAdd, zpow_one, fourier_apply,
    zero_zsmul, AddCircle.toCircle_zero, Circle.coe_one, mul_one]
  rfl

private theorem phase_horizontal_ne_one (k : ℤ) (hk : k • α ≠ 0) :
    phase α (Multiplicative.ofAdd 1) (k, 0) ≠ 1 := by
  rw [phase_horizontal_one_step]
  intro he
  apply hk
  apply AddCircle.injective_toCircle one_ne_zero
  rw [AddCircle.toCircle_zero]
  exact Subtype.ext he

/-- A fixed Koopman vector is almost everywhere constant for an irrational parameter. -/
theorem fixed_ae_const (hα : ∀ k : ℤ, k ≠ 0 → k • α ≠ 0)
    (f : Lp ℂ 2 (system α).measure) (hf : ∀ g, (system α).koopmanRep g f = f) :
    ∃ c : ℂ, f =ᵐ[(system α).measure] (fun _ => c) := by
  let c := ⟪mode α (0, 0), f⟫_ℂ
  have hfP : f ∈ purePointPart (system α).koopmanRep :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, fun g => by simpa using hf g⟩)
  have hOrth (u : ℤ × ℤ) (hu : u ≠ (0, 0)) : ⟪mode α u, f⟫_ℂ = 0 := by
    by_cases hv : u.2 = 0
    · have hk : u.1 ≠ 0 := fun hz => hu (Prod.ext hz hv)
      let g := Multiplicative.ofAdd (1 : ℤ)
      have hU := ((system α).koopmanRep g).inner_map_map (mode α (u.1, 0)) f
      rw [hf, koopman_mode] at hU
      simp only [zero_mul, add_zero, inner_smul_left] at hU
      have hne : conj (phase α g (u.1, 0)) - 1 ≠ 0 := by
        rw [sub_ne_zero]
        intro he
        exact phase_horizontal_ne_one α u.1 (hα _ hk) (by
          have h := congrArg (starRingEnd ℂ) he
          simpa only [starRingEnd_self_apply, map_one] using h)
      have hz : (conj (phase α g (u.1, 0)) - 1) * ⟪mode α (u.1, 0), f⟫_ℂ = 0 := by
        rw [sub_mul, hU, one_mul, sub_self]
      rw [show u = (u.1, 0) from Prod.ext rfl hv]
      exact (mul_eq_zero.mp hz).resolve_left hne
    · rw [← inner_conj_symm, vertical_mode_mem_purePointPart_orthogonal α u hv f hfP, map_zero]
  have he : f - c • mode α (0, 0) = 0 := by
    apply eq_zero_of_mode_inner α
    intro u
    rw [inner_sub_right, inner_smul_right, inner_mode]
    by_cases hu : u = (0, 0)
    · subst u
      rw [ite_eq_left rfl, mul_one, sub_self]
    · rw [hOrth u hu, ite_eq_right hu, mul_zero, sub_zero]
  refine ⟨c, ?_⟩
  rw [sub_eq_zero.mp he]
  filter_upwards [Lp.coeFn_smul c (mode α (0, 0)), mode_ae α (0, 0)] with x hs hm
  rw [hs, Pi.smul_apply, hm]
  simp

/-- The skew shift with an irrational parameter is ergodic for product Haar measure. -/
theorem isErgodic (hα : ∀ k : ℤ, k ≠ 0 → k • α ≠ 0) : (system α).IsErgodic := by
  intro A hA hInv
  let S := system α
  let f := indicatorConstLp 2 hA (measure_ne_top S.measure A) (1 : ℂ)
  have hF : f =ᵐ[S.measure] A.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
  have hf (g : Multiplicative ℤ) : S.koopmanRep g f = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving f (S.preserves g),
      (S.preserves g).quasiMeasurePreserving.ae_eq_comp hF, hF, hInv g] with x h1 h2 h3 h4
    change (↑↑(S.koopmanRep g f) : Torus → ℂ) x = f x
    change f (S.act g x) = A.indicator (fun _ => (1 : ℂ)) (S.act g x) at h2
    rw [show (S.koopmanRep g f : Torus → ℂ) x = f (S.act g x) from h1, h2, h3]
    change (S.act g x ∈ A ↔ x ∈ A) at h4
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem (h4.mpr hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun hh => hx (h4.mp hh)), Set.indicator_of_notMem hx]
  obtain ⟨c, hc⟩ := fixed_ae_const α hα f hf
  have he := hF.symm.trans hc
  apply eventuallyEmptyOrUniv_iff.mpr
  by_cases hc0 : c = 0
  · right
    filter_upwards [he] with x hx hAx
    rw [Set.indicator_of_mem hAx, hc0] at hx
    exact one_ne_zero hx
  · left
    filter_upwards [he] with x hx
    by_contra hAx
    rw [Set.indicator_of_notMem hAx] at hx
    exact hc0 hx.symm

/-- A fully specified irrational parameter, the class of the square root of two. -/
noncomputable def irrationalParameter : UnitAddCircle := (Real.sqrt 2 : ℝ)

theorem irrationalParameter_zsmul_ne_zero (k : ℤ) (hk : k ≠ 0) :
    k • irrationalParameter ≠ 0 := by
  intro h
  change k • ((Real.sqrt 2 : ℝ) : AddCircle (1 : ℝ)) = 0 at h
  rw [← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  apply (irrational_iff_ne_rational _).mp irrational_sqrt_two n k hk
  apply (eq_div_iff (Int.cast_ne_zero.mpr hk)).mpr
  simpa only [zsmul_eq_mul, mul_one, mul_comm] using hn.symm

theorem example1_ergodic_toral_nilrotation : (system irrationalParameter).IsErgodic :=
  isErgodic irrationalParameter irrationalParameter_zsmul_ne_zero

end Mixing.ToralNilrotation
