/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorSumFactor
public import Mixing.CantorEigenvectors
public import Mathlib.Tactic.FinCases

/-! # The ultrafilter action on the Cantor sum-coordinate factor -/

@[expose] public section

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing

local notation "𝕋" => UnitAddCircle
local notation "𝕐" => ((UnitAddCircle × UnitAddCircle) × UnitAddCircle)
local notation "haar" => (AddCircle.haarAddCircle : Measure 𝕋)

private def sumTorusHomeomorph : UnitAddTorus (Fin 3) ≃ₜ 𝕐 where
  toFun x := ((x 0, x 1), x 2)
  invFun x := ![x.1.1, x.1.2, x.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := continuous_pi fun i ↦ by fin_cases i <;> fun_prop

private noncomputable def sumTorusPrecomp : C(UnitAddTorus (Fin 3), ℂ) →L[ℂ] C(𝕐, ℂ) := by
  let e : C(𝕐, UnitAddTorus (Fin 3)) := ⟨sumTorusHomeomorph.symm, sumTorusHomeomorph.symm.continuous⟩
  exact ⟨(ContinuousMap.compRightAlgHom ℂ ℂ e).toLinearMap,
    ContinuousMap.compRightAlgHom_continuous ℂ ℂ e⟩

private theorem sumTorusPrecomp_surjective : Function.Surjective sumTorusPrecomp := by
  intro f
  refine ⟨f.comp ⟨sumTorusHomeomorph, sumTorusHomeomorph.continuous⟩, ?_⟩
  ext x
  change f (sumTorusHomeomorph (sumTorusHomeomorph.symm x)) = f x
  rw [sumTorusHomeomorph.apply_symm_apply]

/-- The character in the two base coordinates and the summed fibre coordinate. -/
noncomputable def example6SumCharacter (n : Fin 3 → ℤ) : C(𝕐, ℂ) where
  toFun x := circlePairFourier ![n 0, n 1] x.1 * fourier (n 2) x.2
  continuous_toFun := by fun_prop

private theorem sumTorusPrecomp_fourier (n : Fin 3 → ℤ) :
    sumTorusPrecomp (UnitAddTorus.mFourier n) = example6SumCharacter n := by
  ext x
  change (∏ i : Fin 3, fourier (n i) (sumTorusHomeomorph.symm x i)) =
    (fourier (n 0) x.1.1 * fourier (n 1) x.1.2) * fourier (n 2) x.2
  rw [Fin.prod_univ_succ, Fin.prod_univ_two]
  change fourier (n 0) x.1.1 * (fourier (n 1) x.1.2 * fourier (n 2) x.2) = _
  rw [mul_assoc]

private theorem sumCharacter_dense :
    (Submodule.span ℂ (Set.range example6SumCharacter)).topologicalClosure = ⊤ := by
  have hdense := sumTorusPrecomp_surjective.denseRange.topologicalClosure_map_submodule
    (UnitAddTorus.span_mFourier_closure_eq_top (d := Fin 3))
  have hRange : (⇑sumTorusPrecomp.toLinearMap) ''
      Set.range (UnitAddTorus.mFourier (d := Fin 3)) = Set.range example6SumCharacter := by
    ext f
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (sumTorusPrecomp_fourier n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, sumTorusPrecomp_fourier n⟩
  rwa [Submodule.map_span, hRange] at hdense

/-- The characters as Koopman vectors on the sum-coordinate factor. -/
noncomputable def example6SumCharacterLp (n : Fin 3 → ℤ) : Lp ℂ 2 example6SumSystem.measure :=
  ContinuousMap.toLp (E := ℂ) 2 example6SumSystem.measure ℂ (example6SumCharacter n)

private theorem sumCharacterLp_ae (n : Fin 3 → ℤ) :
    example6SumCharacterLp n =ᵐ[example6SumSystem.measure] example6SumCharacter n :=
  ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) example6SumSystem.measure (example6SumCharacter n)

private theorem sumCharacterLp_dense :
    (Submodule.span ℂ (Set.range example6SumCharacterLp)).topologicalClosure = ⊤ := by
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 example6SumSystem.measure ℂ) :=
    ContinuousMap.toLp_denseRange ℂ example6SumSystem.measure ℂ (by norm_num : (2 : ENNReal) ≠ ⊤)
  have h := hd.topologicalClosure_map_submodule sumCharacter_dense
  rw [Submodule.map_span, ← Set.range_comp'] at h
  exact h

private noncomputable def sumBaseWeight (m n : Fin 3 → ℤ) : C(𝕋 × 𝕋, ℂ) :=
  circlePairFourier ![m 0, m 1] * star (circlePairFourier ![n 0, n 1])

private theorem sumCharacter_coeff (m n : Fin 3 → ℤ) (j : ℤ) :
    ⟪example6SumCharacterLp m,
      example6SumSystem.koopmanRep (Multiplicative.ofAdd j) (example6SumCharacterLp n)⟫_ℂ =
      (∫ b, conj (sumBaseWeight m n b) * fourier (n 2 * j) (example6Angle b) ∂example6Base) *
        ∫ y, fourier (-(m 2) + n 2) y ∂haar := by
  let g := Multiplicative.ofAdd j
  have hpoint (x : 𝕐) :
      conj (example6SumCharacter m x) * example6SumCharacter n (example6SumSystem.act g x) =
      (conj (sumBaseWeight m n x.1) * fourier (n 2 * j) (example6Angle x.1)) *
        fourier (-(m 2) + n 2) x.2 := by
    let b := x.1
    let y := x.2
    let d := example6Angle b
    change conj (circlePairFourier ![m 0, m 1] b * fourier (m 2) y) *
      (circlePairFourier ![n 0, n 1] b * fourier (n 2) (y + j • d)) =
      _ * fourier (-(m 2) + n 2) y
    have hweight :
        conj (sumBaseWeight m n b) =
          conj (circlePairFourier ![m 0, m 1] b) * circlePairFourier ![n 0, n 1] b := by
      simp only [sumBaseWeight, ContinuousMap.mul_apply, ContinuousMap.star_apply,
        map_mul, starRingEnd_apply, star_star]
    rw [hweight, map_mul, ← fourier_neg, fourier_circle_add, fourier_circle_zsmul, fourier_add]
    ring
  have hstep : example6SumSystem.koopmanRep g (example6SumCharacterLp n) =ᵐ[example6SumSystem.measure]
      fun x ↦ example6SumCharacter n (example6SumSystem.act g x) :=
    (Lp.coeFn_compMeasurePreserving _ (example6SumSystem.preserves g)).trans
      ((example6SumSystem.preserves g).quasiMeasurePreserving.ae_eq_comp (sumCharacterLp_ae n))
  rw [MeasureTheory.L2.inner_def]
  change (∫ x : 𝕐, ⟪example6SumCharacterLp m x,
    example6SumSystem.koopmanRep g (example6SumCharacterLp n) x⟫_ℂ ∂example6Base.prod haar) = _
  rw [← integral_prod_mul
    (fun b ↦ conj (sumBaseWeight m n b) * fourier (n 2 * j) (example6Angle b))
    (fun y : 𝕋 ↦ fourier (-(m 2) + n 2) y)]
  apply integral_congr_ae
  filter_upwards [sumCharacterLp_ae m, hstep] with x hx hxstep
  rw [hx, hxstep, RCLike.inner_apply', hpoint]

private theorem sumCharacter_coeff_decay (m n : Fin 3 → ℤ) (hn : n 2 ≠ 0) :
    Tendsto (fun j : ℤ ↦ ⟪example6SumCharacterLp m,
      example6SumSystem.koopmanRep (Multiplicative.ofAdd j) (example6SumCharacterLp n)⟫_ℂ)
      cofinite (𝓝 0) := by
  let h := ContinuousMap.toLp (E := ℂ) 2 example6Base ℂ (sumBaseWeight m n)
  have hEq (j : ℤ) :
      (∫ b, conj (h b) * fourier (n 2 * j) (example6Angle b) ∂example6Base) =
      ∫ b, conj (sumBaseWeight m n b) * fourier (n 2 * j) (example6Angle b) ∂example6Base := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
      example6Base (sumBaseWeight m n)] with b hb
    change h b = sumBaseWeight m n b at hb
    rw [hb]
  have hlim := (example6_weighted_fibre_fourier_tendsto h (n 2) hn).mul
    (tendsto_const_nhds (x := ∫ y, fourier (-(m 2) + n 2) y ∂haar))
  simpa only [hEq, sumCharacter_coeff, zero_mul] using hlim

/-- Every nonzero fibre mode of the sum-coordinate factor is killed by every free ultrafilter. -/
theorem example6_sum_character_annihilated (n : Fin 3 → ℤ) (hn : n 2 ≠ 0)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite) :
    ultrafilterOperator example6SumSystem.koopmanRep p (example6SumCharacterLp n) = 0 := by
  let x := ultrafilterOperator example6SumSystem.koopmanRep p (example6SumCharacterLp n)
  have hspan : Submodule.span ℂ (Set.range example6SumCharacterLp) ≤ (innerSL ℂ x).ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, rfl⟩
    change ⟪x, example6SumCharacterLp m⟫_ℂ = 0
    rw [inner_eq_zero_symm]
    have hi : Function.Injective (Multiplicative.toAdd : Multiplicative ℤ → ℤ) := fun _ _ h ↦ h
    have hc : Tendsto (fun g : Multiplicative ℤ ↦
        ⟪example6SumCharacterLp m, example6SumSystem.koopmanRep g (example6SumCharacterLp n)⟫_ℂ)
        cofinite (𝓝 0) := (sumCharacter_coeff_decay m n hn).comp hi.tendsto_cofinite
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff _ p _ _) (hc.mono_left hp)
  have ht := Submodule.topologicalClosure_minimal _ hspan (innerSL ℂ x).isClosed_ker
  rw [sumCharacterLp_dense] at ht
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (ht Submodule.mem_top)


/-- Pullback along the projection onto the two Cantor base coordinates. -/
noncomputable def example6BaseEmbedding : Lp ℂ 2 example6Base →ₗᵢ[ℂ]
    Lp ℂ 2 example6SumSystem.measure :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst (measurePreserving_fst (ν := haar))

/-- The closed subspace of functions of the base coordinates alone. -/
noncomputable def example6BaseLp : Submodule ℂ (Lp ℂ 2 example6SumSystem.measure) :=
  example6BaseEmbedding.toLinearMap.range

theorem example6BaseLp_closed : IsClosed (example6BaseLp : Set (Lp ℂ 2 example6SumSystem.measure)) :=
  example6BaseEmbedding.isometry.isUniformInducing.isComplete_range.isClosed

private theorem example6BaseEmbedding_koopman_fixed (f : Lp ℂ 2 example6Base)
    (g : Multiplicative ℤ) :
    example6SumSystem.koopmanRep g (example6BaseEmbedding f) = example6BaseEmbedding f := by
  let hπ : MeasurePreserving (Prod.fst : 𝕐 → 𝕋 × 𝕋) example6SumSystem.measure example6Base :=
    measurePreserving_fst (ν := haar)
  have h := Lp.coeFn_compMeasurePreserving f hπ
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving (example6BaseEmbedding f)
      (example6SumSystem.preserves g)).trans
    (((example6SumSystem.preserves g).quasiMeasurePreserving.ae_eq_comp h).trans h.symm)

theorem example6BaseEmbedding_ultrafilter_fixed (f : Lp ℂ 2 example6Base)
    (p : Ultrafilter (Multiplicative ℤ)) :
    ultrafilterOperator example6SumSystem.koopmanRep p (example6BaseEmbedding f) =
      example6BaseEmbedding f := by
  apply ext_inner_left ℂ
  intro y
  have hlim := tendsto_ultrafilterOperator_coeff example6SumSystem.koopmanRep p y
    (example6BaseEmbedding f)
  simp_rw [example6BaseEmbedding_koopman_fixed] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem sumCharacterLp_mem_base (n : Fin 3 → ℤ) (hn : n 2 = 0) :
    example6SumCharacterLp n ∈ example6BaseLp := by
  let f := circlePairFourier ![n 0, n 1]
  let hπ : MeasurePreserving (Prod.fst : 𝕐 → 𝕋 × 𝕋) example6SumSystem.measure example6Base :=
    measurePreserving_fst (ν := haar)
  refine ⟨circlePairFourierLp example6Base ![n 0, n 1], Lp.ext ?_⟩
  refine ((Lp.coeFn_compMeasurePreserving _ hπ).trans
    (hπ.quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) example6Base f))).trans ?_
  have hpoint : (f ∘ Prod.fst) =ᵐ[example6SumSystem.measure] example6SumCharacter n :=
    Eventually.of_forall fun x ↦ by
      change f x.1 = f x.1 * fourier (n 2) x.2
      rw [hn, fourier_zero, mul_one]
  exact hpoint.trans (sumCharacterLp_ae n).symm

/-- The range of every free ultrafilter action is precisely the subspace of base-only functions. -/
theorem example6_sum_ultrafilter_range (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite) :
    (ultrafilterOperator example6SumSystem.koopmanRep p).range = example6BaseLp := by
  let T := ultrafilterOperator example6SumSystem.koopmanRep p
  have hspan : Submodule.span ℂ (Set.range example6SumCharacterLp) ≤
      example6BaseLp.comap T.toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change T (example6SumCharacterLp n) ∈ example6BaseLp
    by_cases hn : n 2 = 0
    · obtain ⟨f, hf⟩ := sumCharacterLp_mem_base n hn
      change example6BaseEmbedding f = example6SumCharacterLp n at hf
      change ultrafilterOperator example6SumSystem.koopmanRep p
        (example6SumCharacterLp n) ∈ example6BaseLp
      rw [← hf, example6BaseEmbedding_ultrafilter_fixed]
      exact LinearMap.mem_range_self example6BaseEmbedding.toLinearMap f
    · rw [example6_sum_character_annihilated n hn p hp]
      exact Submodule.zero_mem _
  have ht := Submodule.topologicalClosure_minimal _ hspan
    (example6BaseLp_closed.preimage T.continuous)
  rw [sumCharacterLp_dense] at ht
  refine le_antisymm ?_ ?_
  · rintro _ ⟨f, rfl⟩
    exact ht Submodule.mem_top
  · rintro _ ⟨f, rfl⟩
    exact ⟨example6BaseEmbedding f, example6BaseEmbedding_ultrafilter_fixed f p⟩

/-- The free ultrafilter action on the factor in Examples 6 and 7 is a self-adjoint
projection onto the base-only subspace. -/
theorem example6_sum_ultrafilter_projection (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite) :
    let T := ultrafilterOperator example6SumSystem.koopmanRep p
    T * T = T ∧ IsSelfAdjoint T ∧ T.range = example6BaseLp := by
  let T := ultrafilterOperator example6SumSystem.koopmanRep p
  have hr := example6_sum_ultrafilter_range p hp
  have hI : T * T = T := by
    apply ContinuousLinearMap.ext
    intro f
    have hf : T f ∈ example6BaseLp := by
      rw [← hr]
      exact LinearMap.mem_range_self T.toLinearMap f
    obtain ⟨u, hu⟩ := hf
    change example6BaseEmbedding u = T f at hu
    change T (T f) = T f
    rw [← hu, example6BaseEmbedding_ultrafilter_fixed]
  exact ⟨hI, isSelfAdjoint_of_idempotent_contraction T hI
    (ultrafilterOperator_norm_le_one example6SumSystem.koopmanRep p), hr⟩

theorem example6SumCharacterLp_ne_zero (n : Fin 3 → ℤ) : example6SumCharacterLp n ≠ 0 := by
  intro hzero
  have hAE : example6SumCharacterLp n =ᵐ[example6SumSystem.measure] (fun _ : 𝕐 ↦ (0 : ℂ)) := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 example6SumSystem.measure
  obtain ⟨x, hx, hxzero⟩ := ((sumCharacterLp_ae n).and hAE).exists
  have hnorm : ‖example6SumCharacter n x‖ = 1 := by
    change ‖(fourier (n 0) x.1.1 * fourier (n 1) x.1.2) * fourier (n 2) x.2‖ = 1
    simp only [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  rw [← hx, hxzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- The projection in Example 6 has proper range, since it kills the nonzero fibre mode one. -/
theorem example6BaseLp_ne_top : example6BaseLp ≠ ⊤ := by
  intro htop
  let n : Fin 3 → ℤ := ![0, 0, 1]
  have hn : n 2 ≠ 0 := one_ne_zero
  have hmem : example6SumCharacterLp n ∈ example6BaseLp := htop ▸ Submodule.mem_top
  obtain ⟨f, hf⟩ := hmem
  change example6BaseEmbedding f = example6SumCharacterLp n at hf
  let p : Ultrafilter (Multiplicative ℤ) := Ultrafilter.of cofinite
  have h := example6_sum_character_annihilated n hn p (Ultrafilter.of_le cofinite)
  rw [← hf, example6BaseEmbedding_ultrafilter_fixed, hf] at h
  exact example6SumCharacterLp_ne_zero n h

end Mixing
