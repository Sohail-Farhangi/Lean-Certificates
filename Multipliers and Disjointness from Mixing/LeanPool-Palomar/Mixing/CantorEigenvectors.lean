/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorSpectral
public import Mixing.Koopman
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Ultrafilter eigenvectors in the Cantor skew rotation -/

@[expose] public section

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing

local notation "𝕋" => UnitAddCircle
local notation "𝕏" => (UnitAddCircle × UnitAddCircle)

private def torusAsProduct : UnitAddTorus (Fin 2) ≃ₜ 𝕏 := Homeomorph.finTwoArrow

private noncomputable def torusPrecomposition : C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] C(𝕏, ℂ) := by
  let e : C(𝕏, UnitAddTorus (Fin 2)) := ⟨torusAsProduct.symm, torusAsProduct.symm.continuous⟩
  exact ⟨(ContinuousMap.compRightAlgHom ℂ ℂ e).toLinearMap,
    ContinuousMap.compRightAlgHom_continuous ℂ ℂ e⟩

private theorem torusPrecomposition_surjective : Function.Surjective torusPrecomposition := by
  intro f
  refine ⟨f.comp ⟨torusAsProduct, torusAsProduct.continuous⟩, ?_⟩
  ext x
  change f (torusAsProduct (torusAsProduct.symm x)) = f x
  rw [torusAsProduct.apply_symm_apply]

/-- The two-frequency continuous character on the base and fibre circle. -/
noncomputable def circlePairFourier (n : Fin 2 → ℤ) : C(𝕏, ℂ) where
  toFun := example5CantorCharacter (n 0) (n 1)
  continuous_toFun := by unfold example5CantorCharacter; fun_prop

theorem circlePairFourier_apply (n : Fin 2 → ℤ) (x : 𝕏) :
    circlePairFourier n x = example5CantorCharacter (n 0) (n 1) x := rfl

private theorem torusPrecomposition_mFourier (n : Fin 2 → ℤ) :
    torusPrecomposition (UnitAddTorus.mFourier n) = circlePairFourier n := by
  ext x
  change (∏ i : Fin 2, fourier (n i) (torusAsProduct.symm x i)) =
    example5CantorCharacter (n 0) (n 1) x
  rw [Fin.prod_univ_two]
  rfl

private theorem circlePairFourier_closure_span :
    (Submodule.span ℂ (Set.range circlePairFourier)).topologicalClosure = ⊤ := by
  have hdense := torusPrecomposition_surjective.denseRange.topologicalClosure_map_submodule
    (UnitAddTorus.span_mFourier_closure_eq_top (d := Fin 2))
  have hRange : (⇑torusPrecomposition.toLinearMap) ''
      Set.range (UnitAddTorus.mFourier (d := Fin 2)) = Set.range circlePairFourier := by
    ext f
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (torusPrecomposition_mFourier n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨n, rfl⟩, torusPrecomposition_mFourier n⟩
  rwa [Submodule.map_span, hRange] at hdense

/-- The two-frequency character viewed as a vector in the complex L² space. -/
noncomputable def circlePairFourierLp (μ : Measure 𝕏) [IsFiniteMeasure μ]
    (n : Fin 2 → ℤ) : Lp ℂ 2 μ :=
  ContinuousMap.toLp (E := ℂ) 2 μ ℂ (circlePairFourier n)

theorem circlePairFourierLp_ae_eq (μ : Measure 𝕏) [IsFiniteMeasure μ]
    (n : Fin 2 → ℤ) : circlePairFourierLp μ n =ᵐ[μ] example5CantorCharacter (n 0) (n 1) := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) μ (circlePairFourier n)] with x hx
  exact hx.trans (circlePairFourier_apply n x)

theorem circlePairFourierLp_closure_span (μ : Measure 𝕏) [IsFiniteMeasure μ] [μ.WeaklyRegular] :
    (Submodule.span ℂ (Set.range (circlePairFourierLp μ))).topologicalClosure = ⊤ := by
  have hLp : DenseRange (ContinuousMap.toLp (E := ℂ) 2 μ ℂ) :=
    ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hdense := hLp.topologicalClosure_map_submodule circlePairFourier_closure_span
  rw [Submodule.map_span, ← Set.range_comp'] at hdense
  exact hdense

/-- The Cantor skew rotation in Example 5. -/
noncomputable def example5CantorSystem : System (Multiplicative ℤ) 𝕏 :=
  circleSkew cantorCircleMeasure 1

theorem cantorSkew_inner_character (m n : Fin 2 → ℤ) (g : Multiplicative ℤ) :
    ⟪circlePairFourierLp example5CantorSystem.measure m, example5CantorSystem.koopmanRep g (circlePairFourierLp example5CantorSystem.measure n)⟫_ℂ =
      ∫ x, example5CantorCharacter (-(m 0)) (-(m 1)) x *
        example5CantorCharacter (n 0) (n 1) (example5CantorSystem.act g x) ∂example5CantorSystem.measure := by
  rw [MeasureTheory.L2.inner_def]
  have hn : example5CantorSystem.koopmanRep g (circlePairFourierLp example5CantorSystem.measure n) =ᵐ[example5CantorSystem.measure]
      fun x ↦ example5CantorCharacter (n 0) (n 1) (example5CantorSystem.act g x) :=
    (Lp.coeFn_compMeasurePreserving _ (example5CantorSystem.preserves g)).trans
      ((example5CantorSystem.preserves g).quasiMeasurePreserving.ae_eq_comp (circlePairFourierLp_ae_eq example5CantorSystem.measure n))
  refine integral_congr_ae ?_
  filter_upwards [circlePairFourierLp_ae_eq example5CantorSystem.measure m, hn] with x hmx hnx
  rw [hmx, hnx, RCLike.inner_apply']
  simp only [example5CantorCharacter, map_mul, ← fourier_neg]

private theorem cantorSkew_ultrafilter_inner_character (m n : Fin 2 → ℤ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    ⟪circlePairFourierLp example5CantorSystem.measure m,
      ultrafilterOperator example5CantorSystem.koopmanRep p (circlePairFourierLp example5CantorSystem.measure n)⟫_ℂ =
      ⟪circlePairFourierLp example5CantorSystem.measure m,
        cantorFourier ((-(n 1) : ℤ) : ℝ) • circlePairFourierLp example5CantorSystem.measure n⟫_ℂ := by
  have hlim := tendsto_ultrafilterOperator_coeff example5CantorSystem.koopmanRep p
    (circlePairFourierLp example5CantorSystem.measure m) (circlePairFourierLp example5CantorSystem.measure n)
  simp_rw [cantorSkew_inner_character] at hlim
  have hvalue := tendsto_nhds_unique hlim
    (example5_cantor_character_correlation_tendsto_ultrafilter (-(m 0)) (-(m 1)) (n 1) (n 0)
      p hp hsupp)
  have h₀ := (cantorSkew_inner_character m n (Multiplicative.ofAdd 0)).trans
    (example5_cantor_character_correlation (-(m 0)) (-(m 1)) (n 1) (n 0) 0)
  rw [show Multiplicative.ofAdd (0 : ℤ) = 1 from rfl, map_one] at h₀
  change ⟪circlePairFourierLp example5CantorSystem.measure m, circlePairFourierLp example5CantorSystem.measure n⟫_ℂ = _ at h₀
  rw [hvalue, inner_smul_right, h₀, mul_zero, zero_sub]
  ring

/-- The ultrafilter eigenvector equation in Example 5, on the actual Koopman L² space. -/
theorem example5_cantor_ultrafilter_eigenvector (n : Fin 2 → ℤ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    ultrafilterOperator example5CantorSystem.koopmanRep p (circlePairFourierLp example5CantorSystem.measure n) =
      cantorFourier ((-(n 1) : ℤ) : ℝ) • circlePairFourierLp example5CantorSystem.measure n := by
  let y := ultrafilterOperator example5CantorSystem.koopmanRep p (circlePairFourierLp example5CantorSystem.measure n) -
    cantorFourier ((-(n 1) : ℤ) : ℝ) • circlePairFourierLp example5CantorSystem.measure n
  have hspan : Submodule.span ℂ (Set.range (circlePairFourierLp example5CantorSystem.measure)) ≤
      (innerSL ℂ y).ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, rfl⟩
    change ⟪y, circlePairFourierLp example5CantorSystem.measure m⟫_ℂ = 0
    rw [inner_eq_zero_symm]
    dsimp only [y]
    rw [inner_sub_right,
      cantorSkew_ultrafilter_inner_character m n p hp hsupp, sub_self]
  have htop := Submodule.topologicalClosure_minimal _ hspan (innerSL ℂ y).isClosed_ker
  rw [circlePairFourierLp_closure_span] at htop
  have hy : ⟪y, y⟫_ℂ = 0 := htop Submodule.mem_top
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hy)


/-- A character has unit pointwise norm and gives a nonzero vector for every probability measure. -/
theorem circlePairFourierLp_ne_zero (μ : Measure 𝕏) [IsProbabilityMeasure μ] (n : Fin 2 → ℤ) :
    circlePairFourierLp μ n ≠ 0 := by
  intro hzero
  have hAE : circlePairFourierLp μ n =ᵐ[μ] (fun _ : 𝕏 ↦ (0 : ℂ)) := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 μ
  obtain ⟨x, hx, hxzero⟩ := ((circlePairFourierLp_ae_eq μ n).and hAE).exists
  have hnorm : ‖example5CantorCharacter (n 0) (n 1) x‖ = 1 := by
    simp only [example5CantorCharacter, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  rw [← hx, hxzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- The fibre character of frequency two is a nonzero p-mixing vector in Example 5. -/
theorem example5_cantor_annihilated_fibre_character
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    ∃ f : Lp ℂ 2 example5CantorSystem.measure, f ≠ 0 ∧
      ultrafilterOperator example5CantorSystem.koopmanRep p f = 0 := by
  let n : Fin 2 → ℤ := ![0, 2]
  refine ⟨circlePairFourierLp example5CantorSystem.measure n, circlePairFourierLp_ne_zero _ _, ?_⟩
  rw [example5_cantor_ultrafilter_eigenvector n p hp hsupp]
  have hz : cantorFourier ((-(n 1) : ℤ) : ℝ) = 0 := by
    have hn₂ : n 1 = 2 := rfl
    rw [hn₂]
    have h := cantorFourier_eq_zero_mod_four_two (-1)
    norm_num at h ⊢
    exact h
  rw [hz, zero_smul]

end Mixing
