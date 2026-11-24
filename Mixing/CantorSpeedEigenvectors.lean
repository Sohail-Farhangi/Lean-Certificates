/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorEigenvectors

/-! # Ultrafilter eigenvectors for the Cantor skew rotations of arbitrary integer speed -/

@[expose] public section

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing

private theorem cantorSpeed_correlations (s a b c d : ℤ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    Tendsto (fun g : Multiplicative ℤ ↦
      ∫ x, example5CantorCharacter a b x *
        example5CantorCharacter d c ((circleSkew cantorCircleMeasure s).act g x)
        ∂(circleSkew cantorCircleMeasure s).measure)
      (p : Filter (Multiplicative ℤ)) (𝓝 (cantorFourier ((-(a + d) : ℤ) : ℝ) *
        cantorFourier ((-c * s : ℤ) : ℝ) *
        (∫ y : UnitAddCircle, fourier (b + c) y ∂AddCircle.haarAddCircle))) := by
  have hInj : Function.Injective (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 4)).injective
  refine (tendsto_injective_sequence_iff _ hInj (fun g ↦
    ∫ x, example5CantorCharacter a b x *
      example5CantorCharacter d c ((circleSkew cantorCircleMeasure s).act g x)
      ∂(circleSkew cantorCircleMeasure s).measure) _).mp ?_ p hp hsupp
  have hfinite (j : ℕ) :
      (∫ x, example5CantorCharacter a b x *
        example5CantorCharacter d c
          ((circleSkew cantorCircleMeasure s).act (Multiplicative.ofAdd ((4 : ℤ)^j)) x)
        ∂(circleSkew cantorCircleMeasure s).measure) =
        cantorFourier (((-c * s) * (4 : ℤ)^j + (-(a + d)) : ℤ) : ℝ) *
          (∫ y : UnitAddCircle, fourier (b + c) y ∂AddCircle.haarAddCircle) := by
    have hact : (circleSkew cantorCircleMeasure s).act (Multiplicative.ofAdd ((4 : ℤ)^j)) =
        (circleSkew cantorCircleMeasure 1).act (Multiplicative.ofAdd ((4 : ℤ)^j * s)) := by
      funext x
      change (x.1, x.2 + ((4 : ℤ)^j * s) • x.1) =
        (x.1, x.2 + (((4 : ℤ)^j * s) * 1) • x.1)
      rw [mul_one]
    have hi : (-c * ((4 : ℤ)^j * s) - (a + d)) =
        (-c * s) * (4 : ℤ)^j + -(a + d) := by ring
    rw [hact]
    change (∫ x, example5CantorCharacter a b x *
        example5CantorCharacter d c
          ((circleSkew cantorCircleMeasure 1).act (Multiplicative.ofAdd ((4 : ℤ)^j * s)) x)
        ∂(circleSkew cantorCircleMeasure 1).measure) = _
    rw [example5_cantor_character_correlation, hi]
  change Tendsto (fun j : ℕ ↦
    ∫ x, example5CantorCharacter a b x * example5CantorCharacter d c
      ((circleSkew cantorCircleMeasure s).act (Multiplicative.ofAdd ((4 : ℤ)^j)) x)
      ∂(circleSkew cantorCircleMeasure s).measure) atTop _
  simp_rw [hfinite]
  exact (cantorFourier_tendsto_four_pow_add (-c * s) (-(a + d))).mul tendsto_const_nhds

private theorem cantorSpeed_inner (s : ℤ) (m n : Fin 2 → ℤ) (g : Multiplicative ℤ) :
    let T := circleSkew cantorCircleMeasure s
    ⟪circlePairFourierLp T.measure m, T.koopmanRep g (circlePairFourierLp T.measure n)⟫_ℂ =
      ∫ x, example5CantorCharacter (-(m 0)) (-(m 1)) x *
        example5CantorCharacter (n 0) (n 1) (T.act g x) ∂T.measure := by
  let T := circleSkew cantorCircleMeasure s
  change ⟪circlePairFourierLp T.measure m, T.koopmanRep g (circlePairFourierLp T.measure n)⟫_ℂ = _
  rw [MeasureTheory.L2.inner_def]
  have hn : T.koopmanRep g (circlePairFourierLp T.measure n) =ᵐ[T.measure]
      fun x ↦ example5CantorCharacter (n 0) (n 1) (T.act g x) :=
    (Lp.coeFn_compMeasurePreserving _ (T.preserves g)).trans
      ((T.preserves g).quasiMeasurePreserving.ae_eq_comp (circlePairFourierLp_ae_eq T.measure n))
  apply integral_congr_ae
  filter_upwards [circlePairFourierLp_ae_eq T.measure m, hn] with x hmx hnx
  rw [hmx, hnx, RCLike.inner_apply']
  simp only [example5CantorCharacter, map_mul, ← fourier_neg]
  rfl

/-- The Cantor character eigenvalue for a skew rotation of integer speed. -/
theorem cantorSpeed_ultrafilter_eigenvector (s : ℤ) (n : Fin 2 → ℤ)
    (p : Ultrafilter (Multiplicative ℤ)) (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    let T := circleSkew cantorCircleMeasure s
    ultrafilterOperator T.koopmanRep p (circlePairFourierLp T.measure n) =
      cantorFourier ((-(n 1) * s : ℤ) : ℝ) • circlePairFourierLp T.measure n := by
  let T := circleSkew cantorCircleMeasure s
  let v := circlePairFourierLp T.measure n
  let c := cantorFourier ((-(n 1) * s : ℤ) : ℝ)
  let y := ultrafilterOperator T.koopmanRep p v - c • v
  have hinner (m : Fin 2 → ℤ) :
      ⟪circlePairFourierLp T.measure m, ultrafilterOperator T.koopmanRep p v⟫_ℂ =
        ⟪circlePairFourierLp T.measure m, c • v⟫_ℂ := by
    have hlim := tendsto_ultrafilterOperator_coeff T.koopmanRep p
      (circlePairFourierLp T.measure m) v
    change Tendsto (fun g ↦ ⟪circlePairFourierLp T.measure m,
      T.koopmanRep g (circlePairFourierLp T.measure n)⟫_ℂ) _ _ at hlim
    have hlim' := hlim.congr (fun g ↦ cantorSpeed_inner s m n g)
    have hvalue := tendsto_nhds_unique hlim'
      (cantorSpeed_correlations s (-(m 0)) (-(m 1)) (n 1) (n 0) p hp hsupp)
    have hbase :
        ⟪circlePairFourierLp T.measure m, v⟫_ℂ =
          cantorFourier ((-(-(m 0) + n 0) : ℤ) : ℝ) *
            ∫ y : UnitAddCircle, fourier (-(m 1) + n 1) y ∂AddCircle.haarAddCircle := by
      have ht := cantorSpeed_inner s m n 1
      change ⟪circlePairFourierLp T.measure m, T.koopmanRep 1 v⟫_ℂ = _ at ht
      have hact₁ : T.act 1 = id := T.act_one
      rw [map_one, hact₁] at ht
      have h₀ := example5_cantor_character_correlation (-(m 0)) (-(m 1)) (n 1) (n 0) 0
      rw [show Multiplicative.ofAdd (0 : ℤ) = 1 from rfl,
        (circleSkew cantorCircleMeasure 1).act_one, mul_zero, zero_sub] at h₀
      exact ht.trans h₀
    rw [hvalue, inner_smul_right, hbase]
    dsimp only [c]
    ring
  have hspan : Submodule.span ℂ (Set.range (circlePairFourierLp T.measure)) ≤ (innerSL ℂ y).ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, rfl⟩
    change ⟪y, circlePairFourierLp T.measure m⟫_ℂ = 0
    rw [inner_eq_zero_symm]
    dsimp only [y]
    rw [inner_sub_right, hinner, sub_self]
  have ht := Submodule.topologicalClosure_minimal _ hspan (innerSL ℂ y).isClosed_ker
  rw [circlePairFourierLp_closure_span] at ht
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp (ht Submodule.mem_top))

end Mixing
