/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconTowerPolynomialLimits
public import Mixing.BoundedKoopman

/-! # The weak operator polynomial limits along the Chacon heights -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

/-- The powers of the Chacon map along multiples of the cutting-and-stacking heights. -/
def chaconHeightTime (m n : ℕ) : Multiplicative ℤ :=
  Multiplicative.ofAdd (↑(m*chaconTowerHeight n) : ℤ)

/-- The polynomial in the inverse Koopman operator, with coefficients given by
the law of the number of crossed spacers. -/
noncomputable def chaconHeightPolynomialOperator (m : ℕ) :
    Lp ℂ 2 chaconTowerSystem.measure →L[ℂ] Lp ℂ 2 chaconTowerSystem.measure :=
  ∑ k ∈ Finset.range (m+1), chaconSpacerProbability m k •
    (chaconTowerSystem.koopmanRep (Multiplicative.ofAdd (-(k : ℤ))) : _ →L[ℂ] _)

private theorem chaconHeight_coeff_bounded (g : Multiplicative ℤ)
    (X Y : BoundedObservable (ChaconOdometer × Bool)) :
    inner ℂ (X.l2 chaconTowerSystem.measure)
        (chaconTowerSystem.koopmanRep g (Y.l2 chaconTowerSystem.measure)) =
      ∫ x, X.conjugate x * Y (chaconTowerSystem.act g x) ∂chaconTowerSystem.measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [X.coe_l2 chaconTowerSystem.measure, chaconTowerSystem.koopman_ae_observable g Y] with x hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply', BoundedObservable.conjugate_apply, System.translated_apply]

private theorem tendsto_chaconHeight_coeff_bounded (m : ℕ)
    (X Y : BoundedObservable (ChaconOdometer × Bool)) :
    Tendsto (fun n : ℕ ↦ inner ℂ (X.l2 chaconTowerSystem.measure)
      (chaconTowerSystem.koopmanRep (chaconHeightTime m n)
        (Y.l2 chaconTowerSystem.measure))) atTop
      (𝓝 (inner ℂ (X.l2 chaconTowerSystem.measure)
        (chaconHeightPolynomialOperator m (Y.l2 chaconTowerSystem.measure)))) := by
  have h := tendsto_chaconTower_polynomial_correlations m Y.measurable X.conjugate.measurable
    X.conjugate.bound_nonneg Y.norm_le X.conjugate.norm_le
  have hcoer (g : Multiplicative ℤ) :
      ((chaconTowerSystem.koopmanRep g : _ →L[ℂ] _) (Y.l2 chaconTowerSystem.measure)) =
        chaconTowerSystem.koopmanRep g (Y.l2 chaconTowerSystem.measure) := rfl
  simp only [chaconHeightPolynomialOperator, sum_apply, smul_apply, inner_sum,
    inner_smul_right_eq_smul, hcoer, chaconHeight_coeff_bounded, chaconHeightTime]
  exact h

/-- Every ultrafilter refining the sequence of tower heights gives the
polynomial limit on the entire Chacon L² space. -/
theorem ultrafilterOperator_chaconHeight (m : ℕ) (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    ultrafilterOperator chaconTowerSystem.koopmanRep (p.map (chaconHeightTime m)) =
      chaconHeightPolynomialOperator m := by
  let L := ultrafilterOperator chaconTowerSystem.koopmanRep (p.map (chaconHeightTime m))
  let Q := chaconHeightPolynomialOperator m
  have hT : Tendsto (chaconHeightTime m) (p : Filter ℕ) ((p.map (chaconHeightTime m) : Ultrafilter _) : Filter _) :=
    le_rfl
  have hBound (X Y : BoundedObservable (ChaconOdometer × Bool)) :
      inner ℂ (X.l2 chaconTowerSystem.measure) (L (Y.l2 chaconTowerSystem.measure)) =
        inner ℂ (X.l2 chaconTowerSystem.measure) (Q (Y.l2 chaconTowerSystem.measure)) := by
    have hL := (tendsto_ultrafilterOperator_coeff chaconTowerSystem.koopmanRep
      (p.map (chaconHeightTime m)) (X.l2 chaconTowerSystem.measure) (Y.l2 chaconTowerSystem.measure)).comp hT
    exact tendsto_nhds_unique hL ((tendsto_chaconHeight_coeff_bounded m X Y).mono_left hp)
  apply ContinuousLinearMap.ext
  intro y
  apply (ext_iff_inner_left ℂ).2
  intro x
  refine (BoundedObservable.denseRange_l2 chaconTowerSystem.measure).induction_on₂ ?_ hBound x y
  exact isClosed_eq (continuous_fst.inner (L.continuous.comp continuous_snd))
    (continuous_fst.inner (Q.continuous.comp continuous_snd))

/-- Janvresse–Prikhod’ko–de la Rue–Ryzhikov, Theorem 2.2, for the concrete
odometer tower, expressed as convergence of every weak operator coefficient. -/
theorem tendsto_chaconHeight_koopman_coeff (m : ℕ)
    (v w : Lp ℂ 2 chaconTowerSystem.measure) :
    Tendsto (fun n ↦ inner ℂ v (chaconTowerSystem.koopmanRep (chaconHeightTime m n) w)) atTop
      (𝓝 (inner ℂ v (chaconHeightPolynomialOperator m w))) := by
  rw [tendsto_iff_ultrafilter]
  intro p hp
  have hT : Tendsto (chaconHeightTime m) (p : Filter ℕ) ((p.map (chaconHeightTime m) : Ultrafilter _) : Filter _) :=
    le_rfl
  have h := (tendsto_ultrafilterOperator_coeff chaconTowerSystem.koopmanRep
    (p.map (chaconHeightTime m)) v w).comp hT
  change Tendsto (fun n ↦ inner ℂ v (chaconTowerSystem.koopmanRep (chaconHeightTime m n) w)) _
    (𝓝 (inner ℂ v (ultrafilterOperator chaconTowerSystem.koopmanRep
      (p.map (chaconHeightTime m)) w))) at h
  rwa [ultrafilterOperator_chaconHeight m p hp] at h

end Mixing
