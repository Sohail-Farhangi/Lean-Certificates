/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.CompactCoefficients
public import SixProblems.CompactRealRealization
public import SixProblems.ErgodicThresholdComparison
public import SixProblems.OperatorialRecurrenceGaussianMixing
public import SixProblems.OperatorialRecurrenceTruncation
public import SixProblems.RealKoopman
public import SixProblems.StableCoefficients

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing Mixing.JdLGBridge RealRepresentation
open scoped InnerProductSpace

variable {G : Type} [Group G] [Countable G]

omit [Countable G] in
private theorem integral_two_factor_correlation {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (S : System G X) (T : System G Y) (a : X → ℝ) (b : Y → ℝ)
    (ha : MemLp a 2 S.measure) (hb : MemLp b 2 T.measure) (hb0 : ∫ y, b y ∂T.measure = 0)
    (g : G) :
    let F (z : X × Y) := a z.1 + b z.2
    (∫ z, F ((S.prod T).act g z) * F z ∂(S.prod T).measure) =
      (∫ x, a (S.act g x) * a x ∂S.measure) + ∫ y, b (T.act g y) * b y ∂T.measure := by
  let A (x : X) := a (S.act g x)
  let B (y : Y) := b (T.act g y)
  have hA : MemLp A 2 S.measure := ha.comp_measurePreserving (S.preserves g)
  have hB : MemLp B 2 T.measure := hb.comp_measurePreserving (T.preserves g)
  let h₁ (z : X × Y) := (A z.1 * a z.1) * (1 : ℝ)
  let h₂ (z : X × Y) := A z.1 * b z.2
  let h₃ (z : X × Y) := a z.1 * B z.2
  let h₄ (z : X × Y) := (1 : ℝ) * (B z.2 * b z.2)
  have hI₁ : Integrable h₁ (S.measure.prod T.measure) :=
    (hA.integrable_mul ha).mul_prod (integrable_const _)
  have hI₂ : Integrable h₂ (S.measure.prod T.measure) :=
    (hA.integrable (by norm_num)).mul_prod (hb.integrable (by norm_num))
  have hI₃ : Integrable h₃ (S.measure.prod T.measure) :=
    (ha.integrable (by norm_num)).mul_prod (hB.integrable (by norm_num))
  have hI₄ : Integrable h₄ (S.measure.prod T.measure) :=
    (integrable_const _).mul_prod (hB.integrable_mul hb)
  have hB0 : ∫ y, B y ∂T.measure = 0 := by
    exact (integral_comp_preserving (T.preserves g) (g := b) hb.aestronglyMeasurable).trans hb0
  change (∫ z : X × Y, (A z.1 + B z.2) * (a z.1 + b z.2) ∂S.measure.prod T.measure) = _
  have he (z : X × Y) : (A z.1+B z.2)*(a z.1+b z.2) = h₁ z + h₂ z + h₃ z + h₄ z := by
    dsimp [h₁,h₂,h₃,h₄]
    ring
  simp_rw [he]
  have hI₁₂ : Integrable (fun z ↦ h₁ z+h₂ z) (S.measure.prod T.measure) := hI₁.add hI₂
  have hI₁₂₃ : Integrable (fun z ↦ h₁ z+h₂ z+h₃ z) (S.measure.prod T.measure) := hI₁₂.add hI₃
  rw [integral_add hI₁₂₃ hI₄, integral_add hI₁₂ hI₃, integral_add hI₁ hI₂]
  simp only [h₁,h₂,h₃,h₄, integral_prod_mul, mul_one, one_mul, hb0, hB0, mul_zero, add_zero]
  rw [integral_fun_fst (fun x ↦ A x*a x), integral_fun_snd (fun y ↦ B y*b y),
    probReal_univ, probReal_univ, one_smul, one_smul]

/-- Splitting an orthogonal representation into its compact and weakly stable
parts gives bounded approximations to its coefficients in ergodic systems. -/
theorem exists_ergodic_coefficient_approximation {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : G →* (E ≃ₗᵢ[ℝ] E)) (v : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      S.IsErgodic ∧ Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ ∀ g,
      |(∫ x, f (S.act g x) * f x ∂S.measure) - ⟪v,U g v⟫_ℝ| < ε := by
  obtain ⟨K,hK⟩ := orthogonalAction_exists_groupIdeal U
  let π := (orthogonalActionCLM U).toMulHom
  let P := K.projection (closureAction π)
  let z := v-P v
  have hz : P z = 0 := by dsimp only [z]; rw [map_sub, K.projection_apply_apply, sub_self]
  have hPc : ∀ x, ‖P x‖ ≤ ‖x‖ := orthogonalAction_closure_contractive U K.identity
  have hPi : ∀ x, P (P x) = P x := K.projection_apply_apply (closureAction π)
  have hPcomm (g : G) (x : E) : P (U g x) = U g (P x) :=
    K.projection_commutes (closureAction π) (closureInclusion π g) x
  have hSplit (g : G) : ⟪v,U g v⟫_ℝ = ⟪P v,U g (P v)⟫_ℝ + ⟪z,U g z⟫_ℝ := by
    have hLeft : ⟪P v,U g z⟫_ℝ = 0 := contractive_projection_orthogonal P hPc (hPi v)
      (by rw [hPcomm,hz,map_zero])
    have hRight : ⟪z,U g (P v)⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact contractive_projection_orthogonal P hPc (by rw [hPcomm,hPi]) hz
    conv_lhs => rw [show v = P v + z by dsimp [z]; abel]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hLeft,hRight,add_zero,zero_add]
  obtain ⟨V,hV,hVI,w,hw⟩ := exists_finite_approximation_of_groupIdeal U K hK v (ε/2) (half_pos hε)
  let := hV
  let U₀ := unitarySubmoduleAction U V hVI
  obtain ⟨X,mX,hX,S,a,hS,ha,⟨C,hC⟩,haCoeff⟩ := exists_ergodic_realization_of_finiteDimensional U₀ w
  let := mX
  let := hX
  let ψ (g : G) := ⟪z,U g z⟫_ℝ
  have hψ : RealPositiveDefinite ψ := realPositiveDefinite_coefficient U z
  obtain ⟨j,hj⟩ := exists_stable_coefficient_sequence U K z hz
  let T := gaussianPathSystem ψ hψ
  have hErg : (S.prod T).IsErgodic := Gaussian.gaussianPath_prod_isErgodic ψ hψ S hS j hj
  obtain ⟨b,hb,⟨D,hD⟩,hb0,hbCoeff⟩ :=
    gaussianPath_exists_bounded_centered_approximation ψ hψ (ε/2) (half_pos hε)
  let F (p : X × (G → ℝ)) := a p.1 + b p.2
  refine ⟨X × (G → ℝ),inferInstance,inferInstance,S.prod T,F,hErg,
    (ha.comp measurable_fst).add (hb.comp measurable_snd),⟨C+D,fun p ↦ ?_⟩,fun g ↦ ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hC _) (hD _))
  · have he := integral_two_factor_correlation S T a b
      (MemLp.of_bound ha.aestronglyMeasurable C (ae_of_all _ hC))
      (MemLp.of_bound hb.aestronglyMeasurable D (ae_of_all _ hD)) hb0 g
    rw [he,hSplit,haCoeff]
    change |⟪(w : E),U g w⟫_ℝ + (∫ y, b (T.act g y) * b y ∂T.measure) -
      (⟪P v,U g (P v)⟫_ℝ + ψ g)| < ε
    rw [add_sub_add_comm]
    apply (abs_add_le _ _).trans_lt
    rw [abs_sub_comm ⟪(w : E),U g w⟫_ℝ]
    exact (add_lt_add (hw g) (hbCoeff g)).trans_le (by linarith)

/-- The real Gaussian shift realizes a positive-definite function as an
orthogonal coefficient. The compact and weak splitting then yields the
bounded ergodic approximations used in Theorem 2.2. -/
theorem hasBoundedErgodicPDApproximation : HasBoundedErgodicPDApproximation G := by
  intro φ hφ δ hδ
  let S := gaussianPathSystem φ hφ
  let := systemMulAction S
  let U := realInverseActionKoopmanRep S.measure S.preserves
  let hX : MemLp (fun t : G → ℝ ↦ t 1) 2 S.measure := gaussianPath_coordinate_memLp φ hφ 1
  let x : Lp ℝ 2 S.measure := hX.toLp (fun t : G → ℝ ↦ t 1)
  have hRep (g : G) : ⟪x,U g x⟫_ℝ = φ g := by
    rw [L2.inner_def]
    have hCov : (∫ t : G → ℝ, t 1 * t g ∂S.measure) = φ g := by
      change (∫ t : G → ℝ, t 1 * t g ∂(gaussianPathMeasure φ hφ)) = φ g
      simpa only [inv_one,one_mul] using gaussianPath_covariance φ hφ 1 g
    rw [← hCov]
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp, (ae_realInverseActionKoopmanRep_apply S.measure S.preserves g x).trans
      ((S.preserves g⁻¹).quasiMeasurePreserving.ae_eq_comp hX.coeFn_toLp)] with t h₁ h₂
    change inner ℝ (x t) (U g x t) = t 1 * t g
    rw [h₁,h₂,real_inner_comm, RCLike.inner_apply']
    simp [S, gaussianPathSystem, gaussianShift, mul_comm]
  obtain ⟨X,mX,hX,S,f,hS,hf,hB,h⟩ := exists_ergodic_coefficient_approximation U x δ hδ
  exact ⟨X,mX,hX,S,f,hS,hf,hB,fun g ↦ hRep g ▸ h g⟩

end SixProblems
