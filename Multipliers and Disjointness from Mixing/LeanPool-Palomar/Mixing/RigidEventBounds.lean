module

public import Mixing.EventMixing
public import Mixing.FibreMass
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section

namespace Mixing

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal ProbabilityTheory

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- The partial rigidity hypothesis of Definition 2, expressed using the
automatic weak limits of the diagonal event correlations. -/
def System.IsPartiallyRigidAlong (S : System G X) (p : Ultrafilter G) (a : ℝ) : Prop :=
  ∀ (A : Set X) (hA : MeasurableSet A), a * S.measure.real A ≤
    (inner ℂ (eventVector S hA) (ultrafilterOperator S.koopmanRep p (eventVector S hA))).re

/-- The domination of event images used in Theorem 5.2. Diagonal correlations
give this stronger pointwise inequality by testing on all measurable sets. -/
theorem System.ae_event_dominated_of_partialRigidity (S : System G X)
    (p : Ultrafilter G) (a : ℝ) (h : S.IsPartiallyRigidAlong p a)
    {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ x ∂S.measure, A.indicator (fun _ ↦ a) x ≤
      ((ultrafilterOperator S.koopmanRep p (eventVector S hA)) x).re := by
  let v := ultrafilterOperator S.koopmanRep p (eventVector S hA)
  have hIntegrable : Integrable (fun x ↦ v x) S.measure :=
    (Lp.memLp v).integrable (by norm_num)
  apply ae_le_of_forall_setIntegral_le (integrable_const a |>.indicator hA) hIntegrable.re
  intro D hD _
  let C := A ∩ D
  have hC : MeasurableSet C := hA.inter hD
  have hCD : ∀ g, S.measure.real (C ∩ S.act g ⁻¹' C) ≤ S.measure.real (D ∩ S.act g ⁻¹' A) := by
    intro g
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact ⟨hx.1.2, hx.2.1⟩
  have h₁ := (Complex.continuous_re.tendsto _).comp
    (tendsto_ultrafilterOperator_coeff S.koopmanRep p (eventVector S hC) (eventVector S hC))
  have h₂ := (Complex.continuous_re.tendsto _).comp
    (tendsto_ultrafilterOperator_coeff S.koopmanRep p (eventVector S hD) (eventVector S hA))
  simp only [Function.comp_def, koopman_event_coeff, Complex.ofReal_re] at h₁ h₂
  have hle := (h C hC).trans (le_of_tendsto_of_tendsto' h₁ h₂ hCD)
  change a * S.measure.real C ≤ (inner ℂ (eventVector S hD) v).re at hle
  rw [eventVector, L2.inner_indicatorConstLp_one] at hle
  change _ ≤ RCLike.re (∫ x in D, v x ∂S.measure) at hle
  rw [← integral_re (hIntegrable.integrableOn)] at hle
  rw [setIntegral_indicator hA, setIntegral_const, smul_eq_mul, inter_comm D A, mul_comm]
  exact hle

private theorem System.ultrafilterOperator_integral (S : System G X) (p : Ultrafilter G)
    (v : Lp ℂ 2 S.measure) :
    (∫ x, (ultrafilterOperator S.koopmanRep p v) x ∂S.measure) = ∫ x, v x ∂S.measure := by
  simp only [← inner_constantOne_left]
  have hlim := tendsto_ultrafilterOperator_coeff S.koopmanRep p (constantOne S.measure) v
  have heq : (fun g ↦ inner ℂ (constantOne S.measure) (S.koopmanRep g v)) =
      fun _ ↦ inner ℂ (constantOne S.measure) v := by
    funext g
    change inner ℂ (constantOne S.measure) (S.koopman g v) = _
    conv_lhs => rw [← S.koopman_constantOne g]
    exact (S.koopman g).inner_map_map _ _
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem event_limit_fibre_majorization {Y : Type*} [MeasurableSpace Y]
    {S : System G X} {T : System G Y} (π : FactorMap S T)
    (κ : Kernel Y X) [IsMarkovKernel κ] (hκ : κ ∘ₘ T.measure = S.measure)
    (p : Ultrafilter G) {a : ℝ} (ha : 0 < a)
    (hRigid : S.IsPartiallyRigidAlong p a)
    (hFactor : Set.range (ultrafilterOperator S.koopmanRep p) ⊆ Set.range π.pullback) :
    ∀ A : Set X, MeasurableSet A →
      ∃ h : Y → ℝ≥0∞, Measurable h ∧
        (∀ᵐ x ∂(κ ∘ₘ T.measure), x ∈ A → ENNReal.ofReal a ≤ h (π.toFun x)) ∧
        (∫⁻ y, h y ∂T.measure) = (κ ∘ₘ T.measure) A := by
  intro A hA
  let v := ultrafilterOperator S.koopmanRep p (eventVector S hA)
  obtain ⟨w, hw⟩ := hFactor ⟨eventVector S hA, rfl⟩
  let H : Y → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (w y).re
  have hH : Measurable H := (Complex.continuous_re.measurable.comp
    (Lp.stronglyMeasurable w).measurable).ennreal_ofReal
  have hW := Lp.coeFn_compMeasurePreserving w π.preserves
  change π.pullback w =ᵐ[S.measure] w ∘ π.toFun at hW
  rw [hw] at hW
  have hLower := S.ae_event_dominated_of_partialRigidity p a hRigid hA
  refine ⟨H, hH, ?_, ?_⟩
  · rw [hκ]
    filter_upwards [hLower, hW] with x hx hWx hxA
    rw [indicator_of_mem hxA, hWx] at hx
    exact ENNReal.ofReal_le_ofReal hx
  · rw [hκ, ← π.preserves.lintegral_comp hH]
    change (∫⁻ x, (H ∘ π.toFun) x ∂S.measure) = _
    have hEq : (H ∘ π.toFun) =ᵐ[S.measure] fun x ↦ ENNReal.ofReal (v x).re :=
      hW.symm.mono fun x hx ↦ congrArg (fun z : ℂ ↦ ENNReal.ofReal z.re) hx
    rw [lintegral_congr_ae hEq]
    have hInt : Integrable (fun x ↦ v x) S.measure := (Lp.memLp v).integrable (by norm_num)
    have hNonneg : ∀ᵐ x ∂S.measure, 0 ≤ (v x).re := by
      filter_upwards [hLower] with x hx
      exact (indicator_nonneg (fun _ _ ↦ ha.le) x).trans hx
    change (∫⁻ x, ENNReal.ofReal (RCLike.re (v x)) ∂S.measure) = _
    rw [← ofReal_integral_eq_lintegral_ofReal hInt.re hNonneg, integral_re hInt,
      S.ultrafilterOperator_integral p, integral_eventVector]
    change ENNReal.ofReal (S.measure A).toReal = S.measure A
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- Finite fibres in the first assertion of Theorem 5.2, given a factor
realization admitting the indicated disintegration and containing all weak-limit images. -/
theorem ae_finite_fibre_support_of_partialRigidity {Y : Type*} [MeasurableSpace Y]
    [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]
    {S : System G X} {T : System G Y} (π : FactorMap S T)
    (κ : Kernel Y X) [IsMarkovKernel κ] (hκ : κ ∘ₘ T.measure = S.measure)
    (hfibre : ∀ᵐ y ∂T.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    (p : Ultrafilter G) {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (hRigid : S.IsPartiallyRigidAlong p a)
    (hFactor : Set.range (ultrafilterOperator S.koopmanRep p) ⊆ Set.range π.pullback) :
    ∀ᵐ y ∂T.measure, ∃ s : Finset X, (s : Set X) = (κ y).support ∧ (κ y) (s : Set X)ᶜ = 0 ∧
      (s.card : ℝ≥0∞) * ENNReal.ofReal a ≤ 1 :=
  ae_finite_fibre_support_of_majorization T.measure κ π.toFun π.preserves.measurable hfibre
    (ENNReal.ofReal a) (ENNReal.ofReal_pos.mpr ha) (by simpa using ENNReal.ofReal_le_ofReal ha₁)
    (event_limit_fibre_majorization π κ hκ p ha hRigid hFactor)

/-- The conditional atom at almost every point of a partially rigid system has
mass at least the rigidity parameter over the generated factor. -/
theorem ae_atom_mass_of_partialRigidity {Y : Type*} [MeasurableSpace Y] [MeasurableEq Y]
    [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]
    {S : System G X} {T : System G Y} (π : FactorMap S T)
    (κ : Kernel Y X) [IsMarkovKernel κ] (hκ : κ ∘ₘ T.measure = S.measure)
    (hfibre : ∀ᵐ y ∂T.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    (p : Ultrafilter G) {a : ℝ} (ha : 0 < a)
    (hRigid : S.IsPartiallyRigidAlong p a)
    (hFactor : Set.range (ultrafilterOperator S.koopmanRep p) ⊆ Set.range π.pullback) :
    ∀ᵐ x ∂S.measure, ENNReal.ofReal a ≤ κ (π.toFun x) {x} := by
  rw [← hκ]
  exact ae_atom_mass_of_fibre_majorization T.measure κ π.toFun π.preserves.measurable hfibre
    (ENNReal.ofReal a) (event_limit_fibre_majorization π κ hκ p ha hRigid hFactor)

end Mixing
