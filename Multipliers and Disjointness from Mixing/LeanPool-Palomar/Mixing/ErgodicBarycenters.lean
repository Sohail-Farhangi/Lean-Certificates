module

public import Mixing.System
public import Mathlib.Dynamics.Ergodic.Extreme
public import Mathlib.Dynamics.Ergodic.RadonNikodym
public import Mathlib.Probability.Kernel.Disintegration.Unique

@[expose] public section

namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]

/-- Ergodicity with respect to the entire acting group. -/
def System.IsErgodic (S : System G X) : Prop :=
  ∀ A : Set X, MeasurableSet A →
    (∀ g, S.act g ⁻¹' A =ᵐ[S.measure] A) → EventuallyEmptyOrUniv A (ae S.measure)

theorem System.ae_eq_const_of_invariance {S : System G X} (hS : S.IsErgodic)
    {W : Type*} [Nonempty W] [MeasurableSpace W]
    [HasCountableSeparatingOn W (MeasurableSet : Set W → Prop) univ]
    {f : X → W} (hf : Measurable f)
    (hInv : ∀ g, f ∘ S.act g =ᵐ[S.measure] f) :
    ∃ c, f =ᵐ[S.measure] Function.const X c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro B hB
  change (∀ᵐ x ∂S.measure, x ∈ f ⁻¹' B) ∨ ∀ᵐ x ∂S.measure, x ∉ f ⁻¹' B
  apply eventuallyEmptyOrUniv_iff.mp
  apply hS _ (hf hB)
  intro g
  filter_upwards [hInv g] with x hx
  change (f (S.act g x) ∈ B) ↔ (f x ∈ B)
  rw [show f (S.act g x) = f x from hx]

/-- Any finite invariant measure absolutely continuous with respect to an
ergodic probability measure is proportional to it. -/
theorem System.eq_smul_of_invariant_absolutelyContinuous {S : System G X} (hS : S.IsErgodic)
    (μ : Measure X) [IsFiniteMeasure μ]
    (hinv : ∀ g, MeasurePreserving (S.act g) μ μ) (hμ : μ ≪ S.measure) :
    μ = μ univ • S.measure := by
  obtain ⟨c, hc⟩ := S.ae_eq_const_of_invariance hS (measurable_rnDeriv μ S.measure)
    (fun g ↦ (hinv g).rnDeriv_comp_aeEq (S.preserves g))
  have hc' : μ = c • S.measure := by
    ext A hA
    rw [← Measure.setLIntegral_rnDeriv hμ, lintegral_congr_ae (hc.filter_mono
      (ae_mono Measure.restrict_le_self))]
    change (∫⁻ _ in A, c ∂S.measure) = _
    rw [setLIntegral_const, smul_apply, smul_eq_mul]
  have he := congrArg (fun m : Measure X ↦ m univ) hc'
  simp only [smul_apply, smul_eq_mul, measure_univ, mul_one] at he
  rw [he]
  exact hc'

/-- An ergodic probability measure can be a barycenter of invariant probability
measures only when the measures in the kernel are almost everywhere equal to it.
This is the first-marginal argument in Lemma 1(i). -/
theorem ae_kernel_eq_of_ergodic_barycenter [StandardBorelSpace X] [Nonempty X]
    {S : System G X} (hS : S.IsErgodic)
    (ν : Measure Y) [IsProbabilityMeasure ν] (κ : Kernel Y X) [IsMarkovKernel κ]
    (havg : κ ∘ₘ ν = S.measure)
    (hinv : ∀ g, ∀ᵐ y ∂ν, MeasurePreserving (S.act g) (κ y) (κ y)) :
    ∀ᵐ y ∂ν, κ y = S.measure := by
  have hrestrict (E : Set Y) : κ ∘ₘ (ν.restrict E) = ν E • S.measure := by
    let τ := κ ∘ₘ (ν.restrict E)
    have hτ : τ ≤ S.measure := by
      apply Measure.le_iff.mpr
      intro A hA
      rw [← havg]
      change (ν.restrict E).bind κ A ≤ ν.bind κ A
      rw [Measure.bind_apply hA κ.aemeasurable, Measure.bind_apply hA κ.aemeasurable]
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    have hτpres (g : G) : MeasurePreserving (S.act g) τ τ := by
      refine ⟨(S.preserves g).measurable, ?_⟩
      rw [Measure.map_comp _ κ (S.preserves g).measurable]
      apply Measure.comp_congr
      filter_upwards [ae_mono Measure.restrict_le_self (hinv g)] with y hy
      rw [Kernel.map_apply _ (S.preserves g).measurable, hy.map_eq]
    have huniv : τ univ = ν E := by
      change (ν.restrict E).bind κ univ = _
      rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]
      simp
    exact (S.eq_smul_of_invariant_absolutelyContinuous hS τ hτpres hτ.absolutelyContinuous).trans
      (congrArg (fun a : ℝ≥0∞ ↦ a • S.measure) huniv)
  have hprod : ν ⊗ₘ κ = ν.prod S.measure := by
    apply Measure.ext_prod
    intro E A hE hA
    rw [Measure.compProd_apply_prod hE hA, Measure.prod_prod]
    change (∫⁻ y in E, κ y A ∂ν) = _
    rw [← Measure.bind_apply hA κ.aemeasurable]
    change (κ ∘ₘ (ν.restrict E)) A = _
    rw [hrestrict, smul_apply, smul_eq_mul]
  let ρ := ν ⊗ₘ κ
  have hfst : ρ.fst = ν := Measure.fst_compProd _ _
  have hκ : ρ = ρ.fst ⊗ₘ κ := by rw [hfst]
  have hconst : ρ = ρ.fst ⊗ₘ Kernel.const Y S.measure := by
    rw [hfst, Measure.compProd_const]
    exact hprod
  have h₁ := eq_condKernel_of_measure_eq_compProd κ hκ
  have h₂ := eq_condKernel_of_measure_eq_compProd (Kernel.const Y S.measure) hconst
  rw [hfst] at h₁ h₂
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  exact hy₁.trans hy₂.symm

end Mixing
