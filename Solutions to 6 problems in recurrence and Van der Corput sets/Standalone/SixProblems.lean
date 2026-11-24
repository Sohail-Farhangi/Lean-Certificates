/- Lean certificate for arXiv:2609.07506v1. -/

module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving

public import Mathlib.MeasureTheory.Measure.Prod

public import Mathlib.Dynamics.Ergodic.Extreme

public import Mathlib.Dynamics.Ergodic.RadonNikodym

public import Mathlib.Probability.Kernel.Disintegration.Unique

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public import Mathlib.Basic.Complex.Basic

public import Mathlib.Probability.ProductMeasure

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public import Mathlib.MeasureTheory.Measure.MeasuredSets

public import Mathlib.Probability.Independence.InfinitePi

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

public import Mathlib.Analysis.InnerProductSpace.Dual

public import Mathlib.Analysis.LocallyConvex.WeakSpace

public import Mathlib.Analysis.Normed.Module.WeakDual

public import Mathlib.Topology.Compactness.Compact

public import Mathlib.Algebra.Group.Subsemigroup.Operations

public import Mathlib.Analysis.Normed.Operator.Basic

public import Mathlib.LinearAlgebra.Projection

public import Mathlib.Topology.Algebra.Semigroup

public import Mathlib.Analysis.Normed.Module.Convex

public import Mathlib.Analysis.Normed.Module.DoubleDual

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

public import Mathlib.Topology.Baire.LocallyCompactRegular

public import Mathlib.Topology.MetricSpace.Sequences

public import Mathlib.Topology.Homeomorph.Lemmas

public import Mathlib.Algebra.QuadraticDiscriminant

public import Mathlib.Analysis.InnerProductSpace.Symmetric

public import Mathlib.Tactic.Linarith

public import Mathlib.Analysis.InnerProductSpace.Spectrum

public import Mathlib.Analysis.Convex.Integral

public import Mathlib.MeasureTheory.Measure.Haar.Unique

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

public import Mathlib.Analysis.Normed.Module.HahnBanach

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

public import Mathlib.MeasureTheory.Function.LocallyIntegrable

public import Mathlib.Analysis.InnerProductSpace.Adjoint

public import Mathlib.Dynamics.Ergodic.Action.OfMinimal

public import Mathlib.Topology.Algebra.Star.Unitary

public import Mathlib.Topology.Algebra.Module.FiniteDimension

public import Mathlib.Topology.Metrizable.CompletelyMetrizable

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

public import Mathlib.LinearAlgebra.Lagrange

public import Mathlib.Analysis.Matrix.Order

public import Mathlib.Analysis.InnerProductSpace.GramMatrix

public import Mathlib.Algebra.Order.Archimedean.Basic

public import Mathlib.Algebra.MvPolynomial.Eval

public import Mathlib.Tactic.Ring

public import Mathlib.MeasureTheory.Integral.Bochner.Set

public import Mathlib.MeasureTheory.Constructions.Projective

public import Mathlib.MeasureTheory.Measure.Prokhorov

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

public import Mathlib.Probability.Distributions.Gaussian.Fernique

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

public import Mathlib.Topology.Instances.EReal.Lemmas

public import Mathlib.Tactic.NormNum

public import Mathlib.Tactic.Positivity

public import Mathlib.Probability.Distributions.Gaussian.CharFun

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public import Mathlib.MeasureTheory.Function.ContinuousMapDense

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

public import Mathlib.Combinatorics.Hindman

public import Mathlib.Topology.Compactification.StoneCech

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

public import Mathlib.MeasureTheory.Function.L2Space

public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

public import Mathlib.Topology.Algebra.MulAction

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

public import Mathlib.Analysis.Normed.Ring.Lemmas

public import Mathlib.Analysis.InnerProductSpace.LinearMap

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public import Mathlib.Topology.Sequences

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality

public import Mathlib.Analysis.InnerProductSpace.Positive

public import Mathlib.Topology.Algebra.PontryaginDual

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

public import Mathlib.Analysis.Normed.Operator.Extend

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

public import Mathlib.MeasureTheory.Integral.Prod

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

public import Mathlib.MeasureTheory.Group.Convolution

public import Mathlib.Topology.Metrizable.Basic

public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

public import Mathlib.Topology.UrysohnsLemma

public import Mathlib.MeasureTheory.Measure.MutuallySingular

public import Mathlib.Analysis.SpecificLimits.Normed

public import Mathlib.MeasureTheory.Group.Integral

public import Mathlib.Topology.Metrizable.Urysohn

public import Mathlib.Data.Finset.SymmDiff

public import Mathlib.Dynamics.Ergodic.EmpiricalMeasure

public import Mathlib.Analysis.SpecificLimits.Basic

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

public import Mathlib.Algebra.Order.Floor.Semiring

public import Mathlib.Analysis.Complex.Basic

public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

public import Mathlib.Probability.Moments.Variance

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

public import Mathlib.Analysis.SpecialFunctions.PolarCoord

public import Mathlib.Probability.Distributions.Gaussian.Real

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/- Source module Mixing.System. -/
section
namespace Mixing

open MeasureTheory

/-- A probability-preserving action, with the probability space left explicit. -/
structure System (G X : Type*) [Group G] [MeasurableSpace X] where
  measure : Measure X
  probability : IsProbabilityMeasure measure
  act : G → X → X
  act_one : act 1 = id
  act_mul : ∀ g h, act (g * h) = act g ∘ act h
  preserves : ∀ g, MeasurePreserving (act g) measure measure

attribute [instance] System.probability

variable {G X Y Z W : Type*} [Group G]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

namespace System

/-- The diagonal action on two probability-preserving systems. -/
def prodAct (S : System G X) (T : System G Y) (g : G) : X × Y → X × Y :=
  Prod.map (S.act g) (T.act g)

@[simp]
theorem prodAct_one (S : System G X) (T : System G Y) : S.prodAct T 1 = id := by
  ext <;> simp [prodAct, S.act_one, T.act_one]

theorem prodAct_mul (S : System G X) (T : System G Y) (g h : G) :
    S.prodAct T (g * h) = S.prodAct T g ∘ S.prodAct T h := by
  ext <;> simp [prodAct, S.act_mul, T.act_mul]

end System

/-- A factor map intertwines the two actions and pushes forward the probability measure. -/
structure FactorMap (S : System G X) (T : System G Y) where
  toFun : X → Y
  preserves : MeasurePreserving toFun S.measure T.measure
  equivariant : ∀ g, toFun ∘ S.act g = T.act g ∘ toFun

/-- An invariant probability measure with the displayed marginals, as in Section 2.2. -/
structure IsJoining (S : System G X) (T : System G Y) (joining : Measure (X × Y)) : Prop where
  probability : IsProbabilityMeasure joining
  fst : MeasurePreserving Prod.fst joining S.measure
  snd : MeasurePreserving Prod.snd joining T.measure
  invariant : ∀ g, MeasurePreserving (S.prodAct T g) joining joining

/-- Disjointness of probability-preserving systems. -/
def Disjoint (S : System G X) (T : System G Y) : Prop :=
  ∀ joining, IsJoining S T joining → joining = S.measure.prod T.measure

theorem product_isJoining (S : System G X) (T : System G Y) :
    IsJoining S T (S.measure.prod T.measure) where
  probability := inferInstance
  fst := measurePreserving_fst
  snd := measurePreserving_snd
  invariant g := (S.preserves g).prod (T.preserves g)

/-- The independent product system. -/
noncomputable def System.prod (S : System G X) (T : System G Y) : System G (X × Y) where
  measure := S.measure.prod T.measure
  probability := inferInstance
  act := S.prodAct T
  act_one := S.prodAct_one T
  act_mul := S.prodAct_mul T
  preserves := (product_isJoining S T).invariant

/-- Composition of factor maps. -/
def FactorMap.comp {R : System G X} {S : System G Y} {T : System G Z}
    (f : FactorMap S T) (k : FactorMap R S) : FactorMap R T where
  toFun := f.toFun ∘ k.toFun
  preserves := f.preserves.comp k.preserves
  equivariant g := by
    rw [Function.comp_assoc, k.equivariant g, ← Function.comp_assoc, f.equivariant g,
      Function.comp_assoc]

/-- Independent products of factor maps between product systems. -/
noncomputable def FactorMap.prod {S : System G X} {T : System G Y} {S' : System G Z} {T' : System G W}
    (f : FactorMap S S') (k : FactorMap T T') : FactorMap (S.prod T) (S'.prod T') where
  toFun := Prod.map f.toFun k.toFun
  preserves := f.preserves.prod k.preserves
  equivariant g := by
    funext x
    exact Prod.ext (congrFun (f.equivariant g) x.1) (congrFun (k.equivariant g) x.2)

namespace IsJoining

variable {S : System G X} {T : System G Y} {joining : Measure (X × Y)}

/-- A joining defines a system on the product space. -/
def system (h : IsJoining S T joining) : System G (X × Y) where
  measure := joining
  probability := h.probability
  act := S.prodAct T
  act_one := S.prodAct_one T
  act_mul := S.prodAct_mul T
  preserves := h.invariant

/-- The first coordinate of a joining is a factor. -/
def fstFactor (h : IsJoining S T joining) : FactorMap h.system S where
  toFun := Prod.fst
  preserves := h.fst
  equivariant _ := rfl

/-- The second coordinate of a joining is a factor. -/
def sndFactor (h : IsJoining S T joining) : FactorMap h.system T where
  toFun := Prod.snd
  preserves := h.snd
  equivariant _ := rfl

/-- Pushing a joining forward by factor maps gives a joining of the factors. -/
theorem map (h : IsJoining S T joining) {S' : System G Z} {T' : System G W}
    (f : FactorMap S S') (k : FactorMap T T') :
    IsJoining S' T' (joining.map (Prod.map f.toFun k.toFun)) := by
  let π := Prod.map f.toFun k.toFun
  have hπ : Measurable π := f.preserves.measurable.prodMap k.preserves.measurable
  refine ⟨(Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 h.probability, ⟨measurable_fst, ?_⟩,
    ⟨measurable_snd, ?_⟩, fun g ↦ ⟨(S'.preserves g).measurable.prodMap
      (T'.preserves g).measurable, ?_⟩⟩
  · rw [Measure.map_map measurable_fst hπ]
    exact ((f.preserves).comp h.fst).map_eq
  · rw [Measure.map_map measurable_snd hπ]
    exact ((k.preserves).comp h.snd).map_eq
  · have haction : Measurable (S'.prodAct T' g) :=
      (S'.preserves g).measurable.prodMap (T'.preserves g).measurable
    have hcommute : S'.prodAct T' g ∘ π = π ∘ S.prodAct T g := by
      funext x
      exact Prod.ext (congrFun (f.equivariant g).symm x.1)
        (congrFun (k.equivariant g).symm x.2)
    rw [Measure.map_map haction hπ, hcommute, ← Measure.map_map hπ (h.invariant g).measurable,
      (h.invariant g).map_eq]

end IsJoining

/-- The graph measure of a factor map joins the extension with the factor. -/
theorem FactorMap.graph_isJoining {S : System G X} {T : System G Y} (f : FactorMap S T) :
    IsJoining S T (S.measure.map fun x ↦ (x, f.toFun x)) := by
  let π : X → X × Y := fun x ↦ (x, f.toFun x)
  have hπ : Measurable π := measurable_id.prodMk f.preserves.measurable
  refine ⟨(Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 S.probability, ⟨measurable_fst, ?_⟩,
    ⟨measurable_snd, ?_⟩, fun g ↦ ⟨(S.preserves g).measurable.prodMap
      (T.preserves g).measurable, ?_⟩⟩
  · rw [Measure.map_map measurable_fst hπ]
    exact Measure.map_id
  · rw [Measure.map_map measurable_snd hπ]
    exact f.preserves.map_eq
  · have haction : Measurable (S.prodAct T g) :=
      (S.preserves g).measurable.prodMap (T.preserves g).measurable
    have hcommute : S.prodAct T g ∘ π = π ∘ S.act g := by
      funext x
      exact Prod.ext rfl (congrFun (f.equivariant g).symm x)
    rw [Measure.map_map haction hπ, hcommute, ← Measure.map_map hπ (S.preserves g).measurable,
      (S.preserves g).map_eq]

end Mixing
end

/- Source module Mixing.ErgodicBarycenters. -/
section
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
end

/- Source module SixProblems.Definitions. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing

/-- The correlation in Definition 4.1, using positive time in the first entry. -/
def correlation {G X : Type*} [Group G] [MeasurableSpace X]
    (S : System G X) (f : X → ℂ) (g : G) : ℂ :=
  ∫ x, f (S.act g x) * (starRingEnd ℂ) (f x) ∂S.measure

/-- The dynamical van der Corput condition of Definition 4.1. -/
def IsVdC {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (f : X → ℂ), Measurable f →
      (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      (∀ r ∈ R, correlation S f r = 0) → ∫ x, f x ∂S.measure = 0

/-- Measure-theoretic compact-group van der Corput condition, relative to
the normalized Haar measure `m`, as in Definition 4.4. -/
def IsMeasureTheoreticVdC {G K : Type} [Group G] [Group K] [MeasurableSpace K]
    (R : Set G) (m : Measure K) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (F : X → K), Measurable F →
      (∀ h ∈ R, S.measure.map (fun x ↦ F (S.act h x) * (F x)⁻¹) = m) →
      S.measure.map F = m

/-- Nice event recurrence, Theorem 2.2(a). -/
def NiceRecurrence {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (A : Set X), MeasurableSet A →
    ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
      (S.measure A).toReal ^ 2 - ε ≤ (S.measure (A ∩ S.act r ⁻¹' A)).toReal

/-- The event test restricted to ergodic systems, Theorem 2.2(b). -/
def ErgodicNiceRecurrence {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X), S.IsErgodic → ∀ (A : Set X), MeasurableSet A →
    ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
      (S.measure A).toReal ^ 2 - ε ≤ (S.measure (A ∩ S.act r ⁻¹' A)).toReal

/-- The bounded-function condition of Theorem 2.2(e). Positive and inverse
time give the same absolute value of the correlation. -/
def NiceVdC {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (f : X → ℂ), Measurable f →
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) → ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
      ‖∫ x, f x ∂S.measure‖ ^ 2 - ε ≤ ‖correlation S f r⁻¹‖

end SixProblems
end

/- Source module SixProblems.BernoulliThreshold. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped ENNReal

variable {G X K : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace K]

/-- The right shift has the left action law, even when `G` is nonabelian. -/
def rightShift (a : G) (t : G → K) : G → K := fun g ↦ t (g * a)

omit [MeasurableSpace K] in
@[simp] theorem rightShift_one (t : G → K) : rightShift (1 : G) t = t := by
  funext g
  simp [rightShift]

omit [MeasurableSpace K] in
theorem rightShift_mul (a b : G) (t : G → K) :
    rightShift (a * b) t = rightShift a (rightShift b t) := by
  funext g
  exact congrArg t (mul_assoc g a b).symm

theorem measurable_rightShift (a : G) : Measurable (rightShift (K := K) a) :=
  Measurable.of_eval (fun g ↦ measurable_pi_apply (g * a))

/-- The right shift preserves every constant product probability. -/
theorem measurePreserving_rightShift (m : Measure K) [IsProbabilityMeasure m] (a : G) :
    MeasurePreserving (rightShift (K := K) a)
      (Measure.infinitePi (fun _ : G ↦ m)) (Measure.infinitePi (fun _ : G ↦ m)) := by
  refine ⟨measurable_rightShift a, ?_⟩
  let e := Equiv.mulRight a
  have he : rightShift (K := K) a = MeasurableEquiv.piCongrLeft (fun _ : G ↦ K) e.symm := by
    funext t g
    change t (e g) = MeasurableEquiv.piCongrLeft (fun _ : G ↦ K) e.symm t g
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : G ↦ K) e.symm t (e g)
    rwa [Equiv.symm_apply_apply, eq_comm] at h
  rw [he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : G ↦ m) e.symm

/-- The Bernoulli system over a probability space `K`. -/
def bernoulliShift (G : Type*) [Group G] (m : Measure K) [IsProbabilityMeasure m] :
    System G (G → K) where
  measure := Measure.infinitePi (fun _ : G ↦ m)
  probability := inferInstance
  act := rightShift
  act_one := funext rightShift_one
  act_mul a b := funext (rightShift_mul a b)
  preserves := measurePreserving_rightShift m

/-- Lebesgue probability supported on the closed unit interval. -/
def unitIntervalLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitIntervalLaw := by
  constructor
  rw [unitIntervalLaw, Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

theorem unitIntervalLaw_Iic {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    unitIntervalLaw (Iic x) = ENNReal.ofReal x := by
  rw [unitIntervalLaw, Measure.restrict_apply measurableSet_Iic]
  have h : Iic x ∩ Icc (0 : ℝ) 1 = Icc 0 x := by
    ext y
    exact ⟨fun h ↦ ⟨h.2.1,h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hx1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

variable (S : System G X)

/-- The event whose Bernoulli coordinate is below the prescribed threshold. -/
def bernoulliThreshold (f : X → ℝ) : Set (X × (G → ℝ)) :=
  {z | z.2 1 ≤ f z.1}

theorem measurableSet_bernoulliThreshold {f : X → ℝ} (hf : Measurable f) :
    MeasurableSet (bernoulliThreshold (G := G) f) :=
  measurableSet_le ((measurable_pi_apply (1 : G)).comp measurable_snd) (hf.comp measurable_fst)

/-- The finite-intersection identity of Proposition 2.1. The index finset
represents any finite tuple of distinct translates. -/
theorem bernoulliThreshold_pattern
    {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (J : Finset G) :
    let T := S.prod (bernoulliShift G unitIntervalLaw)
    (T.measure {z | ∀ g ∈ J, z ∈ T.act g ⁻¹' bernoulliThreshold f}).toReal =
      ∫ x, ∏ g ∈ J, f (S.act g x) ∂S.measure := by
  classical
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let E : Set (X × (G → ℝ)) := {z | ∀ g ∈ J, z ∈ T.act g ⁻¹' bernoulliThreshold f}
  have hE : MeasurableSet E := by
    rw [show E = ⋂ g ∈ J, T.act g ⁻¹' bernoulliThreshold f by ext; simp [E]]
    exact MeasurableSet.biInter J.countable_toSet (fun g _ ↦
      (T.preserves g).measurable (measurableSet_bernoulliThreshold hf))
  have hFiber (x : X) : Prod.mk x ⁻¹' E = (J : Set G).pi (fun g ↦ Iic (f (S.act g x))) := by
    ext t
    simp [E, T, bernoulliThreshold, System.prod, System.prodAct, bernoulliShift, rightShift, Set.mem_pi]
  change (T.measure E).toReal = _
  change ((S.measure.prod (Measure.infinitePi (fun _ : G ↦ unitIntervalLaw))) E).toReal = _
  rw [Measure.prod_apply hE]
  simp_rw [hFiber, Measure.infinitePi_pi _ (fun g _ ↦ measurableSet_Iic),
    unitIntervalLaw_Iic (hf0 _) (hf1 _)]
  have hprod (x : X) : 0 ≤ ∏ g ∈ J, f (S.act g x) :=
    Finset.prod_nonneg (fun g _ ↦ hf0 _)
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun g _ ↦ hf0 (S.act g _))]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hprod)]
  exact (Finset.measurable_prod J (fun g _ ↦ hf.comp (S.preserves g).measurable)).aestronglyMeasurable

end SixProblems
end

/- Source module SixProblems.BernoulliErgodic. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Set MeasureTheory Filter Mixing ProbabilityTheory
open scoped ENNReal ProbabilityTheory symmDiff

variable {G X K : Type*} [MeasurableSpace X] [MeasurableSpace K]

/-- Keep the base point and restrict the Bernoulli configuration to a finite set. -/
private def windowView (I : Finset G) (x : X × (G → K)) : X × (I → K) :=
  (x.1, I.restrict x.2)

private theorem measurable_windowView (I : Finset G) :
    Measurable (windowView (X := X) (K := K) I) :=
  measurable_fst.prodMk ((Finset.measurable_restrict I).comp measurable_snd)

private def windowEvents (X K G : Type*) [MeasurableSpace X] [MeasurableSpace K] :
    Set (Set (X × (G → K))) :=
  {A | ∃ I : Finset G, ∃ C : Set (X × (I → K)), MeasurableSet C ∧ windowView I ⁻¹' C = A}

private theorem windowEvents_measurable {A : Set (X × (G → K))}
    (hA : A ∈ windowEvents X K G) : MeasurableSet A := by
  obtain ⟨I, C, hC, rfl⟩ := hA
  exact hC.preimage (measurable_windowView I)

private theorem windowEvents_univ : (univ : Set (X × (G → K))) ∈ windowEvents X K G :=
  ⟨∅, univ, MeasurableSet.univ, preimage_univ⟩

private def windowShrink {I J : Finset G} (h : I ⊆ J) (x : X × (J → K)) : X × (I → K) :=
  (x.1, Finset.restrict₂ (π := fun _ : G ↦ K) h x.2)

private theorem measurable_windowShrink {I J : Finset G} (h : I ⊆ J) :
    Measurable (windowShrink (X := X) (K := K) h) :=
  measurable_fst.prodMk ((Finset.measurable_restrict₂ (X := fun _ : G ↦ K) h).comp measurable_snd)

private theorem windowEvents_isSetRing : IsSetRing (windowEvents X K G) where
  empty_mem := ⟨∅, ∅, MeasurableSet.empty, preimage_empty⟩
  union_mem := by
    classical
    rintro A B ⟨I, C, hC, rfl⟩ ⟨J, D, hD, rfl⟩
    refine ⟨I ∪ J, windowShrink Finset.subset_union_left ⁻¹' C ∪
      windowShrink Finset.subset_union_right ⁻¹' D,
      (hC.preimage (measurable_windowShrink _)).union (hD.preimage (measurable_windowShrink _)), ?_⟩
    rfl
  sdiff_mem := by
    classical
    rintro A B ⟨I, C, hC, rfl⟩ ⟨J, D, hD, rfl⟩
    refine ⟨I ∪ J, (windowShrink Finset.subset_union_left ⁻¹' C) \
      (windowShrink Finset.subset_union_right ⁻¹' D),
      (hC.preimage (measurable_windowShrink _)).diff (hD.preimage (measurable_windowShrink _)), ?_⟩
    rfl

private theorem windowEvents_generate :
    (inferInstance : MeasurableSpace (X × (G → K))) =
      MeasurableSpace.generateFrom (windowEvents X K G) := by
  let M := MeasurableSpace.generateFrom (windowEvents X K G)
  apply le_antisymm
  · classical
    have hfst : @Measurable (X × (G → K)) X M _ Prod.fst := by
      intro U hU
      exact MeasurableSpace.measurableSet_generateFrom ⟨∅, Prod.fst ⁻¹' U, measurable_fst hU, rfl⟩
    have hcoord (g : G) : @Measurable (X × (G → K)) K M _ (fun z ↦ z.2 g) := by
      intro U hU
      let i : ({g} : Finset G) := ⟨g, Finset.mem_singleton_self g⟩
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨{g}, (fun z : X × (({g} : Finset G) → K) ↦ z.2 i) ⁻¹' U,
          ((measurable_pi_apply i).comp measurable_snd) hU, rfl⟩
    have hsnd : @Measurable (X × (G → K)) (G → K) M _ Prod.snd :=
      measurable_pi_iff.mpr hcoord
    exact hfst.prodMk hsnd
  · exact MeasurableSpace.generateFrom_le fun _ hA ↦ windowEvents_measurable hA

variable (m : Measure K) [IsProbabilityMeasure m]

private abbrev configurationLaw : Measure (G → K) := Measure.infinitePi (fun _ : G ↦ m)

private theorem configurationLaw_iIndepFun :
    iIndepFun (fun g (t : G → K) ↦ t g) (configurationLaw m) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun g ↦ measurable_pi_apply g)).mpr
  simp_rw [(measurePreserving_eval_infinitePi (fun _ : G ↦ m) _).map_eq]
  exact Measure.map_id

private theorem window_measure_inter_cylinder (μ : Measure X) [IsProbabilityMeasure μ]
    (I J : Finset G) (hIJ : _root_.Disjoint I J)
    {C : Set (X × (I → K))} (hC : MeasurableSet C)
    {D : Set (J → K)} (hD : MeasurableSet D) :
    let law := configurationLaw (G := G) m
    (μ.prod law) (windowView I ⁻¹' C ∩ Prod.snd ⁻¹' (J.restrict ⁻¹' D)) =
      (μ.prod law) (windowView I ⁻¹' C) * law (J.restrict ⁻¹' D) := by
  intro law
  have hd' : MeasurableSet (Prod.snd ⁻¹' (J.restrict ⁻¹' D) : Set (X × (G → K))) :=
    measurable_snd (hD.preimage (Finset.measurable_restrict J))
  rw [Measure.prod_apply ((hC.preimage (measurable_windowView I)).inter hd'),
    Measure.prod_apply (hC.preimage (measurable_windowView I))]
  rw [← lintegral_mul_const' _ _ (measure_ne_top _ _)]
  apply lintegral_congr
  intro x
  change law (I.restrict ⁻¹' (Prod.mk x ⁻¹' C) ∩ J.restrict ⁻¹' D) =
    law (I.restrict ⁻¹' (Prod.mk x ⁻¹' C)) * law (J.restrict ⁻¹' D)
  exact ((configurationLaw_iIndepFun (G := G) m).indepFun_finset I J hIJ
    (fun g ↦ measurable_pi_apply g)).measure_inter_preimage_eq_mul _ _
    (hC.preimage (measurable_const.prodMk measurable_id)) hD

variable [Group G]

private theorem exists_shift_disjoint [Infinite G] [DecidableEq G] (I J : Finset G) :
    ∃ g : G, _root_.Disjoint I (J.image fun j ↦ j * g) := by
  classical
  let B := (J.product I).image fun p : G × G ↦ p.1⁻¹ * p.2
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset B
  refine ⟨g, Finset.disjoint_left.mpr fun i hi hi' ↦ hg ?_⟩
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi'
  exact Finset.mem_image.mpr ⟨(j,j*g), Finset.mem_product.mpr ⟨hj,hi⟩,
    inv_mul_cancel_left j g⟩

set_option maxHeartbeats 800000 in
/-- An invariant event in the product has independent finite-coordinate
sections on the Bernoulli side, even after restriction to a base event. -/
private theorem invariant_measure_rect_cylinder [Infinite G] (S : System G X)
    (A : Set (X × (G → K))) (hA : MeasurableSet A)
    (hInv : ∀ g, (S.prod (bernoulliShift G m)).act g ⁻¹' A =ᵐ[(S.prod (bernoulliShift G m)).measure] A)
    {U : Set X} (hU : MeasurableSet U) (J : Finset G) {D : Set (J → K)} (hD : MeasurableSet D) :
    let law := configurationLaw (G := G) m
    let ν := S.measure.prod law
    let V : Set (G → K) := J.restrict ⁻¹' D
    ν (A ∩ (U ×ˢ V)) = ν (A ∩ (U ×ˢ univ)) * law V := by
  classical
  let T := S.prod (bernoulliShift G m)
  let law := configurationLaw (G := G) m
  let ν := T.measure
  let V : Set (G → K) := J.restrict ⁻¹' D
  let W := U ×ˢ V
  let W₀ := U ×ˢ (univ : Set (G → K))
  have hV : MeasurableSet V := hD.preimage (Finset.measurable_restrict J)
  have hW : MeasurableSet W := hU.prod hV
  have hW₀ : MeasurableSet W₀ := hU.prod MeasurableSet.univ
  change ν (A ∩ W) = ν (A ∩ W₀) * law V
  have ha : ν (A ∩ W) ≠ ∞ := measure_ne_top _ _
  have hb : ν (A ∩ W₀) * law V ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  suffices hre : (ν (A ∩ W)).toReal = (ν (A ∩ W₀) * law V).toReal from
    le_antisymm ((ENNReal.toReal_le_toReal ha hb).mp hre.le)
      ((ENNReal.toReal_le_toReal hb ha).mp hre.ge)
  rw [ENNReal.toReal_mul]
  suffices hc : ∀ ε : ℝ, 0 < ε → |ν.real (A ∩ W) - ν.real (A ∩ W₀) * law.real V| < ε by
    by_contra hne
    exact (lt_irrefl _) (hc _ (abs_pos.mpr (sub_ne_zero.mpr hne)))
  intro ε hε
  have hε₀ : 0 < ε / 3 := by positivity
  have hcover : ∃ D : Set (Set (X × (G → K))), D.Countable ∧ D ⊆ windowEvents X K G ∧
      ν (⋃₀ D)ᶜ = 0 := by
    exact ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr windowEvents_univ, by simp⟩
  obtain ⟨Cset, ⟨I,C,hC,rfl⟩, hclose⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ν)
      windowEvents_isSetRing hcover windowEvents_generate hA (ENNReal.ofReal_pos.mpr hε₀)
  let B := windowView I ⁻¹' C
  have hB := hC.preimage (measurable_windowView I)
  have hClose : ν.real (B ∆ A) < ε / 3 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hclose
    rwa [ENNReal.toReal_ofReal hε₀.le] at h
  obtain ⟨g,hg⟩ := exists_shift_disjoint I J
  let L := J.image fun j ↦ j*g
  let Wg := T.act g ⁻¹' W
  let W₀g := T.act g ⁻¹' W₀
  let r (t : L → K) (j : J) : K := t ⟨(j : G) * g, Finset.mem_image_of_mem _ j.property⟩
  let E := r ⁻¹' D
  have hr : Measurable r := Measurable.of_eval fun _ ↦ measurable_pi_apply _
  have hE : MeasurableSet E := hD.preimage hr
  let U' := S.act g ⁻¹' U
  let C' := C ∩ Prod.fst ⁻¹' U'
  have hC' : MeasurableSet C' := hC.inter (measurable_fst ((S.preserves g).measurable hU))
  have hVg : L.restrict ⁻¹' E = rightShift g ⁻¹' V := by rfl
  have hBg : B ∩ Wg = windowView I ⁻¹' C' ∩ Prod.snd ⁻¹' (L.restrict ⁻¹' E) := by
    ext x
    change x ∈ B ∧ ((S.act g x.1) ∈ U ∧ rightShift g x.2 ∈ V) ↔
      (x ∈ B ∧ S.act g x.1 ∈ U) ∧ rightShift g x.2 ∈ V
    exact and_assoc.symm
  have hB₀g : B ∩ W₀g = windowView I ⁻¹' C' := by
    ext x
    change x ∈ B ∧ (S.act g x.1 ∈ U ∧ rightShift g x.2 ∈ univ) ↔ x ∈ B ∧ S.act g x.1 ∈ U
    simp only [mem_univ, and_true]
  have hShiftV : law (L.restrict ⁻¹' E) = law V := by
    rw [hVg]
    exact (measurePreserving_rightShift m g).measure_preimage hV.nullMeasurableSet
  have hfactor : ν.real (B ∩ Wg) = ν.real (B ∩ W₀g) * law.real V := by
    have h := window_measure_inter_cylinder m S.measure I L hg hC' hE
    change ν _ = ν _ * law _ at h
    rw [← hBg, ← hB₀g, hShiftV] at h
    exact (congrArg ENNReal.toReal h).trans ENNReal.toReal_mul
  have hInvariant {F : Set (X × (G → K))} (hF : MeasurableSet F) :
      ν.real (A ∩ F) = ν.real (A ∩ T.act g ⁻¹' F) := by
    have hpres := (T.preserves g).measure_preimage (hA.inter hF).nullMeasurableSet
    have hd : T.act g ⁻¹' (A ∩ F) =ᵐ[ν] A ∩ T.act g ⁻¹' F := by
      filter_upwards [hInv g] with x hx
      change (T.act g x ∈ A ∧ T.act g x ∈ F) ↔ (x ∈ A ∧ T.act g x ∈ F)
      exact and_congr_left' hx
    exact congrArg ENNReal.toReal (hpres.symm.trans (measure_congr hd))
  have hdiff {F : Set (X × (G → K))} (hF : MeasurableSet F) :
      |ν.real (A ∩ F) - ν.real (B ∩ F)| ≤ ν.real (B ∆ A) := by
    have hsub : (A ∩ F) ∆ (B ∩ F) ⊆ B ∆ A := by
      intro x
      simp only [symmDiff_def, mem_union, Set.mem_sdiff, mem_inter_iff]
      tauto
    exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
      (hA.inter hF).nullMeasurableSet (hB.inter hF).nullMeasurableSet).trans
      (measureReal_mono hsub (measure_ne_top ν _))
  have hν₁ := hdiff ((T.preserves g).measurable hW)
  have hν₂ := hdiff ((T.preserves g).measurable hW₀)
  have hlaw0 : 0 ≤ law.real V := ENNReal.toReal_nonneg
  have hlaw1 : law.real V ≤ 1 := (measureReal_mono (subset_univ _) (measure_ne_top _ _)).trans_eq (by simp)
  rw [hInvariant hW, hInvariant hW₀]
  change |ν.real (A ∩ Wg) - ν.real (A ∩ W₀g) * law.real V| < ε
  calc
    _ ≤ |ν.real (A ∩ Wg) - ν.real (B ∩ Wg)| +
        |ν.real (B ∩ Wg) - ν.real (A ∩ W₀g) * law.real V| := abs_sub_le _ _ _
    _ ≤ ν.real (B ∆ A) + ν.real (B ∆ A) := by
      refine add_le_add hν₁ ?_
      rw [hfactor, ← sub_mul, abs_mul, abs_of_nonneg hlaw0, abs_sub_comm]
      exact (mul_le_mul_of_nonneg_right hν₂ hlaw0).trans
        (mul_le_of_le_one_right ENNReal.toReal_nonneg hlaw1)
    _ < ε := by linarith

set_option maxHeartbeats 800000 in
/-- The product of an ergodic action with an infinite-group Bernoulli shift
is ergodic. This is the ergodicity clause of Proposition 2.1. -/
theorem bernoulli_prod_isErgodic [Infinite G] (S : System G X) (hS : S.IsErgodic) :
    (S.prod (bernoulliShift G m)).IsErgodic := by
  intro A hA hInv
  let T := S.prod (bernoulliShift G m)
  let law := configurationLaw (G := G) m
  let ν := T.measure
  let ρ := ν.restrict A
  let η := ρ.map Prod.fst
  have hρ₁ (g : G) : MeasurePreserving (T.act g) ρ ρ := by
    have h := (T.preserves g).restrict_preimage hA
    have hr : T.measure.restrict (T.act g ⁻¹' A) = ρ := Measure.restrict_congr_set (hInv g)
    rwa [hr] at h
  have hη₁ (g : G) : MeasurePreserving (S.act g) η η := by
    refine ⟨(S.preserves g).measurable, ?_⟩
    have hcomp : S.act g ∘ Prod.fst = Prod.fst ∘ T.act g := rfl
    change (ρ.map Prod.fst).map (S.act g) = η
    rw [Measure.map_map (S.preserves g).measurable measurable_fst, hcomp,
      ← Measure.map_map measurable_fst (hρ₁ g).measurable, (hρ₁ g).map_eq]
  have hη_le : η ≤ S.measure := by
    calc
      η ≤ ν.map Prod.fst := Measure.map_mono Measure.restrict_le_self measurable_fst
      _ = S.measure := by
        change (S.measure.prod law).map Prod.fst = S.measure
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hη_eq := S.eq_smul_of_invariant_absolutelyContinuous hS η hη₁ hη_le.absolutelyContinuous
  have hη_univ : η univ = ν A := by
    change ρ.map Prod.fst univ = _
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
  have hProd : ρ = η.prod law := by
    apply Measure.ext_prod
    intro U V hU hV
    let ξ := (ρ.restrict (Prod.fst ⁻¹' U)).map Prod.snd
    have hξ_apply {W : Set (G → K)} (hW : MeasurableSet W) : ξ W = ρ (U ×ˢ W) := by
      rw [Measure.map_apply measurable_snd hW, Measure.restrict_apply (measurable_snd hW)]
      congr 1
      exact inter_comm _ _
    have hρ_apply {W : Set (G → K)} (hW : MeasurableSet W) :
        ρ (U ×ˢ W) = ν (A ∩ (U ×ˢ W)) := by
      rw [Measure.restrict_apply (hU.prod hW), inter_comm]
    have hη_apply : η U = ν (A ∩ (U ×ˢ univ)) := by
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU), inter_comm]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    have heq : ξ = η U • law := by
      let C := measurableCylinders (fun _ : G ↦ K)
      apply Measure.ext_of_generateFrom_of_iUnion C (fun _ ↦ univ)
        generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
        (by rw [iUnion_const]) (fun _ ↦ univ_mem_measurableCylinders _) (fun _ ↦ measure_ne_top _ _)
      intro W hW
      obtain ⟨J, D, hD, rfl⟩ := (mem_measurableCylinders W).mp hW
      have h := invariant_measure_rect_cylinder m S A hA hInv hU J hD
      change ξ (J.restrict ⁻¹' D) = (η U • law) (J.restrict ⁻¹' D)
      rw [hξ_apply (hD.preimage (Finset.measurable_restrict J)),
        hρ_apply (hD.preimage (Finset.measurable_restrict J)), smul_apply,
        smul_eq_mul, hη_apply]
      exact h
    rw [← hξ_apply hV, heq, Measure.prod_prod, smul_apply, smul_eq_mul]
  have hρ_eq : ρ = ν A • ν := by
    rw [hProd, hη_eq, hη_univ, Measure.prod_smul_left]
    rfl
  have hzero := congrArg (fun q : Measure (X × (G → K)) ↦ q Aᶜ) hρ_eq
  change (ν.restrict A) Aᶜ = (ν A • ν) Aᶜ at hzero
  rw [Measure.restrict_apply hA.compl, compl_inter_self, measure_empty, smul_apply,
    smul_eq_mul] at hzero
  change Filter.EventuallyEmptyOrUniv A (ae ν)
  apply eventuallyEmptyOrUniv_iff.mpr
  rcases mul_eq_zero.mp hzero.symm with h | h
  · exact Or.inr (by simpa [ae_iff] using h)
  · exact Or.inl (ae_iff.mpr h)

end SixProblems
end

/- Source module SixProblems.BernoulliProposition. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing

/-- Proposition 2.1, including the preservation of ergodicity. A finite set
of group elements represents a tuple of distinct translates. -/
theorem proposition2_1 {G X : Type} [Group G] [Countable G] [Infinite G]
    [MeasurableSpace X] [StandardBorelSpace X] (S : System G X)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ∃ (Y : Type) (mY : MeasurableSpace Y) (_ : @StandardBorelSpace Y mY)
      (T : @System G Y _ mY) (C : Set Y),
      MeasurableSet C ∧
      (∀ J : Finset G, (T.measure {y | ∀ g ∈ J, y ∈ T.act g ⁻¹' C}).toReal =
        ∫ x, ∏ g ∈ J, f (S.act g x) ∂S.measure) ∧
      (S.IsErgodic → T.IsErgodic) := by
  exact ⟨X × (G → ℝ), inferInstance, inferInstance, S.prod (bernoulliShift G unitIntervalLaw),
    bernoulliThreshold f, measurableSet_bernoulliThreshold hf,
    bernoulliThreshold_pattern S hf hf0 hf1, bernoulli_prod_isErgodic unitIntervalLaw S⟩

end SixProblems
end

/- Source module SixProblems.HilbertWeakCompactness. -/
section
/-
Adapted under Apache-2.0 from the Hilbert-space weak operator compactness
proof in Sohail Farhangi's certificate for arXiv:2410.21759.
This version works over both the real and complex scalars.
-/


/-!
# Weak operator compactness for Hilbert-space contractions

Transport Banach–Alaoglu through the Riesz isometry for the vector balls.
The product of the vector balls is compact, and the equations for a
linear operator cut out a closed subset.
-/


open Set
open scoped ComplexConjugate Topology

namespace SixProblems

section HilbertBalls

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem isCompact_weakHilbert_ball (r : ℝ) :
    IsCompact {u : WeakSpace 𝕜 E | ‖(toWeakSpace 𝕜 E).symm u‖ ≤ r} := by
  let R := InnerProductSpace.toDual 𝕜 E
  let inverse (f : WeakDual 𝕜 E) : WeakSpace 𝕜 E :=
    toWeakSpace 𝕜 E (R.symm (WeakDual.toStrongDual f))
  have hcont : Continuous inverse := by
    apply WeakBilin.continuous_of_continuous_eval
    intro y
    let v := R.symm y
    have h (f : WeakDual 𝕜 E) : y (R.symm (WeakDual.toStrongDual f)) = conj (f v) := by
      calc
        _ = inner 𝕜 v (R.symm (WeakDual.toStrongDual f)) :=
          InnerProductSpace.toDual_symm_apply.symm
        _ = conj (inner 𝕜 (R.symm (WeakDual.toStrongDual f)) v) :=
          (inner_conj_symm v _).symm
        _ = conj (f v) := congrArg (starRingEnd 𝕜)
          (InnerProductSpace.toDual_symm_apply (x := v) (y := WeakDual.toStrongDual f))
    change Continuous (fun f : WeakDual 𝕜 E ↦ y (R.symm (WeakDual.toStrongDual f)))
    simp_rw [h]
    exact RCLike.continuous_conj.comp (WeakBilin.eval_continuous _ v)
  have hset : inverse '' (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r) =
      {u : WeakSpace 𝕜 E | ‖(toWeakSpace 𝕜 E).symm u‖ ≤ r} := by
    ext u
    constructor
    · rintro ⟨f, hf, rfl⟩
      change dist (WeakDual.toStrongDual f) 0 ≤ r at hf
      change ‖R.symm (WeakDual.toStrongDual f)‖ ≤ r
      rw [R.symm.norm_map]
      rwa [dist_zero_right] at hf
    · intro hu
      let x := (toWeakSpace 𝕜 E).symm u
      refine ⟨(R x).toWeakDual, ?_, ?_⟩
      · change dist (R x) 0 ≤ r
        rw [dist_zero_right, R.norm_map]
        exact hu
      · change toWeakSpace 𝕜 E (R.symm (R x)) = u
        rw [R.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rw [← hset]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 E) r).image hcont

end HilbertBalls

section OperatorBalls

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A weakly compact vector ball at every radius gives weak operator
compactness of each operator ball. -/
theorem isCompact_wot_operatorBall_of_compact_vectorBalls (R : ℝ) (hR : 0 ≤ R)
    (hballs : ∀ r : ℝ, IsCompact {u : WeakSpace 𝕜 E | ‖(toWeakSpace 𝕜 E).symm u‖ ≤ r}) :
    IsCompact {T : E →WOT[𝕜] E | ‖T.toCLM‖ ≤ R} := by
  let ball (x : E) : Set (WeakSpace 𝕜 E) := {u | ‖(toWeakSpace 𝕜 E).symm u‖ ≤ R * ‖x‖}
  let addEq (x y : E) : Set (E → WeakSpace 𝕜 E) := {u | u (x + y) = u x + u y}
  let smulEq (c : 𝕜) (x : E) : Set (E → WeakSpace 𝕜 E) := {u | u (c • x) = c • u x}
  let equations := (⋂ x, ⋂ y, addEq x y) ∩ (⋂ c, ⋂ x, smulEq c x)
  let good := Set.pi Set.univ ball ∩ equations
  have hEq : IsClosed equations := by
    apply IsClosed.inter
    · exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
    · exact isClosed_iInter fun c ↦ isClosed_iInter fun x ↦
        isClosed_eq (continuous_apply (c • x)) ((continuous_apply x).const_smul c)
  have hcompact : IsCompact good :=
    (isCompact_univ_pi fun x ↦ hballs (R * ‖x‖)).inter_right hEq
  have hbound (u : good) (x : E) : ‖(toWeakSpace 𝕜 E).symm (u.val x)‖ ≤ R * ‖x‖ :=
    u.property.1 x (mem_univ x)
  let linear (u : good) : E →ₗ[𝕜] E :=
    { toFun := fun x ↦ (toWeakSpace 𝕜 E).symm (u.val x)
      map_add' := fun x y ↦ by
        have h : u.val (x + y) = u.val x + u.val y :=
          mem_iInter.1 (mem_iInter.1 u.property.2.1 x) y
        rw [h, map_add]
      map_smul' := fun c x ↦ by
        have h : u.val (c • x) = c • u.val x :=
          mem_iInter.1 (mem_iInter.1 u.property.2.2 c) x
        rw [h, map_smul]
        rfl }
  let operator (u : good) : E →WOT[𝕜] E :=
    ContinuousLinearMapWOT.ofCLM ((linear u).mkContinuous R (hbound u))
  have hcont : Continuous operator := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro x f
    change Continuous (fun u : good ↦ f ((toWeakSpace 𝕜 E).symm (u.val x)))
    exact (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).comp
      ((continuous_apply x).comp continuous_subtype_val)
  have hsurj : Set.range operator = {T : E →WOT[𝕜] E | ‖T.toCLM‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨u, rfl⟩
      exact ContinuousLinearMap.opNorm_le_bound _ hR (hbound u)
    · intro hT
      have hT' : ‖T.toCLM‖ ≤ R := hT
      let u (x : E) := toWeakSpace 𝕜 E (T x)
      have hu : u ∈ good := by
        refine ⟨fun x _ ↦ ?_, ?_, ?_⟩
        · change ‖(toWeakSpace 𝕜 E).symm (toWeakSpace 𝕜 E (T x))‖ ≤ R * ‖x‖
          rw [LinearEquiv.symm_apply_apply]
          exact T.toCLM.le_of_opNorm_le hT' x
        · exact mem_iInter.2 fun x ↦ mem_iInter.2 fun y ↦ by
            change u (x + y) = u x + u y
            simp [u, map_add]
        · exact mem_iInter.2 fun c ↦ mem_iInter.2 fun x ↦ by
            change u (c • x) = c • u x
            simp [u, map_smul]
      refine ⟨⟨u, hu⟩, ?_⟩
      apply ContinuousLinearMapWOT.toCLM_injective
      apply ContinuousLinearMap.ext
      intro x
      exact (toWeakSpace 𝕜 E).symm_apply_apply (T x)
  let : CompactSpace good := isCompact_iff_compactSpace.mp hcompact
  rw [← hsurj]
  exact isCompact_range hcont

end OperatorBalls

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem isCompact_wot_contractions :
    IsCompact {T : E →WOT[𝕜] E | ‖T.toCLM‖ ≤ 1} :=
  isCompact_wot_operatorBall_of_compact_vectorBalls 1 zero_le_one isCompact_weakHilbert_ball

end SixProblems
end

/- Source module Mixing.SupportingJdLG.Core. -/
section
/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/


/-!
# The group ideal and the JdLG projection

The identity of the smallest group ideal determines the reversible and almost
weakly stable parts of every continuous linear action of the semigroup. We
also construct the group ideal from uniqueness of the minimal idempotent in
a compact Hausdorff semigroup with continuous right translations.
-/


namespace Mixing.JdLGBridge

/-- A two-sided ideal of a semigroup that is a group for the inherited multiplication. -/
structure GroupIdeal (S : Type*) [Semigroup S] where
  carrier : Set S
  identity : S
  identity_mem : identity ∈ carrier
  mul_mem_left : ∀ a : S, ∀ {b : S}, b ∈ carrier → a * b ∈ carrier
  mul_mem_right : ∀ {a : S}, a ∈ carrier → ∀ b : S, a * b ∈ carrier
  identity_mul : ∀ {a : S}, a ∈ carrier → identity * a = a
  mul_identity : ∀ {a : S}, a ∈ carrier → a * identity = a
  inverse_exists : ∀ {a : S}, a ∈ carrier →
    ∃ b ∈ carrier, b * a = identity ∧ a * b = identity

namespace GroupIdeal

variable {S : Type*} [Semigroup S] (K : GroupIdeal S)

instance : Nonempty K.carrier := ⟨⟨K.identity, K.identity_mem⟩⟩

noncomputable instance : Group K.carrier where
  mul a b := ⟨a.1 * b.1, K.mul_mem_right a.2 b.1⟩
  one := ⟨K.identity, K.identity_mem⟩
  inv a := ⟨(K.inverse_exists a.2).choose, (K.inverse_exists a.2).choose_spec.1⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (K.identity_mul a.2)
  mul_one a := Subtype.ext (K.mul_identity a.2)
  inv_mul_cancel a := Subtype.ext (K.inverse_exists a.2).choose_spec.2.1

@[simp] theorem coe_one : ((1 : K.carrier) : S) = K.identity := rfl

@[simp] theorem coe_mul (a b : K.carrier) : ((a * b : K.carrier) : S) = a.1 * b.1 := rfl

/-- The identity of the group ideal is an idempotent of the ambient semigroup. -/
theorem identity_idempotent : K.identity * K.identity = K.identity :=
  K.identity_mul K.identity_mem

/-- The identity of the group ideal commutes with every ambient element. -/
theorem identity_mul_eq_mul_identity (s : S) : K.identity * s = s * K.identity := by
  calc
    K.identity * s = (K.identity * s) * K.identity :=
      (K.mul_identity (K.mul_mem_right K.identity_mem s)).symm
    _ = K.identity * (s * K.identity) := mul_assoc _ _ _
    _ = s * K.identity := K.identity_mul (K.mul_mem_left s K.identity_mem)

/-- A group has just one idempotent. -/
theorem eq_identity_of_idempotent {a : S} (ha : a ∈ K.carrier) (haa : a * a = a) :
    a = K.identity := by
  obtain ⟨b, hb, hba, _⟩ := K.inverse_exists ha
  calc
    a = K.identity * a := (K.identity_mul ha).symm
    _ = (b * a) * a := by rw [hba]
    _ = b * a := by rw [mul_assoc, haa]
    _ = K.identity := hba

/-- A group ideal is contained in every nonempty two-sided ideal. -/
theorem subset_of_ideal {I : Set S} (hI : I.Nonempty)
    (hleft : ∀ s : S, ∀ {a : S}, a ∈ I → s * a ∈ I)
    (hright : ∀ {a : S}, a ∈ I → ∀ s : S, a * s ∈ I) : K.carrier ⊆ I := by
  obtain ⟨a, ha⟩ := hI
  obtain ⟨b, hb, hba, _⟩ := K.inverse_exists (K.mul_mem_left a K.identity_mem)
  have hidentity : K.identity ∈ I := hba ▸ hleft b (hright ha K.identity)
  intro x hx
  exact K.identity_mul hx ▸ hright hidentity x

/-- Projection onto the group ideal by multiplication by its identity. -/
noncomputable def groupRetraction : S →ₙ* K.carrier where
  toFun s := ⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩
  map_mul' a b := Subtype.ext <| by
    change K.identity * (a * b) = (K.identity * a) * (K.identity * b)
    rw [← mul_assoc, ← mul_assoc (K.identity * a),
      K.mul_identity (K.mul_mem_right K.identity_mem a)]

theorem groupRetraction_surjective : Function.Surjective K.groupRetraction := fun a =>
  ⟨a.1, Subtype.ext (K.identity_mul a.2)⟩

/-- A surjective semigroup homomorphism sends a group ideal to a group ideal. -/
def map {T : Type*} [Semigroup T] (φ : S →ₙ* T) (hφ : Function.Surjective φ) : GroupIdeal T where
  carrier := φ '' K.carrier
  identity := φ K.identity
  identity_mem := ⟨K.identity, K.identity_mem, rfl⟩
  mul_mem_left := by
    rintro t _ ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := hφ t
    exact ⟨a * b, K.mul_mem_left a hb, φ.map_mul a b⟩
  mul_mem_right := by
    rintro _ ⟨a, ha, rfl⟩ t
    obtain ⟨b, rfl⟩ := hφ t
    exact ⟨a * b, K.mul_mem_right ha b, φ.map_mul a b⟩
  identity_mul := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, K.identity_mul ha]
  mul_identity := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, K.mul_identity ha]
  inverse_exists := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba, hab⟩ := K.inverse_exists ha
    exact ⟨φ b, ⟨b, hb, rfl⟩,
      by rw [← map_mul, hba], by rw [← map_mul, hab]⟩

end GroupIdeal

/-- Minimality in the usual order on idempotents, `f ≤ e` when `fe = ef = f`. -/
def IsMinimalIdempotent {S : Type*} [Semigroup S] (e : S) : Prop :=
  e * e = e ∧ ∀ f : S, f * f = f → f * e = f → e * f = f → f = e

theorem GroupIdeal.isMinimalIdempotent_identity {S : Type*} [Semigroup S] (K : GroupIdeal S) :
    IsMinimalIdempotent K.identity := by
  refine ⟨K.identity_idempotent, fun f hff hfe _ => ?_⟩
  apply K.eq_identity_of_idempotent _ hff
  exact hfe ▸ K.mul_mem_left f K.identity_mem

theorem GroupIdeal.eq_identity_of_isMinimalIdempotent {S : Type*} [Semigroup S]
    (K : GroupIdeal S) {f : S} (hf : IsMinimalIdempotent f) : f = K.identity := by
  have hff : (K.identity * f) * (K.identity * f) = K.identity * f := by
    have h := congrArg (fun a : K.carrier => (a : S)) (K.groupRetraction.map_mul f f)
    exact h.symm.trans (congrArg (K.identity * ·) hf.1)
  have hid : K.identity * f = K.identity :=
    K.eq_identity_of_idempotent (K.mul_mem_right K.identity_mem f) hff
  exact (hf.2 K.identity K.identity_idempotent hid
    ((K.identity_mul_eq_mul_identity f).symm.trans hid)).symm

section CompactSemigroup

variable {S : Type*} [Semigroup S]

/-- A subset stable under multiplication on the left by every ambient element. -/
def LeftIdeal (L : Set S) : Prop :=
  ∀ a : S, ∀ ⦃b : S⦄, b ∈ L → a * b ∈ L

/-- A nonempty left ideal that is minimal among nonempty left ideals. -/
def MinimalLeftIdeal (L : Set S) : Prop :=
  L.Nonempty ∧ LeftIdeal L ∧
    ∀ V : Set S, V.Nonempty → LeftIdeal V → V ⊆ L → V = L

theorem principal_leftIdeal (x : S) : LeftIdeal (Set.range (· * x)) := by
  intro a b hb
  obtain ⟨c, rfl⟩ := hb
  exact ⟨a * c, mul_assoc a c x⟩

theorem principal_eq_of_minimalLeftIdeal {L : Set S} (hL : MinimalLeftIdeal L)
    {x : S} (hx : x ∈ L) : Set.range (· * x) = L := by
  let : Nonempty S := ⟨x⟩
  apply hL.2.2 _ (Set.range_nonempty _) (principal_leftIdeal x)
  rintro _ ⟨y, rfl⟩
  exact hL.2.1 y hx

theorem minimalLeftIdeal_image {L : Set S} (hL : MinimalLeftIdeal L) (s : S) :
    MinimalLeftIdeal ((· * s) '' L) := by
  refine ⟨hL.1.image _, ?_, ?_⟩
  · intro a b hb
    obtain ⟨c, hc, rfl⟩ := hb
    exact ⟨a * c, hL.2.1 a hc, mul_assoc a c s⟩
  · intro V hV hVleft hVL
    let U : Set S := {x ∈ L | x * s ∈ V}
    have hU : U.Nonempty := by
      obtain ⟨v, hv⟩ := hV
      obtain ⟨x, hx, rfl⟩ := hVL hv
      exact ⟨x, hx, hv⟩
    have hUleft : LeftIdeal U := by
      intro a y hy
      exact ⟨hL.2.1 a hy.1, (mul_assoc a y s).symm ▸ hVleft a hy.2⟩
    have hUL : U = L := hL.2.2 U hU hUleft fun _ h => h.1
    refine le_antisymm hVL ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxU : x ∈ U := hUL.symm ▸ hx
    exact hxU.2

theorem exists_compact_minimalLeftIdeal [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [Nonempty S]
    (hcont : ∀ s : S, Continuous (· * s)) :
    ∃ L : Set S, IsCompact L ∧ MinimalLeftIdeal L := by
  let P : Set (Set S) := {L | IsClosed L ∧ L.Nonempty ∧ LeftIdeal L}
  have hmin : ∃ L, Minimal (· ∈ P) L := by
    refine zorn_superset _ fun C hCP hC => ?_
    refine ⟨⋂₀ C, ⟨isClosed_sInter fun L hL => (hCP hL).1, ?_, ?_⟩,
      fun L hL => Set.sInter_subset_of_mem hL⟩
    · obtain rfl | hCnonempty := C.eq_empty_or_nonempty
      · rw [Set.sInter_empty]
        exact Set.univ_nonempty
      convert
        @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ _ _ hCnonempty.coe_sort
          ((↑) : C → Set S) ?_ ?_ ?_ ?_
      · exact Set.sInter_eq_iInter
      · exact DirectedOn.directed_val (IsChain.directedOn hC.symm)
      · exact fun L => (hCP L.2).2.1
      · exact fun L => (hCP L.2).1.isCompact
      · exact fun L => (hCP L.2).1
    · exact fun a _ hb => Set.mem_sInter.mpr fun L hL =>
        (hCP hL).2.2 a (Set.mem_sInter.mp hb L hL)
  obtain ⟨L, hL⟩ := hmin
  refine ⟨L, hL.prop.1.isCompact, hL.prop.2.1, hL.prop.2.2, ?_⟩
  intro V hV hVleft hVL
  obtain ⟨v, hv⟩ := hV
  have hsubset : Set.range (· * v) ⊆ V := by
    rintro _ ⟨w, rfl⟩
    exact hVleft w hv
  have hEq : Set.range (· * v) = L := hL.eq_of_subset
    ⟨(isCompact_range (hcont v)).isClosed, Set.range_nonempty _, principal_leftIdeal v⟩
    (hsubset.trans hVL)
  exact le_antisymm hVL (hEq ▸ hsubset)

theorem isMinimalIdempotent_of_mem_minimalLeftIdeal {L : Set S}
    (hL : MinimalLeftIdeal L) {e : S} (he : e ∈ L) (heid : e * e = e) :
    IsMinimalIdempotent e := by
  refine ⟨heid, fun f hff hfe hef => ?_⟩
  have hf : f ∈ L := hfe ▸ hL.2.1 f he
  have he' : e ∈ Set.range (· * f) := (principal_eq_of_minimalLeftIdeal hL hf).symm ▸ he
  obtain ⟨a, ha⟩ := he'
  change a * f = e at ha
  calc
    f = e * f := hef.symm
    _ = (a * f) * f := by rw [ha]
    _ = a * f := by rw [mul_assoc, hff]
    _ = e := ha

variable [TopologicalSpace S] [T2Space S]

private theorem unique_idempotent_mem_minimalLeftIdeal {e : S}
    (hcont : ∀ s : S, Continuous (· * s))
    (heUnique : ∀ f : S, IsMinimalIdempotent f → f = e)
    {L : Set S} (hcompact : IsCompact L) (hL : MinimalLeftIdeal L) : e ∈ L := by
  obtain ⟨f, hf, hff⟩ := exists_idempotent_in_compact_subsemigroup hcont L hL.1 hcompact
    (fun a _ _ hb => hL.2.1 a hb)
  exact heUnique f (isMinimalIdempotent_of_mem_minimalLeftIdeal hL hf hff) ▸ hf

variable [CompactSpace S]

/-- In a compact Hausdorff semigroup with continuous right translations,
uniqueness of the minimal idempotent gives a compact group ideal. -/
theorem exists_compact_groupIdeal_of_existsUnique_minimalIdempotent
    (hcont : ∀ s : S, Continuous (· * s)) (h : ∃! e : S, IsMinimalIdempotent e) :
    ∃ K : GroupIdeal S, IsCompact K.carrier := by
  obtain ⟨e, he, heUnique⟩ := h
  let : Nonempty S := ⟨e⟩
  obtain ⟨L, hcompact, hL⟩ := exists_compact_minimalLeftIdeal hcont
  have heL := unique_idempotent_mem_minimalLeftIdeal hcont heUnique hcompact hL
  have hprincipal := principal_eq_of_minimalLeftIdeal hL heL
  have image_eq (s : S) : (· * s) '' L = L := by
    have hmin := minimalLeftIdeal_image hL s
    have he' := unique_idempotent_mem_minimalLeftIdeal hcont heUnique
      (hcompact.image (hcont s)) hmin
    exact (principal_eq_of_minimalLeftIdeal hmin he').symm.trans hprincipal
  have hrightId {a : S} (ha : a ∈ L) : a * e = a := by
    have ha' : a ∈ Set.range (· * e) := hprincipal.symm ▸ ha
    obtain ⟨x, rfl⟩ := ha'
    rw [mul_assoc, he.1]
  have inv_pair {a : S} (ha : a ∈ L) : ∃ b ∈ L, b * a = e ∧ a * b = e := by
    have he' : e ∈ (· * a) '' L := (image_eq a).symm ▸ heL
    obtain ⟨b, hb, hba⟩ := he'
    change b * a = e at hba
    refine ⟨b, hb, hba, heUnique _ (isMinimalIdempotent_of_mem_minimalLeftIdeal hL
      (hL.2.1 a hb) ?_)⟩
    rw [mul_assoc, ← mul_assoc b a b, hba, ← mul_assoc, hrightId ha]
  refine ⟨⟨L, e, heL, hL.2.1, ?_, ?_, @hrightId, @inv_pair⟩, hcompact⟩
  · intro a ha s
    exact image_eq s ▸ (show a * s ∈ (· * s) '' L from ⟨a, ha, rfl⟩)
  · intro a ha
    obtain ⟨b, _, hba, hab⟩ := inv_pair ha
    rw [← hab, mul_assoc, hba, hrightId ha]

/-- The minimal-idempotent criterion for a compact group ideal. -/
theorem exists_compact_groupIdeal_iff_existsUnique_minimalIdempotent
    (hcont : ∀ s : S, Continuous (· * s)) :
    (∃ K : GroupIdeal S, IsCompact K.carrier) ↔ ∃! e : S, IsMinimalIdempotent e := by
  refine ⟨?_, exists_compact_groupIdeal_of_existsUnique_minimalIdempotent hcont⟩
  rintro ⟨K, _⟩
  exact ⟨K.identity, K.isMinimalIdempotent_identity,
    fun _ h => K.eq_identity_of_isMinimalIdempotent h⟩

/-- A nonempty compact commutative semigroup has a unique minimal idempotent. -/
theorem existsUnique_minimalIdempotent_of_commutative [Nonempty S]
    (hcont : ∀ s : S, Continuous (· * s)) (hcomm : ∀ a b : S, a * b = b * a) :
    ∃! e : S, IsMinimalIdempotent e := by
  obtain ⟨L, hcompact, hL⟩ := exists_compact_minimalLeftIdeal hcont
  obtain ⟨e, he, hee⟩ := exists_idempotent_in_compact_subsemigroup hcont L hL.1 hcompact
    (fun a _ _ hb => hL.2.1 a hb)
  have hmin := isMinimalIdempotent_of_mem_minimalLeftIdeal hL he hee
  refine ⟨e, hmin, fun f hf => ?_⟩
  have hfe : (f * e) * e = f * e := by rw [mul_assoc, hee]
  have hef : (f * e) * f = f * e := by
    rw [mul_assoc, hcomm e f, ← mul_assoc, hf.1]
  have hff : (f * e) * (f * e) = f * e := by rw [← mul_assoc, hef, hfe]
  have hEqE := hmin.2 (f * e) hff hfe ((hcomm e (f * e)).trans hfe)
  have hEqF := hf.2 (f * e) hff hef ((hcomm f (f * e)).trans hef)
  exact hEqF.symm.trans hEqE

end CompactSemigroup

section Operators

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Equation (1), expressed for the semigroup acting by bounded operators. -/
def IsReversible (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  ∀ a : S, ∃ b : S, ρ b (ρ a x) = x

/-- Equation (1)'s almost weakly stable part, expressed using the operator closure. -/
def IsAlmostWeaklyStable (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  ∃ a : S, ρ a x = 0

variable (K : GroupIdeal S) (ρ : S →ₙ* (E →L[𝕜] E))

/-- The JdLG projection is the action of the group-ideal identity. -/
def GroupIdeal.projection : E →L[𝕜] E := ρ K.identity

theorem GroupIdeal.projection_apply_apply (x : E) : K.projection ρ (K.projection ρ x) =
    K.projection ρ x := by
  change (ρ K.identity * ρ K.identity) x = ρ K.identity x
  rw [← map_mul, K.identity_idempotent]

theorem GroupIdeal.projection_commutes (s : S) (x : E) :
    K.projection ρ (ρ s x) = ρ s (K.projection ρ x) := by
  change (ρ K.identity * ρ s) x = (ρ s * ρ K.identity) x
  rw [← map_mul, ← map_mul, K.identity_mul_eq_mul_identity]

theorem GroupIdeal.reversible_iff_fixed (x : E) :
    IsReversible ρ x ↔ K.projection ρ x = x := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h K.identity
    calc
      K.projection ρ x = K.projection ρ (ρ b (K.projection ρ x)) :=
        congrArg (K.projection ρ) hb.symm
      _ = ρ b (K.projection ρ (K.projection ρ x)) := K.projection_commutes ρ b _
      _ = x := by rw [K.projection_apply_apply]; exact hb
  · intro hx a
    obtain ⟨b, hb, hba, _⟩ := K.inverse_exists (K.mul_mem_right K.identity_mem a)
    refine ⟨b, ?_⟩
    change (ρ b * ρ a) x = x
    have hb' : b * a = K.identity := by rwa [← mul_assoc, K.mul_identity hb] at hba
    rw [← map_mul, hb']
    exact hx

theorem GroupIdeal.stable_iff_projection_eq_zero (x : E) :
    IsAlmostWeaklyStable ρ x ↔ K.projection ρ x = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, _, hba, _⟩ := K.inverse_exists (K.mul_mem_right K.identity_mem a)
    change ρ K.identity x = 0
    rw [← hba, map_mul, map_mul]
    change ρ b (ρ K.identity (ρ a x)) = 0
    simp [ha]
  · exact fun h => ⟨K.identity, h⟩

theorem GroupIdeal.projection_isIdempotentElem :
    IsIdempotentElem (K.projection ρ).toLinearMap := by
  change (K.projection ρ).toLinearMap * (K.projection ρ).toLinearMap =
    (K.projection ρ).toLinearMap
  ext x
  exact K.projection_apply_apply ρ x

/-- The reversible part is the image of the projection. -/
theorem GroupIdeal.reversible_iff_mem_range (x : E) :
    IsReversible ρ x ↔ x ∈ LinearMap.range (K.projection ρ).toLinearMap := by
  exact (K.reversible_iff_fixed ρ x).trans
    (LinearMap.IsIdempotentElem.mem_range_iff (K.projection_isIdempotentElem ρ)).symm

/-- The almost weakly stable part is the kernel of the projection. -/
theorem GroupIdeal.stable_iff_mem_ker (x : E) :
    IsAlmostWeaklyStable ρ x ↔ x ∈ LinearMap.ker (K.projection ρ).toLinearMap :=
  (K.stable_iff_projection_eq_zero ρ x).trans LinearMap.mem_ker.symm

/-- The reversible range and the almost weakly stable kernel are complementary. -/
theorem GroupIdeal.range_isCompl_ker :
    IsCompl (LinearMap.range (K.projection ρ).toLinearMap)
      (LinearMap.ker (K.projection ρ).toLinearMap) :=
  LinearMap.IsIdempotentElem.isCompl (K.projection_isIdempotentElem ρ)

/-- The reversible range is a closed subspace of the Banach space. -/
theorem GroupIdeal.isClosed_range_projection :
    IsClosed (LinearMap.range (K.projection ρ).toLinearMap : Set E) := by
  have hEq : (LinearMap.range (K.projection ρ).toLinearMap : Set E) =
      {x | K.projection ρ x = x} := by
    ext x
    exact LinearMap.IsIdempotentElem.mem_range_iff (K.projection_isIdempotentElem ρ)
  rw [hEq]
  exact isClosed_eq (K.projection ρ).continuous continuous_id

/-- The stable kernel is a closed subspace of the Banach space. -/
theorem GroupIdeal.isClosed_ker_projection :
    IsClosed (LinearMap.ker (K.projection ρ).toLinearMap : Set E) := by
  change IsClosed {x | K.projection ρ x = 0}
  exact isClosed_eq (K.projection ρ).continuous continuous_const

/-- The projection and its complementary projection give the two components of a vector. -/
theorem GroupIdeal.projection_splitting (x : E) :
    IsReversible ρ (K.projection ρ x) ∧
    IsAlmostWeaklyStable ρ (x - K.projection ρ x) ∧
    x = K.projection ρ x + (x - K.projection ρ x) := by
  refine ⟨(K.reversible_iff_fixed ρ _).mpr (K.projection_apply_apply ρ x), ?_, ?_⟩
  · apply (K.stable_iff_projection_eq_zero ρ _).mpr
    rw [map_sub, K.projection_apply_apply, sub_self]
  · rw [add_comm, sub_add_cancel]

/-- The projection intertwines under a quotient homomorphism on the acting semigroups. -/
theorem GroupIdeal.projection_intertwines {T F : Type*} [Semigroup T] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (φ : S →ₙ* T) (hφ : Function.Surjective φ)
    (τ : T →ₙ* (F →L[𝕜] F)) (f : E →L[𝕜] F)
    (hf : ∀ s x, τ (φ s) (f x) = f (ρ s x)) (x : E) :
    (K.map φ hφ).projection τ (f x) = f (K.projection ρ x) := hf K.identity x

/-- The range and kernel identities of Theorem 2.3(ii), given the induced surjective homomorphism
on the acting semigroups. -/
theorem GroupIdeal.projection_range_kernel_map {T F : Type*} [Semigroup T]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (φ : S →ₙ* T) (hφ : Function.Surjective φ)
    (τ : T →ₙ* (F →L[𝕜] F)) (f : E →L[𝕜] F) (hfSurj : Function.Surjective f)
    (hf : ∀ s x, τ (φ s) (f x) = f (ρ s x)) :
    (LinearMap.range (K.projection ρ).toLinearMap).map f.toLinearMap =
        LinearMap.range ((K.map φ hφ).projection τ).toLinearMap ∧
      (LinearMap.ker (K.projection ρ).toLinearMap).map f.toLinearMap =
        LinearMap.ker ((K.map φ hφ).projection τ).toLinearMap := by
  have hP := K.projection_intertwines ρ φ hφ τ f hf
  constructor
  · ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨f y, hP y⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hfSurj y
      exact ⟨K.projection ρ x, ⟨x, rfl⟩, (hP x).symm⟩
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (K.map φ hφ).projection τ (f x) = 0
      rw [hP, show K.projection ρ x = 0 from hx, map_zero]
    · intro hz
      obtain ⟨x, rfl⟩ := hfSurj z
      refine ⟨x - K.projection ρ x, ?_, ?_⟩
      · change K.projection ρ (x - K.projection ρ x) = 0
        rw [map_sub, K.projection_apply_apply, sub_self]
      · change f (x - K.projection ρ x) = f x
        rw [map_sub, ← hP, show (K.map φ hφ).projection τ (f x) = 0 from hz, sub_zero]

end Operators

section WeakOperator

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The given representation viewed in the weak operator topology. -/
def weakRepresentation (π : S →ₙ* (E →L[𝕜] E)) : S →ₙ* (E →WOT[𝕜] E) :=
  ContinuousLinearMapWOT.ringEquiv.symm.toMulHom.comp π

/-- The weak operator closure of the represented semigroup. -/
def weakOperatorClosure (π : S →ₙ* (E →L[𝕜] E)) : Subsemigroup (E →WOT[𝕜] E) :=
  (weakRepresentation π).srange.topologicalClosure

/-- The action of the operator closure, returning ordinary continuous linear maps. -/
def closureAction (π : S →ₙ* (E →L[𝕜] E)) : (weakOperatorClosure π) →ₙ* (E →L[𝕜] E) :=
  ContinuousLinearMapWOT.ringEquiv.toMulHom.comp (MulMemClass.subtype (weakOperatorClosure π))

/-- The original semigroup maps into its weak operator closure with dense image. -/
def closureInclusion (π : S →ₙ* (E →L[𝕜] E)) : S →ₙ* weakOperatorClosure π :=
  (weakRepresentation π).codRestrict (weakOperatorClosure π) fun s => subset_closure ⟨s, rfl⟩

@[simp] theorem closureAction_inclusion (π : S →ₙ* (E →L[𝕜] E)) (s : S) :
    closureAction π (closureInclusion π s) = π s := rfl

theorem denseRange_closureInclusion (π : S →ₙ* (E →L[𝕜] E)) :
    DenseRange (closureInclusion π) := by
  intro a
  rw [closure_subtype, ← Set.range_comp]
  exact a.2

/-- The paper's JdLG-admissibility condition on the weak operator closure. -/
def IsJdLGAdmissible (π : S →ₙ* (E →L[𝕜] E)) : Prop :=
  IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E)) ∧
    ∃! e : weakOperatorClosure π, IsMinimalIdempotent e

variable [SeparatingDual 𝕜 E]

/-- The weak operator closure of an admissible representation has a compact group ideal. -/
theorem exists_groupIdeal_of_admissible {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) :
    ∃ K : GroupIdeal (weakOperatorClosure π), IsCompact K.carrier := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  exact exists_compact_groupIdeal_of_existsUnique_minimalIdempotent
    continuous_mul_const hπ.2

/-- Almost weak stability means that zero belongs to the weak closure of the original orbit. -/
theorem stable_iff_zero_mem_weakOrbitClosure {π : S →ₙ* (E →L[𝕜] E)}
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      (0 : WeakSpace 𝕜 E) ∈ closure (Set.range fun s : S => toWeakSpace 𝕜 E (π s x)) := by
  let evaluation : (E →WOT[𝕜] E) → WeakSpace 𝕜 E := fun a => toWeakSpace 𝕜 E (a x)
  have hEval : Continuous evaluation := WeakBilin.continuous_of_continuous_eval _
    fun y => ContinuousLinearMapWOT.continuous_dual_apply x y
  have hImage : evaluation '' (weakOperatorClosure π : Set (E →WOT[𝕜] E)) =
      closure (Set.range fun s : S => toWeakSpace 𝕜 E (π s x)) := by
    apply le_antisymm
    · have hEvalRange : evaluation '' Set.range (weakRepresentation π) =
          Set.range (fun s : S => toWeakSpace 𝕜 E (π s x)) := by
        rw [← Set.range_comp]
        rfl
      change evaluation '' closure (Set.range (weakRepresentation π)) ⊆ _
      rw [← hEvalRange]
      exact image_closure_subset_closure_image hEval
    · apply closure_minimal _ (hcompact.image hEval).isClosed
      rintro _ ⟨s, rfl⟩
      exact ⟨weakRepresentation π s, (closureInclusion π s).2, rfl⟩
  rw [← hImage]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.1, a.2, (congrArg (toWeakSpace 𝕜 E) ha).trans (map_zero _)⟩
  · rintro ⟨a, ha, hz⟩
    exact ⟨⟨a, ha⟩, (toWeakSpace 𝕜 E).injective (hz.trans (map_zero _).symm)⟩

/-- The commutative case of Theorem 1.2(i). Weak compactness of the operator closure suffices. -/
theorem admissible_of_commutative [Nonempty S] {π : S →ₙ* (E →L[𝕜] E)}
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E)))
    (hcomm : ∀ a b : S, π a * π b = π b * π a) : IsJdLGAdmissible π := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty (weakOperatorClosure π) := ⟨⟨weakRepresentation π (Classical.arbitrary S),
    subset_closure ⟨Classical.arbitrary S, rfl⟩⟩⟩
  have : IsMulCommutative (weakRepresentation π).srange := by
    apply IsMulCommutative.of_setLike_mul_comm
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    apply ContinuousLinearMapWOT.ringEquiv.injective
    rw [map_mul, map_mul]
    exact hcomm a b
  let : IsMulCommutative (weakOperatorClosure π) := inferInstanceAs
    (IsMulCommutative (weakRepresentation π).srange.topologicalClosure)
  exact ⟨hcompact, existsUnique_minimalIdempotent_of_commutative continuous_mul_const
    (fun a b => mul_comm' a b)⟩

/-- The JdLG decomposition for a relatively weakly compact, admissible representation.
The projection belongs to the weak operator closure, commutes with that closure,
and identifies the two spaces of equation (1) as its range and kernel. -/
theorem decomposition_of_admissible {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) :
    ∃ e : weakOperatorClosure π,
      IsMinimalIdempotent e ∧
      (∀ a : weakOperatorClosure π, e * a = a * e) ∧
      IsCompl (LinearMap.range (closureAction π e).toLinearMap)
        (LinearMap.ker (closureAction π e).toLinearMap) ∧
      (∀ x : E, IsReversible (closureAction π) x ↔
        x ∈ LinearMap.range (closureAction π e).toLinearMap) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        x ∈ LinearMap.ker (closureAction π e).toLinearMap := by
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  exact ⟨K.identity, K.isMinimalIdempotent_identity, K.identity_mul_eq_mul_identity,
    K.range_isCompl_ker _, K.reversible_iff_mem_range _, K.stable_iff_mem_ker _⟩


end WeakOperator

end Mixing.JdLGBridge
end

/- Source module Mixing.SupportingJdLG.Orbits. -/
section
/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/


/-!
# Norm-precompact orbits and reversibility

Under the norm-separation hypothesis of Theorem 3.1, a norm-precompact
orbit belongs to the reversible part. The argument applies the separation
hypothesis to the almost weakly stable component of the vector.
-/


namespace Mixing.JdLGBridge

open Set

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The orbit has a compact closure in the norm topology. -/
def HasPrecompactOrbit (π : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  IsCompact (closure (Set.range fun s ↦ π s x))

private theorem weakOperatorClosure_apply_mem_normOrbitClosure
    (π : S →ₙ* (E →L[𝕜] E)) (x : E) (hx : HasPrecompactOrbit π x)
    (A : weakOperatorClosure π) : A.1 x ∈ closure (Set.range fun s ↦ π s x) := by
  let C := closure (Set.range fun s ↦ π s x)
  let weak := toWeakSpaceCLM 𝕜 E
  have hclosed : IsClosed (weak '' C) := (hx.image weak.continuous).isClosed
  let evaluate : (E →WOT[𝕜] E) → WeakSpace 𝕜 E := fun T ↦ weak (T x)
  have heval : Continuous evaluate :=
    WeakBilin.continuous_of_continuous_eval _ fun f ↦
      ContinuousLinearMapWOT.continuous_dual_apply x f
  have hsub : ((weakRepresentation π).srange : Set (E →WOT[𝕜] E)) ⊆
      evaluate ⁻¹' (weak '' C) := by
    rintro _ ⟨s, rfl⟩
    exact ⟨π s x, subset_closure ⟨s, rfl⟩, rfl⟩
  have hA := closure_minimal hsub (hclosed.preimage heval) A.2
  obtain ⟨y, hy, heq⟩ := hA
  exact ((toWeakSpace 𝕜 E).injective heq) ▸ hy

/-- The precompact-orbit-to-reversible implication in Theorem 3.1. The uniform
positive lower bound for each nonzero precompact orbit excludes any nonzero
almost weakly stable component. -/
theorem reversible_of_precompactOrbit_of_separated
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (hseparated : ∀ y : E, y ≠ 0 → HasPrecompactOrbit π y →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : S, δ ≤ ‖π s y‖)
    (x : E) (hx : HasPrecompactOrbit π x) : IsReversible (closureAction π) x := by
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  let P := K.projection (closureAction π)
  let y := x - P x
  have hyzero : P y = 0 := by
    change P (x - P x) = 0
    rw [map_sub, K.projection_apply_apply (closureAction π) x, sub_self]
  let changeVector : E → E := fun z ↦ z - P z
  have hcont : Continuous changeVector := continuous_id.sub P.continuous
  have hcomm (s : S) : P (π s x) = π s (P x) := by
    let A : weakOperatorClosure π := ⟨weakRepresentation π s, subset_closure ⟨s, rfl⟩⟩
    exact K.projection_commutes (closureAction π) A x
  have hsub : Set.range (fun s ↦ π s y) ⊆
      changeVector '' closure (Set.range (fun s ↦ π s x)) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨π s x, subset_closure ⟨s, rfl⟩, ?_⟩
    change π s x - P (π s x) = π s (x - P x)
    rw [hcomm, map_sub]
  have hC := hx.image hcont
  have hy : HasPrecompactOrbit π y :=
    hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  have hzero : (0 : E) ∈ closure (Set.range fun s ↦ π s y) := by
    have hp := weakOperatorClosure_apply_mem_normOrbitClosure π y hy K.identity
    change P y ∈ closure (Set.range fun s ↦ π s y) at hp
    simpa only [hyzero] using hp
  apply (K.reversible_iff_fixed (closureAction π) x).2
  by_contra hfix
  have hne : y ≠ 0 := fun hy ↦ hfix ((sub_eq_zero.mp hy).symm)
  obtain ⟨δ, hδ, hlower⟩ := hseparated y hne hy
  have hclosed : IsClosed {z : E | δ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have hsubset : Set.range (fun s : S ↦ π s y) ⊆ {z : E | δ ≤ ‖z‖} := by
    rintro _ ⟨s, rfl⟩
    exact hlower s
  have hδzero : δ ≤ ‖(0 : E)‖ := closure_minimal hsubset hclosed hzero
  exact hδ.not_ge (by simpa using hδzero)

end Mixing.JdLGBridge
end

/- Source module Mixing.SupportingJdLG.ReversibleOrbits. -/
section
/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/


/-! # Compact norms of reversible orbits

A countable monoid generates a compact subgroup in a compact semitopological
group. An orbit of that subgroup is norm-separable by Hahn–Banach separation.
Baire category on the compact subgroup then upgrades weak orbit continuity
to norm continuity. The sequential criterion for compactness applies this
argument to an arbitrary sequence of points in the original orbit.
-/


open Filter Set Topology

namespace Mixing.JdLGBridge

section Bounds

variable {X 𝕜 E : Type*} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A weakly operator-continuous family indexed by a compact space is uniformly
bounded in operator norm on a Banach space. -/
theorem exists_operatorBound_of_compact_wot [CompleteSpace E] (A : X → E →L[𝕜] E)
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a, ‖A a‖ ≤ C := by
  have hpoint (x : E) : ∃ C, ∀ a, ‖A a x‖ ≤ C := by
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun a ↦ NormedSpace.inclusionInDoubleDual 𝕜 E (A a x)) fun f ↦ by
        have hcont : Continuous fun a ↦ ‖f (A a x)‖ :=
          ((ContinuousLinearMapWOT.continuous_dual_apply x f).comp hA).norm
        obtain ⟨B, hB⟩ := (isCompact_range hcont).bddAbove
        exact ⟨B, fun a ↦ hB (mem_range_self a)⟩
    refine ⟨C, fun a ↦ ?_⟩
    rw [← (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).norm_map (A a x)]
    exact hC a
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun a ↦ (hC a).trans (le_max_left _ _)⟩

end Bounds

section CompactGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [SeparatelyContinuousMul G]

private theorem exists_subgroup_topologicalClosure (M : Submonoid G) :
    ∃ H : Subgroup G, (H : Set G) = (M.topologicalClosure : Set G) := by
  let N := M.topologicalClosure
  have hInv {a : G} (ha : a ∈ N) : a⁻¹ ∈ N := by
    let A := (a * ·) '' (N : Set G)
    have hcompact : IsCompact A := M.isClosed_topologicalClosure.isCompact.image
      (continuous_const_mul a)
    have hnonempty : A.Nonempty := ⟨a * 1, 1, N.one_mem, rfl⟩
    have hmul : ∀ p ∈ A, ∀ q ∈ A, p * q ∈ A := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      exact ⟨p * (a * q), N.mul_mem hp (N.mul_mem ha hq), (mul_assoc a p (a * q)).symm⟩
    obtain ⟨e, he, hee⟩ := exists_idempotent_in_compact_subsemigroup continuous_mul_const
      A hnonempty hcompact hmul
    have he1 : e = 1 := mul_left_cancel (hee.trans (mul_one e).symm)
    obtain ⟨y, hy, hay⟩ := he
    change a * y = e at hay
    have hy1 : y = a⁻¹ := by calc
      y = a⁻¹ * (a * y) := by simp
      _ = a⁻¹ := by rw [hay, he1, mul_one]
    exact hy1 ▸ hy
  exact ⟨{ N with inv_mem' := hInv }, rfl⟩

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private theorem isClosed_image_convex_toWeakSpace {C : Set E} [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [LocallyConvexSpace ℝ E] (hC : IsClosed C) (hcC : Convex ℝ C) :
    IsClosed (toWeakSpace 𝕜 E '' C) := by
  rw [← hC.closure_eq, hcC.toWeakSpace_closure 𝕜]
  exact isClosed_closure

variable (A : G →ₙ* (E →L[𝕜] E))

omit [CompactSpace G] [T2Space G] [SeparatelyContinuousMul G] in
private theorem continuous_weak_eval
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) (x : E) :
    Continuous fun a ↦ toWeakSpace 𝕜 E (A a x) :=
  WeakBilin.continuous_of_continuous_eval _ fun f ↦
    (ContinuousLinearMapWOT.continuous_dual_apply x f).comp hA

private theorem continuous_orbit_of_separable
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ a, ‖A a‖ ≤ C) (x : E)
    (hs : TopologicalSpace.IsSeparable (range fun a ↦ A a x)) :
    Continuous fun a ↦ A a x := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  have hweak := continuous_weak_eval A hA x
  obtain ⟨D, hcD, hD⟩ := hs
  let : Countable D := hcD.to_subtype
  apply continuous_iff_continuousAt.2
  intro b
  apply Metric.tendsto_nhds.2
  intro ε hε
  let r := ε / (4 * C)
  have hr : 0 < r := div_pos hε (mul_pos (by norm_num) hC)
  let F (v : D) : Set G := {a | A a x ∈ Metric.closedBall (v : E) r}
  have hclosed (v : D) : IsClosed (F v) := by
    have hweakClosed := isClosed_image_convex_toWeakSpace (𝕜 := 𝕜)
      (Metric.isClosed_closedBall (x := (v : E)) (ε := r)) (convex_closedBall _ _)
    convert hweakClosed.preimage hweak using 1
    ext a
    simp only [F, mem_ofPred_eq, mem_preimage, mem_image]
    exact ⟨fun h ↦ ⟨_, h, rfl⟩,
      fun ⟨y, hy, heq⟩ ↦ (toWeakSpace 𝕜 E).injective heq ▸ hy⟩
  have hcover : (⋃ v, F v) = univ := by
    apply eq_univ_of_forall
    intro a
    obtain ⟨v, hv, hva⟩ := Metric.mem_closure_iff.1 (hD (mem_range_self a)) r hr
    exact mem_iUnion.2 ⟨⟨v, hv⟩, hva.le⟩
  obtain ⟨v, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have hba : (a * b⁻¹) * b = a := by simp [mul_assoc]
  have hev : ∀ᶠ g in 𝓝 b, (a * b⁻¹) * g ∈ F v := by
    apply (continuous_const_mul (a * b⁻¹)).continuousAt (x := b)
    change F v ∈ 𝓝 ((a * b⁻¹) * b)
    rw [hba]
    exact mem_interior_iff_mem_nhds.1 ha
  have hau : a ∈ F v := interior_subset ha
  have hav : A a x ∈ Metric.closedBall (v : E) r := hau
  filter_upwards [hev] with g hg
  have hd : dist (A ((a * b⁻¹) * g) x) (A a x) ≤ r + r :=
    (dist_triangle_right _ _ _).trans (add_le_add hg hav)
  have hfirst : A (b * a⁻¹) (A ((a * b⁻¹) * g) x) = A g x := by
    change (A (b * a⁻¹) * A ((a * b⁻¹) * g)) x = _
    rw [← map_mul]
    simp [mul_assoc]
  have hsecond : A (b * a⁻¹) (A a x) = A b x := by
    change (A (b * a⁻¹) * A a) x = _
    rw [← map_mul]
    simp [mul_assoc]
  calc
    dist (A g x) (A b x) =
        ‖A (b * a⁻¹) (A ((a * b⁻¹) * g) x - A a x)‖ := by
      rw [map_sub, hfirst, hsecond, dist_eq_norm]
    _ ≤ C * dist (A ((a * b⁻¹) * g) x) (A a x) := by
      rw [dist_eq_norm]
      exact (A (b * a⁻¹)).le_of_opNorm_le (hbound _) _
    _ ≤ C * (r + r) := mul_le_mul_of_nonneg_left hd hC.le
    _ < ε := by
      have hEq : C * (r + r) = ε / 2 := by
        dsimp only [r]
        field_simp
        ring
      rw [hEq]
      linarith

private theorem countable_submonoid_of_countable {M : Type*} [Monoid M] {s : Set M}
    (hs : s.Countable) : (Submonoid.closure s : Set M).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := FreeMonoid.toListEquiv.injective.countable
  rw [Submonoid.closure_eq_mrange]
  exact countable_range _

/-- A weakly continuous action of a compact semitopological group by bounded
operators on a Banach space has norm-compact orbits. The representation need
only be multiplicative. Its identity operator may be a projection. -/
theorem isCompact_normOrbit_of_wot [CompleteSpace E]
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) (x : E) :
    IsCompact (range fun a ↦ A a x) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot (fun a ↦ A a) hA
  apply IsSeqCompact.isCompact
  intro u hu
  choose g hg using hu
  let M : Submonoid G := Submonoid.closure (range g)
  obtain ⟨H, hH⟩ := exists_subgroup_topologicalClosure M
  have hMc : (M : Set G).Countable := countable_submonoid_of_countable (countable_range g)
  let D := (fun a : G ↦ A a x) '' (M : Set G)
  let V : Set E := Submodule.span ℝ D
  have hV : Convex ℝ V := (Submodule.span ℝ D).convex
  have hWeakClosed := isClosed_image_convex_toWeakSpace (𝕜 := 𝕜) isClosed_closure hV.closure
  have hWeakSub : (M : Set G) ⊆
      (fun a : G ↦ toWeakSpace 𝕜 E (A a x)) ⁻¹' (toWeakSpace 𝕜 E '' closure V) :=
    fun a ha ↦ ⟨A a x, subset_closure (Submodule.subset_span ⟨a, ha, rfl⟩), rfl⟩
  have hHclosed : IsClosed (H : Set G) := hH ▸ isClosed_closure
  let : CompactSpace H := isCompact_iff_compactSpace.1 hHclosed.isCompact
  let : SeparatelyContinuousMul H := IsInducing.separatelyContinuousMul H.subtype (by
    rw [H.coe_subtype]
    exact IsInducing.subtypeVal)
  have hclosure := closure_minimal hWeakSub (hWeakClosed.preimage (continuous_weak_eval A hA x))
  have hOrbitSub : range (fun a : H ↦ A a.1 x) ⊆ closure V := by
    rintro _ ⟨a, rfl⟩
    have ha : a.1 ∈ closure (M : Set G) := by
      change a.1 ∈ (M.topologicalClosure : Set G)
      rw [← hH]
      exact a.2
    obtain ⟨z, hz, he⟩ := hclosure ha
    change A a.1 x ∈ closure V
    rwa [← (toWeakSpace 𝕜 E).injective he]
  have hsep : TopologicalSpace.IsSeparable (range fun a : H ↦ A a.1 x) :=
    ((hMc.image _).isSeparable.span.closure).mono hOrbitSub
  have hcont := continuous_orbit_of_separable (A.comp H.subtype.toMulHom)
    (hA.comp continuous_subtype_val) hC (fun a ↦ hbound a) x hsep
  have hseq := (isCompact_range hcont).isSeqCompact
  have huH (n : ℕ) : u n ∈ range (fun a : H ↦ A a.1 x) := by
    have hn : g n ∈ H := by
      change g n ∈ (H : Set G)
      rw [hH]
      exact M.le_topologicalClosure (Submonoid.subset_closure (mem_range_self n))
    exact ⟨⟨g n, hn⟩, hg n⟩
  obtain ⟨y, ⟨a, rfl⟩, φ, hφ, huφ⟩ := hseq huH
  exact ⟨A a.1 x, mem_range_self a.1, φ, hφ, huφ⟩

end CompactGroup

end Mixing.JdLGBridge
end

/- Source module Mixing.SupportingJdLG.ReversibleAction. -/
section
/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/


/-! # Reversible orbits and the group ideal of a weak operator closure -/


open Filter Set Topology

namespace Mixing.JdLGBridge

section GroupIdeal

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {π : S →ₙ* (E →L[𝕜] E)} (K : GroupIdeal (weakOperatorClosure π))

/-- The group ideal acts by its ambient norm-continuous linear operators. -/
noncomputable def GroupIdeal.operatorAction : K.carrier →ₙ* (E →L[𝕜] E) :=
  (closureAction π).comp ⟨Subtype.val, fun _ _ ↦ rfl⟩

theorem GroupIdeal.continuous_wot_operatorAction :
    Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (K.operatorAction a) :=
  continuous_subtype_val.comp continuous_subtype_val

theorem GroupIdeal.isCompact_normOrbit [CompleteSpace E] (hK : IsCompact K.carrier)
    (x : E) : IsCompact (Set.range fun a ↦ K.operatorAction a x) := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : SeparatelyContinuousMul K.carrier := IsInducing.separatelyContinuousMul
    (⟨Subtype.val, fun _ _ ↦ rfl⟩ : K.carrier →ₙ* weakOperatorClosure π)
    (IsInducing.subtypeVal (t := K.carrier))
  exact isCompact_normOrbit_of_wot K.operatorAction K.continuous_wot_operatorAction x

/-- Every reversible vector has norm-precompact orbit. This proves the
forward implication in Theorem 3.1 without a separability hypothesis. -/
theorem precompactOrbit_of_reversible [CompleteSpace E] (hπ : IsJdLGAdmissible π) (x : E)
    (hx : IsReversible (closureAction π) x) : HasPrecompactOrbit π x := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  have hx' := (K.reversible_iff_fixed (closureAction π) x).1 hx
  have hsub : range (fun s ↦ π s x) ⊆ range (fun a ↦ K.operatorAction a x) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨K.groupRetraction (closureInclusion π s), ?_⟩
    change closureAction π (K.identity * closureInclusion π s) x = π s x
    rw [K.identity_mul_eq_mul_identity, map_mul]
    change closureAction π (closureInclusion π s) (K.projection (closureAction π) x) = π s x
    rw [hx']
    rfl
  have hcompact := K.isCompact_normOrbit hK x
  exact hcompact.of_isClosed_subset isClosed_closure (closure_minimal hsub hcompact.isClosed)

/-- The norm-precompact-orbit characterization under the separation hypothesis of
Theorem 3.1. -/
theorem reversible_iff_precompactOrbit_of_separated [CompleteSpace E]
    (hπ : IsJdLGAdmissible π)
    (hseparated : ∀ y : E, y ≠ 0 → HasPrecompactOrbit π y →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : S, δ ≤ ‖π s y‖) (x : E) :
    IsReversible (closureAction π) x ↔ HasPrecompactOrbit π x :=
  ⟨precompactOrbit_of_reversible hπ x, reversible_of_precompactOrbit_of_separated hπ hseparated x⟩

end GroupIdeal

section Representations

variable {G 𝕜 E : Type*} [Group G] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- Corollary 3.2. A unital group representation satisfies the norm-separation
hypothesis, since each operator has its represented inverse in the same
uniformly bounded family. -/
theorem group_reversible_iff_precompactOrbit (π : G →* (E →L[𝕜] E))
    (hπ : IsJdLGAdmissible π.toMulHom) (x : E) :
    IsReversible (closureAction π.toMulHom) x ↔ HasPrecompactOrbit π.toMulHom x := by
  apply reversible_iff_precompactOrbit_of_separated hπ
  let : CompactSpace (weakOperatorClosure π.toMulHom) := isCompact_iff_compactSpace.1 hπ.1
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot
    (fun a ↦ closureAction π.toMulHom a) continuous_subtype_val
  intro y hy _
  refine ⟨‖y‖ / C, div_pos (norm_pos_iff.2 hy) hC, ?_⟩
  intro g
  apply (div_le_iff₀ hC).2
  have hB : ‖π g⁻¹‖ ≤ C := hbound (closureInclusion π.toMulHom g⁻¹)
  have hnorm : ‖π g⁻¹ (π g y)‖ ≤ C * ‖π g y‖ := (π g⁻¹).le_of_opNorm_le hB _
  have hinv : π g⁻¹ (π g y) = y := by
    change (π g⁻¹ * π g) y = y
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hinv, mul_comm] at hnorm
  exact hnorm

end Representations

end Mixing.JdLGBridge
end

/- Source module SixProblems.OrthogonalDecomposition. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Mixing.JdLGBridge Set
open scoped InnerProductSpace

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Group G]

theorem contractive_projection_orthogonal (P : E →L[ℝ] E) (hC : ∀ x, ‖P x‖ ≤ ‖x‖)
    {u v : E} (hu : P u = u) (hv : P v = 0) : ⟪u,v⟫_ℝ = 0 := by
  have hpoly (t : ℝ) : ‖v‖^2 * (t*t) + (2*⟪u,v⟫_ℝ) * t + 0 ≥ 0 := by
    have h := hC (u+t • v)
    rw [map_add, map_smul, hu, hv, smul_zero, add_zero] at h
    have h' := pow_le_pow_left₀ (norm_nonneg u) h 2
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h'
    linarith only [h', show ‖v‖^2 * (t*t) + (2*⟪u,v⟫_ℝ)*t + 0 =
      2 * (t * ⟪u,v⟫_ℝ) + t ^ 2 * ‖v‖ ^ 2 by ring]
  have hh := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hh
  nlinarith [sq_nonneg (2 * ⟪u,v⟫_ℝ)]

theorem contractive_projection_symmetric (P : E →L[ℝ] E) (hC : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hId : ∀ x, P (P x) = P x) : P.IsSymmetric := by
  intro x y
  have h (u v : E) : ⟪P u,v - P v⟫_ℝ = 0 :=
    contractive_projection_orthogonal P hC (hId u) (by rw [map_sub, hId, sub_self])
  change ⟪P x,y⟫_ℝ = ⟪x,P y⟫_ℝ
  have hx := h x y
  have hy := h y x
  rw [inner_sub_right] at hx hy
  rw [real_inner_comm x (P y), real_inner_comm (P x) (P y)] at hy
  linarith

/-- The norm of an orthogonal projection attains the norm of a vector exactly
when the projection fixes the vector. -/
theorem contractive_projection_fixes_of_norm_eq (P : E →L[ℝ] E)
    (hC : ∀ x, ‖P x‖ ≤ ‖x‖) (hId : ∀ x, P (P x) = P x)
    {x : E} (h : ‖P x‖ = ‖x‖) : P x = x := by
  have ho : ⟪P x,x - P x⟫_ℝ = 0 :=
    contractive_projection_orthogonal P hC (hId x) (by rw [map_sub, hId, sub_self])
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
  rw [show P x + (x - P x) = x by abel, h] at he
  have hn : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

/-- The continuous linear representation underlying an orthogonal action. -/
def orthogonalActionCLM (U : G →* (E ≃ₗᵢ[ℝ] E)) : G →* (E →L[ℝ] E) where
  toFun g := (U g).toLinearIsometry.toContinuousLinearMap
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul]

variable [CompleteSpace E]

theorem orthogonalAction_isCompact_closure (U : G →* (E ≃ₗᵢ[ℝ] E)) :
    IsCompact (weakOperatorClosure (orthogonalActionCLM U).toMulHom : Set (E →WOT[ℝ] E)) := by
  apply (isCompact_wot_contractions (E := E)).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro _ ⟨g,rfl⟩
    exact (U g).toLinearIsometry.norm_toContinuousLinearMap_le
  · exact (isCompact_wot_contractions (E := E)).isClosed

theorem orthogonalAction_closure_contractive (U : G →* (E ≃ₗᵢ[ℝ] E))
    (a : weakOperatorClosure (orthogonalActionCLM U).toMulHom) (x : E) :
    ‖closureAction (orthogonalActionCLM U).toMulHom a x‖ ≤ ‖x‖ := by
  have hs : (weakOperatorClosure (orthogonalActionCLM U).toMulHom : Set (E →WOT[ℝ] E)) ⊆
      {A | ‖A.toCLM‖ ≤ 1} := closure_minimal (by
    rintro _ ⟨g,rfl⟩
    exact (U g).toLinearIsometry.norm_toContinuousLinearMap_le) isCompact_wot_contractions.isClosed
  change ‖a.val.toCLM x‖ ≤ ‖x‖
  simpa only [one_mul] using a.val.toCLM.le_of_opNorm_le (hs a.property) x

/-- WOT closure of an orthogonal representation has a compact group ideal.
The identity of a minimal left ideal is a contractive projection. Minimality
forces its range to be invariant, so the projection commutes with the closure. -/
theorem orthogonalAction_exists_groupIdeal (U : G →* (E ≃ₗᵢ[ℝ] E)) :
    ∃ K : GroupIdeal (weakOperatorClosure (orthogonalActionCLM U).toMulHom), IsCompact K.carrier := by
  let π := (orthogonalActionCLM U).toMulHom
  let W := weakOperatorClosure π
  let : CompactSpace W := isCompact_iff_compactSpace.mp (orthogonalAction_isCompact_closure U)
  let : Nonempty W := ⟨closureInclusion π (1 : G)⟩
  obtain ⟨L,hLc,hL⟩ := exists_compact_minimalLeftIdeal (S := W) continuous_mul_const
  obtain ⟨e,he,hee⟩ := exists_idempotent_in_compact_subsemigroup continuous_mul_const
    L hL.1 hLc (fun a _ _ hb ↦ hL.2.1 a hb)
  let P := closureAction π e
  have hId (x : E) : P (P x) = P x := by
    change (closureAction π e * closureAction π e) x = _
    rw [← map_mul, hee]
  have hC : ∀ x, ‖P x‖ ≤ ‖x‖ := orthogonalAction_closure_contractive U e
  have hS (x y : E) : ⟪P x,y⟫_ℝ = ⟪x,P y⟫_ℝ :=
    contractive_projection_symmetric P hC hId x y
  have hInvariant (g : G) (x : E) : P (U g (P x)) = U g (P x) := by
    let a := e * closureInclusion π g * e
    have ha : a ∈ L := hL.2.1 _ he
    obtain ⟨b,hb⟩ : e ∈ range (· * a) := (principal_eq_of_minimalLeftIdeal hL ha).symm ▸ he
    change b * (e * closureInclusion π g * e) = e at hb
    have hbe : closureAction π b (P (U g (P x))) = P x := by
      change (closureAction π b * (closureAction π e * closureAction π (closureInclusion π g) *
        closureAction π e)) x = _
      rw [← map_mul, ← map_mul, ← map_mul, hb]
    apply contractive_projection_fixes_of_norm_eq P hC hId
    apply le_antisymm (hC _)
    calc
      ‖U g (P x)‖ = ‖P x‖ := (U g).norm_map _
      _ = ‖closureAction π b (P (U g (P x)))‖ := congrArg norm hbe.symm
      _ ≤ _ := orthogonalAction_closure_contractive U b _
  have hcomm (g : G) (x : E) : P (U g x) = U g (P x) := by
    have hU (u v : E) : ⟪u,U g v⟫_ℝ = ⟪U g⁻¹ u,v⟫_ℝ := by
      rw [← (U g).inner_map_map (U g⁻¹ u) v]
      change _ = ⟪(U g * U g⁻¹) u,U g v⟫_ℝ
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have hz : P (U g (x - P x)) = 0 := by
      apply ext_inner_left ℝ
      intro y
      rw [inner_zero_right, ← hS, hU]
      exact contractive_projection_orthogonal P hC (hInvariant g⁻¹ y)
        (by rw [map_sub, hId, sub_self])
    rwa [map_sub, map_sub, hInvariant, sub_eq_zero] at hz
  have hcentral (a : W) : e * a = a * e := by
    refine (denseRange_closureInclusion π).induction_on a
      (isClosed_eq (continuous_const_mul e) (continuous_mul_const e)) ?_
    intro g
    apply Subtype.ext
    apply ContinuousLinearMapWOT.toCLM_injective
    apply ContinuousLinearMap.ext
    exact hcomm g
  have hLprincipal : range (· * e) = L := principal_eq_of_minimalLeftIdeal hL he
  have hright {a : W} (ha : a ∈ L) (b : W) : a*b ∈ L := by
    obtain ⟨c,rfl⟩ : a ∈ range (· * e) := hLprincipal.symm ▸ ha
    rw [mul_assoc, hcentral b, ← mul_assoc]
    exact hL.2.1 _ he
  have hOneRight {a : W} (ha : a ∈ L) : a*e = a := by
    obtain ⟨b,rfl⟩ : a ∈ range (· * e) := hLprincipal.symm ▸ ha
    rw [mul_assoc, hee]
  refine ⟨⟨L,e,he,hL.2.1,hright,fun {a} ha ↦ (hcentral a).trans (hOneRight ha),
    hOneRight,?_⟩,hLc⟩
  intro a ha
  obtain ⟨b,hb⟩ : e ∈ range (· * a) := (principal_eq_of_minimalLeftIdeal hL ha).symm ▸ he
  change b*a = e at hb
  let c := b*e
  have hc : c ∈ L := hL.2.1 _ he
  have hca : c*a = e := by
    dsimp [c]
    rw [mul_assoc, hcentral a, hOneRight ha, hb]
  obtain ⟨d,hd⟩ : e ∈ range (· * c) := (principal_eq_of_minimalLeftIdeal hL hc).symm ▸ he
  change d*c = e at hd
  have hda : d*e = a := by
    calc
      d*e = d*(c*a) := by rw [hca]
      _ = e*a := by rw [← mul_assoc, hd]
      _ = a := (hcentral a).trans (hOneRight ha)
  refine ⟨c,hc,hca,?_⟩
  rw [← hda, mul_assoc, hcentral c, hOneRight hc, hd]

end SixProblems
end

/- Source module SixProblems.RealCompactAverage. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section
namespace SixProblems.RealRepresentation

open Filter MeasureTheory MeasureTheory.Measure InnerProductSpace Set
open scoped InnerProductSpace

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The average of the rank-one operators built from the orbit of a vector
in a strongly continuous unitary representation of a compact group. -/
def compactRepresentationAverage (μ : Measure K) (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H) :
    H →L[ℝ] H :=
  ∫ k, rankOne ℝ (ρ k x) (ρ k x) ∂μ

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [CompleteSpace H] in
private theorem continuous_rankOne_orbit (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (hρ : Continuous fun k ↦ ρ k x) : Continuous (fun k ↦ rankOne ℝ (ρ k x) (ρ k x)) := by
  exact ((ContinuousLinearMap.smulRightL ℝ H H).continuous.comp
    ((innerSL ℝ).continuous.comp hρ)).clm_apply hρ

omit [IsTopologicalGroup K] [CompleteSpace H] in
private theorem integrable_rankOne_orbit (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    Integrable (fun k ↦ rankOne ℝ (ρ k x) (ρ k x)) μ :=
  (continuous_rankOne_orbit ρ x hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [CompleteSpace H] in
private theorem compact_rankOne_self (x : H) : IsCompactOperator (rankOne ℝ x x) := by
  let a := (1 : ℝ →L[ℝ] ℝ).smulRight x
  have hc : IsCompactOperator a := isCompactOperator_of_locallyCompactSpace_rng a
  have he : rankOne ℝ x x = a.comp (innerSL ℝ x) := by
    ext y
    simp [a]
  rw [he]
  exact hc.comp_clm (innerSL ℝ x)

omit [IsTopologicalGroup K] in
theorem isCompactOperator_compactRepresentationAverage (μ : Measure K) [IsProbabilityMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    IsCompactOperator (compactRepresentationAverage μ ρ x) := by
  let C := (compactOperator (RingHom.id ℝ) H H).restrictScalars ℝ
  have hC : IsClosed (C : Set (H →L[ℝ] H)) := isClosed_setOfPred_isCompactOperator
  exact C.convex.integral_mem hC (ae_of_all _ fun k ↦ compact_rankOne_self (ρ k x))
    (integrable_rankOne_orbit μ ρ x hρ)

omit [IsTopologicalGroup K] in
theorem compactRepresentationAverage_apply (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) (y : H) :
    compactRepresentationAverage μ ρ x y = ∫ k, rankOne ℝ (ρ k x) (ρ k x) y ∂μ := by
  exact ((ContinuousLinearMap.apply ℝ H y).integral_comp_comm
    (integrable_rankOne_orbit μ ρ x hρ)).symm

omit [IsTopologicalGroup K] in
theorem inner_compactRepresentationAverage (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) (y z : H) :
    ⟪y, compactRepresentationAverage μ ρ x z⟫_ℝ =
      ∫ k, ⟪y, rankOne ℝ (ρ k x) (ρ k x) z⟫_ℝ ∂μ := by
  have hi := (ContinuousLinearMap.apply ℝ H z).integrable_comp
    (integrable_rankOne_orbit μ ρ x hρ)
  rw [compactRepresentationAverage_apply μ ρ x hρ]
  exact ((innerSL ℝ y).integral_comp_comm hi).symm

omit [IsTopologicalGroup K] in
theorem isSymmetric_compactRepresentationAverage (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    (compactRepresentationAverage μ ρ x).IsSymmetric := by
  intro y z
  change ⟪compactRepresentationAverage μ ρ x y, z⟫_ℝ =
    ⟪y, compactRepresentationAverage μ ρ x z⟫_ℝ
  rw [real_inner_comm z (compactRepresentationAverage μ ρ x y),
    inner_compactRepresentationAverage μ ρ x hρ, inner_compactRepresentationAverage μ ρ x hρ]
  apply integral_congr_ae
  exact ae_of_all _ fun k ↦
    (real_inner_comm (rankOne ℝ (ρ k x) (ρ k x) y) z).trans
      (isSymmetric_rankOne_self (ρ k x) y z)

/-- The compact average commutes with the entire representation. -/
theorem compactRepresentationAverage_commutes (μ : Measure K) [IsFiniteMeasure μ]
    [IsMulLeftInvariant μ] (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (x : H)
    (hρ : Continuous fun k ↦ ρ k x) (a : K) (y : H) :
    ρ a (compactRepresentationAverage μ ρ x y) =
      compactRepresentationAverage μ ρ x (ρ a y) := by
  let v (k : K) := rankOne ℝ (ρ k x) (ρ k x) y
  let w (k : K) := rankOne ℝ (ρ k x) (ρ k x) (ρ a y)
  have hi := (ContinuousLinearMap.apply ℝ H y).integrable_comp (integrable_rankOne_orbit μ ρ x hρ)
  have hw := (ContinuousLinearMap.apply ℝ H (ρ a y)).integrable_comp
    (integrable_rankOne_orbit μ ρ x hρ)
  have he (k : K) : ρ a (v k) = w (a*k) := by
    simp only [v, w, rankOne_apply, map_mul]
    change ρ a (⟪ρ k x,y⟫_ℝ • ρ k x) =
      ⟪ρ a (ρ k x),ρ a y⟫_ℝ • ρ a (ρ k x)
    rw [map_smul, LinearIsometryEquiv.inner_map_map]
  rw [compactRepresentationAverage_apply μ ρ x hρ, compactRepresentationAverage_apply μ ρ x hρ]
  change ρ a (∫ k, v k ∂μ) = ∫ k, w k ∂μ
  calc
    _ = ∫ k, ρ a (v k) ∂μ :=
      ((ρ a).toLinearIsometry.toContinuousLinearMap.integral_comp_comm hi).symm
    _ = ∫ k, w (a*k) ∂μ := integral_congr_ae (ae_of_all _ he)
    _ = _ := by
      have ht := measurePreserving_mul_left μ a
      have hW : AEStronglyMeasurable w (μ.map (fun k ↦ a*k)) := by
        change AEStronglyMeasurable w (μ.map (a * ·))
        rw [ht.map_eq]
        exact hw.aestronglyMeasurable
      have he' := integral_map ht.aemeasurable hW
      rw [ht.map_eq] at he'
      exact he'.symm

omit [IsTopologicalGroup K] in
theorem compactRepresentationAverage_ne_zero (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (ρ : K →* (H ≃ₗᵢ[ℝ] H)) {x : H}
    (hx : x ≠ 0) (hρ : Continuous fun k ↦ ρ k x) :
    compactRepresentationAverage μ ρ x ≠ 0 := by
  let v (k : K) := ‖⟪ρ k x,x⟫_ℝ‖ ^ 2
  have hc : Continuous v := (hρ.inner continuous_const).norm.pow _
  have he : v 1 ≠ 0 := by
    have hOne : ρ 1 x = x := by rw [map_one]; rfl
    change ‖⟪ρ 1 x,x⟫_ℝ‖ ^ 2 ≠ 0
    rw [hOne]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (fun h ↦ hx (inner_self_eq_zero.mp h)))
  have hp : 0 < ∫ k, v k ∂μ :=
    hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (HasCompactSupport.of_compactSpace _)
      (fun _ ↦ sq_nonneg _) he
  have hReal : ⟪x, compactRepresentationAverage μ ρ x x⟫_ℝ = ∫ k, v k ∂μ := by
    rw [inner_compactRepresentationAverage μ ρ x hρ]
    apply integral_congr_ae
    refine ae_of_all _ fun k ↦ ?_
    change ⟪x, rankOne ℝ (ρ k x) (ρ k x) x⟫_ℝ = v k
    rw [rankOne_apply, real_inner_smul_right, real_inner_comm (ρ k x) x]
    simp [v, sq]
  intro hz
  rw [hz, zero_apply, inner_zero_right] at hReal
  exact hp.ne' hReal.symm

end SixProblems.RealRepresentation
end

/- Source module SixProblems.RealCompactDensity. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems.RealRepresentation

open MeasureTheory MeasureTheory.Measure InnerProductSpace Module.End Set

section Invariant

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (U : G →* (H ≃ₗᵢ[ℝ] H))

def IsInvariantSubmodule (K : Submodule ℝ H) : Prop :=
  ∀ g : G, ∀ x ∈ K, U g x ∈ K

theorem IsInvariantSubmodule.sup {U : G →* (H ≃ₗᵢ[ℝ] H)} {K L : Submodule ℝ H}
    (hK : IsInvariantSubmodule U K) (hL : IsInvariantSubmodule U L) :
    IsInvariantSubmodule U (K ⊔ L) := by
  intro g x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨U g a, hK g a ha, U g b, hL g b hb, rfl⟩

theorem IsInvariantSubmodule.closure {U : G →* (H ≃ₗᵢ[ℝ] H)} {K : Submodule ℝ H}
    (hK : IsInvariantSubmodule U K) : IsInvariantSubmodule U K.topologicalClosure := by
  intro g x hx
  have hImage : U g '' (K : Set H) ⊆ K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hK g a ha
  exact closure_mono hImage (image_closure_subset_closure_image (U g).continuous ⟨x, hx, rfl⟩)

theorem IsInvariantSubmodule.orthogonal {U : G →* (H ≃ₗᵢ[ℝ] H)} {K : Submodule ℝ H}
    (hK : IsInvariantSubmodule U K) : IsInvariantSubmodule U Kᗮ := by
  intro g x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hg : U g (U g⁻¹ y) = y := by
    change (U g * U g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    ⟪y, U g x⟫_ℝ = ⟪U g (U g⁻¹ y), U g x⟫_ℝ := by rw [hg]
    _ = ⟪U g⁻¹ y, x⟫_ℝ := (U g).inner_map_map _ _
    _ = 0 := hx _ (hK g⁻¹ y hy)

/-- Restriction of a unitary group action to an invariant subspace. -/
noncomputable def unitarySubmoduleAction (W : Submodule ℝ H)
    (hW : ∀ g x, x ∈ W → U g x ∈ W) : G →* (W ≃ₗᵢ[ℝ] W) where
  toFun g :=
    { toLinearEquiv :=
        { (U g).toLinearMap.restrict (hW g) with
          invFun := fun x => ⟨U g⁻¹ x, hW g⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (show (U g⁻¹ * U g) x = x by
            rw [← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun x => Subtype.ext (show (U g * U g⁻¹) x = x by
            rw [← map_mul, mul_inv_cancel, map_one]; rfl) }
      norm_map' := fun x => (U g).norm_map x }
  map_one' := by
    ext x
    change U 1 x = (x : H)
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change U (g * h) x = U g (U h x)
    rw [map_mul]
    rfl


end Invariant

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A nonzero strongly continuous unitary representation of a compact group
has a nonzero finite-dimensional invariant subspace. -/
theorem exists_finiteDimensional_invariantSubmodule_of_compact [Nontrivial H]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    ∃ W : Submodule ℝ H, W ≠ ⊥ ∧ FiniteDimensional ℝ W ∧ IsInvariantSubmodule ρ W := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let A := compactRepresentationAverage m ρ v
  have hA := isCompactOperator_compactRepresentationAverage m ρ v (hρ v)
  have hSym := isSymmetric_compactRepresentationAverage m ρ v (hρ v)
  have hne := compactRepresentationAverage_ne_zero m ρ hv (hρ v)
  have he : ¬ ∀ z, HasEigenvalue A.toLinearMap z → z = 0 :=
    fun h ↦ hne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hA hSym).mp h)
  push Not at he
  obtain ⟨z, hz, hzero⟩ := he
  let W := eigenspace A.toLinearMap z
  refine ⟨W, hasEigenvalue_iff.mp hz,
    ContinuousLinearMap.finite_dimensional_eigenspace hA z hzero, fun k w hw ↦ ?_⟩
  have hw' := mem_eigenspace_iff.mp hw
  apply mem_eigenspace_iff.mpr
  change A (ρ k w) = z • ρ k w
  rw [← compactRepresentationAverage_commutes m ρ v (hρ v), show A w = z • w from hw', map_smul]

/-- Finite-dimensional invariant subspaces have dense linear span in a
strongly continuous unitary representation of a compact group. -/
theorem eq_top_of_contains_finiteInvariantSubmodules
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (P : Submodule ℝ H) (hP : IsClosed (P : Set H))
    (h : ∀ (V : Submodule ℝ H), FiniteDimensional ℝ V → IsInvariantSubmodule ρ V → V ≤ P) :
    P = ⊤ := by
  let A : Set H := {x | ∃ V : Submodule ℝ H, FiniteDimensional ℝ V ∧ IsInvariantSubmodule ρ V ∧ x ∈ V}
  let Q := (Submodule.span ℝ A).topologicalClosure
  have hQP : Q ≤ P := Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro x ⟨V,hfin,hV,hx⟩; exact h V hfin hV hx)) hP
  have hQA (x : H) (hx : x ∈ A) : x ∈ Q :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hx)
  have hQinv : IsInvariantSubmodule ρ Q := by
    apply IsInvariantSubmodule.closure
    intro g x hmem
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨V,hfin,hV,hxV⟩ := hx
      exact Submodule.subset_span ⟨V,hfin,hV,hV g x hxV⟩
    | zero => simp
    | add x y _ _ hx hy => exact map_add (ρ g) x y ▸ Submodule.add_mem _ hx hy
    | smul c x _ hx => exact map_smul (ρ g) c x ▸ Submodule.smul_mem _ c hx
  have hQ : Q = ⊤ := by
    let : CompleteSpace Q := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let D := Qᗮ
    apply Submodule.orthogonal_eq_bot_iff.mp
    by_contra hD
    let : Nontrivial D := Submodule.nontrivial_iff_ne_bot.mpr hD
    let V := unitarySubmoduleAction ρ D hQinv.orthogonal
    have hV (x : D) : Continuous (fun k ↦ V k x) := (hρ x).subtype_mk _
    obtain ⟨W,hWne,hWfin,hWinv⟩ := exists_finiteDimensional_invariantSubmodule_of_compact m V hV
    obtain ⟨x,hx,hxne⟩ : ∃ x ∈ W, x ≠ 0 := by
      by_contra! he
      exact hWne ((Submodule.eq_bot_iff W).mpr he)
    let W' := W.map D.subtype
    have hWinv' : IsInvariantSubmodule ρ W' := by
      rintro k _ ⟨y,hy,rfl⟩
      exact ⟨V k y, hWinv k y hy, rfl⟩
    let : FiniteDimensional ℝ W := hWfin
    have he : (D.subtype.comp W.subtype).range = W' := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hWfin' : FiniteDimensional ℝ W' := he ▸ inferInstanceAs
      (FiniteDimensional ℝ (D.subtype.comp W.subtype).range)
    have hxQ : (x : H) ∈ Q := hQA x ⟨W',hWfin',hWinv',⟨x,hx,rfl⟩⟩
    exact hxne (Subtype.ext (inner_self_eq_zero.mp (x.property _ hxQ)))
  exact top_unique (hQ ▸ hQP)

/-- A vector in a compact representation can be approximated in norm by a
vector belonging to a single finite-dimensional invariant subspace. -/
theorem exists_finiteInvariant_approximation
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℝ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (x : H) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Submodule ℝ H, FiniteDimensional ℝ V ∧ IsInvariantSubmodule ρ V ∧
      ∃ y : V, ‖x - (y : H)‖ < ε := by
  let P : Submodule ℝ H := {
    carrier := {x | ∃ V : Submodule ℝ H, FiniteDimensional ℝ V ∧ IsInvariantSubmodule ρ V ∧ x ∈ V}
    zero_mem' := ⟨⊥,inferInstance,by simp [IsInvariantSubmodule],Submodule.zero_mem _⟩
    add_mem' := by
      rintro x y ⟨V,hV,hVI,hx⟩ ⟨W,hW,hWI,hy⟩
      let := hV
      let := hW
      exact ⟨V ⊔ W,inferInstance,hVI.sup hWI,Submodule.mem_sup.mpr ⟨x,hx,y,hy,rfl⟩⟩
    smul_mem' := by
      rintro c x ⟨V,hV,hVI,hx⟩
      exact ⟨V,hV,hVI,V.smul_mem c hx⟩ }
  have hP := eq_top_of_contains_finiteInvariantSubmodules m ρ hρ P.topologicalClosure
    (Submodule.isClosed_topologicalClosure _) (fun V hfin hVI y hy ↦
      Submodule.le_topologicalClosure _ ⟨V,hfin,hVI,hy⟩)
  have hx : x ∈ closure (P : Set H) := (congrArg (fun Q : Submodule ℝ H ↦ x ∈ Q) hP).mpr trivial
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨V,hfin,hVI,hyV⟩ := hy
  exact ⟨V,hfin,hVI,⟨y,hyV⟩,by simpa only [dist_eq_norm] using hxy⟩

end SixProblems.RealRepresentation
end

/- Source module Mixing.SupportingJdLG.ReversibleTopology. -/
section
/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/


/-! # Group operations on the compact operator ideal -/


open Filter Set Topology

namespace Mixing.JdLGBridge

section Orbits

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [SeparatelyContinuousMul G] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- Weak and norm convergence agree on the compact norm orbit. -/
theorem continuous_normOrbit_of_wot (A : G →ₙ* (E →L[𝕜] E))
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) (x : E) :
    Continuous fun a ↦ A a x := by
  let orbit := range fun a ↦ A a x
  have hO : IsCompact orbit := isCompact_normOrbit_of_wot A hA x
  have hweak : Continuous fun a ↦ toWeakSpace 𝕜 E (A a x) :=
    WeakBilin.continuous_of_continuous_eval _ fun f ↦
      (ContinuousLinearMapWOT.continuous_dual_apply x f).comp hA
  apply continuous_iff_isClosed.2
  intro F hF
  have hc : IsClosed (toWeakSpace 𝕜 E '' (F ∩ orbit)) :=
    ((hO.inter_left hF).image (toWeakSpaceCLM 𝕜 E).continuous).isClosed
  convert hc.preimage hweak using 1
  ext a
  simp only [mem_preimage, mem_image, mem_inter_iff]
  exact ⟨fun h ↦ ⟨A a x, ⟨h, mem_range_self a⟩, rfl⟩,
    fun ⟨y, hy, hya⟩ ↦ (toWeakSpace 𝕜 E).injective hya ▸ hy.1⟩

end Orbits

section Evaluation

variable {X 𝕜 E : Type*} [TopologicalSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Uniformly bounded operators with continuous pointwise evaluation also
have continuous joint evaluation. -/
theorem continuous_apply_of_operatorBound (A : X → E →L[𝕜] E) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ a, ‖A a‖ ≤ C) (hnorm : ∀ x, Continuous fun a ↦ A a x) :
    Continuous fun p : X × E ↦ A p.1 p.2 := by
  apply continuous_iff_continuousAt.2
  intro p
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hfst : ∀ᶠ q : X × E in 𝓝 p, dist (A q.1 p.2) (A p.1 p.2) < ε / 2 :=
    Metric.tendsto_nhds.1 ((hnorm p.2).comp continuous_fst).continuousAt _ (by positivity)
  have hsnd : ∀ᶠ q : X × E in 𝓝 p, dist q.2 p.2 < ε / (2 * C) :=
    Metric.tendsto_nhds.1 continuous_snd.continuousAt _ (by positivity)
  filter_upwards [hfst, hsnd] with q hq₁ hq₂
  have hdist : dist (A q.1 q.2) (A q.1 p.2) ≤ C * dist q.2 p.2 := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (A q.1).le_of_opNorm_le (hbound q.1) _
  calc
    dist (A q.1 q.2) (A p.1 p.2) ≤
        dist (A q.1 q.2) (A q.1 p.2) + dist (A q.1 p.2) (A p.1 p.2) :=
      dist_triangle _ _ _
    _ ≤ C * dist q.2 p.2 + dist (A q.1 p.2) (A p.1 p.2) := add_le_add_left hdist _
    _ < C * (ε / (2 * C)) + ε / 2 := add_lt_add (mul_lt_mul_of_pos_left hq₂ hC) hq₁
    _ = ε := by field_simp; ring

end Evaluation

section Inverse

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]

/-- Inversion is continuous in a compact Hausdorff group whose multiplication
is jointly continuous. Its graph projects bijectively onto the first factor. -/
theorem continuous_inv_of_compact_mul (hmul : Continuous fun p : G × G ↦ p.1 * p.2) :
    Continuous (fun a : G ↦ a⁻¹) := by
  let graph : Set (G × G) := {p | p.1 * p.2 = 1}
  have hgraph : IsClosed graph := isClosed_eq hmul continuous_const
  let : CompactSpace graph := isCompact_iff_compactSpace.1 hgraph.isCompact
  let e : graph ≃ G :=
    { toFun := fun p ↦ p.1.1
      invFun := fun a ↦ ⟨(a, a⁻¹), mul_inv_cancel a⟩
      left_inv := fun ⟨⟨a, b⟩, h⟩ ↦ by
        apply Subtype.ext
        have hb : b = a⁻¹ := by
          calc
            b = a⁻¹ * (a * b) := by simp
            _ = a⁻¹ := by rw [show a * b = 1 from h, mul_one]
        exact Prod.ext rfl hb.symm
      right_inv := fun _ ↦ rfl }
  have he : Continuous e := continuous_subtype_val.fst
  exact continuous_subtype_val.snd.comp he.continuous_symm_of_equiv_compact_to_t2

end Inverse

section OperatorGroup

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {π : S →ₙ* (E →L[𝕜] E)} (K : GroupIdeal (weakOperatorClosure π))

theorem GroupIdeal.continuous_norm_eval (hK : IsCompact K.carrier) (x : E) :
    Continuous fun a ↦ K.operatorAction a x := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : SeparatelyContinuousMul K.carrier := IsInducing.separatelyContinuousMul
    (⟨Subtype.val, fun _ _ ↦ rfl⟩ : K.carrier →ₙ* weakOperatorClosure π)
    (IsInducing.subtypeVal (t := K.carrier))
  exact continuous_normOrbit_of_wot K.operatorAction K.continuous_wot_operatorAction x

/-- The compact group ideal of a weak operator semigroup has jointly continuous
group operations. This follows from norm continuity of its orbit maps. -/
theorem GroupIdeal.isTopologicalGroup_of_isCompact (hK : IsCompact K.carrier) :
    IsTopologicalGroup K.carrier := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot
    (fun a ↦ K.operatorAction a) K.continuous_wot_operatorAction
  have hA := K.continuous_norm_eval hK
  have happly := continuous_apply_of_operatorBound (fun a ↦ K.operatorAction a) hC hbound hA
  have hind : IsInducing (fun a : K.carrier ↦ (a.1.1 : E →WOT[𝕜] E)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hm : Continuous fun p : K.carrier × K.carrier ↦ p.1 * p.2 := by
    apply hind.continuous_iff.2
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro x f
    have hc : Continuous fun p : K.carrier × K.carrier ↦
        K.operatorAction p.1 (K.operatorAction p.2 x) :=
      happly.comp (continuous_fst.prodMk ((hA x).comp continuous_snd))
    exact f.continuous.comp hc
  exact { continuous_mul := hm, continuous_inv := continuous_inv_of_compact_mul hm }

end OperatorGroup

end Mixing.JdLGBridge
end

/- Source module Mixing.SupportingJdLG.Stable. -/
section
/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/


/-!
# Haar coefficients on the almost weakly stable part

Lemma 4.1 of Barthmann, Farhangi and Kuznetsova, arXiv:2509.24003v3, uses the
compact group ideal of the weakly almost periodic compactification. This file
proves the coefficient criterion on a compact group ideal using normalized Haar
measure and continuous matrix coefficients.
-/


open MeasureTheory Set TopologicalSpace
open scoped BigOperators

namespace Mixing.JdLGBridge

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized to give the whole compact group mass one. -/
noncomputable def normalizedHaar : Measure G :=
  Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩

instance : (normalizedHaar G).IsHaarMeasure := by
  unfold normalizedHaar
  infer_instance

instance : IsProbabilityMeasure (normalizedHaar G) where
  measure_univ := by
    unfold normalizedHaar
    exact Measure.haarMeasure_self

end CompactGroup

section InvariantMeasure

variable {S G : Type*} [Semigroup S] [TopologicalSpace S] [T2Space S]
  [MeasurableSpace S] [BorelSpace S]
  [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The retraction onto the compact group ideal transports every left-invariant probability
to a full-support left-invariant probability on the group. Joint continuity of multiplication
is unnecessary for this transfer. -/
theorem exists_fullSupportProbability_groupIdeal (i : G →ₙ* S) (hi : Continuous i)
    (hinjective : Function.Injective i) (hleft : ∀ s : S, Continuous (fun t => s * t))
    (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s) (μ : Measure S)
    [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ Measure.IsMulLeftInvariant ν ∧
      ν.IsOpenPosMeasure ∧ μ = ν.map i := by
  have hembedding := (hi.isClosedEmbedding hinjective).isEmbedding
  let p : S → G := fun s => (habsorb s).choose
  have hpi (s : S) : i (p s) = i 1 * s := (habsorb s).choose_spec
  have hp : Continuous p := by
    apply hembedding.continuous_iff.mpr
    rw [show i ∘ p = fun s => i 1 * s from funext hpi]
    exact hleft (i 1)
  have hgleft (g : G) : Continuous (fun t : G => g * t) := by
    apply hembedding.continuous_iff.mpr
    change Continuous (fun t : G => i (g * t))
    simpa only [map_mul, Function.comp_def] using (hleft (i g)).comp hi
  let ν : Measure G := μ.map p
  have hνprobability : IsProbabilityMeasure ν := by
    unfold ν
    infer_instance
  have hνinvariant : Measure.IsMulLeftInvariant ν := ⟨fun g => by
    have heq : (g * ·) ∘ p = p ∘ (i g * ·) := by
      funext s
      apply hinjective
      change i (g * p s) = i (p (i g * s))
      rw [map_mul, hpi, hpi, ← mul_assoc, ← map_mul, mul_one, ← mul_assoc, ← map_mul, one_mul]
    unfold ν
    rw [Measure.map_map (hgleft g).measurable hp.measurable, heq,
      ← Measure.map_map hp.measurable (hleft (i g)).measurable,
      Measure.IsMulLeftInvariant.map_mul_left_eq_self]⟩
  have hνfullSupport : ν.IsOpenPosMeasure := by
    constructor
    intro U hU hnonempty hzero
    obtain ⟨u, hu⟩ := hnonempty
    let cover : G → Set G := fun g => (g * ·) ⁻¹' U
    have hcover : (univ : Set G) ⊆ ⋃ g, cover g := by
      intro t _
      apply mem_iUnion.mpr
      exact ⟨u * t⁻¹, by simpa [cover, mul_assoc] using hu⟩
    obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover cover
      (fun g => hU.preimage (hgleft g)) hcover
    have hnull (g : G) : ν (cover g) = 0 := by
      rw [show ν (cover g) = (ν.map (g * ·)) U from
        (Measure.map_apply (hgleft g).measurable hU.measurableSet).symm,
        hνinvariant.map_mul_left_eq_self g, hzero]
    have hle : ν univ ≤ 0 := calc
      ν univ ≤ ν (⋃ g ∈ F, cover g) := measure_mono hF
      _ ≤ ∑ g ∈ F, ν (cover g) := measure_biUnion_finset_le _ _
      _ = 0 := by simp only [hnull, Finset.sum_const_zero]
    simp [hνprobability.measure_univ] at hle
  refine ⟨ν, hνprobability, hνinvariant, hνfullSupport, ?_⟩
  unfold ν
  rw [Measure.map_map hi.measurable hp.measurable,
    show i ∘ p = (i 1 * ·) from funext hpi, Measure.IsMulLeftInvariant.map_mul_left_eq_self]

/-- If the compact ideal is a topological group, an invariant probability is the pushforward
of its normalized Haar measure. -/
theorem leftInvariantProbability_eq_groupIdealHaar [IsTopologicalGroup G]
    (i : G →ₙ* S) (hi : Continuous i) (hinjective : Function.Injective i)
    (hleft : ∀ s : S, Continuous (fun t => s * t)) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (μ : Measure S) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] :
    μ = (normalizedHaar G).map i := by
  obtain ⟨ν, hνprobability, hνinvariant, _, hμ⟩ :=
    exists_fullSupportProbability_groupIdeal i hi hinjective hleft habsorb μ
  have : ν.IsHaarMeasure :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior ν univ isCompact_univ
      (by simp) (by simp) (by simp)
  have hν : ν = normalizedHaar G := Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν _
  rwa [← hν]

end InvariantMeasure

section Annihilator

variable {S G E : Type*} [Semigroup S] [Group G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A vector killed by one semigroup element is killed by the identity of the group ideal.
The range condition is the absorption used in this implication. -/
theorem exists_annihilator_iff_group_identity (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s) (x : E) :
    (∃ s : S, ρ s x = 0) ↔ ρ (i 1) x = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨g, hg⟩ := habsorb s
    have hzero : ρ (i g) x = 0 := by
      rw [hg, map_mul]
      change ρ (i 1) (ρ s x) = 0
      rw [hs, map_zero]
    have heq : ρ (i (g⁻¹ * g)) x = ρ (i g⁻¹) (ρ (i g) x) := by
      simp only [map_mul]; rfl
    rw [inv_mul_cancel, hzero, map_zero] at heq
    exact heq
  · intro hx
    exact ⟨i 1, hx⟩

end Annihilator

section Coefficients

variable {S G E : Type*} [Semigroup S] [Group G] [TopologicalSpace G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Haar integral of a power of the norm of a scalar coefficient. -/
noncomputable def haarCoefficientMoment [IsTopologicalGroup G]
    (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (x : E) (f : StrongDual ℂ E) (p : ℝ) : ℝ :=
  ∫ g, ‖f (ρ (i g) x)‖ ^ p ∂normalizedHaar G

/-- For a weakly continuous orbit on the group ideal, the moment at any positive power for a
full-support measure vanishes exactly when the identity of the group ideal kills the vector. -/
theorem fullSupportCoefficientMoments_eq_zero_iff (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (x : E) (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun g => f (ρ (i g) x)))
    (ν : Measure G) [IsFiniteMeasure ν] [ν.IsOpenPosMeasure]
    {p : ℝ} (hp : 0 < p) :
    (∀ f : StrongDual ℂ E, (∫ g, ‖f (ρ (i g) x)‖ ^ p ∂ν) = 0) ↔ ρ (i 1) x = 0 := by
  constructor
  · intro h
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro f
    let integrand : G → ℝ := fun g => ‖f (ρ (i g) x)‖ ^ p
    have hcont : Continuous integrand := (hcontinuous f).norm.rpow_const (fun _ => Or.inr hp.le)
    have hnneg : 0 ≤ integrand := fun _ => Real.rpow_nonneg (norm_nonneg _) _
    have haezero := (integral_eq_zero_iff_of_nonneg hnneg
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp (h f)
    have heq := (hcont.ae_eq_iff_eq ν continuous_zero).mp haezero
    have hone : ‖f (ρ (i 1) x)‖ ^ p = 0 := congrFun heq 1
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hp.ne').mp hone)
  · intro h f
    have hzero (g : G) : ρ (i g) x = 0 := by
      have heq : ρ (i (g * 1)) x = ρ (i g) (ρ (i 1) x) := by simp only [map_mul]; rfl
      rw [mul_one, h, map_zero] at heq
      exact heq
    simp [hzero, Real.zero_rpow hp.ne']

/-- The equivalence specialized to normalized Haar measure on a compact topological group. -/
theorem haarCoefficientMoments_eq_zero_iff [IsTopologicalGroup G]
    (i : G →ₙ* S) (ρ : S →ₙ* (E →L[ℂ] E))
    (x : E) (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun g => f (ρ (i g) x)))
    {p : ℝ} (hp : 0 < p) :
    (∀ f : StrongDual ℂ E, haarCoefficientMoment i ρ x f p = 0) ↔ ρ (i 1) x = 0 :=
  fullSupportCoefficientMoments_eq_zero_iff i ρ x hcontinuous (normalizedHaar G) hp

/-- The three clauses of the Haar coefficient criterion, on the compact group ideal of a
semigroup of operators. In particular, vanishing for one common positive power suffices. -/
theorem almostWeaklyStable_iff_haarCoefficientMoments [IsTopologicalGroup G] (i : G →ₙ* S)
    (ρ : S →ₙ* (E →L[ℂ] E)) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (x : E) (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun g => f (ρ (i g) x))) :
    ((∃ s : S, ρ s x = 0) ↔ ∀ p : ℝ, 0 < p → ∀ f : StrongDual ℂ E,
        haarCoefficientMoment i ρ x f p = 0) ∧
      ((∃ s : S, ρ s x = 0) ↔ ∃ p : ℝ, 0 < p ∧ ∀ f : StrongDual ℂ E,
        haarCoefficientMoment i ρ x f p = 0) := by
  have hannihilator := exists_annihilator_iff_group_identity i ρ habsorb x
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hx p hp
    exact (haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous hp).2 (hannihilator.1 hx)
  · intro h
    exact hannihilator.2 ((haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous zero_lt_one).1
      (h 1 zero_lt_one))
  · intro hx
    exact ⟨1, zero_lt_one, (haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous zero_lt_one).2
      (hannihilator.1 hx)⟩
  · rintro ⟨p, hp, h⟩
    exact hannihilator.2 ((haarCoefficientMoments_eq_zero_iff i ρ x hcontinuous hp).1 h)

/-- The almost weak stability criterion for any left-invariant probability on the compact
semigroup, expressed through its scalar matrix coefficients. -/
theorem almostWeaklyStable_iff_invariantProbabilityMoments
    [TopologicalSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    (i : G →ₙ* S) (hi : Continuous i) (hinjective : Function.Injective i)
    (hleft : ∀ s : S, Continuous (fun t => s * t)) (habsorb : ∀ s : S, ∃ g : G, i g = i 1 * s)
    (ρ : S →ₙ* (E →L[ℂ] E)) (x : E)
    (hcontinuous : ∀ f : StrongDual ℂ E, Continuous (fun s => f (ρ s x)))
    (μ : Measure S) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ] :
    ((∃ s : S, ρ s x = 0) ↔ ∀ p : ℝ, 0 < p → ∀ f : StrongDual ℂ E,
        (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = 0) ∧
      ((∃ s : S, ρ s x = 0) ↔ ∃ p : ℝ, 0 < p ∧ ∀ f : StrongDual ℂ E,
        (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = 0) := by
  obtain ⟨ν, hνprobability, _, hνsupport, hμ⟩ :=
    exists_fullSupportProbability_groupIdeal i hi hinjective hleft habsorb μ
  have hmoments (p : ℝ) (hp : 0 < p) (f : StrongDual ℂ E) :
      (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = ∫ g, ‖f (ρ (i g) x)‖ ^ p ∂ν := by
    have hf : Continuous (fun s => ‖f (ρ s x)‖ ^ p) :=
      (hcontinuous f).norm.rpow_const (fun _ => Or.inr hp.le)
    rw [hμ, integral_map hi.measurable.aemeasurable hf.aestronglyMeasurable]
  have hcriterion (p : ℝ) (hp : 0 < p) :
      (∀ f : StrongDual ℂ E, (∫ s, ‖f (ρ s x)‖ ^ p ∂μ) = 0) ↔ ∃ s : S, ρ s x = 0 := by
    simp_rw [hmoments p hp]
    exact (fullSupportCoefficientMoments_eq_zero_iff i ρ x (fun f =>
      (hcontinuous f).comp hi) ν hp).trans
        (exists_annihilator_iff_group_identity i ρ habsorb x).symm
  refine ⟨⟨fun hx p hp => (hcriterion p hp).2 hx, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    exact (hcriterion 1 zero_lt_one).1 (h 1 zero_lt_one)
  · intro hx
    exact ⟨1, zero_lt_one, (hcriterion 1 zero_lt_one).2 hx⟩
  · rintro ⟨p, hp, hf⟩
    exact (hcriterion p hp).1 hf

end Coefficients

end Mixing.JdLGBridge
end

/- Source module SixProblems.CompactCoefficients. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter MeasureTheory Mixing.JdLGBridge Set RealRepresentation
open scoped InnerProductSpace Topology

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section GroupIdeal

variable (U : G →* (E ≃ₗᵢ[ℝ] E))
  (K : GroupIdeal (weakOperatorClosure (orthogonalActionCLM U).toMulHom))

local notation "π" => MonoidHom.toMulHom (orthogonalActionCLM U)
local notation "P" => K.projection (closureAction π)

theorem groupIdealOperator_mem_range (a : K.carrier) (x : E) :
    K.operatorAction a x ∈ (P).range := by
  refine ⟨K.operatorAction a x,?_⟩
  change (closureAction π K.identity * closureAction π a.val) x = closureAction π a.val x
  rw [← map_mul, K.identity_mul a.property]

private theorem groupIdealProjection_eq_self (x : (P).range) : P x = (x : E) := by
  obtain ⟨y,hy⟩ := x.property
  change P y = (x : E) at hy
  rw [← hy, K.projection_apply_apply]

variable [CompleteSpace E]

/-- On the range of the group-ideal identity, the compact group acts by
orthogonal operators. Both an operator and its group inverse are contractions. -/
def groupIdealOrthogonalAction : K.carrier →* ((P).range ≃ₗᵢ[ℝ] (P).range) where
  toFun a :=
    { toLinearEquiv :=
        { (K.operatorAction a).toLinearMap.restrict (fun x _ ↦ groupIdealOperator_mem_range U K a x) with
          invFun := fun x ↦ ⟨K.operatorAction a⁻¹ x, groupIdealOperator_mem_range U K a⁻¹ x⟩
          left_inv := by
            intro x
            apply Subtype.ext
            change (K.operatorAction a⁻¹ * K.operatorAction a) x = (x : E)
            rw [← map_mul, inv_mul_cancel]
            exact groupIdealProjection_eq_self U K x
          right_inv := by
            intro x
            apply Subtype.ext
            change (K.operatorAction a * K.operatorAction a⁻¹) x = (x : E)
            rw [← map_mul, mul_inv_cancel]
            exact groupIdealProjection_eq_self U K x }
      norm_map' := by
        intro x
        change ‖K.operatorAction a x‖ = ‖(x : E)‖
        apply le_antisymm (orthogonalAction_closure_contractive U a.val x)
        calc
          ‖(x : E)‖ = ‖K.operatorAction a⁻¹ (K.operatorAction a x)‖ := by
            congr 1
            change (x : E) = (K.operatorAction a⁻¹ * K.operatorAction a) x
            rw [← map_mul, inv_mul_cancel]
            exact (groupIdealProjection_eq_self U K x).symm
          _ ≤ _ := orthogonalAction_closure_contractive U (a⁻¹).val _ }
  map_one' := by
    ext x
    exact groupIdealProjection_eq_self U K x
  map_mul' a b := by
    ext x
    change K.operatorAction (a*b) x = (K.operatorAction a * K.operatorAction b) x
    rw [map_mul]

/-- The original action on the range agrees with its image in the compact
group ideal. -/
theorem groupIdealOrthogonalAction_retraction (g : G) (x : (P).range) :
    ((groupIdealOrthogonalAction U K (K.groupRetraction (closureInclusion π g))) x : E) = U g x := by
  change closureAction π (K.identity * closureInclusion π g) x = _
  rw [K.identity_mul_eq_mul_identity, map_mul]
  change U g (P x) = _
  rw [groupIdealProjection_eq_self U K x]

/-- Approximation of the projected vector by a vector in a finite-dimensional
invariant real subspace, with a uniform bound on its coefficient error. -/
theorem exists_finite_approximation_of_groupIdeal (hK : IsCompact K.carrier)
    (v : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ (V : Submodule ℝ E), FiniteDimensional ℝ V ∧ IsInvariantSubmodule U V ∧
      ∃ w : V, ∀ g, |⟪P v,U g (P v)⟫_ℝ - ⟪(w : E),U g w⟫_ℝ| < ε := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel _
  let : BorelSpace K.carrier := ⟨rfl⟩
  let ρ := groupIdealOrthogonalAction U K
  have hρ (x : (P).range) : Continuous fun k ↦ ρ k x :=
    (K.continuous_norm_eval hK (x : E)).subtype_mk _
  let u : (P).range := ⟨P v,⟨v,rfl⟩⟩
  let : CompleteSpace (P).range := K.isClosed_range_projection (closureAction π) |>.completeSpace_coe
  let δ := min 1 (ε / (2*‖P v‖+2))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  obtain ⟨W,hW,hWI,w,hw⟩ := exists_finiteInvariant_approximation
    (normalizedHaar K.carrier) ρ hρ u δ hδ
  let V := W.map (P).range.subtype
  have hVI : IsInvariantSubmodule U V := by
    rintro g _ ⟨x,hx,rfl⟩
    refine ⟨ρ (K.groupRetraction (closureInclusion π g)) x,hWI _ _ hx,?_⟩
    exact groupIdealOrthogonalAction_retraction U K g x
  have hV : FiniteDimensional ℝ V := by
    let := hW
    have he : ((P).range.subtype.comp W.subtype).range = V := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    exact he ▸ inferInstanceAs (FiniteDimensional ℝ ((P).range.subtype.comp W.subtype).range)
  let z : V := ⟨(w : E),⟨w,w.property,rfl⟩⟩
  refine ⟨V,hV,hVI,z,fun g ↦ ?_⟩
  let a := P v
  let b := (z : E)
  have hab : ‖a-b‖ < δ := hw
  have hb : ‖b‖ ≤ ‖a‖ + ‖a-b‖ := by
    calc
      _ = ‖a + -(a-b)‖ := congrArg norm (by abel)
      _ ≤ _ := by grw [norm_add_le, norm_neg]
  have hsum : ‖a‖ + ‖b‖ ≤ 2*‖a‖+2 := by
    have h₁ : δ ≤ 1 := min_le_left _ _
    linarith
  have herr : |⟪a,U g a⟫_ℝ - ⟪b,U g b⟫_ℝ| ≤ ‖a-b‖*(‖a‖+‖b‖) := by
    rw [show ⟪a,U g a⟫_ℝ - ⟪b,U g b⟫_ℝ = ⟪a-b,U g a⟫_ℝ + ⟪b,U g (a-b)⟫_ℝ by
      simp only [inner_sub_left, map_sub, inner_sub_right]; ring]
    apply (abs_add_le _ _).trans
    have h₁ := norm_inner_le_norm (𝕜 := ℝ) (a-b) (U g a)
    have h₂ := norm_inner_le_norm (𝕜 := ℝ) b (U g (a-b))
    rw [LinearIsometryEquiv.norm_map] at h₁ h₂
    simpa only [Real.norm_eq_abs, mul_add, mul_comm ‖a-b‖ ‖b‖] using add_le_add h₁ h₂
  calc
    _ ≤ ‖a-b‖*(‖a‖+‖b‖) := herr
    _ ≤ ‖a-b‖*(2*‖a‖+2) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ < δ*(2*‖a‖+2) := mul_lt_mul_of_pos_right hab (by positivity)
    _ ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)

end GroupIdeal

end SixProblems
end

/- Source module SixProblems.CompactOrthogonalGroup. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Set Mixing Mixing.JdLGBridge

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Regard an orthogonal representation as a homomorphism into the unitary
group of the real algebra of bounded operators. -/
def orthogonalUnitaryHom (U : G →* (E ≃ₗᵢ[ℝ] E)) : G →* unitary (E →L[ℝ] E) :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp U

/-- For a finite-dimensional space this subgroup carries a compact metrizable topology. -/
def orthogonalClosure (U : G →* (E ≃ₗᵢ[ℝ] E)) : Subgroup (unitary (E →L[ℝ] E)) :=
  (orthogonalUnitaryHom U).range.topologicalClosure

private theorem unitary_compactSpace [FiniteDimensional ℝ E] :
    CompactSpace (unitary (E →L[ℝ] E)) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset isClosed_unitary
  intro T hT
  rw [Metric.mem_closedBall, dist_zero_right]
  apply ContinuousLinearMap.opNorm_le_bound T zero_le_one
  intro x
  simpa only [one_mul] using (Unitary.norm_map ⟨T,hT⟩ x).le

instance [FiniteDimensional ℝ E] (U : G →* (E ≃ₗᵢ[ℝ] E)) : CompactSpace (orthogonalClosure U) := by
  let : CompactSpace (unitary (E →L[ℝ] E)) := unitary_compactSpace
  exact isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact

/-- The original group maps densely into the compact closure. -/
def orthogonalClosureHom (U : G →* (E ≃ₗᵢ[ℝ] E)) : G →* orthogonalClosure U :=
  (orthogonalUnitaryHom U).codRestrict (orthogonalClosure U) fun g ↦
    Subgroup.le_topologicalClosure _ ⟨g,rfl⟩

theorem denseRange_orthogonalClosureHom (U : G →* (E ≃ₗᵢ[ℝ] E)) :
    DenseRange (orthogonalClosureHom U) := by
  intro x
  apply closure_subtype.mpr
  rw [← range_comp]
  exact x.property

/-- The tautological orthogonal representation of the closure on the same space. -/
def orthogonalClosureRep (U : G →* (E ≃ₗᵢ[ℝ] E)) : orthogonalClosure U →* (E ≃ₗᵢ[ℝ] E) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp (orthogonalClosure U).subtype

theorem orthogonalClosureRep_apply_hom (U : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) :
    orthogonalClosureRep U (orthogonalClosureHom U g) = U g :=
  Unitary.linearIsometryEquiv.apply_symm_apply (U g)

theorem continuous_orthogonalClosureRep_apply (U : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    Continuous (fun k ↦ orthogonalClosureRep U k x) := by
  change Continuous (fun k : orthogonalClosure U ↦ (k.val.val : E →L[ℝ] E) x)
  exact (continuous_subtype_val.comp continuous_subtype_val).clm_apply continuous_const

section HaarRotation

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

/-- Left multiplication through a homomorphism into a compact group, with
normalized Haar measure. -/
def haarRotation (α : G →* K) : System G K where
  measure := normalizedHaar K
  probability := inferInstance
  act g k := α g * k
  act_one := by ext k; rw [map_one, one_mul]; rfl
  act_mul g h := by ext k; simp [map_mul, mul_assoc]
  preserves g := measurePreserving_mul_left _ (α g)

/-- A dense subgroup of a compact metrizable group acts ergodically on Haar measure. -/
theorem haarRotation_isErgodic [T2Space K] (α : G →* K) (hα : DenseRange α) :
    (haarRotation α).IsErgodic := by
  intro A hA hInv
  change Filter.EventuallyEmptyOrUniv A (ae (normalizedHaar K))
  apply aeconst_of_dense_setOfPred_preimage_smul_ae (M := K) hA.nullMeasurableSet
  apply hα.mono
  rintro _ ⟨g,rfl⟩
  exact hInv g

end HaarRotation

end SixProblems
end

/- Source module SixProblems.CompactRealRealization. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Bounded Haar realization of finite-dimensional real matrix coefficients -/

noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Set Mixing Mixing.JdLGBridge Polynomial InnerProductSpace
open scoped InnerProductSpace

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem polynomial_symmetric {A : Module.End ℝ E} (hA : A.IsSymmetric) (p : ℝ[X]) :
    (aeval A p).IsSymmetric := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (hA.pow n).smul (by simp)

private theorem commute_aeval_of_commute {A B : Module.End ℝ E} (h : Commute A B) (p : ℝ[X]) :
    Commute A (aeval B p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    have hc : Commute A (algebraMap ℝ (Module.End ℝ E) c) := (Algebra.commutes c A).symm
    exact hc.mul_right (h.pow_right n)

variable [FiniteDimensional ℝ E]

/-- If a nonnegative self-adjoint operator has no zero-eigenvalue component on
`v`, a polynomial in the operator acts as its inverse square root on `v`. -/
private theorem exists_normalizing_polynomial (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (hnonneg : ∀ x, 0 ≤ ⟪x,A x⟫_ℝ) (v : E)
    (hzero : ∀ x, A x = 0 → ⟪x,v⟫_ℝ = 0) :
    ∃ q : ℝ[X], aeval A q (A (aeval A q v)) = v := by
  classical
  let d := Module.finrank ℝ E
  let b := hA.eigenvectorBasis (n := d) rfl
  let eigenvalue : Fin d → ℝ := hA.eigenvalues rfl
  let s := Finset.univ.image eigenvalue
  let c (t : ℝ) := (Real.sqrt t)⁻¹
  let q := Lagrange.interpolate s id c
  have heigenvalue (i : Fin d) : 0 ≤ eigenvalue i := by
    apply eigenvalue_nonneg_of_nonneg (hA.hasEigenvalue_eigenvalues rfl i)
    exact hnonneg
  have hq (i : Fin d) : q.eval (eigenvalue i) = c (eigenvalue i) :=
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ he ↦ he) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let B := aeval A q
  have hB := polynomial_symmetric hA q
  have hAb (i : Fin d) : A (b i) = eigenvalue i • b i := hA.apply_eigenvectorBasis rfl i
  have hBb (i : Fin d) : B (b i) = c (eigenvalue i) • b i := by
    rw [show B (b i) = q.eval (eigenvalue i) • b i from Module.End.aeval_apply_of_mem_apply_eq_smul (hAb i), hq]
  have hAinner (i : Fin d) (w : E) : ⟪b i, A w⟫_ℝ = eigenvalue i * ⟪b i,w⟫_ℝ := by
    rw [← hA, hAb, real_inner_smul_left]
  have hBinner (i : Fin d) (w : E) : ⟪b i, B w⟫_ℝ = c (eigenvalue i) * ⟪b i,w⟫_ℝ := by
    rw [← hB, hBb, real_inner_smul_left]
  refine ⟨q, b.repr.injective ?_⟩
  change b.repr (B (A (B v))) = b.repr v
  ext i
  simp only [b.repr_apply_apply]
  rw [hBinner, hAinner, hBinner]
  by_cases h0 : eigenvalue i = 0
  · have hz : A (b i) = 0 := by rw [hAb, h0, zero_smul]
    rw [hzero _ hz, mul_zero, mul_zero, mul_zero]
  · have hpos : 0 < eigenvalue i := lt_of_le_of_ne (heigenvalue i) (fun he ↦ h0 he.symm)
    have hsqrt : Real.sqrt (eigenvalue i) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    have he : c (eigenvalue i) * (eigenvalue i * c (eigenvalue i)) = 1 := by
      dsimp [c]
      calc
        _ = (Real.sqrt (eigenvalue i))⁻¹ * ((Real.sqrt (eigenvalue i)) ^ 2 * (Real.sqrt (eigenvalue i))⁻¹) :=
          congrArg (fun t ↦ (Real.sqrt (eigenvalue i))⁻¹ * (t * (Real.sqrt (eigenvalue i))⁻¹)) (Real.sq_sqrt (heigenvalue i)).symm
        _ = 1 := by field_simp [hsqrt]
    rw [← mul_assoc, ← mul_assoc, mul_assoc (c (eigenvalue i)) (eigenvalue i), he, one_mul]

end Normalization

section Realization

variable {K E : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The coefficient of a vector in a finite-dimensional orthogonal representation
of a compact group is a correlation of a continuous real function on that group. -/
theorem exists_continuous_haar_realization (m : Measure K) [IsProbabilityMeasure m]
    [IsMulLeftInvariant m] [m.IsOpenPosMeasure] (ρ : K →* (E ≃ₗᵢ[ℝ] E))
    (hρ : ∀ x, Continuous fun k ↦ ρ k x) (v : E) :
    ∃ f : C(K, ℝ), (∃ C : ℝ, ∀ k, ‖f k‖ ≤ C) ∧
      ∀ a, (∫ k, f (a * k) * f k ∂m) = ⟪v, ρ a v⟫_ℝ := by
  let A := RealRepresentation.compactRepresentationAverage m ρ v
  have hA (x y : E) : ⟪x,A y⟫_ℝ = ∫ k, ⟪x,ρ k v⟫_ℝ * ⟪y,ρ k v⟫_ℝ ∂m :=
    by
      rw [RealRepresentation.inner_compactRepresentationAverage m ρ v (hρ v)]
      apply integral_congr_ae
      exact ae_of_all _ fun k ↦ by
        change ⟪x,rankOne ℝ (ρ k v) (ρ k v) y⟫_ℝ = ⟪x,ρ k v⟫_ℝ * ⟪y,ρ k v⟫_ℝ
        rw [rankOne_apply, real_inner_smul_right, real_inner_comm (ρ k v) y, mul_comm]
  have hAs : A.toLinearMap.IsSymmetric :=
    RealRepresentation.isSymmetric_compactRepresentationAverage m ρ v (hρ v)
  have hAn (x : E) : 0 ≤ ⟪x,A x⟫_ℝ := by
    rw [hA]
    exact integral_nonneg (fun _ ↦ mul_self_nonneg _)
  have hAz (x : E) (hx : A x = 0) : ⟪x,v⟫_ℝ = 0 := by
    by_contra hne
    let u (k : K) := ⟪x,ρ k v⟫_ℝ ^ 2
    have hc : Continuous u := (continuous_const.inner (hρ v)).pow 2
    have hne' : u 1 ≠ 0 := by
      dsimp [u]
      rw [map_one]
      exact pow_ne_zero _ hne
    have hp := hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := m)
      (HasCompactSupport.of_compactSpace _) (fun k ↦ sq_nonneg ⟪x,ρ k v⟫_ℝ) hne'
    have hz := hA x x
    rw [hx, inner_zero_right] at hz
    exact hp.ne' (by simpa only [u, pow_two] using hz.symm)
  obtain ⟨q,hq⟩ := exists_normalizing_polynomial A.toLinearMap hAs hAn v hAz
  let B := aeval A.toLinearMap q
  have hB := polynomial_symmetric hAs q
  have hAB (a : K) (y : E) : ρ a (B y) = B (ρ a y) := by
    have hcomm : Commute (ρ a).toLinearMap A.toLinearMap := by
      apply LinearMap.ext
      exact RealRepresentation.compactRepresentationAverage_commutes m ρ v (hρ v) a
    exact DFunLike.congr_fun (commute_aeval_of_commute hcomm q).eq y
  let f : C(K, ℝ) := ⟨fun k ↦ ⟪B v,ρ k v⟫_ℝ, continuous_const.inner (hρ v)⟩
  have hmove (a : K) (x y : E) : ⟪ρ a⁻¹ x,y⟫_ℝ = ⟪x,ρ a y⟫_ℝ := by
    rw [← (ρ a).inner_map_map (ρ a⁻¹ x) y]
    change ⟪(ρ a * ρ a⁻¹) x,ρ a y⟫_ℝ = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨f, ⟨‖B v‖ * ‖v‖, fun k ↦ ?_⟩, fun a ↦ ?_⟩
  · change ‖⟪B v,ρ k v⟫_ℝ‖ ≤ _
    simpa only [LinearIsometryEquiv.norm_map] using norm_inner_le_norm (B v) (ρ k v)
  · calc
      _ = ∫ k, ⟪ρ a⁻¹ (B v),ρ k v⟫_ℝ * ⟪B v,ρ k v⟫_ℝ ∂m := by
        apply integral_congr_ae
        exact ae_of_all _ fun k ↦ by
          change ⟪B v,ρ (a * k) v⟫_ℝ * ⟪B v,ρ k v⟫_ℝ =
            ⟪ρ a⁻¹ (B v),ρ k v⟫_ℝ * ⟪B v,ρ k v⟫_ℝ
          rw [hmove, map_mul]
          rfl
      _ = ⟪ρ a⁻¹ (B v),A (B v)⟫_ℝ := (hA _ _).symm
      _ = ⟪ρ a⁻¹ v,v⟫_ℝ := by rw [hAB, hB, show B (A (B v)) = v from hq]
      _ = _ := hmove a v v

end Realization

set_option maxHeartbeats 1200000 in
/-- Every finite-dimensional real orthogonal coefficient has an exact realization
by a bounded measurable real function on a standard Borel ergodic system. -/
theorem exists_ergodic_realization_of_finiteDimensional
    {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (U : G →* (E ≃ₗᵢ[ℝ] E)) (v : E) :
    ∃ (X : Type) (_mX : MeasurableSpace X) (_ : StandardBorelSpace X)
      (S : System G X) (f : X → ℝ),
      S.IsErgodic ∧ Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
      ∀ g, (∫ x, f (S.act g x) * f x ∂S.measure) = ⟪v,U g v⟫_ℝ := by
  let : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  let K := orthogonalClosure U
  let : PolishSpace (E →L[ℝ] E) := inferInstance
  let : PolishSpace (unitary (E →L[ℝ] E)) := isClosed_unitary.polishSpace
  let : PolishSpace K := (Subgroup.isClosed_topologicalClosure (orthogonalUnitaryHom U).range).polishSpace
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : StandardBorelSpace K := inferInstance
  let m := normalizedHaar K
  let ρ := orthogonalClosureRep U
  let α := orthogonalClosureHom U
  obtain ⟨f,hBound,hCorr⟩ := exists_continuous_haar_realization m ρ
    (continuous_orthogonalClosureRep_apply U) v
  let S := haarRotation α
  have hS : S.IsErgodic := haarRotation_isErgodic α (denseRange_orthogonalClosureHom U)
  refine ⟨K, ‹MeasurableSpace K›, ‹StandardBorelSpace K›, S, f, hS, f.continuous.measurable, hBound, ?_⟩
  intro g
  change (∫ k, f (α g * k) * f k ∂m) = _
  rw [hCorr, orthogonalClosureRep_apply_hom U g]

end SixProblems
end

/- Source module SixProblems.PositiveDefinite. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

open scoped InnerProductSpace

variable {G : Type*} [Group G]

/-- A real positive-definite function on a group. Right differences make
each covariance matrix invariant under simultaneous right translation. -/
def RealPositiveDefinite (φ : G → ℝ) : Prop :=
  ∀ I : Finset G, (Matrix.of fun i j : I ↦ φ ((i : G) * (j : G)⁻¹)).PosSemidef

/-- The finite-matrix and finitely supported quadratic-form definitions agree. -/
theorem realPositiveDefinite_iff_posSemidef {φ : G → ℝ} :
    RealPositiveDefinite φ ↔ (Matrix.of fun g h : G ↦ φ (g * h⁻¹)).PosSemidef :=
  (Matrix.posSemidef_iff_submatrix_finset (M := Matrix.of fun g h : G ↦ φ (g * h⁻¹))).symm

namespace RealPositiveDefinite

/-- Reindexing the covariance matrix allows repeated group elements. -/
theorem reindex {φ : G → ℝ} (hφ : RealPositiveDefinite φ) {I : Type*} (g : I → G) :
    (Matrix.of fun i j ↦ φ (g i * (g j)⁻¹)).PosSemidef :=
  (realPositiveDefinite_iff_posSemidef.mp hφ).submatrix g

theorem inv_eq {φ : G → ℝ} (hφ : RealPositiveDefinite φ) (g : G) :
    φ g⁻¹ = φ g := by
  let u : Bool → G := fun b ↦ if b then g else 1
  simpa [u] using (hφ.reindex u).isHermitian.apply true false

theorem one_nonneg {φ : G → ℝ} (hφ : RealPositiveDefinite φ) : 0 ≤ φ 1 := by
  have h := (hφ.reindex (fun _ : Unit ↦ (1 : G))).diag_nonneg (i := ())
  simpa using h

/-- Every value of a real positive-definite function is bounded in absolute
value by the value at the identity. The two-point tests use the vectors
`(1, 1)` and `(1, -1)`. -/
theorem abs_le_one {φ : G → ℝ} (hφ : RealPositiveDefinite φ) (g : G) :
    |φ g| ≤ φ 1 := by
  let u : Bool → G := fun b ↦ if b then g else 1
  let v : Bool → ℝ := fun b ↦ if b then 1 else -1
  have hu := (hφ.reindex u).dotProduct_mulVec_nonneg (fun _ ↦ (1 : ℝ))
  have hv := (hφ.reindex u).dotProduct_mulVec_nonneg v
  simp [u, Matrix.mulVec, dotProduct, hφ.inv_eq g] at hu
  simp [u, v, Matrix.mulVec, dotProduct, hφ.inv_eq g] at hv
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end RealPositiveDefinite

/-- Real coefficients of unitary representations are positive definite.
The Gram vectors here are the inverse translates of `x`. -/
theorem realPositiveDefinite_coefficient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    RealPositiveDefinite (fun g ↦ ⟪x, U g x⟫_ℝ) := by
  intro I
  let v (i : I) := U ((i : G)⁻¹) x
  have hgram := Matrix.posSemidef_gram ℝ v
  convert hgram using 1
  ext i j
  change ⟪x, U ((i : G) * (j : G)⁻¹) x⟫_ℝ = ⟪v i, v j⟫_ℝ
  -- Apply the same unitary to both entries of the Gram coefficient.
  symm
  rw [← (U (i : G)).inner_map_map]
  change ⟪(U (i : G) * U ((i : G)⁻¹)) x, (U (i : G) * U ((j : G)⁻¹)) x⟫_ℝ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- Real parts of complex unitary coefficients are real positive definite.
They are Gram matrices for the realification of the Hilbert space. -/
theorem realPositiveDefinite_re_coefficient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* (E ≃ₗᵢ[ℂ] E)) (x : E) :
    RealPositiveDefinite (fun g ↦ (⟪x, U g x⟫_ℂ).re) := by
  intro I
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let v (i : I) := U ((i : G)⁻¹) x
  convert Matrix.posSemidef_gram ℝ v using 1
  ext i j
  change (⟪x, U ((i : G) * (j : G)⁻¹) x⟫_ℂ).re = (⟪v i, v j⟫_ℂ).re
  congr 1
  symm
  rw [← (U (i : G)).inner_map_map]
  change ⟪(U (i : G) * U ((i : G)⁻¹)) x, (U (i : G) * U ((j : G)⁻¹)) x⟫_ℂ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The epsilon formulation of the nonnegative-supremum criterion, including
the empty set convention. This is Theorem 2.2(d). -/
def NonnegativeOnPositiveDefinite (R : Set G) : Prop :=
  ∀ φ : G → ℝ, RealPositiveDefinite φ →
    ∀ ε > 0, ∃ r ∈ R, -ε ≤ φ r

/-- For a nonempty set, the epsilon formulation is precisely the supremum
formulation of Theorem 2.2(d). -/
theorem nonnegativeOnPositiveDefinite_iff_sSup {R : Set G} (hR : R.Nonempty) :
    NonnegativeOnPositiveDefinite R ↔ ∀ φ : G → ℝ, RealPositiveDefinite φ →
      0 ≤ sSup (φ '' R) := by
  constructor
  · intro h φ hφ
    by_contra! hneg
    have hbdd : BddAbove (φ '' R) :=
      ⟨φ 1, fun _ ⟨g, _, hg⟩ ↦ hg ▸ (abs_le.mp (hφ.abs_le_one g)).2⟩
    obtain ⟨g, hg, hval⟩ := h φ hφ (-(sSup (φ '' R)) / 2) (by linarith)
    have hs := le_csSup hbdd (Set.mem_image_of_mem _ hg)
    linarith
  · intro h φ hφ ε hε
    by_contra! hneg
    have hs : sSup (φ '' R) ≤ -ε := csSup_le (hR.image φ) (by
      rintro _ ⟨g, hg, rfl⟩
      exact (hneg g hg).le)
    linarith [h φ hφ]

end SixProblems
end

/- Source module SixProblems.PartitionRegularity. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

variable {G : Type*} [Group G]

namespace RealPositiveDefinite

theorem const {c : ℝ} (hc : 0 ≤ c) : RealPositiveDefinite (fun _ : G ↦ c) := by
  intro I
  have h := (Matrix.posSemidef_vecMulVec_self_star (fun _ : I ↦ (1 : ℝ))).smul hc
  convert h using 1
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.smul_apply]

theorem add {φ ψ : G → ℝ} (hφ : RealPositiveDefinite φ) (hψ : RealPositiveDefinite ψ) :
    RealPositiveDefinite (fun g ↦ φ g + ψ g) :=
  fun I ↦ (hφ I).add (hψ I)

theorem mul {φ ψ : G → ℝ} (hφ : RealPositiveDefinite φ) (hψ : RealPositiveDefinite ψ) :
    RealPositiveDefinite (fun g ↦ φ g * ψ g) := by
  classical
  exact fun I ↦ (hφ I).hadamard (hψ I)

theorem smul {φ : G → ℝ} (hφ : RealPositiveDefinite φ) {c : ℝ} (hc : 0 ≤ c) :
    RealPositiveDefinite (fun g ↦ c * φ g) := by
  intro I
  exact (hφ I).smul hc

theorem pow {φ : G → ℝ} (hφ : RealPositiveDefinite φ) (n : ℕ) :
    RealPositiveDefinite (fun g ↦ φ g ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const (G := G) zero_le_one
  | succ k ih => simpa only [pow_succ] using ih.mul hφ

theorem finset_prod {I : Type*} (s : Finset I) (F : I → G → ℝ)
    (hF : ∀ i ∈ s, RealPositiveDefinite (F i)) :
    RealPositiveDefinite (fun g ↦ ∏ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using const (G := G) zero_le_one
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).mul (ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)))

theorem finset_sum {I : Type*} (s : Finset I) (F : I → G → ℝ)
    (hF : ∀ i ∈ s, RealPositiveDefinite (F i)) :
    RealPositiveDefinite (fun g ↦ ∑ i ∈ s, F i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const (G := G) (le_refl (0 : ℝ))
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self _ _)).add (ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj)))

end RealPositiveDefinite

/-- Lemma 3.1. A polynomial with nonnegative coefficients preserves real
positive definiteness under pointwise evaluation. The two-variable statement
uses `I = Fin 2`. -/
theorem lemma3_1 {I : Type*} (F : I → G → ℝ) (hF : ∀ i, RealPositiveDefinite (F i))
    (p : MvPolynomial I ℝ) (hp : ∀ d, 0 ≤ p.coeff d) :
    RealPositiveDefinite (fun g ↦ MvPolynomial.eval (fun i ↦ F i g) p) := by
  simp_rw [MvPolynomial.eval_eq]
  apply RealPositiveDefinite.finset_sum
  intro d _
  apply RealPositiveDefinite.smul _ (hp d)
  exact RealPositiveDefinite.finset_prod d.support _ (fun i _ ↦ (hF i).pow (d i))

/-- Lemma 3.2. The polynomial barrier is strictly negative by a uniform
amount when either input lies below `-ε`. -/
theorem lemma3_2 {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M) :
    ∃ δ > 0, ∃ K : ℕ, ∀ x y : ℝ, x ∈ Set.Icc (-M) M → y ∈ Set.Icc (-M) M →
      (x < -ε ∨ y < -ε) → x * (2 * M + y) ^ K + y * (2 * M + x) ^ K ≤ -δ := by
  have hM : 0 < M := hε.trans hεM
  have htwoM : 0 < 2 * M := by linarith
  have hsmall : 0 < 2 * M - ε := by linarith
  let q := (2 * M - ε) / (2 * M)
  have hq : q < 1 := (div_lt_one htwoM).mpr (by linarith)
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (x := ε / 2 / M) (by positivity) hq
  have hK' : M * (2 * M - ε) ^ K ≤ (ε / 2) * (2 * M) ^ K := by
    simp only [q, div_pow] at hK
    have h := (div_lt_div_iff₀ (pow_pos htwoM K) hM).mp hK
    simpa only [mul_comm] using h.le
  let δ := (ε / 2) * M ^ K
  have hδ : 0 < δ := mul_pos (half_pos hε) (pow_pos hM K)
  refine ⟨δ, hδ, K, fun x y hx hy hneg ↦ ?_⟩
  have hfirst (a b : ℝ) (ha : a ∈ Set.Icc (-M) M) (hb : b ∈ Set.Icc (-M) M)
      (haneg : a < -ε) : a * (2 * M + b) ^ K + b * (2 * M + a) ^ K ≤ -δ := by
    have hbase_a : M ≤ 2 * M + a := by linarith [ha.1]
    have hbase_b : M ≤ 2 * M + b := by linarith [hb.1]
    have ha_pow : 0 ≤ (2 * M + a) ^ K := pow_nonneg (hM.le.trans hbase_a) _
    have hb_pow : 0 ≤ (2 * M + b) ^ K := pow_nonneg (hM.le.trans hbase_b) _
    have hpow_small : (2 * M + a) ^ K ≤ (2 * M - ε) ^ K :=
      pow_le_pow_left₀ (hM.le.trans hbase_a) (by linarith) K
    by_cases hb0 : b ≤ 0
    · have hb_term : b * (2 * M + a) ^ K ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb0 ha_pow
      calc
        _ ≤ (-ε) * (2 * M + b) ^ K := by
          linarith [mul_le_mul_of_nonneg_right haneg.le hb_pow]
        _ ≤ (-ε) * M ^ K := mul_le_mul_of_nonpos_left
          (pow_le_pow_left₀ hM.le hbase_b K) (neg_nonpos.mpr hε.le)
        _ ≤ -δ := by
          dsimp [δ]
          linarith [mul_le_mul_of_nonneg_right (show -ε ≤ -(ε / 2) by linarith)
            (pow_nonneg hM.le K)]
    · have hb_bound : (2 * M) ^ K ≤ (2 * M + b) ^ K :=
        pow_le_pow_left₀ htwoM.le (by linarith) K
      have hmain : a * (2 * M + b) ^ K ≤ (-ε) * (2 * M) ^ K :=
        (mul_le_mul_of_nonneg_right haneg.le hb_pow).trans
          (mul_le_mul_of_nonpos_left hb_bound (neg_nonpos.mpr hε.le))
      have hother : b * (2 * M + a) ^ K ≤ (ε / 2) * (2 * M) ^ K :=
        (mul_le_mul_of_nonneg_right hb.2 ha_pow).trans
          ((mul_le_mul_of_nonneg_left hpow_small hM.le).trans hK')
      have hwide : M ^ K ≤ (2 * M) ^ K := pow_le_pow_left₀ hM.le (by linarith) K
      calc
        _ ≤ -(ε / 2) * (2 * M) ^ K := by linarith
        _ ≤ -δ := by
          dsimp [δ]
          linarith [mul_le_mul_of_nonpos_left hwide (show -(ε / 2) ≤ 0 by linarith)]
  rcases hneg with hxneg | hyneg
  · exact hfirst x y hx hy hxneg
  · rw [add_comm]
    exact hfirst y x hy hx hyneg

/-- Failure of the nonnegative-supremum criterion gives a uniform
negative positive-definite witness on the set. -/
theorem not_nonnegativeOnPositiveDefinite_iff {R : Set G} :
    ¬NonnegativeOnPositiveDefinite R ↔
      ∃ φ : G → ℝ, RealPositiveDefinite φ ∧ ∃ ε > 0, ∀ g ∈ R, φ g < -ε := by
  unfold NonnegativeOnPositiveDefinite
  push Not
  rfl

/-- Theorem 3.3 in the positive-definite characterization from Theorem 2.2(d).
The nonnegative-supremum criterion is partition regular. -/
theorem theorem3_3_positiveDefinite {A B : Set G}
    (hA : ¬NonnegativeOnPositiveDefinite A) (hB : ¬NonnegativeOnPositiveDefinite B) :
    ¬NonnegativeOnPositiveDefinite (A ∪ B) := by
  obtain ⟨φ, hφ, ε₁, hε₁, hφneg⟩ := not_nonnegativeOnPositiveDefinite_iff.mp hA
  obtain ⟨ψ, hψ, ε₂, hε₂, hψneg⟩ := not_nonnegativeOnPositiveDefinite_iff.mp hB
  let ε := min ε₁ ε₂
  let M := max (max (φ 1) (ψ 1)) ε + 1
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hεM : ε < M := by dsimp [M]; linarith [le_max_right (max (φ 1) (ψ 1)) ε]
  have hM : 0 ≤ M := (hε.trans hεM).le
  have hφM : φ 1 ≤ M := by dsimp [M]; linarith [
    (le_max_left (φ 1) (ψ 1)).trans (le_max_left (max (φ 1) (ψ 1)) ε)]
  have hψM : ψ 1 ≤ M := by dsimp [M]; linarith [
    (le_max_right (φ 1) (ψ 1)).trans (le_max_left (max (φ 1) (ψ 1)) ε)]
  obtain ⟨δ, hδ, K, hbound⟩ := lemma3_2 hε hεM
  let χ (g : G) := φ g * (2 * M + ψ g) ^ K + ψ g * (2 * M + φ g) ^ K
  have hconst : RealPositiveDefinite (fun _ : G ↦ 2 * M) :=
    RealPositiveDefinite.const (mul_nonneg (by norm_num) hM)
  have hχ : RealPositiveDefinite χ :=
    (hφ.mul ((hconst.add hψ).pow K)).add (hψ.mul ((hconst.add hφ).pow K))
  refine not_nonnegativeOnPositiveDefinite_iff.mpr ⟨χ, hχ, δ / 2, half_pos hδ, fun g hg ↦ ?_⟩
  have hφg := abs_le.mp ((hφ.abs_le_one g).trans hφM)
  have hψg := abs_le.mp ((hψ.abs_le_one g).trans hψM)
  have hneg : φ g < -ε ∨ ψ g < -ε := by
    rcases hg with hg | hg
    · exact Or.inl ((hφneg g hg).trans_le (neg_le_neg (min_le_left ε₁ ε₂)))
    · exact Or.inr ((hψneg g hg).trans_le (neg_le_neg (min_le_right ε₁ ε₂)))
  exact (hbound (φ g) (ψ g) hφg hψg hneg).trans_lt (by linarith)

/-- Corollary 3.4 in the positive-definite characterization. -/
theorem corollary3_4_positiveDefinite {I : Type*} (s : Finset I) (D : I → Set G)
    (hD : NonnegativeOnPositiveDefinite (⋃ i ∈ s, D i)) :
    ∃ i ∈ s, NonnegativeOnPositiveDefinite (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨g, hg, _⟩ := hD (fun _ ↦ 0) (RealPositiveDefinite.const le_rfl) 1 zero_lt_one
    simp at hg
  | insert i s hi ih =>
    change NonnegativeOnPositiveDefinite (⋃ j ∈ (↑(insert i s) : Set I), D j) at hD
    rw [Finset.coe_insert, Set.biUnion_insert] at hD
    by_cases hDi : NonnegativeOnPositiveDefinite (D i)
    · exact ⟨i, Finset.mem_insert_self _ _, hDi⟩
    · have hrest : NonnegativeOnPositiveDefinite (⋃ j ∈ s, D j) := by
        by_contra hrest
        exact theorem3_3_positiveDefinite hDi hrest hD
      obtain ⟨j, hj, hDj⟩ := ih hrest
      exact ⟨j, Finset.mem_insert_of_mem hj, hDj⟩

end SixProblems
end

/- Source module SixProblems.NiceRecurrence. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set

variable {G X : Type*} [Group G] [MeasurableSpace X]

theorem event_return_measure_inv (S : System G X) {A : Set X} (hA : MeasurableSet A) (g : G) :
    S.measure (A ∩ S.act g⁻¹ ⁻¹' A) = S.measure (A ∩ S.act g ⁻¹' A) := by
  have hEq : S.act g ⁻¹' (A ∩ S.act g⁻¹ ⁻¹' A) = A ∩ S.act g ⁻¹' A := by
    ext x
    have h : S.act g⁻¹ (S.act g x) = x := by
      change (S.act g⁻¹ ∘ S.act g) x = x
      rw [← S.act_mul, inv_mul_cancel, S.act_one]
      rfl
    simp [h, and_comm]
  have hMeas := hA.inter ((S.preserves g⁻¹).measurable hA)
  rw [← hEq, (S.preserves g).measure_preimage hMeas.nullMeasurableSet]

theorem correlation_indicatorOne (S : System G X) {A : Set X} (hA : MeasurableSet A) (g : G) :
    correlation S (A.indicator (fun _ : X ↦ (1 : ℂ))) g =
      (S.measure (A ∩ S.act g ⁻¹' A)).toReal := by
  classical
  let f := A.indicator (fun _ : X ↦ (1 : ℂ))
  let B := A ∩ S.act g ⁻¹' A
  have hB : MeasurableSet B := hA.inter ((S.preserves g).measurable hA)
  have he (x : X) : f (S.act g x) * (starRingEnd ℂ) (f x) =
      B.indicator (fun _ : X ↦ (1 : ℂ)) x := by
    by_cases hx : x ∈ A <;> by_cases hy : S.act g x ∈ A <;> simp [f, B, hx, hy]
  change (∫ x, f (S.act g x) * (starRingEnd ℂ) (f x) ∂S.measure) = _
  simp_rw [he]
  rw [integral_indicator hB, setIntegral_const, Complex.real_smul, mul_one]
  rfl

/-- Testing the bounded-function condition on indicator functions gives
nice event recurrence, the implication (e) to (a) of Theorem 2.2. -/
theorem niceRecurrence_of_niceVdC {G : Type} [Group G] {R : Set G}
    (hR : NiceVdC R) : NiceRecurrence R := by
  classical
  intro X _ _ S A hA ε hε
  let f := A.indicator (fun _ : X ↦ (1 : ℂ))
  have hf : Measurable f := measurable_const.indicator hA
  have hB (x : X) : ‖f x‖ ≤ 1 := by
    by_cases h : x ∈ A <;> simp [f,h]
  obtain ⟨r, hr, hr'⟩ := hR S f hf ⟨1,hB⟩ ε hε
  refine ⟨r,hr,?_⟩
  change ‖∫ x, A.indicator (fun _ : X ↦ (1 : ℂ)) x ∂S.measure‖ ^ 2 - ε ≤
    ‖correlation S f r⁻¹‖ at hr'
  rw [integral_indicator hA, setIntegral_const, Complex.real_smul, mul_one,
    correlation_indicatorOne S hA, event_return_measure_inv S hA,
    Complex.norm_real, Complex.norm_real, Measure.real_def, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_of_nonneg ENNReal.toReal_nonneg] at hr'
  exact hr'

/-- The implication (a) to (b) of Theorem 2.2. -/
theorem ergodicNiceRecurrence_of_niceRecurrence {G : Type} [Group G] {R : Set G}
    (hR : NiceRecurrence R) : ErgodicNiceRecurrence R :=
  fun S _ A hA ε hε ↦ hR S A hA ε hε

end SixProblems
end

/- Source module SixProblems.ErgodicThresholdComparison. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set

variable {G X : Type} [Group G] [MeasurableSpace X]

/-- Ergodic realization up to an arbitrarily small uniform error in the
coefficient; this is the form of realization needed for nice recurrence. -/
def HasBoundedErgodicPDApproximation (G : Type) [Group G] : Prop :=
  ∀ φ : G → ℝ, RealPositiveDefinite φ → ∀ δ > 0,
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      S.IsErgodic ∧ Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧ ∀ g,
      |(∫ x, f (S.act g x) * f x ∂S.measure) - φ g| < δ

private theorem integral_affine_half (S : System G X) {f : X → ℝ}
    (hf : Integrable f S.measure) (b : ℝ) :
    ∫ x, 1/2 + b*f x ∂S.measure = 1/2 + b*(∫ x, f x ∂S.measure) := by
  rw [integral_add (integrable_const _) (hf.const_mul _), integral_const, integral_const_mul,
    probReal_univ, one_smul]

private theorem integral_affine_half_mul (S : System G X) {f : X → ℝ}
    (hf : Integrable f S.measure) (b : ℝ) (g : G)
    (hmul : Integrable (fun x ↦ f (S.act g x) * f x) S.measure) :
    (∫ x, (1/2 + b*f (S.act g x))*(1/2 + b*f x) ∂S.measure) =
      1/4 + b*(∫ x, f x ∂S.measure) + b^2*(∫ x, f (S.act g x) * f x ∂S.measure) := by
  have hfg := (S.preserves g).integrable_comp_of_integrable hf
  have hmf : AEStronglyMeasurable f (S.measure.map (S.act g)) :=
    (S.preserves g).map_eq.symm ▸ hf.aestronglyMeasurable
  have he := integral_map (S.preserves g).aemeasurable hmf
  rw [(S.preserves g).map_eq] at he
  have hp (x : X) : (1/2 + b*f (S.act g x))*(1/2 + b*f x) =
      (1/4 + (b/2)*f (S.act g x)) + (b/2)*f x + b^2*(f (S.act g x)*f x) := by ring
  have hconst : Integrable (fun _ : X ↦ (1/4 : ℝ)) S.measure := integrable_const _
  have hshift : Integrable (fun x ↦ (b/2)*f (S.act g x)) S.measure := hfg.const_mul _
  have hterm : Integrable (fun x ↦ (b/2)*f x) S.measure := hf.const_mul _
  have hprod : Integrable (fun x ↦ b^2*(f (S.act g x)*f x)) S.measure := hmul.const_mul _
  have hsum : Integrable (fun x ↦ 1/4 + (b/2)*f (S.act g x)) S.measure := hconst.add hshift
  have hsum' : Integrable (fun x ↦ 1/4 + (b/2)*f (S.act g x) + (b/2)*f x) S.measure := hsum.add hterm
  simp_rw [hp]
  rw [integral_add hsum' hprod, integral_add hsum hterm, integral_add hconst hshift,
    integral_const, probReal_univ, one_smul]
  simp_rw [integral_const_mul]
  change _ = (∫ x, f (S.act g x) ∂S.measure) at he
  rw [← he]
  ring

/-- With the ergodic realization established, this is the implication
from condition (b) to condition (d) of Theorem 2.2. -/
theorem nonnegativePD_of_ergodicNiceRecurrence [Countable G] [Infinite G]
    (hRealize : HasBoundedErgodicPDApproximation G) {R : Set G}
    (hNice : ErgodicNiceRecurrence R) : NonnegativeOnPositiveDefinite R := by
  classical
  intro φ hφ ε hε
  by_contra! hneg
  obtain ⟨X,mX,hX,S,f,hS,hf,⟨C,hC⟩,hApprox⟩ := hRealize φ hφ (ε/2) (half_pos hε)
  let := mX
  let := hX
  let b := (2*(|C|+1))⁻¹
  have hb : 0 < b := inv_pos.mpr (by positivity)
  have hB (x : X) : |b * f x| ≤ 1/2 := by
    rw [abs_mul, abs_of_pos hb]
    change (2*(|C|+1))⁻¹ * |f x| ≤ 1/2
    rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    have hx := (hC x).trans (le_abs_self C)
    change |f x| ≤ |C| at hx
    linarith
  let F (x : X) := 1/2 + b*f x
  have hF : Measurable F := measurable_const.add (measurable_const.mul hf)
  have hF0 (x : X) : 0 ≤ F x := by dsimp [F]; linarith [(abs_le.mp (hB x)).1]
  have hF1 (x : X) : F x ≤ 1 := by dsimp [F]; linarith [(abs_le.mp (hB x)).2]
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let A := bernoulliThreshold (G := G) F
  have hA : MeasurableSet A := measurableSet_bernoulliThreshold hF
  have hT : T.IsErgodic := bernoulli_prod_isErgodic unitIntervalLaw S hS
  have hη : 0 < b^2*(ε/2) := mul_pos (sq_pos_of_pos hb) (half_pos hε)
  obtain ⟨r,hr,hret⟩ := hNice T hT A hA (b^2*(ε/2)) hη
  have hr₁ : r ≠ 1 := by
    intro h
    have hφ0 := hφ.one_nonneg
    have hrneg := hneg r hr
    rw [h] at hrneg
    linarith
  have hMass : (T.measure A).toReal = ∫ x, F x ∂S.measure := by
    have h := bernoulliThreshold_pattern S hF hF0 hF1 {1}
    change (T.measure {z | ∀ g ∈ ({1} : Finset G), z ∈ T.act g ⁻¹' A}).toReal = _ at h
    have he : {z | ∀ g ∈ ({1} : Finset G), z ∈ T.act g ⁻¹' A} = A := by
      ext z
      simp [T.act_one]
    rw [he] at h
    simpa only [Finset.prod_singleton,S.act_one,id_eq] using h
  have hRet : (T.measure (A ∩ T.act r ⁻¹' A)).toReal = ∫ x, F (S.act r x) * F x ∂S.measure := by
    have h := bernoulliThreshold_pattern S hF hF0 hF1 {r,1}
    change (T.measure {z | ∀ g ∈ ({r,1} : Finset G), z ∈ T.act g ⁻¹' A}).toReal = _ at h
    have he : {z | ∀ g ∈ ({r,1} : Finset G), z ∈ T.act g ⁻¹' A} = A ∩ T.act r ⁻¹' A := by
      ext z
      simp [T.act_one,and_comm]
    rw [he] at h
    have hn : r ∉ ({1} : Finset G) := by simpa using hr₁
    simpa only [Finset.prod_insert hn,Finset.prod_singleton,S.act_one,id_eq] using h
  have hL : MemLp f 2 S.measure := MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hi := hL.integrable (by norm_num)
  have hCorr := integral_affine_half_mul S hi b r
    ((hL.comp_measurePreserving (S.preserves r)).integrable_mul hL)
  change (∫ x, F (S.act r x) * F x ∂S.measure) = _ at hCorr
  rw [hMass,hRet,hCorr,integral_affine_half S hi] at hret
  have hSmall := (abs_lt.mp (hApprox r)).2
  have hStrict : (∫ x, f (S.act r x) * f x ∂S.measure) < -(ε/2) := by linarith [hneg r hr]
  have hLarge : -(ε/2) ≤ (∫ x, f (S.act r x) * f x ∂S.measure) := by
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hb)
    nlinarith [sq_nonneg (b * (∫ x, f x ∂S.measure))]
  exact hStrict.not_ge hLarge

end SixProblems
end

/- Source module SixProblems.OperatorialRecurrenceGaussianKernel. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! Finite-coordinate Gaussian laws and countable projective limits. Adapted from the Apache-2.0 formalization in SharpRecurrence/GaussianProcess.lean. -/


open Function MeasureTheory ProbabilityTheory Set WithLp

open scoped Classical ENNReal NNReal ProbabilityTheory RealInnerProductSpace ComplexConjugate

namespace SixProblems.Gaussian

noncomputable section

variable {Γ : Type*}

private theorem measurable_ereal_toReal : Measurable EReal.toReal := by
  classical
  let s : Set EReal := {⊥, ⊤}ᶜ
  have hs : MeasurableSet s := (measurableSet_singleton _ |>.insert _).compl
  have h := EReal.continuousOn_toReal.measurable_piecewise
    (continuousOn_const (c := (0 : ℝ))) hs
  convert h using 1
  funext x
  change x.toReal = s.piecewise EReal.toReal (fun _ ↦ 0) x
  by_cases hx : x ∈ s
  · rw [Set.piecewise_eq_of_mem s _ _ hx]
  · rw [Set.piecewise_eq_of_notMem s _ _ hx]
    have hbad : x = ⊥ ∨ x = ⊤ := by
      simpa only [s, mem_compl_iff, not_not, mem_insert_iff, mem_singleton_iff] using hx
    rcases hbad with rfl | rfl <;> simp

private def pad (J : Finset Γ) (x : J → ℝ) (i : Γ) : EReal :=
  if hi : i ∈ J then (x ⟨i, hi⟩ : EReal) else 0

private theorem measurable_pad (J : Finset Γ) : Measurable (pad J) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ J
  · simp only [pad, dite_eq_left hi]
    exact continuous_coe_real_ereal.measurable.comp (measurable_pi_apply (⟨i, hi⟩ : J))
  · simp [pad, hi]

private def compactify (I : Finset Γ) (x : I → ℝ) (i : I) : EReal := (x i : EReal)

private theorem measurable_compactify (I : Finset Γ) : Measurable (compactify I) :=
  Measurable.of_eval fun i ↦ continuous_coe_real_ereal.measurable.comp (measurable_pi_apply i)

private theorem continuous_project (I : Finset Γ) :
    Continuous (I.restrict (π := fun _ : Γ ↦ EReal)) :=
  continuous_pi fun i ↦ continuous_apply (i : Γ)

/-- Countable real projective extension, by compactifying each coordinate and applying the
finite intersection property to the closed conditions prescribing the finite marginals. -/
theorem exists_real_projective_limit [Countable Γ] (P : (I : Finset Γ) → Measure (I → ℝ))
    [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : Γ ↦ ℝ) P) :
    ∃ μ : Measure (Γ → ℝ), IsProjectiveLimit (α := fun _ : Γ ↦ ℝ) μ P := by
  classical
  let prob (I : Finset Γ) : ProbabilityMeasure (I → ℝ) := ⟨P I, inferInstance⟩
  let fiber (I : Finset Γ) : Set (ProbabilityMeasure (Γ → EReal)) :=
    {μ | μ.map (I.restrict (π := fun _ ↦ EReal)) = (prob I).map (compactify I)}
  have hclosed (I : Finset Γ) : IsClosed (fiber I) :=
    isClosed_eq (ProbabilityMeasure.continuous_map (continuous_project I)) continuous_const
  have hfinite (D : Finset (Finset Γ)) : (⋂ I ∈ D, fiber I).Nonempty := by
    let J := D.biUnion id
    refine ⟨(prob J).map (pad J), ?_⟩
    simp only [mem_iInter]
    intro I hI
    have hsub : I ⊆ J := Finset.subset_biUnion_of_mem id hI
    change ((prob J).map (pad J)).map (I.restrict (π := fun _ ↦ EReal)) =
      (prob I).map (compactify I)
    apply ProbabilityMeasure.toMeasure_injective
    change ((P J).map (pad J)).map (I.restrict (π := fun _ ↦ EReal)) = (P I).map (compactify I)
    rw [Measure.map_map (continuous_project I).measurable (measurable_pad J)]
    have heq : I.restrict (π := fun _ ↦ EReal) ∘ pad J =
        compactify I ∘ Finset.restrict₂ (π := fun _ ↦ ℝ) hsub := by
      funext x i
      simp [pad, compactify, hsub i.2]
    rw [heq, ← Measure.map_map (measurable_compactify I) (Finset.measurable_restrict₂ hsub),
      ← hP J I hsub]
  obtain ⟨ν, hν⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  let recover (x : Γ → EReal) (i : Γ) : ℝ := (x i).toReal
  have hrecover : Measurable recover :=
    Measurable.of_eval fun i ↦ measurable_ereal_toReal.comp (measurable_pi_apply i)
  refine ⟨(ν : Measure (Γ → EReal)).map recover, ?_⟩
  intro I
  let recoverI (x : I → EReal) (i : I) : ℝ := (x i).toReal
  have hrecoverI : Measurable recoverI :=
    Measurable.of_eval fun i ↦ measurable_ereal_toReal.comp (measurable_pi_apply i)
  have hνI := mem_iInter.mp hν I
  have hνI' := congrArg (fun p : ProbabilityMeasure (I → EReal) ↦ (p : Measure (I → EReal))) hνI
  change (ν : Measure (Γ → EReal)).map (I.restrict (π := fun _ ↦ EReal)) =
    (P I).map (compactify I) at hνI'
  rw [Measure.map_map I.measurable_restrict hrecover,
    show I.restrict (π := fun _ ↦ ℝ) ∘ recover =
      recoverI ∘ I.restrict (π := fun _ ↦ EReal) from rfl,
    ← Measure.map_map hrecoverI (continuous_project I).measurable, hνI',
    Measure.map_map hrecoverI (measurable_compactify I)]
  rw [show recoverI ∘ compactify I = id by funext x i; simp [recoverI, compactify], Measure.map_id]

/-- The centered Gaussian law on a finite set of times, in product coordinates. -/
def finiteGaussianFamily (c : Γ → Γ → ℝ) (I : Finset Γ) : Measure (I → ℝ) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ I)
    (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))).map
      (MeasurableEquiv.toLp 2 (I → ℝ)).symm

instance finiteGaussianFamily_isProbability (c : Γ → Γ → ℝ) (I : Finset Γ) :
    IsProbabilityMeasure (finiteGaussianFamily c I) := by
  unfold finiteGaussianFamily
  infer_instance

private theorem preserving_ofLp (c : Γ → Γ → ℝ) (I : Finset Γ) :
    MeasurePreserving ofLp
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))) (finiteGaussianFamily c I) where
  measurable := by fun_prop
  map_eq := rfl

theorem preserving_toLp (c : Γ → Γ → ℝ) (I : Finset Γ) :
    MeasurePreserving (toLp 2) (finiteGaussianFamily c I)
      (multivariateGaussian (0 : EuclideanSpace ℝ I)
        (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))) where
  measurable := by fun_prop
  map_eq := by
    rw [finiteGaussianFamily, Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

theorem finiteGaussianFamily_projective (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    IsProjectiveMeasureFamily (α := fun _ : Γ ↦ ℝ) (finiteGaussianFamily c) := by
  intro I J hJI
  nth_rw 2 [finiteGaussianFamily]
  rw [Measure.map_map]
  · have h : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ EuclideanSpace.restrict₂ hJI := by ext; simp
    rw [h]
    symm
    have hr := measurePreserving_restrict₂_multivariateGaussian (μ := (0 : EuclideanSpace ℝ I))
      (hc I) hJI
    change MeasurePreserving _ _ (multivariateGaussian (0 : EuclideanSpace ℝ J)
      (Matrix.of fun i j : J ↦ c (i : Γ) (j : Γ))) at hr
    exact ((preserving_ofLp c J).comp hr).map_eq
  · exact Finset.measurable_restrict₂ _
  · fun_prop


/-- Taking any list of coordinates preserves Gaussianity and reindexes the covariance.
    The coordinate map need not be injective. -/
theorem euclideanGaussian_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (k : ι → κ)
    (hk : ∀ i j, B (k i) (k j) = A i j) :
    MeasurePreserving (fun x : EuclideanSpace ℝ κ ↦ toLp 2 (fun i ↦ x (k i)))
      (multivariateGaussian (0 : EuclideanSpace ℝ κ) B)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) A) := by
  let g : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i ↦ EuclideanSpace.proj (k i))
  change MeasurePreserving g _ _
  refine ⟨g.continuous.measurable, ?_⟩
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian, map_zero]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have heval (i : ι) : (fun u ↦ ⟪(EuclideanSpace.basisFun ι ℝ).toBasis i, u⟫) ∘ g =
        fun u ↦ u (k i) := by ext; simp [PiLp.inner_apply, show ∀ x i, g x i = x (k i) from fun _ _ ↦ rfl]
    simp_rw [heval, covariance_eval_multivariateGaussian hB,
      covarianceBilin_multivariateGaussian hA]
    simpa using hk i j
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact g.continuous.measurable.aemeasurable
  · exact IsGaussian.memLp_two_id

/-- The unique countable path law with the prescribed finite centered Gaussian marginals. -/
def pathLaw [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    Measure (Γ → ℝ) :=
  Classical.choose (exists_real_projective_limit (finiteGaussianFamily c)
    (finiteGaussianFamily_projective c hc))

theorem pathLaw_projective [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    IsProjectiveLimit (α := fun _ : Γ ↦ ℝ) (pathLaw c hc) (finiteGaussianFamily c) :=
  Classical.choose_spec (exists_real_projective_limit (finiteGaussianFamily c)
    (finiteGaussianFamily_projective c hc))

instance pathLaw_isProbability [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef) :
    IsProbabilityMeasure (pathLaw c hc) := (pathLaw_projective c hc).isProbabilityMeasure

theorem kernel_posSemidef_tuple (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    {ι : Type*} [Fintype ι] (v : ι → Γ) :
    (Matrix.of fun i j ↦ c (v i) (v j)).PosSemidef := by
  classical
  let I := Finset.univ.image v
  let k : ι → I := fun i ↦ ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  exact (hc I).submatrix k

/-- Every finite list of evaluations has its centered Gaussian law, with repetitions allowed. -/
theorem pathLaw_tuple [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Γ) :
    MeasurePreserving (fun x : Γ → ℝ ↦ toLp 2 (fun i ↦ x (v i))) (pathLaw c hc)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (Matrix.of fun i j ↦ c (v i) (v j))) := by
  classical
  let I := Finset.univ.image v
  let k : ι → I := fun i ↦ ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  have hI : MeasurePreserving (I.restrict (π := fun _ : Γ ↦ ℝ)) (pathLaw c hc)
      (finiteGaussianFamily c I) := ⟨I.measurable_restrict, pathLaw_projective c hc I⟩
  let hr := euclideanGaussian_reindex (kernel_posSemidef_tuple c hc v) (hc I) k (fun _ _ ↦ rfl)
  exact hr.comp ((preserving_toLp c I).comp hI)

/-- A path law is determined by all its finite Gaussian marginals. -/
theorem pathLaw_unique [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (μ : Measure (Γ → ℝ)) (hμ : ∀ (I : Finset Γ),
      μ.map (fun x : Γ → ℝ ↦ toLp 2 (I.restrict x)) =
        multivariateGaussian (0 : EuclideanSpace ℝ I) (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ))) :
    μ = pathLaw c hc := by
  apply IsProjectiveLimit.unique _ (pathLaw_projective c hc)
  intro I
  change μ.map (I.restrict (π := fun _ : Γ ↦ ℝ)) = finiteGaussianFamily c I
  rw [← (preserving_ofLp c I).map_eq, ← hμ I, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Every coordinate change preserving the covariance preserves the whole path law. -/
theorem pathLaw_invariant [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (q : Γ → Γ) (hq : ∀ i j, c (q i) (q j) = c i j) :
    MeasurePreserving (fun x : Γ → ℝ ↦ x ∘ q) (pathLaw c hc) (pathLaw c hc) := by
  have hm : Measurable (fun x : Γ → ℝ ↦ x ∘ q) :=
    Measurable.of_eval fun i ↦ measurable_pi_apply (q i)
  refine ⟨hm, pathLaw_unique c hc _ fun I ↦ ?_⟩
  have h := pathLaw_tuple c hc (fun i : I ↦ q i)
  rw [Measure.map_map (by fun_prop) hm]
  change (pathLaw c hc).map (fun x ↦ toLp 2 (fun i : I ↦ x (q i))) = _
  have hmat : (Matrix.of fun i j : I ↦ c (q i) (q j)) =
      (Matrix.of fun i j : I ↦ c i j) := Matrix.ext fun i j ↦ hq i j
  exact h.map_eq.trans (congrArg (multivariateGaussian (0 : EuclideanSpace ℝ I)) hmat)

/-- A coordinate has the usual real Gaussian law, even when its variance is zero. -/
theorem pathLaw_coordinate [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i : Γ) : MeasurePreserving (fun x : Γ → ℝ ↦ x i) (pathLaw c hc)
      (gaussianReal 0 (c i i).toNNReal) := by
  let a : Unit → Γ := fun _ ↦ i
  have h := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ Unit))
    (kernel_posSemidef_tuple c hc a) (i := ())).comp (pathLaw_tuple c hc a)
  simpa only [a, Function.comp_def, Matrix.of_apply, PiLp.zero_apply] using h

theorem pathLaw_coordinate_memLp [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i : Γ) : MemLp (fun x : Γ → ℝ ↦ x i) 2 (pathLaw c hc) :=
  (IsGaussian.memLp_two_id (μ := gaussianReal 0 (c i i).toNNReal)).comp_measurePreserving
    (pathLaw_coordinate c hc i)

theorem pathLaw_coordinate_mean [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i : Γ) : (∫ x, x i ∂(pathLaw c hc)) = 0 := by
  have h := pathLaw_coordinate c hc i
  rw [← integral_id_gaussianReal (μ := 0) (v := (c i i).toNNReal), ← h.map_eq]
  have hId : AEStronglyMeasurable (fun x : ℝ ↦ x)
      ((pathLaw c hc).map (fun x ↦ x i)) := aestronglyMeasurable_id
  exact (integral_map h.measurable.aemeasurable hId).symm

theorem pathLaw_covariance [Countable Γ] (c : Γ → Γ → ℝ)
    (hc : ∀ I : Finset Γ, (Matrix.of fun i j : I ↦ c (i : Γ) (j : Γ)).PosSemidef)
    (i j : Γ) : (∫ x, x i * x j ∂(pathLaw c hc)) = c i j := by
  let a : Bool → Γ := fun b ↦ if b then i else j
  have hI := pathLaw_tuple c hc a
  have he := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ Bool))
    (kernel_posSemidef_tuple c hc a) true false
  rw [← hI.map_eq, covariance_map] at he
  · simp only [Function.comp_def, a, Bool.false_eq_true, ite_false, ite_true, Matrix.of_apply] at he
    rw [covariance_eq_sub (pathLaw_coordinate_memLp c hc i) (pathLaw_coordinate_memLp c hc j),
      pathLaw_coordinate_mean c hc i, zero_mul, sub_zero] at he
    exact he
  on_goal 3 => exact hI.measurable.aemeasurable
  all_goals fun_prop

end

end SixProblems.Gaussian
end

/- Source module SixProblems.OperatorialRecurrenceGaussian. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



open Function MeasureTheory ProbabilityTheory WithLp
open scoped Classical NNReal ProbabilityTheory

namespace SixProblems

noncomputable section

variable {G : Type*} [Group G]

theorem groupCovariance_posSemidef (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (I : Finset G) :
    (Matrix.of fun i j : I ↦ φ ((i : G)⁻¹ * (j : G))).PosSemidef := by
  simpa only [inv_inv] using hφ.reindex (fun i : I ↦ (i : G)⁻¹)

/-- The left shift on group-indexed real paths. -/
def gaussianShift (g : G) (x : G → ℝ) (i : G) : ℝ := x (g⁻¹ * i)

variable [Countable G]

/-- The real Gaussian path measure with covariance `φ (i⁻¹ * j)`. -/
def gaussianPathMeasure (φ : G → ℝ) (hφ : RealPositiveDefinite φ) : Measure (G → ℝ) :=
  Gaussian.pathLaw (fun i j : G ↦ φ (i⁻¹ * j)) (groupCovariance_posSemidef φ hφ)

instance gaussianPathMeasure_isProbability (φ : G → ℝ) (hφ : RealPositiveDefinite φ) :
    IsProbabilityMeasure (gaussianPathMeasure φ hφ) :=
  Gaussian.pathLaw_isProbability _ _

theorem gaussianShift_preserves (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (g : G) :
    MeasurePreserving (gaussianShift g) (gaussianPathMeasure φ hφ) (gaussianPathMeasure φ hφ) := by
  change MeasurePreserving (fun x : G → ℝ ↦ x ∘ (fun k : G ↦ g⁻¹ * k)) _ _
  apply Gaussian.pathLaw_invariant
  intro i j
  simp [mul_assoc]

/-- The measure-preserving Gaussian translation on the path space. -/
def gaussianPathSystem (φ : G → ℝ) (hφ : RealPositiveDefinite φ) : Mixing.System G (G → ℝ) where
  measure := gaussianPathMeasure φ hφ
  probability := inferInstance
  act := gaussianShift
  act_one := by
    funext x i
    simp [gaussianShift]
  act_mul g h := by
    funext x i
    simp [gaussianShift, mul_assoc]
  preserves := gaussianShift_preserves φ hφ

theorem gaussianPath_tuple (φ : G → ℝ) (hφ : RealPositiveDefinite φ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G) :
    MeasurePreserving (fun x : G → ℝ ↦ toLp 2 (fun i ↦ x (g i))) (gaussianPathMeasure φ hφ)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι)
        (Matrix.of fun i j ↦ φ ((g i)⁻¹ * g j))) :=
  Gaussian.pathLaw_tuple _ _ g

theorem gaussianPath_coordinate_law (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i : G) :
    MeasurePreserving (fun x : G → ℝ ↦ x i) (gaussianPathMeasure φ hφ)
      (gaussianReal 0 (φ 1).toNNReal) := by
  simpa only [gaussianPathMeasure, inv_mul_cancel] using
    Gaussian.pathLaw_coordinate (fun i j : G ↦ φ (i⁻¹ * j)) (groupCovariance_posSemidef φ hφ) i

theorem gaussianPath_coordinate_memLp (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i : G) :
    MemLp (fun x : G → ℝ ↦ x i) 2 (gaussianPathMeasure φ hφ) :=
  Gaussian.pathLaw_coordinate_memLp _ _ i

theorem gaussianPath_coordinate_mean (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i : G) :
    (∫ x, x i ∂(gaussianPathMeasure φ hφ)) = 0 :=
  Gaussian.pathLaw_coordinate_mean _ _ i

theorem gaussianPath_covariance (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (i j : G) :
    (∫ x, x i * x j ∂(gaussianPathMeasure φ hφ)) = φ (i⁻¹ * j) :=
  Gaussian.pathLaw_covariance _ _ i j

/-- Lemma 5.1. Existence and uniqueness of the law are stated for all finite tuples,
    including those with repeated coordinates. -/
theorem lemma5_1 (φ : G → ℝ) (hφ : RealPositiveDefinite φ) :
    ∃ μ : Measure (G → ℝ), IsProbabilityMeasure μ ∧
      (∀ (n : ℕ) (g : Fin n → G), μ.map (fun x ↦ toLp 2 (fun i ↦ x (g i))) =
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
          (Matrix.of fun i j ↦ φ ((g i)⁻¹ * g j))) ∧
      (∀ ν : Measure (G → ℝ),
        (∀ (n : ℕ) (g : Fin n → G), ν.map (fun x ↦ toLp 2 (fun i ↦ x (g i))) =
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            (Matrix.of fun i j ↦ φ ((g i)⁻¹ * g j))) → ν = μ) ∧
      (∀ i j : G, (∫ x, x i * x j ∂μ) = φ (i⁻¹ * j)) ∧
      ∀ a : G, MeasurePreserving (gaussianShift a) μ μ := by
  refine ⟨gaussianPathMeasure φ hφ, inferInstance, fun _ g ↦ (gaussianPath_tuple φ hφ g).map_eq,
    ?_, gaussianPath_covariance φ hφ, gaussianShift_preserves φ hφ⟩
  intro ν hν
  apply Gaussian.pathLaw_unique
  intro I
  let e := Fintype.equivFin I
  let v : Fin (Fintype.card I) → G := fun i ↦ (e.symm i : G)
  let C : G → G → ℝ := fun i j ↦ φ (i⁻¹ * j)
  have hC := groupCovariance_posSemidef φ hφ
  have h := Gaussian.euclideanGaussian_reindex (hC I) (Gaussian.kernel_posSemidef_tuple C hC v)
    e (fun i j ↦ by simp [C, v])
  rw [← h.map_eq, ← hν _ v, Measure.map_map h.measurable (by fun_prop)]
  congr 1
  funext x
  apply PiLp.ext
  intro i
  change x i = x (v (e i))
  simp [v]

end

end SixProblems
end

/- Source module SixProblems.OperatorialRecurrenceGaussianCharacters. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems.Gaussian

noncomputable section

open Filter MeasureTheory ProbabilityTheory WithLp Matrix
open scoped Classical Topology RealInnerProductSpace

variable {G : Type*}

/-- The characteristic-function test of a finite collection of path coordinates. -/
def gaussianCylChar {ι : Type*} [Fintype ι]
    (j : ι → G) (a : ι → ℝ) (x : G → ℝ) : ℂ :=
  Complex.exp (((∑ i, a i * x (j i) : ℝ) : ℂ) * Complex.I)

theorem continuous_gaussianCylChar {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) :
    Continuous (gaussianCylChar j a) := by
  unfold gaussianCylChar
  fun_prop

theorem measurable_gaussianCylChar {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) :
    Measurable (gaussianCylChar j a) := by
  unfold gaussianCylChar
  fun_prop

theorem norm_gaussianCylChar {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) (x : G → ℝ) :
    ‖gaussianCylChar j a x‖ = 1 := by
  simp [gaussianCylChar, Complex.norm_exp, Complex.mul_re]

variable [Group G] [Countable G] (φ : G → ℝ) (hφ : RealPositiveDefinite φ)

/-- The variance associated to a finite Gaussian test. -/
def quadratic {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ k, a i * a k * φ ((j i)⁻¹ * j k)

theorem gaussianCylChar_integral {ι : Type*} [Fintype ι] (j : ι → G) (a : ι → ℝ) :
    (∫ x, gaussianCylChar j a x ∂gaussianPathMeasure φ hφ) =
      Complex.exp (-(quadratic φ j a : ℂ) / 2) := by
  let C : Matrix ι ι ℝ := Matrix.of fun i k ↦ φ ((j i)⁻¹ * j k)
  let a₂ : EuclideanSpace ℝ ι := toLp 2 a
  let ρ := multivariateGaussian (0 : EuclideanSpace ℝ ι) C
  have hC : C.PosSemidef := Gaussian.kernel_posSemidef_tuple
    (fun i k : G ↦ φ (i⁻¹ * k)) (groupCovariance_posSemidef φ hφ) j
  have hQ : a₂ ⬝ᵥ C *ᵥ a₂ = quadratic φ j a := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, quadratic, C, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by
      change a i * (φ ((j i)⁻¹ * j k) * a k) = _
      ring
  have hChar := charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hC a₂
  change charFun ρ a₂ = _ at hChar
  rw [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, hQ, ← neg_div] at hChar
  have hI := gaussianPath_tuple φ hφ j
  change MeasurePreserving _ _ ρ at hI
  rw [← hChar, charFun_apply, ← hI.map_eq,
    integral_map hI.measurable.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  refine ae_of_all _ fun x ↦ ?_
  simp [gaussianCylChar, PiLp.inner_apply, a₂]

omit [Group G] [Countable G] in
theorem gaussianCylChar_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → G) (a : ι → ℝ) (k : κ → G) (b : κ → ℝ) (x : G → ℝ) :
    gaussianCylChar j a x * gaussianCylChar k b x =
      gaussianCylChar (Sum.elim j k) (Sum.elim a b) x := by
  simp [gaussianCylChar, Fintype.sum_sum_type, Complex.ofReal_add, add_mul, Complex.exp_add]

include hφ in
omit [Countable G] in
private theorem quadratic_join {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ι → G) (a : ι → ℝ) (k : κ → G) (b : κ → ℝ) (g : G) :
    quadratic φ (Sum.elim j (fun l ↦ g⁻¹ * k l)) (Sum.elim a b) =
      quadratic φ j a + quadratic φ k b +
        (∑ i, ∑ l, a i * b l * φ ((j i)⁻¹ * g⁻¹ * k l)) +
        ∑ l, ∑ i, b l * a i * φ ((j i)⁻¹ * g⁻¹ * k l) := by
  have h₁ (i : ι) (l : κ) : φ ((g⁻¹ * k l)⁻¹ * j i) = φ ((j i)⁻¹ * g⁻¹ * k l) := by
    rw [← hφ.inv_eq ((j i)⁻¹ * g⁻¹ * k l)]
    simp [mul_assoc]
  have h₂ (i l : κ) : (g⁻¹ * k i)⁻¹ * (g⁻¹ * k l) = (k i)⁻¹ * k l := by group
  simp only [quadratic, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib,
    h₁, h₂]
  simp only [mul_assoc]
  ac_rfl

/-- Vanishing cross covariances yield independence in the limit for finite characteristic
    tests on the Gaussian path. -/
theorem gaussianCylChar_mul_shift_tendsto {ι κ J : Type*} [Fintype ι] [Fintype κ]
    (j : ι → G) (a : ι → ℝ) (k : κ → G) (b : κ → ℝ) (g : J → G) (L : Filter J)
    (hCov : ∀ r s : G, Tendsto (fun z ↦ φ (r * (g z)⁻¹ * s)) L (𝓝 0)) :
    Tendsto (fun z ↦ ∫ x, gaussianCylChar j a x *
      gaussianCylChar k b (gaussianShift (g z) x) ∂gaussianPathMeasure φ hφ) L
      (𝓝 ((∫ x, gaussianCylChar j a x ∂gaussianPathMeasure φ hφ) *
        (∫ x, gaussianCylChar k b x ∂gaussianPathMeasure φ hφ))) := by
  simp_rw [show ∀ (z : J) (x : G → ℝ),
    gaussianCylChar k b (gaussianShift (g z) x) =
      gaussianCylChar (fun l ↦ (g z)⁻¹ * k l) b x from fun _ _ ↦ rfl,
    gaussianCylChar_mul, gaussianCylChar_integral, quadratic_join φ hφ]
  have h₁ : Tendsto (fun z ↦ ∑ i, ∑ l, a i * b l * φ ((j i)⁻¹ * (g z)⁻¹ * k l))
      L (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ ↦ tendsto_finsetSum Finset.univ
        (fun l _ ↦ (tendsto_const_nhds (x := a i * b l)).mul (hCov (j i)⁻¹ (k l))))
  have h₂ : Tendsto (fun z ↦ ∑ l, ∑ i, b l * a i * φ ((j i)⁻¹ * (g z)⁻¹ * k l))
      L (𝓝 0) := by
    simpa only [mul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun l _ ↦ tendsto_finsetSum Finset.univ
        (fun i _ ↦ (tendsto_const_nhds (x := b l * a i)).mul (hCov (j i)⁻¹ (k l))))
  rw [← Complex.exp_add]
  have ht := ((show Continuous (fun s : ℝ ↦ Complex.exp (-(s : ℂ) / 2)) by fun_prop).tendsto
    (quadratic φ j a + quadratic φ k b + 0 + 0)).comp
      (((tendsto_const_nhds (x := quadratic φ j a + quadratic φ k b)).add h₁).add h₂)
  have he : Complex.exp (-(quadratic φ j a : ℂ) / 2 + -(quadratic φ k b : ℂ) / 2) =
      Complex.exp (-((quadratic φ j a + quadratic φ k b : ℝ) : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  simpa only [Function.comp_def, he, add_zero] using ht

end

end SixProblems.Gaussian
end

/- Source module SixProblems.OperatorialRecurrenceGaussianDensity. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Density of finite Gaussian characteristic tests -/


open MeasureTheory Filter
open scoped BigOperators ComplexConjugate Topology ENNReal

namespace SixProblems.Gaussian

/-- A finite list of coordinate indices and real frequencies for a cylindrical character. -/
structure GaussianTest (G : Type*) where
  size : ℕ
  times : Fin size → G
  frequencies : Fin size → ℝ

variable {G : Type*}

/-- A cylindrical character belongs to L² for any finite path measure. -/
theorem GaussianTest.memLp (a : GaussianTest G) (μ : Measure (G → ℝ))
    [IsFiniteMeasure μ] : MemLp (gaussianCylChar a.times a.frequencies) 2 μ :=
  MemLp.of_bound (measurable_gaussianCylChar _ _).aestronglyMeasurable 1
    (.of_forall fun _ ↦ (norm_gaussianCylChar _ _ _).le)

/-- The L² vector associated to a finite Gaussian character. -/
noncomputable def GaussianTest.toVector (a : GaussianTest G) (μ : Measure (G → ℝ))
    [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  (a.memLp μ).toLp _

local notation "Paths" => ((G × ℕ) → Circle)

noncomputable local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private noncomputable def compactGaussianEncoding (x : G → ℝ) (i : G × ℕ) : Circle :=
  Circle.exp (x i.1 / ((i.2 : ℝ) + 1))

private theorem compactGaussianEncoding_continuous : Continuous (compactGaussianEncoding (G := G)) := by
  refine continuous_pi fun i ↦ ?_
  have hi : Continuous (fun x : G → ℝ ↦ x i.1) := continuous_apply i.1
  exact Circle.exp.continuous.comp (hi.div_const ((i.2 : ℝ) + 1))

private theorem compactGaussianEncoding_injective : Function.Injective
    (compactGaussianEncoding (G := G)) := by
  intro x y h
  funext i
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (|x i| + |y i|) / Real.pi)
  let d : ℝ := N + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hπ := Real.pi_pos
  have hb := (div_lt_iff₀ hπ).mp hN
  have hxd : |x i| ≤ (Real.pi / 2) * d := by
    dsimp only [d]
    nlinarith [abs_nonneg (y i)]
  have hyd : |y i| ≤ (Real.pi / 2) * d := by
    dsimp only [d]
    nlinarith [abs_nonneg (x i)]
  have hx : x i / d ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rcases abs_le.mp hxd with ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hd).mpr (by linarith only [hl]), (div_le_iff₀ hd).mpr hu⟩
  have hy : y i / d ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rcases abs_le.mp hyd with ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hd).mpr (by linarith only [hl]), (div_le_iff₀ hd).mpr hu⟩
  have he : Circle.exp (x i / d) = Circle.exp (y i / d) := congrFun h (i, N)
  have hEq := Circle.exp_injOn_Icc (a := -(Real.pi / 2)) (b := Real.pi / 2)
    (by linarith) hx hy he
  exact mul_right_cancel₀ hd.ne' ((div_eq_div_iff hd.ne' hd.ne').mp hEq)

section Pullback

variable [Countable G]

private theorem compactGaussianEncoding_embedding : MeasurableEmbedding
    (compactGaussianEncoding (G := G)) :=
  compactGaussianEncoding_continuous.measurableEmbedding compactGaussianEncoding_injective

variable (μ : Measure (G → ℝ)) [IsProbabilityMeasure μ]

private noncomputable def compactGaussianMeasure : Measure Paths :=
  μ.map compactGaussianEncoding

private instance : IsProbabilityMeasure (compactGaussianMeasure μ) :=
  (Measure.isProbabilityMeasure_map_iff compactGaussianEncoding_embedding.measurable.aemeasurable).mpr
    inferInstance

omit [IsProbabilityMeasure μ] in
private theorem compactGaussianEncoding_preserving :
    MeasurePreserving compactGaussianEncoding μ (compactGaussianMeasure μ) :=
  ⟨compactGaussianEncoding_embedding.measurable, rfl⟩

omit [IsProbabilityMeasure μ] in
private theorem compactGaussianRecovery_preserving :
    MeasurePreserving compactGaussianEncoding_embedding.invFun (compactGaussianMeasure μ)
      μ := by
  refine ⟨compactGaussianEncoding_embedding.measurable_invFun, ?_⟩
  rw [compactGaussianMeasure, Measure.map_map compactGaussianEncoding_embedding.measurable_invFun
    compactGaussianEncoding_embedding.measurable,
    compactGaussianEncoding_embedding.leftInverse_invFun.comp_eq_id, Measure.map_id]

private noncomputable def compactGaussianPullback :
    Lp ℂ 2 (compactGaussianMeasure μ) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (compactGaussianEncoding_preserving μ)

omit [IsProbabilityMeasure μ] in
private theorem compactGaussianPullback_surjective : Function.Surjective (compactGaussianPullback μ) := by
  intro f
  refine ⟨Lp.compMeasurePreserving _ (compactGaussianRecovery_preserving μ) f, ?_⟩
  change Lp.compMeasurePreserving _ (compactGaussianEncoding_preserving μ)
    (Lp.compMeasurePreserving _ (compactGaussianRecovery_preserving μ) f) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h (x : G → ℝ) : (compactGaussianEncoding_embedding.invFun ∘ compactGaussianEncoding) x = x :=
    compactGaussianEncoding_embedding.leftInverse_invFun x
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving f
    ((compactGaussianRecovery_preserving μ).comp (compactGaussianEncoding_preserving μ))).trans
      (.of_forall fun x ↦ congrArg f (h x))

end Pullback

local notation "Letter" => ((G × ℕ) × ℤ)

private noncomputable def compactCoordinatePower (a : Letter) : C(Paths, ℂ) where
  toFun x := (x a.1 ^ a.2 : Circle)
  continuous_toFun := by fun_prop

private noncomputable def compactGaussianWord (w : List Letter) : C(Paths, ℂ) :=
  (w.map compactCoordinatePower).prod

private theorem compactGaussianWord_append (u v : List Letter) :
    compactGaussianWord (u ++ v) = compactGaussianWord u * compactGaussianWord v := by
  simp [compactGaussianWord, List.prod_append]

private def flipLetter (a : Letter) : Letter := (a.1, -a.2)

private theorem compactCoordinatePower_star (a : Letter) :
    star (compactCoordinatePower a) = compactCoordinatePower (flipLetter a) := by
  ext z
  change star ((z a.1 ^ a.2 : Circle) : ℂ) = ((z a.1 ^ (-a.2) : Circle) : ℂ)
  rw [zpow_neg, Circle.coe_inv_eq_conj, starRingEnd_apply]

private theorem compactGaussianWord_star (w : List Letter) :
    star (compactGaussianWord w) = compactGaussianWord (w.map flipLetter) := by
  induction w with
  | nil => simp [compactGaussianWord]
  | cons a w ih =>
    change star (compactCoordinatePower a * compactGaussianWord w) =
      compactCoordinatePower (flipLetter a) * compactGaussianWord (w.map flipLetter)
    rw [star_mul, compactCoordinatePower_star, ih, mul_comm]

private noncomputable def compactGaussianAlgebra : StarSubalgebra ℂ C(Paths, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range compactGaussianWord)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range compactGaussianWord) ≤
      star (Algebra.adjoin ℂ (Set.range compactGaussianWord))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨w, rfl⟩
    exact Algebra.subset_adjoin ⟨w.map flipLetter, (compactGaussianWord_star w).symm⟩

private theorem compactGaussianAlgebra_separates :
    (compactGaussianAlgebra (G := G)).SeparatesPoints := by
  intro x y h
  obtain ⟨i, hi⟩ := not_forall.mp (fun he ↦ h (funext he))
  refine ⟨_, ⟨compactGaussianWord [(i, 1)], Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
  change ((x i ^ (1 : ℤ) : Circle) : ℂ) * 1 ≠ ((y i ^ (1 : ℤ) : Circle) : ℂ) * 1
  simp only [zpow_one, mul_one]
  exact fun he ↦ hi (Subtype.ext he)

private theorem compactGaussianWords_span :
    (Submodule.span ℂ (Set.range (compactGaussianWord (G := G)))).topologicalClosure = ⊤ := by
  have hs : (compactGaussianAlgebra (G := G)).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range compactGaussianWord) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Set.Subset.trans (fun _ hx ↦ ?_) Submodule.subset_span
    refine Submonoid.closure_induction (fun _ h ↦ h) ⟨[], rfl⟩ ?_ hx
    rintro _ _ _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u ++ v, compactGaussianWord_append u v⟩
  rw [← hs]
  exact congrArg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      compactGaussianAlgebra_separates)

private noncomputable def wordTest (w : List Letter) : GaussianTest G where
  size := w.length
  times i := (w.get i).1.1
  frequencies i := ((w.get i).2 : ℝ) / (((w.get i).1.2 : ℝ) + 1)

private theorem compactGaussianWord_encode (w : List Letter) (x : G → ℝ) :
    compactGaussianWord w (compactGaussianEncoding x) =
      gaussianCylChar (wordTest w).times (wordTest w).frequencies x := by
  have hget : w.map compactCoordinatePower = List.ofFn (fun i ↦ compactCoordinatePower (w.get i)) := by
    change w.map compactCoordinatePower = List.ofFn (compactCoordinatePower ∘ w.get)
    rw [← List.map_ofFn, List.ofFn_get]
  rw [compactGaussianWord, hget, List.prod_ofFn]
  simp only [ContinuousMap.prod_apply, compactCoordinatePower, ContinuousMap.coe_mk,
    compactGaussianEncoding, Circle.coe_zpow, Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_sum]
  unfold gaussianCylChar
  congr 1
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  unfold wordTest
  push_cast
  ring

variable [Countable G] (μ : Measure (G → ℝ)) [IsProbabilityMeasure μ]

/-- The Gaussian cylindrical test vectors span a dense subspace of the full complex L² space. -/
theorem gaussianTestVectors_dense :
    (Submodule.span ℂ (Set.range (fun a : GaussianTest G => a.toVector μ))).topologicalClosure = ⊤ := by
  let L := ContinuousMap.toLp (E := ℂ) 2 (compactGaussianMeasure μ) ℂ
  have hLdense : DenseRange L :=
    ContinuousMap.toLp_denseRange ℂ (compactGaussianMeasure μ) ℂ (by norm_num : (2 : ENNReal) ≠ ⊤)
  have ht := hLdense.topologicalClosure_map_submodule compactGaussianWords_span
  have hPullback : DenseRange (compactGaussianPullback μ).toContinuousLinearMap :=
    (compactGaussianPullback_surjective μ).denseRange
  have hu := hPullback.topologicalClosure_map_submodule ht
  have hIncluded : ((Submodule.span ℂ (Set.range compactGaussianWord)).map L.toLinearMap).map
      (compactGaussianPullback μ).toLinearMap ≤ Submodule.span ℂ (Set.range (fun a : GaussianTest G => a.toVector μ)) := by
    rw [Submodule.map_span, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨_, ⟨w, rfl⟩, rfl⟩, rfl⟩
    refine ⟨wordTest w, ?_⟩
    apply Lp.ext
    refine ((wordTest w).memLp μ).coeFn_toLp.trans ?_
    have hc := (Lp.coeFn_compMeasurePreserving (L (compactGaussianWord w))
      (compactGaussianEncoding_preserving μ)).trans
      ((compactGaussianEncoding_preserving μ).quasiMeasurePreserving.ae_eq_comp
        (ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) (compactGaussianMeasure μ) (compactGaussianWord w)))
    have hw : gaussianCylChar (wordTest w).times (wordTest w).frequencies =ᵐ[μ]
        (fun x ↦ compactGaussianWord w (compactGaussianEncoding x)) :=
      .of_forall fun x ↦ (compactGaussianWord_encode w x).symm
    exact hw.trans hc.symm
  have hle := Submodule.topologicalClosure_mono hIncluded
  change ((Submodule.span ℂ (Set.range compactGaussianWord)).map L.toLinearMap
    |>.map (compactGaussianPullback μ).toLinearMap).topologicalClosure = ⊤ at hu
  rw [hu] at hle
  exact le_antisymm le_top hle

end SixProblems.Gaussian
end

/- Source module Mixing.WeakOperatorCompactness. -/
section
/-!
# Weak operator compactness for Hilbert-space contractions

Transport Banach–Alaoglu through the Riesz isometry for the vector balls.
The product of the vector balls is compact, and the equations for a
linear operator cut out a closed subset.
-/


open Set
open scoped ComplexConjugate Topology

namespace Mixing

section HilbertBalls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isCompact_weakHilbert_ball (r : ℝ) :
    IsCompact {u : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm u‖ ≤ r} := by
  let R := InnerProductSpace.toDual ℂ E
  let inverse (f : WeakDual ℂ E) : WeakSpace ℂ E :=
    toWeakSpace ℂ E (R.symm (WeakDual.toStrongDual f))
  have hcont : Continuous inverse := by
    apply WeakBilin.continuous_of_continuous_eval
    intro y
    let v := R.symm y
    have h (f : WeakDual ℂ E) : y (R.symm (WeakDual.toStrongDual f)) = conj (f v) := by
      calc
        _ = inner ℂ v (R.symm (WeakDual.toStrongDual f)) :=
          InnerProductSpace.toDual_symm_apply.symm
        _ = conj (inner ℂ (R.symm (WeakDual.toStrongDual f)) v) :=
          (inner_conj_symm v _).symm
        _ = conj (f v) := congrArg (starRingEnd ℂ)
          (InnerProductSpace.toDual_symm_apply (x := v) (y := WeakDual.toStrongDual f))
    change Continuous (fun f : WeakDual ℂ E ↦ y (R.symm (WeakDual.toStrongDual f)))
    simp_rw [h]
    exact Complex.continuous_conj.comp (WeakBilin.eval_continuous _ v)
  have hset : inverse '' (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 r) =
      {u : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm u‖ ≤ r} := by
    ext u
    constructor
    · rintro ⟨f, hf, rfl⟩
      change dist (WeakDual.toStrongDual f) 0 ≤ r at hf
      change ‖R.symm (WeakDual.toStrongDual f)‖ ≤ r
      rw [R.symm.norm_map]
      rwa [dist_zero_right] at hf
    · intro hu
      let x := (toWeakSpace ℂ E).symm u
      refine ⟨(R x).toWeakDual, ?_, ?_⟩
      · change dist (R x) 0 ≤ r
        rw [dist_zero_right, R.norm_map]
        exact hu
      · change toWeakSpace ℂ E (R.symm (R x)) = u
        rw [R.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rw [← hset]
  exact (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) r).image hcont

end HilbertBalls

section OperatorBalls

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A weakly compact vector ball at every radius gives weak operator
compactness of each operator ball. -/
theorem isCompact_wot_operatorBall_of_compact_vectorBalls (R : ℝ) (hR : 0 ≤ R)
    (hballs : ∀ r : ℝ, IsCompact {u : WeakSpace ℂ E | ‖(toWeakSpace ℂ E).symm u‖ ≤ r}) :
    IsCompact {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ R} := by
  let ball (x : E) : Set (WeakSpace ℂ E) := {u | ‖(toWeakSpace ℂ E).symm u‖ ≤ R * ‖x‖}
  let addEq (x y : E) : Set (E → WeakSpace ℂ E) := {u | u (x + y) = u x + u y}
  let smulEq (c : ℂ) (x : E) : Set (E → WeakSpace ℂ E) := {u | u (c • x) = c • u x}
  let equations := (⋂ x, ⋂ y, addEq x y) ∩ (⋂ c, ⋂ x, smulEq c x)
  let good := Set.pi Set.univ ball ∩ equations
  have hEq : IsClosed equations := by
    apply IsClosed.inter
    · exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))
    · exact isClosed_iInter fun c ↦ isClosed_iInter fun x ↦
        isClosed_eq (continuous_apply (c • x)) ((continuous_apply x).const_smul c)
  have hcompact : IsCompact good :=
    (isCompact_univ_pi fun x ↦ hballs (R * ‖x‖)).inter_right hEq
  have hbound (u : good) (x : E) : ‖(toWeakSpace ℂ E).symm (u.val x)‖ ≤ R * ‖x‖ :=
    u.property.1 x (mem_univ x)
  let linear (u : good) : E →ₗ[ℂ] E :=
    { toFun := fun x ↦ (toWeakSpace ℂ E).symm (u.val x)
      map_add' := fun x y ↦ by
        have h : u.val (x + y) = u.val x + u.val y :=
          mem_iInter.1 (mem_iInter.1 u.property.2.1 x) y
        rw [h, map_add]
      map_smul' := fun c x ↦ by
        have h : u.val (c • x) = c • u.val x :=
          mem_iInter.1 (mem_iInter.1 u.property.2.2 c) x
        rw [h, map_smul]
        rfl }
  let operator (u : good) : E →WOT[ℂ] E :=
    ContinuousLinearMapWOT.ofCLM ((linear u).mkContinuous R (hbound u))
  have hcont : Continuous operator := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro x f
    change Continuous (fun u : good ↦ f ((toWeakSpace ℂ E).symm (u.val x)))
    exact (WeakBilin.eval_continuous (topDualPairing ℂ E).flip f).comp
      ((continuous_apply x).comp continuous_subtype_val)
  have hsurj : Set.range operator = {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨u, rfl⟩
      exact ContinuousLinearMap.opNorm_le_bound _ hR (hbound u)
    · intro hT
      have hT' : ‖T.toCLM‖ ≤ R := hT
      let u (x : E) := toWeakSpace ℂ E (T x)
      have hu : u ∈ good := by
        refine ⟨fun x _ ↦ ?_, ?_, ?_⟩
        · change ‖(toWeakSpace ℂ E).symm (toWeakSpace ℂ E (T x))‖ ≤ R * ‖x‖
          rw [LinearEquiv.symm_apply_apply]
          exact T.toCLM.le_of_opNorm_le hT' x
        · exact mem_iInter.2 fun x ↦ mem_iInter.2 fun y ↦ by
            change u (x + y) = u x + u y
            simp [u, map_add]
        · exact mem_iInter.2 fun c ↦ mem_iInter.2 fun x ↦ by
            change u (c • x) = c • u x
            simp [u, map_smul]
      refine ⟨⟨u, hu⟩, ?_⟩
      apply ContinuousLinearMapWOT.toCLM_injective
      apply ContinuousLinearMap.ext
      intro x
      exact (toWeakSpace ℂ E).symm_apply_apply (T x)
  let : CompactSpace good := isCompact_iff_compactSpace.mp hcompact
  rw [← hsurj]
  exact isCompact_range hcont

end OperatorBalls

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem isCompact_wot_contractions :
    IsCompact {T : E →WOT[ℂ] E | ‖T.toCLM‖ ≤ 1} :=
  isCompact_wot_operatorBall_of_compact_vectorBalls 1 zero_le_one isCompact_weakHilbert_ball

end Mixing
end

/- Source module Mixing.UltrafilterAction. -/
section
/-!
# The ultrafilter operator action

The paper uses additive notation for its group. Here the group law is written
multiplicatively, so that the paper's `p+q` appears as `p*q`.
-/


open Filter Set
open scoped ComplexConjugate Topology

namespace Mixing

noncomputable section

/-- The Stone–Čech product on ultrafilters of a discrete semigroup. -/
scoped instance ultrafilterSemigroup {S : Type*} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

/-- Evaluation of the Stone–Čech extension gives the ultrafilter limit. -/
theorem tendsto_ultrafilterExtend {S T : Type*} [TopologicalSpace T] [T2Space T]
    [CompactSpace T] (f : S → T) (p : Ultrafilter S) :
    Tendsto f (p : Filter S) (𝓝 (Ultrafilter.extend f p)) :=
  ultrafilter_extend_eq_iff.mp rfl

/-- The extension of a homomorphism to a compact Hausdorff semitopological
semigroup preserves multiplication. -/
theorem ultrafilterExtend_mul {S T : Type*} [Semigroup S] [Semigroup T] [TopologicalSpace T]
    [T2Space T] [CompactSpace T] (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T) (p q : Ultrafilter S) :
    Ultrafilter.extend f (p * q) = Ultrafilter.extend f p * Ultrafilter.extend f q := by
  apply ultrafilter_extend_eq_iff.mpr
  change Tendsto f ((p * q : Ultrafilter S) : Filter S) _
  rw [Filter.tendsto_def]
  intro neighborhood hNeighborhood
  obtain ⟨V, hSubset, hOpen, hProduct⟩ := mem_nhds_iff.mp hNeighborhood
  change ∀ᶠ s in ((p * q : Ultrafilter S) : Filter S), f s ∈ neighborhood
  rw [Ultrafilter.eventually_mul]
  have hOuter : ∀ᶠ x in (p : Filter S), f x * Ultrafilter.extend f q ∈ V :=
    (((continuousRight _).tendsto _).comp (tendsto_ultrafilterExtend f p)).eventually
      (hOpen.mem_nhds hProduct)
  filter_upwards [hOuter] with x hx
  have hInner : ∀ᶠ y in (q : Filter S), f x * f y ∈ V :=
    (((continuousLeft _).tendsto _).comp (tendsto_ultrafilterExtend f q)).eventually
      (hOpen.mem_nhds hx)
  filter_upwards [hInner] with y hy
  rw [map_mul]
  exact hSubset hy

section Operators

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The original unitary action as a homomorphism into continuous linear maps. -/
def linearRepresentation (U : G →* (H ≃ₗᵢ[ℂ] H)) : G →ₙ* (H →L[ℂ] H) where
  toFun g := (U g).toContinuousLinearEquiv.toContinuousLinearMap
  map_mul' g h := by
    ext x
    change U (g * h) x = U g (U h x)
    rw [map_mul]
    rfl

/-- The original unitary action viewed in the weak operator topology. -/
def weakRepresentation (U : G →* (H ≃ₗᵢ[ℂ] H)) : G →ₙ* (H →WOT[ℂ] H) :=
  ContinuousLinearMapWOT.ringEquiv.symm.toMulHom.comp (linearRepresentation U)

/-- The weak operator closure of the original unitary action as a semigroup. -/
def weakOperatorClosure (U : G →* (H ≃ₗᵢ[ℂ] H)) : Subsemigroup (H →WOT[ℂ] H) :=
  (weakRepresentation U).srange.topologicalClosure

/-- The canonical map from the group into the weak operator closure. -/
def weakClosureInclusion (U : G →* (H ≃ₗᵢ[ℂ] H)) : G →ₙ* weakOperatorClosure U :=
  (weakRepresentation U).codRestrict (weakOperatorClosure U) fun g => subset_closure ⟨g, rfl⟩

/-- Equation (4), the weak operator closure is commutative for an abelian group. -/
theorem weakOperatorClosure_commutative [IsMulCommutative G]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) : IsMulCommutative (weakOperatorClosure U) := by
  have : IsMulCommutative (weakRepresentation U).srange := by
    apply IsMulCommutative.of_setLike_mul_comm
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm' a b]
  exact inferInstanceAs (IsMulCommutative (weakRepresentation U).srange.topologicalClosure)

variable [CompleteSpace H] (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- Equation (4), the weak operator closure of the representation is compact. -/
theorem weakOperatorClosure_isCompact : IsCompact (weakOperatorClosure U : Set (H →WOT[ℂ] H)) :=
  isCompact_wot_contractions.of_isClosed_subset isClosed_closure
    (closure_minimal (by
      rintro _ ⟨g, rfl⟩
      change ‖linearRepresentation U g‖ ≤ 1
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        change ‖U g x‖ ≤ 1 * ‖x‖
        rw [LinearIsometryEquiv.norm_map, one_mul]) isCompact_wot_contractions.isClosed)

instance weakOperatorClosure_compactSpace : CompactSpace (weakOperatorClosure U) :=
  isCompact_iff_compactSpace.mp (weakOperatorClosure_isCompact U)

/-- The weak operator ultrafilter limit, denoted by `U^p` in the paper. -/
noncomputable def ultrafilterOperator (p : Ultrafilter G) : H →L[ℂ] H :=
  (Ultrafilter.extend (weakClosureInclusion U) p).1.toCLM

/-- The ultrafilter action is the weak operator limit of the original representation. -/
theorem tendsto_ultrafilterOperator (p : Ultrafilter G) :
    Tendsto (weakRepresentation U) (p : Filter G)
      (𝓝 (ContinuousLinearMapWOT.ofCLM (ultrafilterOperator U p))) :=
  (continuous_subtype_val.tendsto _).comp (tendsto_ultrafilterExtend (weakClosureInclusion U) p)

/-- The coefficient formula for the weak operator ultrafilter limit. -/
theorem tendsto_ultrafilterOperator_coeff (p : Ultrafilter G) (x y : H) :
    Tendsto (fun g => inner ℂ x (U g y)) (p : Filter G)
      (𝓝 (inner ℂ x (ultrafilterOperator U p y))) := by
  exact ((ContinuousLinearMapWOT.continuous_dual_apply y
    (InnerProductSpace.toDual ℂ H x)).tendsto _).comp (tendsto_ultrafilterOperator U p)

/-- Every operator in the ultrafilter action is contractive. -/
theorem ultrafilterOperator_norm_le_one (p : Ultrafilter G) : ‖ultrafilterOperator U p‖ ≤ 1 := by
  apply closure_minimal _ (isCompact_wot_contractions (E := H)).isClosed
    (Ultrafilter.extend (weakClosureInclusion U) p).2
  rintro _ ⟨g, rfl⟩
  change ‖linearRepresentation U g‖ ≤ 1
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    change ‖U g x‖ ≤ 1 * ‖x‖
    rw [LinearIsometryEquiv.norm_map, one_mul]

/-- Equation (5), the homomorphism law for ultrafilter operators. -/
theorem ultrafilterOperator_mul (p q : Ultrafilter G) :
    ultrafilterOperator U (p * q) = ultrafilterOperator U p * ultrafilterOperator U q := by
  unfold ultrafilterOperator
  rw [ultrafilterExtend_mul continuous_const_mul continuous_mul_const]
  rfl

/-- The ultrafilter obtained by applying group inversion, denoted by `-p` in the paper. -/
def inverseUltrafilter (p : Ultrafilter G) : Ultrafilter G := p.map Inv.inv

/-- Proposition 2(i), inversion of an ultrafilter corresponds to the Hilbert adjoint. -/
theorem ultrafilterOperator_inverse (p : Ultrafilter G) :
    ultrafilterOperator U (inverseUltrafilter p) = (ultrafilterOperator U p).adjoint := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  have hInv := tendsto_ultrafilterOperator_coeff U (inverseUltrafilter p) x y
  have hInv' : Tendsto (fun g : G => inner ℂ x (U g⁻¹ y)) (p : Filter G)
      (𝓝 (inner ℂ x (ultrafilterOperator U (inverseUltrafilter p) y))) :=
    hInv.comp tendsto_map
  have hc := (Complex.continuous_conj.tendsto _).comp (tendsto_ultrafilterOperator_coeff U p y x)
  have hEq (g : G) : inner ℂ x (U g⁻¹ y) = conj (inner ℂ y (U g x)) := by
    rw [inner_conj_symm, map_inv]
    change inner ℂ x (((U g).symm : H →L[ℂ] H) y) = _
    rw [← LinearIsometryEquiv.adjoint_eq_symm]
    exact ContinuousLinearMap.adjoint_inner_right (U g : H →L[ℂ] H) x y
  simp only [hEq] at hInv'
  rw [inner_conj_symm, ← (ContinuousLinearMap.adjoint_inner_right (ultrafilterOperator U p) x y)] at hc
  exact tendsto_nhds_unique hInv' hc

/-- Proposition 2(i), all operators in the action of an abelian group are normal. -/
theorem ultrafilterOperator_normal [IsMulCommutative G] (p : Ultrafilter G) :
    IsStarNormal (ultrafilterOperator U p) := by
  constructor
  change (ultrafilterOperator U p).adjoint * ultrafilterOperator U p =
    ultrafilterOperator U p * (ultrafilterOperator U p).adjoint
  rw [← ultrafilterOperator_inverse U p]
  let _ := weakOperatorClosure_commutative U
  exact congrArg (fun T : weakOperatorClosure U => T.1.toCLM)
    (mul_comm' (Ultrafilter.extend (weakClosureInclusion U) (inverseUltrafilter p))
      (Ultrafilter.extend (weakClosureInclusion U) p))

omit [CompleteSpace H] in
/-- Any two ultrafilter operators commute for an abelian group. -/
theorem ultrafilterOperator_commute_pair [IsMulCommutative G] (p q : Ultrafilter G) :
    Commute (ultrafilterOperator U p) (ultrafilterOperator U q) := by
  let _ := weakOperatorClosure_commutative U
  exact congrArg (fun T : weakOperatorClosure U => T.1.toCLM)
    (mul_comm' (Ultrafilter.extend (weakClosureInclusion U) p)
      (Ultrafilter.extend (weakClosureInclusion U) q))

/-- A representation is `𝒰`-mixing if all operators corresponding to `p ∈ 𝒰` vanish. -/
def IsUMixing (P : Set (Ultrafilter G)) : Prop :=
  ∀ p ∈ P, ultrafilterOperator U p = 0

end Operators

end

end Mixing
end

/- Source module Mixing.NormalOperator. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Normal operators and the image–kernel decomposition -/


open ContinuousLinearMap
open scoped InnerProductSpace

namespace Mixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 4, equation (1). The image is the algebraic range of a bounded operator. -/
theorem normal_range_orthogonal (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    T.rangeᗮ = T.ker :=
  hT.orthogonal_range

/-- Lemma 4, equation (2). The norm closure of the image and the kernel are complementary. -/
theorem normal_rangeClosure_isCompl_ker (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    IsCompl T.range.topologicalClosure T.ker := by
  rw [← normal_range_orthogonal T hT, ← T.range.orthogonal_orthogonal_eq_closure]
  exact T.rangeᗮ.isCompl_orthogonal.symm

/-- Lemma 5, with the span of the union of the ranges written as an indexed supremum. -/
theorem normal_iInf_ker_orthogonal {ι : Type*} (T : ι → (H →L[ℂ] H))
    (hT : ∀ i, IsStarNormal (T i)) :
    (⨅ i, (T i).ker)ᗮ = (⨆ i, (T i).range).topologicalClosure := by
  simp_rw [← normal_range_orthogonal (T _) (hT _)]
  rw [Submodule.iInf_orthogonal, Submodule.orthogonal_orthogonal_eq_closure]

/-- Lemma 5 in the closed-linear-span form stated in the paper. -/
theorem normal_iInf_ker_orthogonal_eq_span {ι : Type*} (T : ι → (H →L[ℂ] H))
    (hT : ∀ i, IsStarNormal (T i)) :
    (⨅ i, (T i).ker)ᗮ =
      (Submodule.span ℂ (⋃ i, ((T i).range : Set H))).topologicalClosure := by
  simpa only [Submodule.span_iUnion, Submodule.span_eq] using normal_iInf_ker_orthogonal T hT

/-- Operators with the same kernel have this kernel for their product if the right
factor is normal. -/
theorem ker_mul_eq_ker_of_right_normal {A B : H →L[ℂ] H}
    (hB : IsStarNormal B) (hAB : A.ker = B.ker) :
    (A * B).ker = B.ker := by
  ext x
  change A (B x) = 0 ↔ B x = 0
  constructor
  · intro h
    have h₁ : B x ∈ B.range := ⟨x, rfl⟩
    have h₂ : B x ∈ B.rangeᗮ := by
      rw [normal_range_orthogonal B hB, ← hAB]
      exact h
    exact (Submodule.disjoint_def.mp B.range.orthogonal_disjoint) (B x) h₁ h₂
  · intro h
    rw [h, map_zero]

/-- Proposition 2(ii) for positive powers. -/
theorem normal_ker_pow (T : H →L[ℂ] H) (hT : IsStarNormal T) {n : ℕ} (hn : 0 < n) :
    (T ^ n).ker = T.ker := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  clear hn
  induction k with
  | zero => exact congrArg (fun A : H →L[ℂ] H ↦ A.ker) (pow_one T)
  | succ k ih =>
    rw [pow_succ]
    exact ker_mul_eq_ker_of_right_normal hT ih

/-- Proposition 2(ii) in its adjoint–operator–power form. -/
theorem normal_ker_adjoint_ker_pow (T : H →L[ℂ] H) (hT : IsStarNormal T) {n : ℕ}
    (hn : 0 < n) :
    T.adjoint.ker = T.ker ∧ T.ker = (T ^ n).ker :=
  ⟨hT.ker_adjoint_eq_ker, (normal_ker_pow T hT hn).symm⟩

/-- Proposition 2(ii) for positive total degree in an operator and its adjoint. -/
theorem normal_ker_mul_adjoint_pow (T : H →L[ℂ] H) (hT : IsStarNormal T) {n m : ℕ}
    (h : 1 ≤ n + m) :
    (T ^ n * T.adjoint ^ m).ker = T.ker := by
  let _ : IsStarNormal T := hT
  have hAdj : IsStarNormal T.adjoint := ContinuousLinearMap.star_eq_adjoint T ▸ inferInstance
  by_cases hn : n = 0
  · subst n
    have hm : 0 < m := by omega
    rw [pow_zero, one_mul, normal_ker_pow _ hAdj hm]
    exact hT.ker_adjoint_eq_ker
  · by_cases hm : m = 0
    · subst m
      simpa only [pow_zero, mul_one] using normal_ker_pow T hT (Nat.pos_of_ne_zero hn)
    · have hRight : (T.adjoint ^ m).ker = T.ker :=
        (normal_ker_pow _ hAdj (Nat.pos_of_ne_zero hm)).trans hT.ker_adjoint_eq_ker
      let _ : IsStarNormal T.adjoint := hAdj
      rw [ker_mul_eq_ker_of_right_normal inferInstance
          ((normal_ker_pow T hT (Nat.pos_of_ne_zero hn)).trans hRight.symm), hRight]

/-- The operator fact used in Lemma 7. An idempotent contraction is self-adjoint. -/
theorem isSelfAdjoint_of_idempotent_contraction (T : H →L[ℂ] H)
    (hIdem : T * T = T) (hNorm : ‖T‖ ≤ 1) : IsSelfAdjoint T := by
  have hAdjNorm : ‖T.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hNorm
  have hApply (x : H) : T (T x) = T x :=
    congrArg (fun A : H →L[ℂ] H ↦ A x) hIdem
  have hEq (x : H) : T.adjoint (T x) = T x := by
    have hle := T.adjoint.le_of_opNorm_le hAdjNorm (T x)
    rw [one_mul] at hle
    have hInner : ⟪T.adjoint (T x), T x⟫_ℂ = ⟪T x, T x⟫_ℂ := by
      rw [T.adjoint_inner_left, hApply]
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hExp := norm_sub_sq (𝕜 := ℂ) (T.adjoint (T x)) (T x)
    rw [hInner, inner_self_eq_norm_sq] at hExp
    have hsq := pow_le_pow_left₀ (norm_nonneg (T.adjoint (T x))) hle 2
    nlinarith
  have he : T = star T * T := by
    ext x
    exact (hEq x).symm
  exact he ▸ IsSelfAdjoint.star_mul_self T

end Mixing
end

/- Source module Mixing.MixingFamilies. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-!
# Equivalent families for mixing

Proposition 3 of arXiv:2604.12915v2.
-/


open Filter Set
open scoped Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (P : Set (Ultrafilter G))

/-- A string of `n+1` factors taken from the family. The recursion starts at one
because an ultrafilter semigroup has no need of an identity for this construction. -/
def ultrafilterProductsSucc (P : Set (Ultrafilter G)) : ℕ → Set (Ultrafilter G)
  | 0 => P
  | n + 1 => {r | ∃ p ∈ ultrafilterProductsSucc P n, ∃ q ∈ P, r = p * q}

/-- The family of all inverse–original pairs, written Δ in the paper. -/
def ultrafilterDelta : Set (Ultrafilter G) :=
  (fun p => inverseUltrafilter p * p) '' P

/-- The unsigned and inverse ultrafilters generate this semigroup. -/
def signedUltrafilterSemigroup : Subsemigroup (Ultrafilter G) :=
  Subsemigroup.closure (P ∪ inverseUltrafilter '' P)

/-- The closure of the set obtained by multiplying the signed semigroup on
both sides by arbitrary ultrafilters. -/
def closedSignedUltrafilterIdeal : Set (Ultrafilter G) :=
  closure {r | ∃ x y z : Ultrafilter G, y ∈ signedUltrafilterSemigroup P ∧ r = x * y * z}

theorem continuous_ultrafilterOperator_wot :
    Continuous (fun p : Ultrafilter G => ContinuousLinearMapWOT.ofCLM (ultrafilterOperator U p)) :=
  continuous_subtype_val.comp (continuous_ultrafilter_extend (weakClosureInclusion U))

theorem isClosed_ultrafilterOperator_eq_zero :
    IsClosed {p | ultrafilterOperator U p = 0} := by
  have h := isClosed_eq (continuous_ultrafilterOperator_wot U) continuous_const
    (g := fun _ => (0 : H →WOT[ℂ] H))
  simpa only [← ContinuousLinearMapWOT.ofCLM_zero,
    ContinuousLinearMapWOT.ofCLM_injective.eq_iff] using h

omit [CompleteSpace H] in
/-- Equation (6), the common kernel of a mixing family is all of the Hilbert space. -/
theorem isUMixing_iff_iInf_ker_eq_top :
    IsUMixing U P ↔ (⨅ p : P, (ultrafilterOperator U p).ker) = ⊤ := by
  rw [iInf_eq_top]
  constructor
  · intro h p
    rw [h p p.property]
    exact LinearMap.ker_zero
  · intro h p hp
    apply ContinuousLinearMap.ext
    intro x
    change x ∈ (ultrafilterOperator U p).ker
    rw [h ⟨p, hp⟩]
    exact Submodule.mem_top

theorem isUMixing_iff_signedUltrafilterSemigroup :
    IsUMixing U P ↔ IsUMixing U (signedUltrafilterSemigroup P) := by
  constructor
  · intro h p hp
    refine Subsemigroup.closure_induction (s := P ∪ inverseUltrafilter '' P)
      (p := fun q _ => ultrafilterOperator U q = 0) ?_ ?_ hp
    · rintro q (hq | ⟨r, hr, rfl⟩)
      · exact h q hq
      · rw [ultrafilterOperator_inverse, h r hr]
        simp
    · intro q r _ _ hq _
      rw [ultrafilterOperator_mul, hq, zero_mul]
  · intro h p hp
    exact h p (Subsemigroup.subset_closure (Or.inl hp))

theorem isUMixing_iff_closedSignedUltrafilterIdeal :
    IsUMixing U P ↔ IsUMixing U (closedSignedUltrafilterIdeal P) := by
  rw [isUMixing_iff_signedUltrafilterSemigroup U P]
  constructor
  · intro h
    apply closure_minimal _ (isClosed_ultrafilterOperator_eq_zero U)
    rintro r ⟨x, y, z, hy, rfl⟩
    change ultrafilterOperator U (x * y * z) = 0
    rw [ultrafilterOperator_mul, ultrafilterOperator_mul, h y hy, mul_zero, zero_mul]
  · intro h p hp
    have hp' : p ∈ closedSignedUltrafilterIdeal P := by
      apply subset_closure
      refine ⟨pure 1, p, pure 1, hp, ?_⟩
      apply Ultrafilter.coe_inj.mp
      ext s
      change (∀ᶠ g in (p : Filter G), g ∈ s) ↔
        ∀ᶠ g in ((pure 1 * p * pure 1 : Ultrafilter G) : Filter G), g ∈ s
      simp [Ultrafilter.eventually_mul]
    exact h p hp'

theorem isUMixing_iff_ultrafilterSemigroup :
    IsUMixing U P ↔ IsUMixing U (Subsemigroup.closure P : Set (Ultrafilter G)) := by
  constructor
  · intro h p hp
    exact (isUMixing_iff_signedUltrafilterSemigroup U P).mp h p
      (Subsemigroup.closure_mono (subset_union_left : P ⊆ P ∪ _) hp)
  · intro h p hp
    exact h p (Subsemigroup.subset_closure hp)

theorem IsUMixing.ultrafilterProductsSucc {U : G →* (H ≃ₗᵢ[ℂ] H)} {P : Set (Ultrafilter G)}
    (h : IsUMixing U P) (n : ℕ) : IsUMixing U (ultrafilterProductsSucc P n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rintro _ ⟨p, hp, q, _, rfl⟩
    rw [ultrafilterOperator_mul, ih p hp, zero_mul]

/-- Repeating the same factor in a nonempty product gives the corresponding positive
power of its ultrafilter operator. -/
theorem exists_ultrafilterProductsSucc_eq_pow {p : Ultrafilter G} (hp : p ∈ P) (n : ℕ) :
    ∃ q ∈ ultrafilterProductsSucc P n, ultrafilterOperator U q = (ultrafilterOperator U p) ^ (n + 1) := by
  induction n with
  | zero => exact ⟨p, hp, (pow_one _).symm⟩
  | succ n ih =>
    obtain ⟨q, hq, hEq⟩ := ih
    refine ⟨q * p, ⟨q, hq, p, hp, rfl⟩, ?_⟩
    rw [ultrafilterOperator_mul, hEq, ← pow_succ]

section Abelian

variable [IsMulCommutative G]

theorem isUMixing_iff_ultrafilterProductsSucc (n : ℕ) :
    IsUMixing U P ↔ IsUMixing U (ultrafilterProductsSucc P n) := by
  constructor
  · intro h
    exact h.ultrafilterProductsSucc n
  · intro h p hp
    obtain ⟨q, hq, hEq⟩ := exists_ultrafilterProductsSucc_eq_pow U P hp n
    have hpow := normal_ker_pow (ultrafilterOperator U p) (ultrafilterOperator_normal U p)
      (Nat.zero_lt_succ n)
    rw [← hEq, h q hq] at hpow
    apply ContinuousLinearMap.ext
    intro x
    change x ∈ (ultrafilterOperator U p).ker
    rw [← hpow]
    rfl

theorem isUMixing_iff_all_ultrafilterProducts :
    IsUMixing U P ↔ ∀ n : ℕ, 0 < n → IsUMixing U (ultrafilterProductsSucc P n) :=
  ⟨fun h n _ => h.ultrafilterProductsSucc n,
    fun h => (isUMixing_iff_ultrafilterProductsSucc U P 1).mpr (h 1 Nat.one_pos)⟩

theorem isUMixing_iff_some_ultrafilterProducts :
    IsUMixing U P ↔ ∃ n : ℕ, 0 < n ∧ IsUMixing U (ultrafilterProductsSucc P n) := by
  constructor
  · intro h
    exact ⟨1, Nat.one_pos, h.ultrafilterProductsSucc 1⟩
  · rintro ⟨n, _, hn⟩
    exact (isUMixing_iff_ultrafilterProductsSucc U P n).mpr hn

end Abelian

theorem isUMixing_iff_ultrafilterDelta :
    IsUMixing U P ↔ IsUMixing U (ultrafilterDelta P) := by
  constructor
  · rintro h _ ⟨p, hp, rfl⟩
    rw [ultrafilterOperator_mul, h p hp, mul_zero]
  · intro h p hp
    have h' := h _ ⟨p, hp, rfl⟩
    rw [ultrafilterOperator_mul, ultrafilterOperator_inverse] at h'
    have hker := ContinuousLinearMap.ker_adjoint_comp_self (ultrafilterOperator U p)
    change ((ultrafilterOperator U p).adjoint * ultrafilterOperator U p).ker = _ at hker
    rw [h'] at hker
    apply ContinuousLinearMap.ext
    intro x
    change x ∈ (ultrafilterOperator U p).ker
    rw [← hker]
    rfl

/-- Proposition 3. Each alternate family gives exactly the original mixing
condition. In the fourth and fifth equivalences, `n+1` is the actual length, so
`0 < n` means that the length is greater than one. -/
theorem proposition3 [IsMulCommutative G] :
    (IsUMixing U P ↔ IsUMixing U (closedSignedUltrafilterIdeal P)) ∧
    (IsUMixing U P ↔ IsUMixing U (signedUltrafilterSemigroup P)) ∧
    (IsUMixing U P ↔ IsUMixing U (Subsemigroup.closure P : Set (Ultrafilter G))) ∧
    (IsUMixing U P ↔ ∀ n : ℕ, 0 < n → IsUMixing U (ultrafilterProductsSucc P n)) ∧
    (IsUMixing U P ↔ ∃ n : ℕ, 0 < n ∧ IsUMixing U (ultrafilterProductsSucc P n)) ∧
    (IsUMixing U P ↔ IsUMixing U (ultrafilterDelta P)) :=
  ⟨isUMixing_iff_closedSignedUltrafilterIdeal U P, isUMixing_iff_signedUltrafilterSemigroup U P,
    isUMixing_iff_ultrafilterSemigroup U P, isUMixing_iff_all_ultrafilterProducts U P,
    isUMixing_iff_some_ultrafilterProducts U P, isUMixing_iff_ultrafilterDelta U P⟩

end Mixing
end

/- Source module Mixing.SpectralDisjointness. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # The dual of ultrafilter mixing -/


open Filter Set
open scoped InnerProductSpace Mixing Topology

namespace Mixing

universe u v

variable {G : Type*} [Group G]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded linear map intertwines two unitary actions if it respects every group element. -/
def Intertwines (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K))
    (J : H →L[ℂ] K) : Prop :=
  ∀ g x, J (U g x) = V g (J x)

/-- Spectral disjointness is vanishing of all bounded linear intertwiners. -/
def SpectrallyDisjoint (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K)) : Prop :=
  ∀ J : K →L[ℂ] H, Intertwines V U J → J = 0

/-- Intertwining extends from the original action to all ultrafilter operators. -/
theorem Intertwines.ultrafilter {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}
    {J : H →L[ℂ] K} (hJ : Intertwines U V J) (p : Ultrafilter G) (x : H) :
    J (ultrafilterOperator U p x) = ultrafilterOperator V p (J x) := by
  apply ext_inner_left ℂ
  intro y
  rw [← J.adjoint_inner_left]
  apply tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p (J.adjoint y) x)
  convert tendsto_ultrafilterOperator_coeff V p y (J x) using 1
  funext g
  rw [J.adjoint_inner_left, hJ g x]

theorem Intertwines.adjoint {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}
    {J : H →L[ℂ] K} (hJ : Intertwines U V J) :
    Intertwines V U J.adjoint := by
  intro g y
  apply ext_inner_left ℂ
  intro x
  have hU : ((U g : H →L[ℂ] H).adjoint) x = U g⁻¹ x := by
    rw [LinearIsometryEquiv.adjoint_eq_symm, map_inv]
    rfl
  have hV : ∀ z, ((V g : K →L[ℂ] K).adjoint) z = V g⁻¹ z := by
    intro z
    rw [LinearIsometryEquiv.adjoint_eq_symm, map_inv]
    rfl
  calc
    ⟪x, J.adjoint (V g y)⟫_ℂ = ⟪J x, V g y⟫_ℂ := J.adjoint_inner_right _ _
    _ = ⟪V g⁻¹ (J x), y⟫_ℂ := by rw [← hV]; exact ((V g : K →L[ℂ] K).adjoint_inner_left _ _).symm
    _ = ⟪J (U g⁻¹ x), y⟫_ℂ := by rw [hJ]
    _ = ⟪U g⁻¹ x, J.adjoint y⟫_ℂ := (J.adjoint_inner_right _ _).symm
    _ = ⟪x, U g (J.adjoint y)⟫_ℂ := by rw [← hU]; exact (U g : H →L[ℂ] H).adjoint_inner_left _ _

theorem SpectrallyDisjoint.symm {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}
    (h : SpectrallyDisjoint U V) : SpectrallyDisjoint V U := by
  intro J hJ
  have he := h _ hJ.adjoint
  simpa only [ContinuousLinearMap.adjoint_adjoint, map_zero] using
    congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ)) he

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (P : Set (Ultrafilter G))

/-- The common kernel in equations (6) and (7). -/
noncomputable def mixingSubspace : Submodule ℂ H := ⨅ p : P, (ultrafilterOperator U p).ker

omit [CompleteSpace H] in
theorem mixingSubspace_isClosed : IsClosed (mixingSubspace U P : Set H) := by
  change IsClosed ((⨅ p : P, (ultrafilterOperator U p).ker : Submodule ℂ H) : Set H)
  simp only [Submodule.coe_iInf]
  exact isClosed_iInter fun p => (ultrafilterOperator U p).isClosed_ker

/-- Equation (7), the family generates the Hilbert space if its images have dense linear span. -/
def IsUGenerated : Prop :=
  (Submodule.span ℂ (⋃ p : P, ((ultrafilterOperator U p).range : Set H))).topologicalClosure = ⊤

theorem isUGenerated_iff [IsMulCommutative G] : IsUGenerated U P ↔ mixingSubspace U P = ⊥ := by
  unfold IsUGenerated mixingSubspace
  rw [← normal_iInf_ker_orthogonal_eq_span _ (fun p : P => ultrafilterOperator_normal U p),
    Submodule.orthogonal_eq_top_iff]

/-- `V` is annihilated relative to `(P,U)` when the kernels of all indices sharing
the same ultrafilter operator on `U` span densely, for each index in `P`. -/
def IsUAnnihilated (V : G →* (K ≃ₗᵢ[ℂ] K)) : Prop :=
  ∀ p : P, (⨆ q : {q : Ultrafilter G // ultrafilterOperator U q = ultrafilterOperator U p},
    (ultrafilterOperator V q).ker).topologicalClosure = ⊤

omit [CompleteSpace H] [CompleteSpace K] in
theorem isUAnnihilated_of_isUMixing {V : G →* (K ≃ₗᵢ[ℂ] K)} (h : IsUMixing V P) :
    IsUAnnihilated U P V := by
  intro p
  apply top_unique
  refine le_trans ?_ (Submodule.le_topologicalClosure _)
  have hle := le_iSup (fun q : {q : Ultrafilter G //
    ultrafilterOperator U q = ultrafilterOperator U p} => (ultrafilterOperator V q).ker) ⟨p, rfl⟩
  change (ultrafilterOperator V p).ker ≤ _ at hle
  rw [h p p.property] at hle
  simpa only [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero] using hle

/-- Restriction of a unitary group action to an invariant subspace. -/
noncomputable def unitarySubmoduleAction (W : Submodule ℂ H)
    (hW : ∀ g x, x ∈ W → U g x ∈ W) : G →* (W ≃ₗᵢ[ℂ] W) where
  toFun g :=
    { toLinearEquiv :=
        { (U g).toLinearMap.restrict (hW g) with
          invFun := fun x => ⟨U g⁻¹ x, hW g⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (show (U g⁻¹ * U g) x = x by
            rw [← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun x => Subtype.ext (show (U g * U g⁻¹) x = x by
            rw [← map_mul, mul_inv_cancel, map_one]; rfl) }
      norm_map' := fun x => (U g).norm_map x }
  map_one' := by
    ext x
    change U 1 x = (x : H)
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change U (g * h) x = U g (U h x)
    rw [map_mul]
    rfl

omit [CompleteSpace H] in
theorem intertwines_unitarySubmoduleAction (W : Submodule ℂ H)
    (hW : ∀ g x, x ∈ W → U g x ∈ W) :
    Intertwines (unitarySubmoduleAction U W hW) U W.subtypeL :=
  fun _ _ => rfl

/-- The ultrafilter operators commute with the original operators for an abelian group. -/
theorem ultrafilterOperator_commute [IsMulCommutative G] (p : Ultrafilter G) (g : G) (x : H) :
    U g (ultrafilterOperator U p x) = ultrafilterOperator U p (U g x) := by
  apply Intertwines.ultrafilter (J := (U g : H →L[ℂ] H)) (U := U) (V := U) ?_ p x
  intro a y
  change (U g * U a) y = (U a * U g) y
  rw [← map_mul, ← map_mul, mul_comm' g a]

theorem mixingSubspace_invariant [IsMulCommutative G] (g : G) (x : H)
    (hx : x ∈ mixingSubspace U P) : U g x ∈ mixingSubspace U P := by
  simp only [mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe] at hx ⊢
  intro p
  rw [← ultrafilterOperator_commute U p, hx, map_zero]

theorem mixingSubspace_orthogonal_invariant [IsMulCommutative G] (g : G) (x : H)
    (hx : x ∈ (mixingSubspace U P)ᗮ) : U g x ∈ (mixingSubspace U P)ᗮ := by
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hg : U g (U g⁻¹ y) = y := by
    change (U g * U g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    ⟪y, U g x⟫_ℂ = ⟪U g (U g⁻¹ y), U g x⟫_ℂ := by rw [hg]
    _ = ⟪U g⁻¹ y, x⟫_ℂ := (U g).inner_map_map _ _
    _ = 0 := hx _ (mixingSubspace_invariant U P _ _ hy)

variable [IsMulCommutative G]

omit [IsMulCommutative G] in
/-- A map from an annihilated action has image in the common kernel. -/
theorem intertwiner_mem_mixingSubspace {V : G →* (K ≃ₗᵢ[ℂ] K)} {J : K →L[ℂ] H}
    (hJ : Intertwines V U J) (hV : IsUAnnihilated U P V) (x : K) :
    J x ∈ mixingSubspace U P := by
  simp only [mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  intro p
  let A := (ultrafilterOperator U p).comp J
  have hle : (⨆ q : {q : Ultrafilter G // ultrafilterOperator U q = ultrafilterOperator U p},
    (ultrafilterOperator V q).ker) ≤ A.ker := by
    apply iSup_le
    intro q y hy
    change ultrafilterOperator U p (J y) = 0
    rw [← q.property, ← hJ.ultrafilter q, show ultrafilterOperator V q y = 0 from hy, map_zero]
  have ht := Submodule.topologicalClosure_minimal _ hle A.isClosed_ker
  rw [hV p] at ht
  exact ht (Submodule.mem_top (x := x))

/-- Theorem 3.1, (iii) implies (i). -/
theorem spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated
    {V : G →* (K ≃ₗᵢ[ℂ] K)} (hU : IsUGenerated U P) (hV : IsUAnnihilated U P V) :
    SpectrallyDisjoint U V := by
  intro J hJ
  apply ContinuousLinearMap.ext
  intro x
  have hx := intertwiner_mem_mixingSubspace U P hJ hV x
  rw [(isUGenerated_iff U P).mp hU, Submodule.mem_bot] at hx
  exact hx

/-- Theorem 3.1, (ii) implies (iii). The restricted action on the common
kernel is itself a mixing action, and its inclusion is an intertwiner. -/
theorem isUGenerated_of_spectrallyDisjoint_all_mixing
    (h : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUMixing V P → SpectrallyDisjoint U V) :
    IsUGenerated U P := by
  let W := mixingSubspace U P
  let _ : CompleteSpace W := (mixingSubspace_isClosed U P).completeSpace_coe
  let V := unitarySubmoduleAction U W (mixingSubspace_invariant U P)
  have hJ : Intertwines V U W.subtypeL :=
    intertwines_unitarySubmoduleAction U W (mixingSubspace_invariant U P)
  have hV : IsUMixing V P := by
    intro p hp
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change W.subtypeL (ultrafilterOperator V p x) = 0
    rw [hJ.ultrafilter]
    have hx := x.property
    simp only [W, mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] at hx
    exact hx ⟨p, hp⟩
  have hz := @h W _ _ _ V hV W.subtypeL hJ
  rw [isUGenerated_iff]
  apply le_antisymm _ bot_le
  intro x hx
  exact congrArg (fun J : W →L[ℂ] H => J ⟨x, hx⟩) hz

/-- Theorem 3.1. The generation criterion is equivalent to disjointness from
every annihilated action and to disjointness from every mixing action. -/
theorem theorem3_1 :
    (IsUGenerated U P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUAnnihilated U P V → SpectrallyDisjoint U V) ∧
    (IsUGenerated U P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUMixing V P → SpectrallyDisjoint U V) := by
  constructor
  · constructor
    · exact fun h _ _ _ _ _ hV => spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated U P h hV
    · intro h
      apply isUGenerated_of_spectrallyDisjoint_all_mixing U P
      intro K _ _ _ V hV
      exact @h K _ _ _ V (isUAnnihilated_of_isUMixing U P hV)
  · constructor
    · exact fun h _ _ _ _ _ hV =>
        spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated U P h (isUAnnihilated_of_isUMixing U P hV)
    · exact isUGenerated_of_spectrallyDisjoint_all_mixing U P

/-- Corollary 3, also the Hilbert-space equivalence behind Theorem 1.3(i).
Apply this to the mean-zero Koopman representation to test operator mixing
using disjointness from every generated action. -/
theorem corollary3 :
    IsUMixing U P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUGenerated V P → SpectrallyDisjoint U V := by
  constructor
  · intro h K _ _ _ V hV
    exact (spectrallyDisjoint_of_isUGenerated_of_isUAnnihilated V P hV
      (isUAnnihilated_of_isUMixing V P h)).symm
  · intro h
    let W := (mixingSubspace U P)ᗮ
    let _ : CompleteSpace W := (Submodule.isClosed_orthogonal _).completeSpace_coe
    let V := unitarySubmoduleAction U W (mixingSubspace_orthogonal_invariant U P)
    have hJ : Intertwines V U W.subtypeL :=
      intertwines_unitarySubmoduleAction U W (mixingSubspace_orthogonal_invariant U P)
    have hV : IsUGenerated V P := by
      rw [isUGenerated_iff]
      apply le_antisymm _ bot_le
      intro x hx
      have hx' : (x : H) ∈ mixingSubspace U P := by
        simp only [mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
          ContinuousLinearMap.coe_coe] at hx ⊢
        intro p
        change ultrafilterOperator U p (W.subtypeL x) = 0
        rw [← hJ.ultrafilter p x, hx, map_zero]
      rw [Submodule.mem_bot]
      apply Subtype.ext
      exact (Submodule.disjoint_def.mp (mixingSubspace U P).orthogonal_disjoint) x hx' x.property
    have hz := @h W _ _ _ V hV W.subtypeL hJ
    have hW : (mixingSubspace U P)ᗮ = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact congrArg (fun J : W →L[ℂ] H => J ⟨x, hx⟩) hz
    rw [isUMixing_iff_iInf_ker_eq_top]
    change mixingSubspace U P = ⊤
    have heq := congrArg Submodule.orthogonal hW
    rwa [Submodule.orthogonal_orthogonal_eq_closure, Submodule.bot_orthogonal_eq_top,
      (mixingSubspace_isClosed U P).submodule_topologicalClosure_eq] at heq

end Mixing
end

/- Source module Mixing.Koopman. -/
section
noncomputable section

namespace Mixing

open MeasureTheory Filter
open scoped Topology

universe u

variable {G Y : Type*} {X : Type u} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]

private theorem pullback_congr {μ : Measure X} {ν : Measure Y} {a b : X → Y}
    (ha : MeasurePreserving a μ ν) (hb : MeasurePreserving b μ ν) (hab : a = b)
    (f : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving a ha f = Lp.compMeasurePreserving b hb f := by
  subst b
  rfl

/-- Koopman pullback is composition by the action in the paper's convention. -/
def System.koopman (S : System G X) (g : G) : Lp ℂ 2 S.measure ≃ₗᵢ[ℂ] Lp ℂ 2 S.measure where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (S.act g) (S.preserves g)
  invFun := Lp.compMeasurePreserving (E := ℂ) (p := 2) (S.act g⁻¹) (S.preserves g⁻¹)
  left_inv x := by
    change Lp.compMeasurePreserving _ (S.preserves g⁻¹)
      (Lp.compMeasurePreserving _ (S.preserves g) x) = x
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (pullback_congr _ (MeasurePreserving.id S.measure)
      (by rw [← S.act_mul, mul_inv_cancel, S.act_one]) x).trans
      (Lp.compMeasurePreserving_id_apply x)
  right_inv x := by
    change Lp.compMeasurePreserving _ (S.preserves g)
      (Lp.compMeasurePreserving _ (S.preserves g⁻¹) x) = x
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (pullback_congr _ (MeasurePreserving.id S.measure)
      (by rw [← S.act_mul, inv_mul_cancel, S.act_one]) x).trans
      (Lp.compMeasurePreserving_id_apply x)

/-- The unitary Koopman representation on the full complex L² space. -/
def System.koopmanRep (S : System G X) : G →* (Lp ℂ 2 S.measure ≃ₗᵢ[ℂ] Lp ℂ 2 S.measure) where
  toFun := S.koopman
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change Lp.compMeasurePreserving _ (S.preserves 1) x = x
    calc
      _ = Lp.compMeasurePreserving id (MeasurePreserving.id S.measure) x :=
        pullback_congr _ _ S.act_one x
      _ = x := Lp.compMeasurePreserving_id_apply x
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    change Lp.compMeasurePreserving _ (S.preserves (g * h)) x =
      Lp.compMeasurePreserving _ (S.preserves g) (Lp.compMeasurePreserving _ (S.preserves h) x)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact pullback_congr _ _ (by rw [mul_comm g h, S.act_mul]) x

/-- The vector represented by the constant function one. -/
def constantOne (μ : Measure X) [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  Lp.const 2 μ 1

/-- Orthogonal complement of the constants on the complex L² space. -/
def meanZero (μ : Measure X) [IsFiniteMeasure μ] : Submodule ℂ (Lp ℂ 2 μ) :=
  (ℂ ∙ constantOne μ)ᗮ

instance meanZero_completeSpace (μ : Measure X) [IsFiniteMeasure μ] :
    CompleteSpace (meanZero μ) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

theorem inner_constantOne_left (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    inner ℂ (constantOne μ) f = ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ)] with x hx
  change constantOne μ x = _ at hx
  rw [hx]
  simp [RCLike.inner_apply]

/-- The orthogonal complement of constants is exactly the space of mean-zero functions. -/
theorem mem_meanZero_iff_integral (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    f ∈ meanZero μ ↔ ∫ x, f x ∂μ = 0 := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_constantOne_left]

@[simp]
theorem inner_constantOne_self (μ : Measure X) [IsProbabilityMeasure μ] :
    inner ℂ (constantOne μ) (constantOne μ) = 1 := by
  rw [inner_constantOne_left, constantOne,
    integral_congr_ae (Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ))]
  simp

/-- Subtract the mean of an L² function on a probability space. -/
def center (μ : Measure X) [IsProbabilityMeasure μ] (f : Lp ℂ 2 μ) : meanZero μ :=
  ⟨f - inner ℂ (constantOne μ) f • constantOne μ, by
    rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      inner_smul_right, inner_constantOne_self, mul_one, sub_self]⟩

theorem eq_center_add (μ : Measure X) [IsProbabilityMeasure μ] (f : Lp ℂ 2 μ) :
    f = (center μ f : Lp ℂ 2 μ) + inner ℂ (constantOne μ) f • constantOne μ := by
  change f = f - _ + _
  exact (sub_add_cancel _ _).symm

theorem System.koopman_constantOne (S : System G X) (g : G) :
    S.koopman g (constantOne S.measure) = constantOne S.measure := by
  change Lp.compMeasurePreserving _ (S.preserves g) _ = _
  apply Lp.ext
  have hone := Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)
  exact (Lp.coeFn_compMeasurePreserving _ _).trans
    (((S.preserves g).quasiMeasurePreserving.ae_eq_comp hone).trans hone.symm)

theorem System.koopman_mem_meanZero (S : System G X) (g : G) {f : Lp ℂ 2 S.measure}
    (hf : f ∈ meanZero S.measure) : S.koopman g f ∈ meanZero S.measure := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right] at hf ⊢
  rw [← S.koopman_constantOne g, (S.koopman g).inner_map_map]
  exact hf

/-- The Koopman equivalence restricted to the mean-zero subspace. -/
def System.koopmanZero (S : System G X) (g : G) :
    meanZero S.measure ≃ₗᵢ[ℂ] meanZero S.measure where
  toFun f := ⟨S.koopman g f, S.koopman_mem_meanZero g f.property⟩
  invFun f := ⟨S.koopman g⁻¹ f, S.koopman_mem_meanZero g⁻¹ f.property⟩
  left_inv f := by
    apply Subtype.ext
    change (S.koopmanRep g⁻¹ * S.koopmanRep g) (f : Lp ℂ 2 S.measure) = ↑f
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv f := by
    apply Subtype.ext
    change (S.koopmanRep g * S.koopmanRep g⁻¹) (f : Lp ℂ 2 S.measure) = ↑f
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' f h := Subtype.ext (map_add (S.koopman g) (f : Lp ℂ 2 S.measure) h)
  map_smul' c f := Subtype.ext (map_smul (S.koopman g) c (f : Lp ℂ 2 S.measure))
  norm_map' f := (S.koopman g).norm_map (f : Lp ℂ 2 S.measure)

/-- The Koopman representation on the complex mean-zero L² space. -/
def System.koopmanZeroRep (S : System G X) : G →* (meanZero S.measure ≃ₗᵢ[ℂ] meanZero S.measure) where
  toFun := S.koopmanZero
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Subtype.ext
    change S.koopmanRep 1 _ = _
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Subtype.ext
    change S.koopmanRep (g * h) _ = S.koopmanRep g (S.koopmanRep h _)
    rw [map_mul]
    rfl

/-- The U-mixing condition on the mean-zero Koopman representation. -/
def System.IsUMixing (S : System G X) (P : Set (Ultrafilter G)) : Prop :=
  Mixing.IsUMixing S.koopmanZeroRep P

theorem System.koopman_coeff_eq (S : System G X) (g : G) (f h : Lp ℂ 2 S.measure) :
    inner ℂ f (S.koopmanRep g h) =
      inner ℂ (center S.measure f) (S.koopmanZeroRep g (center S.measure h)) +
        star (inner ℂ (constantOne S.measure) f) * inner ℂ (constantOne S.measure) h := by
  let f₀ := center S.measure f
  let h₀ := center S.measure h
  let c := constantOne S.measure
  have hf : inner ℂ (f₀ : Lp ℂ 2 S.measure) c = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp f₀.property
  have hh : inner ℂ c (S.koopman g h₀) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (S.koopman_mem_meanZero g h₀.property)
  have hfc := eq_center_add S.measure f
  have hhc := eq_center_add S.measure h
  change inner ℂ (center S.measure f : Lp ℂ 2 S.measure) (constantOne S.measure) = 0 at hf
  change inner ℂ (constantOne S.measure)
    (S.koopman g (center S.measure h : Lp ℂ 2 S.measure)) = 0 at hh
  change inner ℂ f (S.koopman g h) =
    inner ℂ (f₀ : Lp ℂ 2 S.measure) (S.koopman g h₀) + star (inner ℂ c f) * inner ℂ c h
  conv_lhs =>
    rw [hfc, hhc]
  simp only [map_add, map_smul, S.koopman_constantOne, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hf, hh, inner_constantOne_self,
    mul_zero, mul_one, zero_add, add_zero]
  rw [mul_comm (inner ℂ (constantOne S.measure) h)]
  rfl

/-- U-mixing is convergence of all Koopman correlations to their independent values. -/
theorem System.isUMixing_iff_lp_correlations (S : System G X) (P : Set (Ultrafilter G)) :
    S.IsUMixing P ↔ ∀ p ∈ P, ∀ f h : Lp ℂ 2 S.measure,
      Tendsto (fun g ↦ inner ℂ f (S.koopmanRep g h)) (p : Filter G)
        (𝓝 (star (∫ x, f x ∂S.measure) * (∫ x, h x ∂S.measure))) := by
  constructor
  · intro hmix p hp f h
    have hlim := tendsto_ultrafilterOperator_coeff S.koopmanZeroRep p
      (center S.measure f) (center S.measure h)
    rw [hmix p hp, zero_apply, inner_zero_right] at hlim
    simpa only [S.koopman_coeff_eq, inner_constantOne_left, zero_add] using
      hlim.add_const (star (∫ x, f x ∂S.measure) * (∫ x, h x ∂S.measure))
  · intro hmix p hp
    apply ContinuousLinearMap.ext
    intro h
    apply ext_inner_left ℂ
    intro f
    have hlim := hmix p hp (f : Lp ℂ 2 S.measure) (h : Lp ℂ 2 S.measure)
    rw [(mem_meanZero_iff_integral _ _).mp f.property,
      (mem_meanZero_iff_integral _ _).mp h.property, star_zero, zero_mul] at hlim
    rw [zero_apply, inner_zero_right]
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff S.koopmanZeroRep p f h) hlim

variable {S : System G X} {T : System G Y}

/-- Isometric pullback on L² induced by a factor map. -/
def FactorMap.pullback (f : FactorMap S T) : Lp ℂ 2 T.measure →ₗᵢ[ℂ] Lp ℂ 2 S.measure :=
  Lp.compMeasurePreservingₗᵢ ℂ f.toFun f.preserves

theorem FactorMap.pullback_one (f : FactorMap S T) :
    f.pullback (constantOne T.measure) = constantOne S.measure := by
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ f.preserves).trans
    ((f.preserves.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_const (p := 2) (μ := T.measure) (1 : ℂ))).trans
      (Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)).symm)

theorem FactorMap.pullback_mem_meanZero (f : FactorMap S T) (x : meanZero T.measure) :
    f.pullback x ∈ meanZero S.measure := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, ← f.pullback_one,
    f.pullback.inner_map_map]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property

theorem FactorMap.pullback_koopman (f : FactorMap S T) (g : G) (x : Lp ℂ 2 T.measure) :
    f.pullback (T.koopmanRep g x) = S.koopmanRep g (f.pullback x) := by
  change Lp.compMeasurePreserving f.toFun f.preserves
      (Lp.compMeasurePreserving _ (T.preserves g) x) =
    Lp.compMeasurePreserving _ (S.preserves g) (Lp.compMeasurePreserving f.toFun f.preserves x)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  exact pullback_congr _ _ (f.equivariant g).symm x

theorem FactorMap.intertwines_pullback (f : FactorMap S T) :
    Intertwines T.koopmanRep S.koopmanRep f.pullback.toContinuousLinearMap :=
  f.pullback_koopman

/-- Pullback on the mean-zero L² spaces of a factor map. -/
def FactorMap.pullbackZero (f : FactorMap S T) : meanZero T.measure →L[ℂ] meanZero S.measure :=
  (f.pullback.toContinuousLinearMap.comp (meanZero T.measure).subtypeL).codRestrict
    (meanZero S.measure) f.pullback_mem_meanZero

theorem FactorMap.intertwines_pullbackZero (f : FactorMap S T) :
    Intertwines T.koopmanZeroRep S.koopmanZeroRep f.pullbackZero :=
  fun g x ↦ Subtype.ext (f.pullback_koopman g x)

/-- The equivalence of Theorem 1.3(i) and its mean-zero Koopman form of (iii). -/
theorem theorem1_3_i_iii (S : System G X) (P : Set (Ultrafilter G)) :
    S.IsUMixing P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUGenerated V P →
        SpectrallyDisjoint S.koopmanZeroRep V :=
  corollary3 S.koopmanZeroRep P

end Mixing
end

/- Source module Mixing.NilrotationGeometryDenseAction. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Extending measure preservation from a dense set of transformations -/


namespace Mixing

open MeasureTheory

/-- For a continuous action, preservation of a finite Borel measure by a dense set of
parameters implies preservation by every parameter. -/
theorem measurePreserving_smul_of_denseRange
    {D K X : Type*} [TopologicalSpace K] [FirstCountableTopology K]
    [TopologicalSpace X] [HasOuterApproxClosed X]
    [SMul K X] [ContinuousSMul K X] [MeasurableSpace X] [BorelSpace X]
    (d : D → K) (hd : DenseRange d) (μ : Measure X) [IsFiniteMeasure μ]
    (hInv : ∀ i, MeasurePreserving (fun x : X ↦ d i • x) μ μ)
    (k : K) : MeasurePreserving (fun x : X ↦ k • x) μ μ := by
  have hmeas : Measurable (fun x : X ↦ k • x) := (continuous_const_smul k).measurable
  refine ⟨hmeas, ?_⟩
  let := μ.isFiniteMeasure_map (fun x : X ↦ k • x)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
  let F (a : K) : ℝ := ∫ x, f (a • x) ∂μ
  have hF : Continuous F := by
    apply continuous_of_dominated (bound := fun _ : X ↦ ‖f‖)
    · exact fun a ↦ (f.continuous.comp (continuous_const_smul a)).aestronglyMeasurable
    · exact fun a ↦ ae_of_all _ fun x ↦ f.norm_coe_le_norm (a • x)
    · exact integrable_const ‖f‖
    · exact ae_of_all _ fun x ↦
        f.continuous.comp (continuous_smul.comp (continuous_id.prodMk continuous_const))
  change F k = ∫ x, f x ∂μ
  have hdF (i : D) : F (d i) = ∫ x, f x ∂μ := by
    change (∫ x, f (d i • x) ∂μ) = ∫ x, f x ∂μ
    rw [← integral_map (hInv i).measurable.aemeasurable f.continuous.aestronglyMeasurable,
      (hInv i).map_eq]
  exact hd.induction_on k (isClosed_eq hF continuous_const) hdF

end Mixing
end

/- Source module Mixing.NilrotationKoopmanAction. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Koopman actions of topological groups on a finite measure space -/

noncomputable section

namespace Mixing

open MeasureTheory

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

private theorem actionPullback_congr {μ : Measure X} {a b : X → X}
    (ha : MeasurePreserving a μ μ) (hb : MeasurePreserving b μ μ) (h : a = b)
    (f : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving a ha f = Lp.compMeasurePreserving b hb f := by
  subst b
  rfl

/-- Pullback by the inverse of a measure-preserving left group action gives
a unitary operator on complex L². -/
def inverseActionKoopman (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) (g : G) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (fun x : X ↦ g⁻¹ • x) (hInv g⁻¹)
  invFun := Lp.compMeasurePreserving (E := ℂ) (p := 2) (fun x : X ↦ g • x) (hInv g)
  left_inv f := by
    change Lp.compMeasurePreserving _ (hInv g)
      (Lp.compMeasurePreserving _ (hInv g⁻¹) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp [Function.comp_apply, ← mul_smul]) f).trans
      (Lp.compMeasurePreserving_id_apply f)
  right_inv f := by
    change Lp.compMeasurePreserving _ (hInv g⁻¹)
      (Lp.compMeasurePreserving _ (hInv g) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp [Function.comp_apply, ← mul_smul]) f).trans
      (Lp.compMeasurePreserving_id_apply f)

/-- The inverse-action Koopman operators form a representation of the acting group. -/
def inverseActionKoopmanRep (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) :
    G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) where
  toFun := inverseActionKoopman μ hInv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving _ (hInv (1 : G)⁻¹) f = f
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp) f).trans (Lp.compMeasurePreserving_id_apply f)
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving _ (hInv (g * h)⁻¹) f =
      Lp.compMeasurePreserving _ (hInv g⁻¹) (Lp.compMeasurePreserving _ (hInv h⁻¹) f)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact actionPullback_congr _ _
      (funext fun x ↦ by simp only [mul_inv_rev, mul_smul, Function.comp_apply]) f

/-- Representative formula for the inverse-action Koopman representation. -/
theorem ae_inverseActionKoopmanRep_apply (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (g : G) (f : Lp ℂ 2 μ) :
    (inverseActionKoopmanRep μ hInv g f : X → ℂ) =ᵐ[μ] fun x ↦ f (g⁻¹ • x) :=
  Lp.coeFn_compMeasurePreserving f (hInv g⁻¹)

/-- For a jointly continuous action, the associated representation is strongly continuous. -/
theorem continuous_inverseActionKoopmanRep [TopologicalSpace G] [ContinuousInv G]
    [TopologicalSpace X] [R1Space X] [ContinuousSMul G X] [BorelSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) (f : Lp ℂ 2 μ) :
    Continuous (fun g ↦ inverseActionKoopmanRep μ hInv g f) := by
  let A (g : G) : C(X, X) := ⟨fun x ↦ g⁻¹ • x, continuous_const_smul _⟩
  have hA : Continuous A :=
    ContinuousMap.continuous_of_continuous_uncurry _ (by
      change Continuous (fun z : G × X ↦ z.1⁻¹ • z.2)
      exact continuous_smul.comp (continuous_fst.inv.prodMk continuous_snd))
  exact continuous_const.compMeasurePreservingLp hA (fun g ↦ hInv g⁻¹) (by norm_num)

/-- On integer time, pullback by the time element agrees with the
inverse-action representation evaluated at the inverse time element. -/
theorem inverseActionKoopmanRep_zpow_neg_apply
    (S : System (Multiplicative ℤ) X) (a : G)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) S.measure S.measure)
    (hAct : ∀ (n : ℤ) (x : X), S.act (Multiplicative.ofAdd n) x = a ^ n • x)
    (n : ℤ) (f : Lp ℂ 2 S.measure) :
    inverseActionKoopmanRep S.measure hInv (a ^ (-n)) f =
      S.koopmanRep (Multiplicative.ofAdd n) f := by
  change Lp.compMeasurePreserving _ (hInv ((a ^ (-n))⁻¹)) f =
    Lp.compMeasurePreserving _ (S.preserves (Multiplicative.ofAdd n)) f
  apply actionPullback_congr
  funext x
  rw [hAct, ← zpow_neg, neg_neg]

/-- Commuting left actions give mutually commuting Koopman representations. -/
theorem commute_inverseActionKoopmanRep {K : Type*} [Group K] [MulAction K X]
    [SMulCommClass G K X] (μ : Measure X)
    (hG : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (hK : ∀ k : K, MeasurePreserving (fun x : X ↦ k • x) μ μ) (g : G) (k : K) :
    Commute (inverseActionKoopmanRep μ hG g) (inverseActionKoopmanRep μ hK k) := by
  apply LinearIsometryEquiv.ext
  intro f
  change Lp.compMeasurePreserving _ (hG g⁻¹) (Lp.compMeasurePreserving _ (hK k⁻¹) f) =
    Lp.compMeasurePreserving _ (hK k⁻¹) (Lp.compMeasurePreserving _ (hG g⁻¹) f)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  exact actionPullback_congr _ _ (funext fun x ↦ (smul_comm g⁻¹ k⁻¹ x).symm) f

end Mixing
end

/- Source module SixProblems.Koopman. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing
open scoped InnerProductSpace

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-- The action underlying a system, used with inverse pullback for
noncommutative acting groups. -/
@[instance_reducible] def systemMulAction (S : System G X) : MulAction G X where
  smul := S.act
  one_smul x := congrFun S.act_one x
  mul_smul g h x := congrFun (S.act_mul g h) x

/-- The convention in the paper, `U_g f = f ∘ T_(g⁻¹)`. -/
def systemKoopman (S : System G X) : G →* (Lp ℂ 2 S.measure ≃ₗᵢ[ℂ] Lp ℂ 2 S.measure) :=
  letI := systemMulAction S
  inverseActionKoopmanRep S.measure S.preserves

theorem ae_systemKoopman (S : System G X) (g : G) (v : Lp ℂ 2 S.measure) :
    (systemKoopman S g v : X → ℂ) =ᵐ[S.measure] fun x ↦ v (S.act g⁻¹ x) :=
  letI := systemMulAction S
  ae_inverseActionKoopmanRep_apply S.measure S.preserves g v

theorem systemKoopman_constantOne (S : System G X) (g : G) :
    systemKoopman S g (constantOne S.measure) = constantOne S.measure := by
  apply Lp.ext
  have hc := Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)
  exact (ae_systemKoopman S g _).trans
    (((S.preserves g⁻¹).quasiMeasurePreserving.ae_eq_comp hc).trans hc.symm)

theorem inner_systemKoopman_of_memLp (S : System G X) {f : X → ℂ}
    (hf : MemLp f 2 S.measure) (g : G) :
    ⟪hf.toLp f, systemKoopman S g (hf.toLp f)⟫_ℂ = correlation S f g⁻¹ := by
  rw [L2.inner_def, correlation]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, (ae_systemKoopman S g _).trans
    ((S.preserves g⁻¹).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)] with x h₁ h₂
  rw [RCLike.inner_apply', h₁, h₂]
  exact mul_comm _ _

theorem bounded_measurable_memLp (S : System G X) {f : X → ℂ} (hf : Measurable f)
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : MemLp f 2 S.measure := by
  obtain ⟨C,hC⟩ := hbound
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

end SixProblems
end

/- Source module SixProblems.ProductErgodicity. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Ergodicity of an independent product with one mixing coordinate -/

noncomputable section

namespace SixProblems

open Set MeasureTheory Filter Mixing
open scoped ENNReal Topology symmDiff

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]

private def measurableRectangles : Set (Set (X × Y)) :=
  image2 (· ×ˢ ·) {U : Set X | MeasurableSet U} {V : Set Y | MeasurableSet V}

private theorem measurableRectangles_isSetSemiring :
    IsSetSemiring (measurableRectangles (X := X) (Y := Y)) := by
  classical
  refine ⟨⟨∅, MeasurableSet.empty, ∅, MeasurableSet.empty, by simp⟩, ?_, ?_⟩
  · rintro _ ⟨U,hU,V,hV,rfl⟩ _ ⟨U',hU',V',hV',rfl⟩
    exact ⟨U ∩ U', hU.inter hU', V ∩ V', hV.inter hV', prod_inter_prod.symm⟩
  · rintro _ ⟨U,hU,V,hV,rfl⟩ _ ⟨U',hU',V',hV',rfl⟩
    let R := (U \ U') ×ˢ V
    let S := (U ∩ U') ×ˢ (V \ V')
    have hR : R ∈ measurableRectangles := ⟨_, hU.diff hU', _, hV, rfl⟩
    have hS : S ∈ measurableRectangles := ⟨_, hU.inter hU', _, hV.diff hV', rfl⟩
    have hd : _root_.Disjoint R S := by
      apply Set.disjoint_left.mpr
      rintro x ⟨hx, _⟩ ⟨hx', _⟩
      exact hx.2 hx'.2
    refine ⟨{R,S}, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_insert, Finset.coe_singleton, insert_subset_iff, singleton_subset_iff]
        using And.intro hR hS
    · rw [Finset.coe_insert, Finset.coe_singleton]
      exact (Set.pairwise_pair.mpr fun _ ↦ ⟨hd, hd.symm⟩)
    · ext x
      simp only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton,
        R, S, mem_union, mem_prod, Set.mem_sdiff, mem_inter_iff]
      tauto

private theorem measureReal_le_one (μ : Measure Y) [IsProbabilityMeasure μ] (A : Set Y) :
    μ.real A ≤ 1 := (measureReal_mono (subset_univ _) (measure_ne_top μ _)).trans_eq (by simp)

/-- Asymptotic independence from a moving rectangle in a product with one
mixing coordinate. Its first-coordinate event can vary arbitrarily. -/
private theorem tendsto_moving_rectangle (S : System G X) (T : System G Y) (g : ℕ → G)
    (hMix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n ↦ T.measure.real (A ∩ T.act (g n) ⁻¹' B)) atTop
        (𝓝 (T.measure.real A * T.measure.real B)))
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (V : Set Y) (hV : MeasurableSet V)
    (A : Set (X × Y)) (hA : MeasurableSet A) :
    let ν := (S.prod T).measure
    Tendsto (fun n ↦ ν.real (A ∩ (U n ×ˢ (T.act (g n) ⁻¹' V))) -
      ν.real (A ∩ (U n ×ˢ univ)) * T.measure.real V) atTop (𝓝 0) := by
  classical
  let ν := (S.prod T).measure
  let F (n : ℕ) := U n ×ˢ (T.act (g n) ⁻¹' V)
  let F₀ (n : ℕ) := U n ×ˢ (univ : Set Y)
  let D (B : Set (X × Y)) (n : ℕ) := ν.real (B ∩ F n) - ν.real (B ∩ F₀ n) * T.measure.real V
  change Tendsto (D A) atTop (𝓝 0)
  have hF n : MeasurableSet (F n) := (hU n).prod ((T.preserves _).measurable hV)
  have hF₀ n : MeasurableSet (F₀ n) := (hU n).prod MeasurableSet.univ
  have hrect {B : Set (X × Y)} (hB : B ∈ measurableRectangles) : Tendsto (D B) atTop (𝓝 0) := by
    obtain ⟨W,hW,Z,hZ,rfl⟩ := hB
    have hz : Tendsto (fun n ↦ T.measure.real (Z ∩ T.act (g n) ⁻¹' V) -
        T.measure.real Z * T.measure.real V) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ ↦ T.measure.real Z * T.measure.real V) atTop
          (𝓝 (T.measure.real Z * T.measure.real V)) := tendsto_const_nhds
      simpa only [sub_self] using (hMix Z V hZ hV).sub hconst
    have hbounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun n ↦ S.measure.real (W ∩ U n)) :=
      ⟨1, eventually_map.mpr (Eventually.of_forall fun n ↦ by
        change ‖S.measure.real (W ∩ U n)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ S.measure.real (W ∩ U n) from ENNReal.toReal_nonneg)]
        exact measureReal_le_one S.measure (W ∩ U n))⟩
    apply (isBoundedUnder_le_mul_tendsto_zero hbounded hz).congr
    intro n
    change _ = (S.measure.prod T.measure).real ((W ×ˢ Z) ∩ F n) -
      (S.measure.prod T.measure).real ((W ×ˢ Z) ∩ F₀ n) * T.measure.real V
    simp only [F, F₀, prod_inter_prod, measureReal_prod_prod, inter_univ]
    ring
  have hfinite {B : Set (X × Y)} (P : Finpartition B)
      (hP : (↑P.parts : Set (Set (X × Y))) ⊆ measurableRectangles) :
      Tendsto (D B) atTop (𝓝 0) := by
    have hsum {C : Set (X × Y)} (hC : MeasurableSet C) :
        ν.real (B ∩ C) = ∑ W ∈ P.parts, ν.real (W ∩ C) := by
      have hd := (Finset.supIndep_iff_pairwiseDisjoint.mp P.supIndep).mono
        (fun (W : Set (X × Y)) ↦ inter_subset_left (s := W) (t := C))
      have hmeas : ∀ W ∈ P.parts, MeasurableSet (W ∩ C) := by
        intro W hW
        obtain ⟨L,hL,R,hR,rfl⟩ := hP hW
        exact (hL.prod hR).inter hC
      have he : B ∩ C = ⋃ W ∈ P.parts, W ∩ C := calc
        B ∩ C = P.parts.sup id ∩ C := congrArg (· ∩ C) P.sup_parts.symm
        _ = _ := by
          rw [Finset.sup_id_set_eq_sUnion, sUnion_eq_biUnion, iUnion₂_inter]
          simp only [Finset.mem_coe]
      rw [he]
      exact measureReal_biUnion_finset hd hmeas
    have hl := tendsto_finsetSum P.parts (fun W hW ↦ hrect (hP hW))
    simp only [Finset.sum_const_zero] at hl
    apply hl.congr
    intro n
    simp only [D, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum (hF n), hsum (hF₀ n)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε₀ : 0 < ε / 3 := by positivity
  have hcover : ∃ C : Set (Set (X × Y)), C.Countable ∧ C ⊆ measurableRectangles ∧
      ν (⋃₀ C)ᶜ = 0 := by
    refine ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr ?_, by simp⟩
    exact ⟨univ, MeasurableSet.univ, univ, MeasurableSet.univ, univ_prod_univ⟩
  obtain ⟨B, hB, hclose⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
    (μ := ν) measurableRectangles_isSetSemiring hcover generateFrom_prod.symm hA
      (ENNReal.ofReal_pos.mpr hε₀)
  obtain ⟨P,hP⟩ := measurableRectangles_isSetSemiring.mem_supClosure_iff.mp hB
  have hBm := measurableSet_generateFrom_of_mem_supClosure hB
  rw [show MeasurableSpace.generateFrom measurableRectangles =
    (inferInstance : MeasurableSpace (X × Y)) from generateFrom_prod] at hBm
  have hdiff {C : Set (X × Y)} (hC : MeasurableSet C) :
      |ν.real (A ∩ C) - ν.real (B ∩ C)| ≤ ν.real (B ∆ A) := by
    have hsub : (A ∩ C) ∆ (B ∩ C) ⊆ B ∆ A := by
      intro x
      simp only [symmDiff_def, mem_union, Set.mem_sdiff, mem_inter_iff]
      tauto
    exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
      (hA.inter hC).nullMeasurableSet (hBm.inter hC).nullMeasurableSet).trans (measureReal_mono hsub)
  have hclose' : ν.real (B ∆ A) < ε / 3 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hclose
    rwa [ENNReal.toReal_ofReal hε₀.le] at h
  filter_upwards [(Metric.tendsto_nhds.mp (hfinite P hP)) _ hε₀] with n hn
  rw [Real.dist_eq, sub_zero] at hn ⊢
  have hcoef : 0 ≤ T.measure.real V := ENNReal.toReal_nonneg
  have herror : |D A n - D B n| ≤ ν.real (B ∆ A) + ν.real (B ∆ A) := by
    calc
      _ = |(ν.real (A ∩ F n) - ν.real (B ∩ F n)) -
          (ν.real (A ∩ F₀ n) - ν.real (B ∩ F₀ n)) * T.measure.real V| := by
        congr 1
        dsimp [D]
        ring
      _ ≤ |ν.real (A ∩ F n) - ν.real (B ∩ F n)| +
          |(ν.real (A ∩ F₀ n) - ν.real (B ∩ F₀ n)) * T.measure.real V| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le _ (0 : ℝ) _
      _ ≤ ν.real (B ∆ A) + ν.real (B ∆ A) := by
        refine add_le_add (hdiff (hF n)) ?_
        rw [abs_mul, abs_of_nonneg hcoef]
        exact (mul_le_mul_of_nonneg_right (hdiff (hF₀ n)) hcoef).trans
          (mul_le_of_le_one_right ENNReal.toReal_nonneg (measureReal_le_one T.measure V))
  calc
    |D A n| ≤ |D A n - D B n| + |D B n| := by simpa only [sub_zero] using abs_sub_le (D A n) (D B n) 0
    _ ≤ ν.real (B ∆ A) + ν.real (B ∆ A) + |D B n| := add_le_add herror le_rfl
    _ < ε := by linarith

private theorem invariant_measure_rect (S : System G X) (T : System G Y) (g : ℕ → G)
    (hMix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n ↦ T.measure.real (A ∩ T.act (g n) ⁻¹' B)) atTop
        (𝓝 (T.measure.real A * T.measure.real B)))
    {A : Set (X × Y)} (hA : MeasurableSet A)
    (hInv : ∀ k, (S.prod T).act k ⁻¹' A =ᵐ[(S.prod T).measure] A)
    {U : Set X} {V : Set Y} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    let ν := (S.prod T).measure
    ν (A ∩ (U ×ˢ V)) = ν (A ∩ (U ×ˢ univ)) * T.measure V := by
  let P := S.prod T
  let ν := P.measure
  let Uₙ (n : ℕ) := S.act (g n) ⁻¹' U
  have hUₙ n : MeasurableSet (Uₙ n) := (S.preserves _).measurable hU
  have hmeasure (k : G) {F : Set (X × Y)} (hF : MeasurableSet F) :
      ν.real (A ∩ F) = ν.real (A ∩ P.act k ⁻¹' F) := by
    have hpres := (P.preserves k).measure_preimage (hA.inter hF).nullMeasurableSet
    have hd : P.act k ⁻¹' (A ∩ F) =ᵐ[ν] A ∩ P.act k ⁻¹' F := by
      filter_upwards [hInv k] with x hx
      change (P.act k x ∈ A ∧ P.act k x ∈ F) ↔ (x ∈ A ∧ P.act k x ∈ F)
      exact and_congr_left' hx
    exact congrArg ENNReal.toReal (hpres.symm.trans (measure_congr hd))
  have hEquiv (n : ℕ) : ν.real (A ∩ (Uₙ n ×ˢ (T.act (g n) ⁻¹' V))) -
      ν.real (A ∩ (Uₙ n ×ˢ univ)) * T.measure.real V =
      ν.real (A ∩ (U ×ˢ V)) - ν.real (A ∩ (U ×ˢ univ)) * T.measure.real V := by
    rw [hmeasure (g n) (hU.prod hV), hmeasure (g n) (hU.prod MeasurableSet.univ)]
    rfl
  have hl := (tendsto_moving_rectangle S T g hMix Uₙ hUₙ V hV A hA).congr hEquiv
  have he := sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hl)
  have h := congrArg ENNReal.ofReal he
  change ENNReal.ofReal (ν (A ∩ (U ×ˢ V))).toReal =
    ENNReal.ofReal ((ν (A ∩ (U ×ˢ univ))).toReal * (T.measure V).toReal) at h
  change ν (A ∩ (U ×ˢ V)) = ν (A ∩ (U ×ˢ univ)) * T.measure V
  rw [← ENNReal.toReal_mul, ENNReal.ofReal_toReal (measure_ne_top ν _),
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (measure_ne_top ν _) (measure_ne_top T.measure _))] at h
  exact h

/-- The product with an ergodic system is ergodic when all measurable event
correlations in the other system converge to independence along one sequence. -/
theorem prod_isErgodic_of_eventMixing (S : System G X) (T : System G Y) (hS : S.IsErgodic)
    (g : ℕ → G) (hMix : ∀ A B : Set Y, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n ↦ T.measure.real (A ∩ T.act (g n) ⁻¹' B)) atTop
        (𝓝 (T.measure.real A * T.measure.real B))) :
    (S.prod T).IsErgodic := by
  intro A hA hInv
  let P := S.prod T
  let ν := P.measure
  let ρ := ν.restrict A
  let η := ρ.map Prod.fst
  have hρ₁ (k : G) : MeasurePreserving (P.act k) ρ ρ := by
    have h := (P.preserves k).restrict_preimage hA
    have hr : ν.restrict (P.act k ⁻¹' A) = ρ := Measure.restrict_congr_set (hInv k)
    rwa [hr] at h
  have hη₁ (k : G) : MeasurePreserving (S.act k) η η := by
    refine ⟨(S.preserves k).measurable, ?_⟩
    have hcomp : S.act k ∘ Prod.fst = Prod.fst ∘ P.act k := rfl
    change (ρ.map Prod.fst).map (S.act k) = η
    rw [Measure.map_map (S.preserves k).measurable measurable_fst, hcomp,
      ← Measure.map_map measurable_fst (hρ₁ k).measurable, (hρ₁ k).map_eq]
  have hη_le : η ≤ S.measure := by
    calc
      η ≤ ν.map Prod.fst := Measure.map_mono Measure.restrict_le_self measurable_fst
      _ = S.measure := by
        change (S.measure.prod T.measure).map Prod.fst = S.measure
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hη_eq := S.eq_smul_of_invariant_absolutelyContinuous hS η hη₁ hη_le.absolutelyContinuous
  have hη_univ : η univ = ν A := by
    change ρ.map Prod.fst univ = _
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
  have hProd : ρ = η.prod T.measure := by
    apply Measure.ext_prod
    intro U V hU hV
    have hη_apply : η U = ν (A ∩ (U ×ˢ univ)) := by
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU), inter_comm]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    rw [Measure.prod_prod, hη_apply, Measure.restrict_apply (hU.prod hV), inter_comm]
    exact invariant_measure_rect S T g hMix hA hInv hU hV
  have hρ_eq : ρ = ν A • ν := by
    rw [hProd, hη_eq, hη_univ, Measure.prod_smul_left]
    rfl
  have hzero := congrArg (fun q : Measure (X × Y) ↦ q Aᶜ) hρ_eq
  change (ν.restrict A) Aᶜ = (ν A • ν) Aᶜ at hzero
  rw [Measure.restrict_apply hA.compl, compl_inter_self, measure_empty, smul_apply, smul_eq_mul] at hzero
  change Filter.EventuallyEmptyOrUniv A (ae ν)
  apply eventuallyEmptyOrUniv_iff.mpr
  rcases mul_eq_zero.mp hzero.symm with h | h
  · exact Or.inr (by simpa [ae_iff] using h)
  · exact Or.inl (ae_iff.mpr h)

end SixProblems
end

/- Source module SixProblems.OperatorialRecurrenceGaussianMixing. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems.Gaussian

noncomputable section

open MeasureTheory Mixing Filter Set TopologicalSpace ContinuousLinearMap InnerProductSpace
open scoped Classical Topology InnerProductSpace ComplexConjugate

private theorem tendsto_zero_of_dense_lipschitz {ι E D : Type*} [PseudoMetricSpace E]
    {F : Filter ι} {d : D → E} (hd : DenseRange d) {b : ι → E → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ i x y, dist (b i x) (b i y) ≤ C * dist x y)
    (h : ∀ j, Tendsto (fun i ↦ b i (d j)) F (𝓝 0)) (x : E) :
    Tendsto (fun i ↦ b i x) F (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨j, hj⟩ := hd.exists_dist_lt x (show 0 < ε / (2 * (C+1)) by positivity)
  filter_upwards [(Metric.tendsto_nhds.1 (h j)) (ε / 2) (by positivity)] with i hi
  have he : C * dist x (d j) < ε / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (C+1))).mp hj
    have hh' := mul_le_mul_of_nonneg_right (show C ≤ C+1 by linarith)
      (show 0 ≤ dist x (d j) from dist_nonneg)
    nlinarith only [hh, hh']
  refine (dist_triangle _ (b i (d j)) _).trans_lt ?_
  have h' := add_lt_add ((hLip i x (d j)).trans_lt he) hi
  linarith only [h']

/-- Under a common operator-norm bound, testing on two dense sets suffices
for convergence of all weak matrix coefficients. -/
private theorem tendsto_inner_zero_of_denseRange_of_opNorm_le {ι D E H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {F : Filter ι}
    {d : D → H} {e : E → H} (hd : DenseRange d) (he : DenseRange e)
    {A : ι → H →L[ℂ] H} {C : ℝ} (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (h : ∀ x y, Tendsto (fun i ↦ ⟪d x, A i (e y)⟫_ℂ) F (𝓝 0)) (x y : H) :
    Tendsto (fun i ↦ ⟪x, A i y⟫_ℂ) F (𝓝 0) := by
  have hLeft (v : E) (u : H) : Tendsto (fun i ↦ ⟪u, A i (e v)⟫_ℂ) F (𝓝 0) := by
    refine tendsto_zero_of_dense_lipschitz hd (b := fun i z ↦ ⟪z, A i (e v)⟫_ℂ)
      (C := C * ‖e v‖) (by positivity) ?_ (fun w ↦ h w v) u
    intro i x y
    rw [dist_eq_norm, dist_eq_norm, ← inner_sub_left]
    calc
      ‖⟪x - y, A i (e v)⟫_ℂ‖ ≤ ‖x - y‖ * ‖A i (e v)‖ := norm_inner_le_norm _ _
      _ ≤ ‖x - y‖ * (C * ‖e v‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
      _ = _ := by ring
  refine tendsto_zero_of_dense_lipschitz he (b := fun i z ↦ ⟪x, A i z⟫_ℂ)
    (C := ‖x‖ * C) (by positivity) ?_ (fun v ↦ hLeft v x) y
  intro i u v
  rw [dist_eq_norm, dist_eq_norm, ← inner_sub_right, ← map_sub]
  calc
    ‖⟪x, A i (u - v)⟫_ℂ‖ ≤ ‖x‖ * ‖A i (u - v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (C * ‖u - v‖) := by
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
    _ = _ := by ring

private theorem test_conj {G : Type*} (a : GaussianTest G) (x : G → ℝ) :
    conj (gaussianCylChar a.times a.frequencies x) =
      gaussianCylChar a.times (fun i ↦ -a.frequencies i) x := by
  simp [gaussianCylChar, ← Complex.exp_conj, Complex.conj_I, Finset.sum_neg_distrib]

variable {G : Type*} [Group G] [Countable G] (φ : G → ℝ) (hφ : RealPositiveDefinite φ)

/-- Vanishing two-sided translates of the covariance give a weak operator limit onto
    constant functions for the Gaussian path system. -/
theorem gaussianPath_koopman_tendsto {J : Type*} (g : J → G) (L : Filter J)
    (hCov : ∀ r s : G, Tendsto (fun z ↦ φ (r * (g z)⁻¹ * s)) L (𝓝 0))
    (x y : Lp ℂ 2 (gaussianPathMeasure φ hφ)) :
    Tendsto (fun z ↦ ⟪x, systemKoopman (gaussianPathSystem φ hφ) (g z)⁻¹ y⟫_ℂ) L
      (𝓝 (⟪x, constantOne (gaussianPathMeasure φ hφ)⟫_ℂ *
         ⟪constantOne (gaussianPathMeasure φ hφ), y⟫_ℂ)) := by
  let S := gaussianPathSystem φ hφ
  let μ := S.measure
  change Lp ℂ 2 μ at x y
  let u := constantOne μ
  let P := rankOne ℂ u u
  let A (z : J) := (systemKoopman S (g z)⁻¹).toLinearIsometry.toContinuousLinearMap - P
  have hAct (z : J) (w : Lp ℂ 2 μ) :
      A z w = systemKoopman S (g z)⁻¹ w - P w := rfl
  have hA (z : J) : ‖A z‖ ≤ 1 + ‖P‖ := by
    exact (norm_sub_le _ _).trans (add_le_add
      (systemKoopman S (g z)⁻¹).toLinearIsometry.norm_toContinuousLinearMap_le le_rfl)
  let V : GaussianTest G → Lp ℂ 2 μ := fun a ↦ a.toVector μ
  have hCoe (a : GaussianTest G) :
      ⟪u, V a⟫_ℂ = ∫ x, gaussianCylChar a.times a.frequencies x ∂μ :=
    (inner_constantOne_left _ _).trans (integral_congr_ae (a.memLp μ).coeFn_toLp)
  have hConj (a : GaussianTest G) :
      ⟪V a, u⟫_ℂ = ∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x ∂μ := by
    rw [← inner_conj_symm, hCoe, ← integral_conj]
    exact integral_congr_ae (.of_forall fun x ↦ test_conj a x)
  have hTest (a b : GaussianTest G) :
      Tendsto (fun z ↦ ⟪V a, A z (V b)⟫_ℂ) L (𝓝 0) := by
    have he (z : J) : ⟪V a, systemKoopman S (g z)⁻¹ (V b)⟫_ℂ =
        ∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x *
          gaussianCylChar b.times b.frequencies (gaussianShift (g z) x) ∂μ := by
      rw [L2.inner_def (μ := S.measure)]
      apply integral_congr_ae
      have hb := (ae_systemKoopman S (g z)⁻¹ (V b)).trans
        ((S.preserves ((g z)⁻¹)⁻¹).quasiMeasurePreserving.ae_eq_comp (b.memLp μ).coeFn_toLp)
      filter_upwards [(a.memLp μ).coeFn_toLp, hb] with x h₁ h₂
      simp only [RCLike.inner_apply', inv_inv] at h₂ ⊢
      rw [show V a x = _ from h₁, h₂, test_conj]
      rfl
    have hlim : Tendsto (fun z ↦ ∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x *
        gaussianCylChar b.times b.frequencies (gaussianShift (g z) x) ∂μ) L
        (𝓝 ((∫ x, gaussianCylChar a.times (fun i ↦ -a.frequencies i) x ∂μ) *
          (∫ x, gaussianCylChar b.times b.frequencies x ∂μ))) :=
      gaussianCylChar_mul_shift_tendsto φ hφ a.times (fun i ↦ -a.frequencies i)
        b.times b.frequencies g L hCov
    have hlimit : Tendsto (fun z ↦ ⟪V a, systemKoopman S (g z)⁻¹ (V b)⟫_ℂ) L
        (𝓝 ⟪V a, P (V b)⟫_ℂ) := by
      simpa only [he, P, inner_right_rankOne_apply, hConj, hCoe] using hlim
    simpa only [hAct, inner_sub_right, sub_self] using
      hlimit.sub (tendsto_const_nhds (x := ⟪V a, P (V b)⟫_ℂ))
  let D := Submodule.span ℂ (Set.range V)
  have hD : DenseRange ((↑) : D → Lp ℂ 2 μ) := by
    rw [DenseRange, Subtype.range_coe]
    exact D.dense_iff_topologicalClosure_eq_top.mpr (gaussianTestVectors_dense μ)
  have hRight (a : GaussianTest G) (w : Lp ℂ 2 μ) (hw : w ∈ D) :
      Tendsto (fun z ↦ ⟪V a, A z w⟫_ℂ) L (𝓝 0) := by
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      exact hTest a b
    | zero => simpa only [map_zero, inner_zero_right] using (tendsto_const_nhds (x := (0 : ℂ)))
    | add v w hv hw hv' hw' =>
      simpa only [map_add, inner_add_right, add_zero] using hv'.add hw'
    | smul c w hw hw' =>
      simpa only [map_smul, inner_smul_right, mul_zero] using tendsto_const_nhds.mul hw'
  have hLeft (w v : Lp ℂ 2 μ) (hw : w ∈ D) (hv : v ∈ D) :
      Tendsto (fun z ↦ ⟪w, A z v⟫_ℂ) L (𝓝 0) := by
    induction hw using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨a, rfl⟩ := hw'
      exact hRight a v hv
    | zero => simpa only [inner_zero_left] using (tendsto_const_nhds (x := (0 : ℂ)))
    | add w₁ w₂ h₁ h₂ ht₁ ht₂ =>
      simpa only [inner_add_left, add_zero] using ht₁.add ht₂
    | smul c w' hw' ht =>
      simpa only [inner_smul_left, mul_zero] using tendsto_const_nhds.mul ht
  have ht := tendsto_inner_zero_of_denseRange_of_opNorm_le hD hD
    (by positivity : 0 ≤ 1 + ‖P‖) hA (fun a b ↦ hLeft a b a.property b.property) x y
  have ht' : Tendsto (fun z ↦ ⟪x, A z y⟫_ℂ + ⟪x, P y⟫_ℂ) L (𝓝 (0 + ⟪x, P y⟫_ℂ)) :=
    ht.add tendsto_const_nhds
  have hP : ⟪x, P y⟫_ℂ = ⟪x, u⟫_ℂ * ⟪u, y⟫_ℂ := inner_right_rankOne_apply x u u y
  change Tendsto (fun z ↦ ⟪x, systemKoopman S (g z)⁻¹ y⟫_ℂ) L (𝓝 (⟪x, u⟫_ℂ * ⟪u, y⟫_ℂ))
  simpa only [hAct, inner_sub_right, sub_add_cancel, zero_add, hP] using ht'

/-- Along the same sequence, the Gaussian action is mixing on all measurable events. -/
theorem gaussianPath_measure_inter_tendsto {J : Type*} (g : J → G) (L : Filter J)
    (hCov : ∀ r s : G, Tendsto (fun z ↦ φ (r * (g z)⁻¹ * s)) L (𝓝 0))
    {U V : Set (G → ℝ)} (hU : MeasurableSet U) (hV : MeasurableSet V) :
    Tendsto (fun z ↦ (gaussianPathMeasure φ hφ).real (U ∩ gaussianShift (g z) ⁻¹' V)) L
      (𝓝 ((gaussianPathMeasure φ hφ).real U * (gaussianPathMeasure φ hφ).real V)) := by
  let S := gaussianPathSystem φ hφ
  let μ := S.measure
  let a : Lp ℂ 2 μ := indicatorConstLp 2 hU (measure_ne_top _ _) 1
  let b : Lp ℂ 2 μ := indicatorConstLp 2 hV (measure_ne_top _ _) 1
  have hA : a =ᵐ[μ] U.indicator (fun _ ↦ (1 : ℂ)) := indicatorConstLp_coeFn
  have hB : b =ᵐ[μ] V.indicator (fun _ ↦ (1 : ℂ)) := indicatorConstLp_coeFn
  have hAa : ⟪a, constantOne μ⟫_ℂ = (μ.real U : ℂ) := by
    rw [← inner_conj_symm, inner_constantOne_left, integral_congr_ae hA, integral_indicator_const]
    · simp
    · exact hU
  have hBb : ⟪constantOne μ, b⟫_ℂ = (μ.real V : ℂ) := by
    rw [inner_constantOne_left, integral_congr_ae hB, integral_indicator_const _ hV]
    simp
  have he (z : J) : ⟪a, systemKoopman S (g z)⁻¹ b⟫_ℂ =
      (μ.real (U ∩ gaussianShift (g z) ⁻¹' V) : ℂ) := by
    have hm : MeasurableSet (U ∩ gaussianShift (g z) ⁻¹' V) :=
      hU.inter ((gaussianShift_preserves φ hφ (g z)).measurable hV)
    have hI : (∫ x, (U ∩ gaussianShift (g z) ⁻¹' V).indicator
        (fun _ ↦ (1 : ℂ)) x ∂μ) = (μ.real (U ∩ gaussianShift (g z) ⁻¹' V) : ℂ) := by
      rw [integral_indicator_const _ hm]
      simp
    rw [L2.inner_def (μ := S.measure), ← hI]
    apply integral_congr_ae
    have hb := (ae_systemKoopman S (g z)⁻¹ b).trans
      ((S.preserves ((g z)⁻¹)⁻¹).quasiMeasurePreserving.ae_eq_comp hB)
    filter_upwards [hA, hb] with x ha hb'
    rw [RCLike.inner_apply', ha, hb']
    change conj (U.indicator (fun _ ↦ (1 : ℂ)) x) *
      V.indicator (fun _ ↦ (1 : ℂ)) (gaussianShift ((g z)⁻¹)⁻¹ x) = _
    by_cases h₁ : x ∈ U <;> by_cases h₂ : gaussianShift (g z) x ∈ V <;>
      simp [inv_inv, Set.indicator, h₁, h₂]
  have ht := gaussianPath_koopman_tendsto φ hφ g L hCov a b
  change Tendsto (fun z ↦ ⟪a, systemKoopman S (g z)⁻¹ b⟫_ℂ) L
    (𝓝 (⟪a, constantOne μ⟫_ℂ * ⟪constantOne μ, b⟫_ℂ)) at ht
  rw [hAa, hBb, ← Complex.ofReal_mul] at ht
  change Tendsto (fun z ↦ μ.real (U ∩ gaussianShift (g z) ⁻¹' V)) L
    (𝓝 (μ.real U * μ.real V))
  simpa only [he, Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto ((μ.real U * μ.real V : ℝ) : ℂ)).comp ht

/-- A Gaussian shift with vanishing coefficients along a sequence preserves
    ergodicity when multiplied by any ergodic action of the same group. -/
theorem gaussianPath_prod_isErgodic {X : Type*} [MeasurableSpace X]
    (S : System G X) (hS : S.IsErgodic) (g : ℕ → G)
    (hCov : ∀ r s : G, Tendsto (fun n ↦ φ (r * (g n)⁻¹ * s)) atTop (𝓝 0)) :
    (S.prod (gaussianPathSystem φ hφ)).IsErgodic :=
  prod_isErgodic_of_eventMixing S (gaussianPathSystem φ hφ) hS g
    (fun _ _ hA hB ↦ gaussianPath_measure_inter_tendsto φ hφ g atTop hCov hA hB)

end

end SixProblems.Gaussian
end

/- Source module SixProblems.OperatorialRecurrenceTruncation. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter WithLp
open scoped Classical Topology ProbabilityTheory ComplexConjugate

private def truncateGaussian (n : ℕ) (x : ℝ) : ℝ := (Icc (-(n : ℝ)) n).indicator id x

private theorem measurable_truncateGaussian (n : ℕ) : Measurable (truncateGaussian n) :=
  measurable_id.indicator measurableSet_Icc

private theorem truncateGaussian_odd (n : ℕ) (x : ℝ) : truncateGaussian n (-x) = -truncateGaussian n x := by
  have he : -x ∈ Icc (-(n : ℝ)) n ↔ x ∈ Icc (-(n : ℝ)) n := by
    rw [mem_Icc, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  by_cases hx : x ∈ Icc (-(n : ℝ)) n
  · simp [truncateGaussian, hx, he.mpr hx]
  · have hnx : -x ∉ Icc (-(n : ℝ)) n := fun h ↦ hx (he.mp h)
    rw [truncateGaussian, truncateGaussian, indicator_of_notMem hnx, indicator_of_notMem hx, neg_zero]

private theorem abs_truncateGaussian_le (n : ℕ) (x : ℝ) : |truncateGaussian n x| ≤ |x| := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) n
  · simp [truncateGaussian, hx]
  · simp [truncateGaussian, hx]

private theorem abs_truncateGaussian_le_nat (n : ℕ) (x : ℝ) : |truncateGaussian n x| ≤ n := by
  by_cases hx : x ∈ Icc (-(n : ℝ)) n
  · simpa [truncateGaussian, hx] using abs_le.mpr hx
  · simp [truncateGaussian, hx]

private theorem eventually_truncateGaussian_eq (x : ℝ) : ∀ᶠ n : ℕ in atTop, truncateGaussian n x = x := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : |x| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  simp [truncateGaussian, abs_le.mp hx]

theorem integral_comp_preserving {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : MeasurePreserving f μ ν) {g : β → E} (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hm : AEStronglyMeasurable g (μ.map f) := hf.map_eq.symm ▸ hg
  rw [← hf.map_eq, integral_map hf.measurable.aemeasurable hm]

variable {G : Type} [Group G] [Countable G]

private theorem truncateGaussian_mean (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (n : ℕ) :
    (∫ x, truncateGaussian n (x (1 : G)) ∂(gaussianPathMeasure φ hφ)) = 0 := by
  let ν := gaussianReal 0 (φ 1).toNNReal
  have hn : MeasurePreserving (fun x : ℝ ↦ -x) ν ν :=
    ⟨measurable_neg, by simp [ν, gaussianReal_map_neg]⟩
  rw [integral_comp_preserving (gaussianPath_coordinate_law φ hφ 1)
    (measurable_truncateGaussian n).aestronglyMeasurable]
  have h := integral_comp_preserving hn (measurable_truncateGaussian n).aestronglyMeasurable
  simp_rw [truncateGaussian_odd, integral_neg] at h
  linarith

/-- Truncated-coordinate correlations depend only on the covariance of the Gaussian pair. -/
private theorem truncateGaussian_corr_eq (φ : G → ℝ) (hφ : RealPositiveDefinite φ)
    (n : ℕ) {g h : G} (he : φ g = φ h) :
    (∫ x, truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1) ∂(gaussianPathMeasure φ hφ)) =
      ∫ x, truncateGaussian n (x h⁻¹) * truncateGaussian n (x 1) ∂(gaussianPathMeasure φ hφ) := by
  let a (j : G) : Bool → G := fun i ↦ if i then j⁻¹ else 1
  let k (x : EuclideanSpace ℝ Bool) := truncateGaussian n (x true) * truncateGaussian n (x false)
  have hk : Measurable k :=
    ((measurable_truncateGaussian n).comp (EuclideanSpace.proj true).continuous.measurable).mul
      ((measurable_truncateGaussian n).comp (EuclideanSpace.proj false).continuous.measurable)
  have hc (j : G) : (∫ x, truncateGaussian n (x j⁻¹) * truncateGaussian n (x 1)
      ∂(gaussianPathMeasure φ hφ)) = ∫ x, k x ∂multivariateGaussian 0
        (Matrix.of fun i l ↦ φ ((a j i)⁻¹ * a j l)) := by
    simpa only [k, a, ite_true, ite_false, Bool.false_eq_true] using
      integral_comp_preserving (gaussianPath_tuple φ hφ (a j)) hk.aestronglyMeasurable
  rw [hc g, hc h]
  have hm : (Matrix.of fun i j ↦ φ ((a g i)⁻¹ * a g j)) =
      (Matrix.of fun i j ↦ φ ((a h i)⁻¹ * a h j)) := by
    ext i j
    cases i <;> cases j <;> simp [a, hφ.inv_eq, he]
  rw [hm]

private theorem truncateGaussian_corr_tendsto (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (g : G) :
    Tendsto (fun n ↦ ∫ x, truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1)
      ∂(gaussianPathMeasure φ hφ)) atTop (𝓝 (φ g)) := by
  let μ := gaussianPathMeasure φ hφ
  have hv : (∫ x, x g⁻¹ * x 1 ∂μ) = φ g := by
    simpa only [inv_inv, mul_one] using gaussianPath_covariance φ hφ g⁻¹ 1
  rw [← hv]
  apply tendsto_integral_of_dominated_convergence (fun x : G → ℝ ↦ ‖x g⁻¹ * x 1‖)
  · intro n
    exact (((measurable_truncateGaussian n).comp (measurable_pi_apply _)).mul
      ((measurable_truncateGaussian n).comp (measurable_pi_apply _))).aestronglyMeasurable
  · exact ((gaussianPath_coordinate_memLp φ hφ g⁻¹).integrable_mul
      (gaussianPath_coordinate_memLp φ hφ 1)).norm
  · intro n
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_truncateGaussian_le n _) (abs_truncateGaussian_le n _)
      (abs_nonneg _) (abs_nonneg _)
  · filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_truncateGaussian_eq (x g⁻¹), eventually_truncateGaussian_eq (x 1)]
      with n h₁ h₂
    rw [h₁, h₂]

/-- Cutoff of the coordinate approximates its correlations uniformly in the
time parameter. If either coordinate lies outside the cutoff, the larger
squared coordinate lies outside and bounds the omitted product. -/
theorem gaussianPath_exists_bounded_centered_approximation
    (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (δ : ℝ) (hδ : 0 < δ) :
    let S := gaussianPathSystem φ hφ
    ∃ f : (G → ℝ) → ℝ, Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
      (∫ x, f x ∂S.measure) = 0 ∧ ∀ g,
        |(∫ x, f (S.act g x) * f x ∂S.measure) - φ g| < δ := by
  let S := gaussianPathSystem φ hφ
  let μ := gaussianPathMeasure φ hφ
  let tail (n : ℕ) (t : ℝ) : ℝ := (Icc (-(n : ℝ)) n)ᶜ.indicator (fun x ↦ x^2) t
  have hTailM (n : ℕ) : Measurable (tail n) :=
    (measurable_id.pow_const 2).indicator measurableSet_Icc.compl
  have hTailLe (n : ℕ) (t : ℝ) : ‖tail n t‖ ≤ t^2 := by
    by_cases ht : t ∈ Icc (-(n : ℝ)) n
    · simpa [tail, ht] using sq_nonneg t
    · simp [tail, ht, Real.norm_eq_abs]
  have hSq (j : G) : Integrable (fun x : G → ℝ ↦ (x j)^2) μ :=
    (gaussianPath_coordinate_memLp φ hφ j).integrable_sq
  have hlim : Tendsto (fun n ↦ ∫ x : G → ℝ, tail n (x 1) ∂μ) atTop (𝓝 0) := by
    rw [← integral_zero (α := G → ℝ) (G := ℝ) (μ := μ)]
    apply tendsto_integral_of_dominated_convergence (fun x : G → ℝ ↦ (x 1)^2)
    · intro n
      exact ((hTailM n).comp (measurable_pi_apply 1)).aestronglyMeasurable
    · exact hSq 1
    · exact fun n ↦ .of_forall fun x ↦ hTailLe n (x 1)
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      obtain ⟨N,hN⟩ := exists_nat_ge |x 1|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : |x 1| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      simp [tail, abs_le.mp hx]
  obtain ⟨n,hn⟩ := (hlim.eventually_lt_const (half_pos hδ)).exists
  let f (x : G → ℝ) := truncateGaussian n (x 1)
  refine ⟨f,(measurable_truncateGaussian n).comp (measurable_pi_apply 1),
    ⟨n,fun x ↦ abs_truncateGaussian_le_nat n (x 1)⟩,truncateGaussian_mean φ hφ n,?_⟩
  intro g
  have hCov : (∫ x : G → ℝ, x g⁻¹ * x 1 ∂μ) = φ g := by
    simpa only [inv_inv,mul_one] using gaussianPath_covariance φ hφ g⁻¹ 1
  have hPt (u v : ℝ) : |truncateGaussian n u * truncateGaussian n v - u*v| ≤ tail n u + tail n v := by
    by_cases hu : u ∈ Icc (-(n : ℝ)) n <;> by_cases hv : v ∈ Icc (-(n : ℝ)) n
    · simp [truncateGaussian,tail,hu,hv]
    · have hUV : |u| ≤ |v| := (abs_le.mpr hu).trans (lt_of_not_ge (fun h ↦ hv (abs_le.mp h))).le
      have hh := mul_le_mul_of_nonneg_right hUV (abs_nonneg v)
      simpa [truncateGaussian,tail,hu,hv,abs_mul,← sq, sq_abs] using hh
    · have hVU : |v| ≤ |u| := (abs_le.mpr hv).trans (lt_of_not_ge (fun h ↦ hu (abs_le.mp h))).le
      have hh := mul_le_mul_of_nonneg_left hVU (abs_nonneg u)
      simpa [truncateGaussian,tail,hu,hv,abs_mul,← sq, sq_abs] using hh
    · simp [truncateGaussian,tail,hu,hv,abs_mul]
      nlinarith [sq_nonneg (|u|-|v|),sq_abs u,sq_abs v,sq_nonneg u,sq_nonneg v]
  have hInt (j : G) : Integrable (fun x : G → ℝ ↦ tail n (x j)) μ :=
    (hSq j).mono' ((hTailM n).comp (measurable_pi_apply j)).aestronglyMeasurable
      (.of_forall fun x ↦ hTailLe n (x j))
  have hPres : (∫ x : G → ℝ, tail n (x g⁻¹) ∂μ) = ∫ x : G → ℝ, tail n (x 1) ∂μ := by
    have hp : (∫ x : G → ℝ, tail n ((S.act g x) 1) ∂S.measure) =
        ∫ x : G → ℝ, tail n (x 1) ∂S.measure :=
      integral_comp_preserving (S.preserves g) (g := fun x ↦ tail n (x 1)) ((hTailM n).comp
        (measurable_pi_apply (1 : G))).aestronglyMeasurable
    simpa only [S, gaussianPathSystem, gaussianShift, mul_one, μ] using hp
  have hCut (j : G) : MemLp (fun x : G → ℝ ↦ truncateGaussian n (x j)) 2 μ :=
    MemLp.of_bound ((measurable_truncateGaussian n).comp (measurable_pi_apply j)).aestronglyMeasurable
      n (.of_forall fun x ↦ abs_truncateGaussian_le_nat n (x j))
  change |(∫ x, truncateGaussian n (x (g⁻¹ * 1)) * truncateGaussian n (x 1) ∂μ) - φ g| < δ
  simp only [mul_one]
  have hCutInt : Integrable (fun x : G → ℝ ↦
      truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1)) μ :=
    (hCut g⁻¹).integrable_mul (hCut 1)
  have hBaseInt : Integrable (fun x : G → ℝ ↦ x g⁻¹ * x 1) μ :=
    (gaussianPath_coordinate_memLp φ hφ g⁻¹).integrable_mul (gaussianPath_coordinate_memLp φ hφ 1)
  rw [← hCov, ← integral_sub hCutInt hBaseInt]
  calc
    _ ≤ ∫ x : G → ℝ, ‖truncateGaussian n (x g⁻¹) * truncateGaussian n (x 1) - x g⁻¹*x 1‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : G → ℝ, (tail n (x g⁻¹) + tail n (x 1)) ∂μ := by
      exact integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) ((hInt g⁻¹).fun_add (hInt 1))
        (ae_of_all _ fun x ↦ hPt (x g⁻¹) (x 1))
    _ < δ := by rw [integral_add (hInt g⁻¹) (hInt 1), hPres]; linarith

/-- A constant strictly negative positive-definite witness gives a bounded counterexample
    on its Gaussian shift. The Gaussian pair law makes the truncated correlations identical,
    so a single added constant cancels every correlation. -/
theorem not_vdC_of_negative_constant_real {H : Set G} (hne : H.Nonempty)
    (φ : G → ℝ) (hφ : RealPositiveDefinite φ) (r : ℝ) (hr : r < 0)
    (hconst : ∀ h ∈ H, φ h = r) : ¬IsVdC H := by
  obtain ⟨g, hg⟩ := hne
  have hlim := truncateGaussian_corr_tendsto φ hφ g
  rw [hconst g hg] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hr).exists
  let S := gaussianPathSystem φ hφ
  let u : (G → ℝ) → ℝ := fun x ↦ truncateGaussian n (x 1)
  let b : ℝ := ∫ x, u (S.act g x) * u x ∂S.measure
  have hnegB : b < 0 := by
    simpa only [b, S, u, gaussianPathSystem, gaussianShift, mul_one] using hn
  let t := Real.sqrt (-b)
  have ht : 0 < t := Real.sqrt_pos.2 (neg_pos.mpr hnegB)
  let f : (G → ℝ) → ℂ := fun x ↦ ((u x+t : ℝ) : ℂ)
  have hu : Measurable u := (measurable_truncateGaussian n).comp (measurable_pi_apply 1)
  have hμ : Integrable u S.measure := Integrable.of_bound hu.aestronglyMeasurable (n : ℝ)
    (.of_forall fun x ↦ abs_truncateGaussian_le_nat n (x 1))
  have hm : (∫ x, u x ∂S.measure) = 0 := truncateGaussian_mean φ hφ n
  have hf : Measurable f := Complex.continuous_ofReal.measurable.comp (hu.add measurable_const)
  have hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨(n : ℝ) + t, fun x ↦ by
    change ‖((u x+t : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact (abs_add_le _ _).trans (add_le_add (abs_truncateGaussian_le_nat n (x 1))
      (le_of_eq (abs_of_pos ht)))⟩
  intro hV
  have hz := hV S f hf hb (fun h hh ↦ ?_)
  · change (∫ x, ((u x + t : ℝ) : ℂ) ∂S.measure) = 0 at hz
    rw [integral_complex_ofReal, integral_add hμ (integrable_const _), hm, integral_const] at hz
    simp [Measure.real, ht.ne'] at hz
  change (∫ x, (((u (S.act h x)+t : ℝ) : ℂ) * conj ((u x+t : ℝ) : ℂ)) ∂S.measure) = 0
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_eq_zero]
  have hi₁ : Integrable (fun x ↦ u (S.act h x)) S.measure :=
    (S.preserves h).integrable_comp_of_integrable hμ
  have hi₂ : Integrable (fun x ↦ u (S.act h x) * u x) S.measure :=
    Integrable.of_bound ((hu.comp (S.preserves h).measurable).mul hu).aestronglyMeasurable
      ((n : ℝ) * n) (.of_forall fun x ↦ by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (abs_truncateGaussian_le_nat n _) (abs_truncateGaussian_le_nat n _)
          (abs_nonneg _) (Nat.cast_nonneg _))
  have he : (∫ x, u (S.act h x) * u x ∂S.measure) = b := by
    simpa only [b, S, u, gaussianPathSystem, gaussianShift, mul_one] using
      truncateGaussian_corr_eq φ hφ n ((hconst h hh).trans (hconst g hg).symm)
  have hact : (∫ x, u (S.act h x) ∂S.measure) = 0 :=
    (integral_comp_preserving (S.preserves h) hu.aestronglyMeasurable).trans hm
  have hExp : (fun x ↦ (u (S.act h x) + t) * (u x + t)) =
      fun x ↦ (u (S.act h x) * u x + u (S.act h x) * t) + (t * u x + t*t) :=
    funext fun _ ↦ by ring
  have hk : Integrable (fun _ : G → ℝ ↦ t*t) S.measure := integrable_const _
  rw [hExp, integral_add (hi₂.fun_add (hi₁.mul_const t)) ((hμ.const_mul t).fun_add hk),
    integral_add hi₂ (hi₁.mul_const t), integral_add (hμ.const_mul t) hk,
    integral_mul_const, integral_const_mul, hm, hact, he, integral_const]
  simp [Measure.real, t, Real.mul_self_sqrt (neg_nonneg.mpr hnegB.le)]

end

end SixProblems
end

/- Source module SixProblems.RealKoopman. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



/-! # Koopman actions of topological groups on a finite measure space -/

noncomputable section

namespace SixProblems

open MeasureTheory

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

private theorem actionPullback_congr {μ : Measure X} {a b : X → X}
    (ha : MeasurePreserving a μ μ) (hb : MeasurePreserving b μ μ) (h : a = b)
    (f : Lp ℝ 2 μ) :
    Lp.compMeasurePreserving a ha f = Lp.compMeasurePreserving b hb f := by
  subst b
  rfl

/-- Pullback by the inverse of a measure-preserving left group action gives
a unitary operator on real L². -/
def realInverseActionKoopman (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) (g : G) :
    Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℝ (fun x : X ↦ g⁻¹ • x) (hInv g⁻¹)
  invFun := Lp.compMeasurePreserving (E := ℝ) (p := 2) (fun x : X ↦ g • x) (hInv g)
  left_inv f := by
    change Lp.compMeasurePreserving _ (hInv g)
      (Lp.compMeasurePreserving _ (hInv g⁻¹) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp [Function.comp_apply, ← mul_smul]) f).trans
      (Lp.compMeasurePreserving_id_apply f)
  right_inv f := by
    change Lp.compMeasurePreserving _ (hInv g⁻¹)
      (Lp.compMeasurePreserving _ (hInv g) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp [Function.comp_apply, ← mul_smul]) f).trans
      (Lp.compMeasurePreserving_id_apply f)

/-- The inverse-action Koopman operators form a representation of the acting group. -/
def realInverseActionKoopmanRep (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) :
    G →* (Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ) where
  toFun := realInverseActionKoopman μ hInv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving _ (hInv (1 : G)⁻¹) f = f
    exact (actionPullback_congr _ (MeasurePreserving.id μ)
      (funext fun x ↦ by simp) f).trans (Lp.compMeasurePreserving_id_apply f)
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    change Lp.compMeasurePreserving _ (hInv (g * h)⁻¹) f =
      Lp.compMeasurePreserving _ (hInv g⁻¹) (Lp.compMeasurePreserving _ (hInv h⁻¹) f)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact actionPullback_congr _ _
      (funext fun x ↦ by simp only [mul_inv_rev, mul_smul, Function.comp_apply]) f

/-- Representative formula for the inverse-action Koopman representation. -/
theorem ae_realInverseActionKoopmanRep_apply (μ : Measure X)
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (g : G) (f : Lp ℝ 2 μ) :
    (realInverseActionKoopmanRep μ hInv g f : X → ℝ) =ᵐ[μ] fun x ↦ f (g⁻¹ • x) :=
  Lp.coeFn_compMeasurePreserving f (hInv g⁻¹)

/-- For a jointly continuous action, the associated representation is strongly continuous. -/
theorem continuous_realInverseActionKoopmanRep [TopologicalSpace G] [ContinuousInv G]
    [TopologicalSpace X] [R1Space X] [ContinuousSMul G X] [BorelSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ) (f : Lp ℝ 2 μ) :
    Continuous (fun g ↦ realInverseActionKoopmanRep μ hInv g f) := by
  let A (g : G) : C(X, X) := ⟨fun x ↦ g⁻¹ • x, continuous_const_smul _⟩
  have hA : Continuous A :=
    ContinuousMap.continuous_of_continuous_uncurry _ (by
      change Continuous (fun z : G × X ↦ z.1⁻¹ • z.2)
      exact continuous_smul.comp (continuous_fst.inv.prodMk continuous_snd))
  exact continuous_const.compMeasurePreservingLp hA (fun g ↦ hInv g⁻¹) (by norm_num)

end SixProblems
end

/- Source module SixProblems.StableCoefficients. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter Mixing.JdLGBridge Set
open scoped InnerProductSpace Topology

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A sequence which sends all translates of a stable coefficient to zero. -/
theorem exists_stable_coefficient_sequence [Countable G]
    (U : G →* (E ≃ₗᵢ[ℝ] E))
    (K : GroupIdeal (weakOperatorClosure (orthogonalActionCLM U).toMulHom))
    (v : E) (hv : K.projection (closureAction (orthogonalActionCLM U).toMulHom) v = 0) :
    ∃ g : ℕ → G, ∀ r s : G,
      Tendsto (fun n ↦ ⟪v,U (r * (g n)⁻¹ * s) v⟫_ℝ) atTop (𝓝 0) := by
  classical
  let π := (orthogonalActionCLM U).toMulHom
  let F (a : weakOperatorClosure π) (p : G × G) :=
    ⟪U p.1⁻¹ v, closureAction π a (U p.2 v)⟫_ℝ
  have hF : Continuous F := continuous_pi fun p ↦ by
    let f := innerSL ℝ (U p.1⁻¹ v)
    exact (ContinuousLinearMapWOT.continuous_dual_apply (U p.2 v) f).comp continuous_subtype_val
  have hF0 : F K.identity = 0 := by
    funext p
    change ⟪U p.1⁻¹ v, K.projection (closureAction π) (U p.2 v)⟫_ℝ = 0
    have h := K.projection_commutes (closureAction π) (closureInclusion π p.2) v
    change K.projection (closureAction π) (U p.2 v) = U p.2 (K.projection (closureAction π) v) at h
    rw [h, hv, map_zero, inner_zero_right]
  have hcl : F K.identity ∈ closure (range (F ∘ closureInclusion π)) := by
    rw [range_comp]
    exact mem_closure_image hF.continuousAt (denseRange_closureInclusion π K.identity)
  obtain ⟨a,ha,ht⟩ := mem_closure_iff_seq_limit.mp hcl
  choose j hj using ha
  refine ⟨fun n ↦ (j n)⁻¹,fun r s ↦ ?_⟩
  have hl := ((continuous_apply (r,s)).tendsto (F K.identity)).comp ht
  rw [hF0] at hl
  have he (n : ℕ) : (a n) (r,s) = ⟪v,U (r*((j n)⁻¹)⁻¹*s) v⟫_ℝ := by
    rw [← hj n]
    change ⟪U r⁻¹ v,U (j n) (U s v)⟫_ℝ = _
    rw [← (U r).inner_map_map]
    change ⟪(U r * U r⁻¹) v,(U r * (U (j n) * U s)) v⟫_ℝ = _
    rw [← map_mul, mul_inv_cancel, map_one, ← map_mul, ← map_mul, inv_inv, mul_assoc]
    rfl
  exact hl.congr he

end SixProblems
end

/- Source module SixProblems.ErgodicPDApproximation. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


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
end

/- Source module SixProblems.NiceOperatorial. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped InnerProductSpace

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The common fixed subspace of a unitary representation. -/
def invariantVectors (U : G →* (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H where
  carrier := {x | ∀ g, U g x = x}
  zero_mem' := fun g ↦ map_zero (U g)
  add_mem' := fun hx hy g ↦ by simp [map_add, hx g, hy g]
  smul_mem' := fun c _ hx g ↦ by simp [map_smul, hx g]

theorem isClosed_invariantVectors (U : G →* (H ≃ₗᵢ[ℂ] H)) :
    IsClosed (invariantVectors U : Set H) := by
  rw [show (invariantVectors U : Set H) = ⋂ g : G, {x | U g x = x} by ext x; simp [invariantVectors]]
  exact isClosed_iInter (fun g ↦ isClosed_eq (U g).continuous continuous_id)

instance [CompleteSpace H] (U : G →* (H ≃ₗᵢ[ℂ] H)) : CompleteSpace (invariantVectors U) :=
  (isClosed_invariantVectors U).completeSpace_coe

/-- The orthogonal projection of Theorem 2.2(c), as an operator on the
ambient Hilbert space. -/
def invariantProjection [CompleteSpace H] (U : G →* (H ≃ₗᵢ[ℂ] H)) : H →L[ℂ] H :=
  (invariantVectors U).starProjection

/-- The unitary test in Theorem 2.2(c). -/
def NiceOperatorialRecurrence {G : Type} [Group G] (R : Set G) : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (x : H) (ε : ℝ), 0 < ε → ∃ r ∈ R,
      ‖invariantProjection U x‖ ^ 2 - ε ≤ ‖⟪x, U r x⟫_ℂ‖

theorem niceOperatorialRecurrence_of_nonnegativePD {G : Type} [Group G]
    {R : Set G} (hR : NonnegativeOnPositiveDefinite R) : NiceOperatorialRecurrence R := by
  intro H _ _ _ U x ε hε
  let P := invariantVectors U
  let u := P.starProjection x
  let v := x-u
  have hu : u ∈ P := P.starProjection_apply_mem x
  have hv : v ∈ Pᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hX : x = u+v := (add_sub_cancel u x).symm
  obtain ⟨r,hr,hvR⟩ := hR _ (realPositiveDefinite_re_coefficient U v) ε hε
  have hgu : U r u = u := hu r
  have hOrtho : ⟪u, U r v⟫_ℂ = 0 := by
    rw [← hgu, (U r).inner_map_map]
    exact hv _ hu
  have hOrtho' : ⟪v,u⟫_ℂ = 0 := inner_eq_zero_symm.mp (hv _ hu)
  have hSplit : ⟪x, U r x⟫_ℂ = ⟪u,u⟫_ℂ + ⟪v,U r v⟫_ℂ := by
    rw [hX, map_add, hgu, inner_add_left, inner_add_right, inner_add_right,
      hOrtho, hOrtho', add_zero, zero_add]
  refine ⟨r,hr,le_trans ?_ (Complex.re_le_norm _)⟩
  change ‖u‖ ^ 2 - ε ≤ _
  rw [hSplit, Complex.add_re]
  change ‖u‖ ^ 2 - ε ≤ RCLike.re (⟪u,u⟫_ℂ) + (⟪v,U r v⟫_ℂ).re
  rw [inner_self_eq_norm_sq]
  linarith

theorem niceVdC_of_niceOperatorialRecurrence {G : Type} [Group G]
    {R : Set G} (hR : NiceOperatorialRecurrence R) : NiceVdC R := by
  intro X _ _ S f hf hbound ε hε
  let U := systemKoopman S
  let P := invariantVectors U
  let hL := bounded_measurable_memLp S hf hbound
  let v := hL.toLp f
  let y := P.starProjection v
  let one := constantOne S.measure
  have hOne : one ∈ P := systemKoopman_constantOne S
  have hv : ⟪one,v-y⟫_ℂ = 0 := (Submodule.sub_starProjection_mem_orthogonal v : v-y ∈ Pᗮ) _ hOne
  have hY : ⟪one,y⟫_ℂ = ∫ x, f x ∂S.measure := by
    rw [inner_sub_right, sub_eq_zero] at hv
    rw [← hv, inner_constantOne_left]
    exact integral_congr_ae hL.coeFn_toLp
  have hn : ‖one‖ = 1 := by
    have h := congrArg Complex.re (inner_constantOne_self S.measure)
    change RCLike.re (⟪one,one⟫_ℂ) = 1 at h
    rw [inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp (by simpa only [Complex.one_re, one_pow] using h)
  have hboundY := norm_inner_le_norm (𝕜 := ℂ) one y
  rw [hY, hn, one_mul] at hboundY
  obtain ⟨r, hr, hr'⟩ := hR U v ε hε
  refine ⟨r, hr, ?_⟩
  have hcoef := inner_systemKoopman_of_memLp S hL r
  change ‖y‖ ^ 2 - ε ≤ ‖⟪v,U r v⟫_ℂ‖ at hr'
  change ⟪v,U r v⟫_ℂ = _ at hcoef
  rw [hcoef] at hr'
  exact le_trans (sub_le_sub_right (pow_le_pow_left₀ (norm_nonneg _) hboundY 2) _) hr'

end SixProblems
end

/- Source module Mixing.CyclicSpectral. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # The commutative operator algebra of a unitary representation -/


open Filter Set WeakDual
open scoped ComplexConjugate InnerProductSpace IsMulCommutative Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable section

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The bounded operators in the norm-closed unital star algebra generated by the action. -/
def spectralAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (linearRepresentation U))).topologicalClosure

theorem linearRepresentation_star (g : G) :
    star (linearRepresentation U g) = linearRepresentation U g⁻¹ := by
  change (U g : H →L[ℂ] H).adjoint = (U g⁻¹ : H →L[ℂ] H)
  rw [LinearIsometryEquiv.adjoint_eq_symm, map_inv]
  rfl

omit [CompleteSpace H] in
theorem linearRepresentation_commute (a b : G) :
    Commute (linearRepresentation U a) (linearRepresentation U b) := by
  change linearRepresentation U a * linearRepresentation U b =
    linearRepresentation U b * linearRepresentation U a
  rw [← map_mul, ← map_mul, mul_comm' a b]

instance spectralAlgebra_isMulCommutative : IsMulCommutative (spectralAlgebra U) := by
  let _ : IsMulCommutative (StarAlgebra.adjoin ℂ (Set.range (linearRepresentation U))) := by
    apply StarAlgebra.isMulCommutative_adjoin
    · rintro _ ⟨g, rfl⟩
      exact ⟨linearRepresentation_star U g ▸ linearRepresentation_commute U g⁻¹ g⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
      exact linearRepresentation_commute U a b
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
      rw [linearRepresentation_star]
      exact linearRepresentation_commute U a b⁻¹
  unfold spectralAlgebra
  infer_instance

instance spectralAlgebra_cstarAlgebra : CStarAlgebra (spectralAlgebra U) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := StarSubalgebra.isClosed_topologicalClosure _)

instance spectralAlgebra_commCStarAlgebra : CommCStarAlgebra (spectralAlgebra U) := inferInstance

/-- The original unitary operators take values in their generated C⋆-algebra. -/
def spectralGenerator : G →* spectralAlgebra U where
  toFun g := ⟨linearRepresentation U g,
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨g, rfl⟩)⟩
  map_one' := Subtype.ext (by
    change linearRepresentation U 1 = 1
    ext x
    change U 1 x = x
    rw [map_one]
    rfl)
  map_mul' a b := Subtype.ext (map_mul (linearRepresentation U) a b)

theorem spectralGenerator_star (g : G) :
    star (spectralGenerator U g) = spectralGenerator U g⁻¹ :=
  Subtype.ext (linearRepresentation_star U g)

/-- The compact Gelfand spectrum of the operator algebra. -/
abbrev RepresentationSpectrum := characterSpace ℂ (spectralAlgebra U)

/-- The inverse Gelfand transform, interpreted as a bounded Hilbert-space operator. -/
def spectralCalculus : C(RepresentationSpectrum U, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (StarSubalgebra.subtype (spectralAlgebra U)).comp
    (gelfandStarTransform (spectralAlgebra U)).symm.toStarAlgHom

/-- Evaluation of a spectrum point on the original generators gives a unitary character. -/
def spectralPointCharacter (z : RepresentationSpectrum U) : G →* Circle where
  toFun g := ⟨z (spectralGenerator U g), by
    apply mem_sphere_zero_iff_norm.mpr
    let f := gelfandStarTransform (spectralAlgebra U)
    have he : conj (z (spectralGenerator U g)) * z (spectralGenerator U g) = 1 := by
      have h : star (spectralGenerator U g) * spectralGenerator U g = 1 := by
        rw [spectralGenerator_star, ← map_mul, inv_mul_cancel, map_one]
      have hEval (a : spectralAlgebra U) : f a z = z a := rfl
      have heq := congrArg (fun a : spectralAlgebra U => f a z) h
      simpa only [map_mul, map_star, map_one, ContinuousMap.mul_apply, ContinuousMap.star_apply,
        ContinuousMap.one_apply, Complex.star_def, hEval] using heq
    have hn := congrArg norm he
    rw [norm_mul, Complex.norm_conj, norm_one] at hn
    nlinarith [norm_nonneg (z (spectralGenerator U g))]⟩
  map_one' := Subtype.ext (by
    change z (spectralGenerator U 1) = 1
    rw [map_one, map_one])
  map_mul' a b := Subtype.ext (by
    change z (spectralGenerator U (a * b)) = z (spectralGenerator U a) * z (spectralGenerator U b)
    rw [map_mul, map_mul])

/-- The continuous function on the spectrum for a single group element. -/
def spectralCoefficient (g : G) : C(RepresentationSpectrum U, ℂ) :=
  gelfandStarTransform (spectralAlgebra U) (spectralGenerator U g)

theorem spectralCoefficient_apply (g : G) (z : RepresentationSpectrum U) :
    spectralCoefficient U g z = (spectralPointCharacter U z g : ℂ) := rfl

theorem spectralCalculus_spectralCoefficient (g : G) :
    spectralCalculus U (spectralCoefficient U g) = linearRepresentation U g := by
  let Γ := gelfandStarTransform (spectralAlgebra U)
  change ((Γ.symm (Γ (spectralGenerator U g)) : spectralAlgebra U) : H →L[ℂ] H) = _
  rw [Γ.symm_apply_apply]
  rfl

/-- A finitely supported coefficient vector evaluated as a trigonometric polynomial. -/
def trigonometricPolynomial (a : G →₀ ℂ) (χ : G →* Circle) : ℂ :=
  a.sum (fun g c => c * (χ g : ℂ))

/-- The same polynomial evaluated at the represented operators. -/
def trigonometricOperator (a : G →₀ ℂ) : H →L[ℂ] H :=
  a.sum (fun g c => c • linearRepresentation U g)

/-- The polynomial made into a continuous function on the representation spectrum. -/
def spectralPolynomial (a : G →₀ ℂ) : C(RepresentationSpectrum U, ℂ) :=
  a.sum (fun g c => c • spectralCoefficient U g)

theorem spectralPolynomial_apply (a : G →₀ ℂ) (z : RepresentationSpectrum U) :
    spectralPolynomial U a z = trigonometricPolynomial a (spectralPointCharacter U z) := by
  simp only [spectralPolynomial, trigonometricPolynomial, Finsupp.sum, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, spectralCoefficient_apply]

theorem spectralCalculus_spectralPolynomial (a : G →₀ ℂ) :
    spectralCalculus U (spectralPolynomial U a) = trigonometricOperator U a := by
  simp only [spectralPolynomial, trigonometricOperator, Finsupp.sum, map_sum, map_smul,
    spectralCalculus_spectralCoefficient]

theorem spectralCalculus_norm (f : C(RepresentationSpectrum U, ℂ)) :
    ‖spectralCalculus U f‖ = ‖f‖ := by
  let Γ := gelfandStarTransform (spectralAlgebra U)
  have h : Isometry Γ := gelfandTransform_isometry (spectralAlgebra U)
  have hn := h.norm_map_of_map_zero (map_zero Γ) (Γ.symm f)
  rw [Γ.apply_symm_apply] at hn
  exact hn.symm

theorem spectralPointCharacter_injective : Function.Injective (spectralPointCharacter U) := by
  intro z w he
  let Γ := gelfandStarTransform (spectralAlgebra U)
  let φ : spectralAlgebra U →⋆ₐ[ℂ] ℂ := (ContinuousMap.evalStarAlgHom ℂ ℂ z).comp Γ.toStarAlgHom
  let ψ : spectralAlgebra U →⋆ₐ[ℂ] ℂ := (ContinuousMap.evalStarAlgHom ℂ ℂ w).comp Γ.toStarAlgHom
  have hφ : Continuous φ := map_continuous z
  have hψ : Continuous ψ := map_continuous w
  have h : φ = ψ := by
    apply StarAlgHom.ext_topologicalClosure hφ hψ
    apply StarAlgHom.ext_adjoin
    rintro ⟨a, ha⟩ ⟨g, rfl⟩
    change (spectralPointCharacter U z g : ℂ) = (spectralPointCharacter U w g : ℂ)
    rw [he]
  exact DFunLike.ext z w (fun a => congrArg (fun F : spectralAlgebra U →⋆ₐ[ℂ] ℂ => F a) h)

end

end Mixing
end

/- Source module Mixing.CyclicMeasure. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Spectral measures of vectors -/


open Filter MeasureTheory Set
open scoped CompactlySupported ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable section

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

instance : MeasurableSpace (RepresentationSpectrum U) := borel _
instance : BorelSpace (RepresentationSpectrum U) := ⟨rfl⟩

variable {X : Type*} [TopologicalSpace X]

/-- A real continuous test function regarded as a complex-valued test function. -/
def complexify (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun z => Complex.ofReal (f z), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem complexify_apply (f : C(X, ℝ)) (z : X) :
    complexify f z = Complex.ofReal (f z) := rfl

theorem complexify_add (f g : C(X, ℝ)) : complexify (f + g) = complexify f + complexify g := by
  ext z
  simp [complexify_apply]

theorem complexify_real_smul (a : ℝ) (f : C(X, ℝ)) :
    complexify (a • f) = (a : ℂ) • complexify f := by
  ext z
  simp [complexify_apply, smul_eq_mul]

theorem complexify_star (f : C(X, ℝ)) : star (complexify f) = complexify f := by
  ext z
  simp [ContinuousMap.star_apply, complexify_apply]

theorem complexify_one : complexify (1 : C(X, ℝ)) = 1 := by
  ext z
  simp

theorem complexify_sqrt_mul_self {f : C(X, ℝ)} (hf : ∀ z, 0 ≤ f z) :
    let g : C(X, ℝ) := ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩
    complexify g * complexify g = complexify f := by
  intro g
  ext z
  simp only [ContinuousMap.mul_apply, complexify_apply, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (Real.mul_self_sqrt (hf z))

/-- Evaluation of the calculus on a vector is a positive functional on
real-valued test functions. -/
def vectorStateLinear (x : H) : C(RepresentationSpectrum U, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).re
  map_add' f g := by
    rw [complexify_add, map_add]
    simp only [add_apply, inner_add_right, Complex.add_re]
  map_smul' a f := by
    rw [complexify_real_smul, map_smul]
    simp only [smul_apply, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, smul_eq_mul]

theorem vectorStateLinear_nonneg (x : H) (f : C(RepresentationSpectrum U, ℝ))
    (hf : 0 ≤ f) : 0 ≤ vectorStateLinear U x f := by
  let g : C(RepresentationSpectrum U, ℝ) :=
    ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩
  let A := spectralCalculus U (complexify g)
  have hStar : A.adjoint = A := by
    change star (spectralCalculus U (complexify g)) = spectralCalculus U (complexify g)
    rw [← map_star, complexify_star]
  have hg : complexify g * complexify g = complexify f :=
    complexify_sqrt_mul_self (fun z => hf z)
  change 0 ≤ (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).re
  rw [← hg, map_mul]
  change 0 ≤ (⟪x, A (A x)⟫_ℂ).re
  have h := A.adjoint_inner_right x (A x)
  rw [hStar] at h
  rw [h]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (A x)).ge.trans' (sq_nonneg _)

theorem vectorStateLinear_mono (x : H) : Monotone (vectorStateLinear U x) := by
  intro f g hfg
  have hSub : 0 ≤ g - f := fun z => sub_nonneg.mpr (hfg z)
  have h := vectorStateLinear_nonneg U x (g - f) hSub
  rwa [map_sub, sub_nonneg] at h

/-- The real-valued positive functional used in the Riesz–Markov construction. -/
def vectorState (x : H) : C_c(RepresentationSpectrum U, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap :=
    (vectorStateLinear U x).comp
      ({ toFun := fun f => f.toContinuousMap
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } :
        C_c(RepresentationSpectrum U, ℝ) →ₗ[ℝ] C(RepresentationSpectrum U, ℝ))
  monotone' _ _ hfg := vectorStateLinear_mono U x hfg

/-- The finite positive spectral measure of a vector on the representation spectrum. -/
def vectorSpectralMeasure (x : H) : Measure (RepresentationSpectrum U) :=
  RealRMK.rieszMeasure (vectorState U x)

instance vectorSpectralMeasure_isFinite (x : H) : IsFiniteMeasure (vectorSpectralMeasure U x) := by
  constructor
  let f : C_c(RepresentationSpectrum U, ℝ) :=
    { toFun := 1
      hasCompactSupport' := HasCompactSupport.of_compactSpace 1 }
  apply (RealRMK.rieszMeasure_le_of_eq_one (Λ := vectorState U x)
    (f := f) (fun _ => zero_le_one) isCompact_univ (fun _ _ => rfl)).trans_lt
  exact ENNReal.ofReal_lt_top

theorem integral_vectorSpectralMeasure_real (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    ∫ z, f z ∂vectorSpectralMeasure U x = (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).re := by
  let fc : C_c(RepresentationSpectrum U, ℝ) :=
    { toContinuousMap := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  have h := RealRMK.integral_rieszMeasure (vectorState U x) fc
  change (∫ z, f z ∂vectorSpectralMeasure U x) = _ at h
  exact h

theorem inner_spectralCalculus_complexify_im (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).im = 0 := by
  let A := spectralCalculus U (complexify f)
  have hStar : A.adjoint = A := by
    change star (spectralCalculus U (complexify f)) = spectralCalculus U (complexify f)
    rw [← map_star, complexify_star]
  have he : conj ⟪x, A x⟫_ℂ = ⟪x, A x⟫_ℂ := by
    rw [inner_conj_symm, ← A.adjoint_inner_right, hStar]
  have h := congrArg Complex.im he
  rw [Complex.conj_im] at h
  exact neg_eq_self.mp h

theorem integral_vectorSpectralMeasure_complexify (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    ∫ z, complexify f z ∂vectorSpectralMeasure U x =
      ⟪x, spectralCalculus U (complexify f) x⟫_ℂ := by
  have h := integral_ofReal (𝕜 := ℂ) (f := ⇑f) (μ := vectorSpectralMeasure U x)
  rw [integral_vectorSpectralMeasure_real U x f] at h
  change (∫ z, Complex.ofReal (f z) ∂vectorSpectralMeasure U x) = _
  refine h.trans ?_
  exact Complex.ext (by simp) (by
    change 0 = (⟪x, spectralCalculus U (complexify f) x⟫_ℂ).im
    exact (inner_spectralCalculus_complexify_im U x f).symm)

set_option maxHeartbeats 1200000 in
/-- Riesz representation of the complex vector state. -/
theorem integral_vectorSpectralMeasure (x : H) (f : C(RepresentationSpectrum U, ℂ)) :
    ∫ z, f z ∂vectorSpectralMeasure U x = ⟪x, spectralCalculus U f x⟫_ℂ := by
  let re : C(RepresentationSpectrum U, ℝ) := ⟨fun z => (f z).re, Complex.continuous_re.comp f.continuous⟩
  let im : C(RepresentationSpectrum U, ℝ) := ⟨fun z => (f z).im, Complex.continuous_im.comp f.continuous⟩
  have hf : f = complexify re + Complex.I • complexify im := by
    ext z
    change f z = Complex.ofReal (f z).re + Complex.I * Complex.ofReal (f z).im
    exact (Complex.re_add_im (f z)).symm.trans (by rw [mul_comm Complex.I])
  rw [hf, map_add, map_smul, add_apply, smul_apply, inner_add_right, inner_smul_right]
  have hRe := (complexify re).continuous.integrable_of_hasCompactSupport
    (μ := vectorSpectralMeasure U x) (HasCompactSupport.of_compactSpace _)
  have hIm := (complexify im).continuous.integrable_of_hasCompactSupport
    (μ := vectorSpectralMeasure U x) (HasCompactSupport.of_compactSpace _)
  refine (integral_add hRe (hIm.smul Complex.I)).trans ?_
  exact congrArg₂ (· + ·) (integral_vectorSpectralMeasure_complexify U x re)
    ((integral_smul (μ := vectorSpectralMeasure U x) Complex.I (⇑(complexify im))).trans
      (congrArg (Complex.I • ·) (integral_vectorSpectralMeasure_complexify U x im)))

theorem vectorSpectralMeasure_mass (x : H) :
    (vectorSpectralMeasure U x Set.univ).toReal = ‖x‖ ^ 2 := by
  have h := integral_vectorSpectralMeasure_real U x (1 : C(RepresentationSpectrum U, ℝ))
  have hRe : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  change (vectorSpectralMeasure U x).real Set.univ = _
  simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, complexify_one,
    map_one, one_apply_eq_self, hRe] using h

/-- The matrix coefficient of a trigonometric polynomial is integrated against
the vector's spectral measure. -/
theorem integral_spectralPolynomial (x : H) (a : G →₀ ℂ) :
    ∫ z, trigonometricPolynomial a (spectralPointCharacter U z) ∂vectorSpectralMeasure U x =
      ⟪x, trigonometricOperator U a x⟫_ℂ := by
  simpa only [spectralPolynomial_apply, spectralCalculus_spectralPolynomial] using
    integral_vectorSpectralMeasure U x (spectralPolynomial U a)

end

end Mixing
end

/- Source module Mixing.CyclicL2. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Realizing the cyclic spectral measure in the original Hilbert space -/


open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable section

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

instance vectorSpectralMeasure_regular (x : H) : (vectorSpectralMeasure U x).Regular :=
  RealRMK.regular_rieszMeasure _

/-- Apply a continuous spectral multiplier to the chosen vector. -/
def spectralVectorLinear (x : H) : C(RepresentationSpectrum U, ℂ) →ₗ[ℂ] H where
  toFun f := spectralCalculus U f x
  map_add' f g := by rw [map_add, add_apply]
  map_smul' a f := by rw [map_smul, smul_apply, RingHom.id_apply]

set_option maxHeartbeats 1200000 in
theorem spectralVectorLinear_inner (x : H) (f g : C(RepresentationSpectrum U, ℂ)) :
    ⟪spectralVectorLinear U x f, spectralVectorLinear U x g⟫_ℂ =
      ∫ z, g z * conj (f z) ∂vectorSpectralMeasure U x := by
  change ⟪spectralCalculus U f x, spectralCalculus U g x⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change ⟪x, (star (spectralCalculus U f) * spectralCalculus U g) x⟫_ℂ = _
  rw [← map_star, ← map_mul, ← integral_vectorSpectralMeasure]
  apply integral_congr_ae
  exact .of_forall fun z => by
    change conj (f z) * g z = g z * conj (f z)
    exact mul_comm _ _

theorem spectralVectorLinear_norm (x : H) (f : C(RepresentationSpectrum U, ℂ)) :
    ‖spectralVectorLinear U x f‖ = ‖ContinuousMap.toLp 2 (vectorSpectralMeasure U x) ℂ f‖ := by
  have h := (spectralVectorLinear_inner U x f f).trans
    (ContinuousMap.inner_toLp (vectorSpectralMeasure U x) f f).symm
  have hNorm := congrArg Complex.re h
  simp only [show ∀ y : H, (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ),
    show ∀ y : Lp ℂ 2 (vectorSpectralMeasure U x), (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2
      from inner_self_eq_norm_sq (𝕜 := ℂ)] at hNorm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hNorm

/-- The vector's cyclic spectral isometry, extending continuous multipliers to
all of the spectral `L²` space. -/
def cyclicSpectralIsometry (x : H) : Lp ℂ 2 (vectorSpectralMeasure U x) →ₗᵢ[ℂ] H :=
  (spectralVectorLinear U x).extendOfIsometry
    (ContinuousMap.toLp_denseRange (p := 2) ℂ (vectorSpectralMeasure U x) ℂ ENNReal.ofNat_ne_top)
    (spectralVectorLinear_norm U x)

theorem cyclicSpectralIsometry_toLp (x : H) (f : C(RepresentationSpectrum U, ℂ)) :
    cyclicSpectralIsometry U x (ContinuousMap.toLp 2 (vectorSpectralMeasure U x) ℂ f) =
      spectralCalculus U f x :=
  LinearMap.extendOfIsometry_eq _ _ _ f

theorem inner_cyclicSpectralIsometry_spectralCalculus (x : H)
    (w : Lp ℂ 2 (vectorSpectralMeasure U x)) (f : C(RepresentationSpectrum U, ℂ)) :
    ⟪cyclicSpectralIsometry U x w, spectralCalculus U f x⟫_ℂ =
      ⟪w, ContinuousMap.toLp 2 (vectorSpectralMeasure U x) ℂ f⟫_ℂ := by
  rw [← cyclicSpectralIsometry_toLp]
  exact (cyclicSpectralIsometry U x).inner_map_map _ _

theorem inner_cyclicSpectralIsometry_indicator (x : H)
    {A : Set (RepresentationSpectrum U)} (hA : MeasurableSet A)
    (f : C(RepresentationSpectrum U, ℂ)) :
    ⟪cyclicSpectralIsometry U x (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ)),
      spectralCalculus U f x⟫_ℂ =
      ∫ z in A, f z ∂vectorSpectralMeasure U x := by
  rw [inner_cyclicSpectralIsometry_spectralCalculus, L2.inner_indicatorConstLp_one]
  exact integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (vectorSpectralMeasure U x) f).filter_mono ae_restrict_le)

/-- A vector in an ultrafilter operator's kernel has no spectral atoms.
The test vector for a point mass is the image of its indicator under the
cyclic spectral isometry. Its matrix coefficient has constant nonzero
modulus if the point mass is positive. -/
theorem vectorSpectralMeasure_noAtoms_of_ultrafilterOperator_apply_eq_zero
    (x : H) (p : Ultrafilter G) (hx : ultrafilterOperator U p x = 0) :
    NullSingletonClass (vectorSpectralMeasure U x) := by
  constructor
  intro z
  let μ := vectorSpectralMeasure U x
  let A := ({z} : Set (RepresentationSpectrum U))
  have hA : MeasurableSet A := measurableSet_singleton _
  let w := cyclicSpectralIsometry U x (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ))
  have hcoeff (g : G) : ⟪w, U g x⟫_ℂ = (μ.real A : ℂ) * spectralCoefficient U g z := by
    change ⟪w, linearRepresentation U g x⟫_ℂ = _
    rw [← spectralCalculus_spectralCoefficient U g]
    change ⟪cyclicSpectralIsometry U x (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℂ)),
      spectralCalculus U (spectralCoefficient U g) x⟫_ℂ = _
    rw [inner_cyclicSpectralIsometry_indicator U x hA]
    change (∫ t in {z}, spectralCoefficient U g t ∂μ) = _
    rw [integral_singleton]
    rfl
  have hNorm (g : G) : ‖⟪w, U g x⟫_ℂ‖ = μ.real A := by
    rw [hcoeff, norm_mul, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
      spectralCoefficient_apply, Circle.norm_coe, mul_one]
  have hlim := (tendsto_ultrafilterOperator_coeff U p w x).norm
  have hzero : μ.real A = 0 := by
    rw [hx, inner_zero_right, norm_zero] at hlim
    have he : Tendsto (fun g : G => ‖⟪w, U g x⟫_ℂ‖) (p : Filter G) (𝓝 (μ.real A)) :=
      tendsto_const_nhds.congr' (.of_forall fun g => (hNorm g).symm)
    exact tendsto_nhds_unique he hlim
  exact (measureReal_eq_zero_iff (measure_ne_top μ A)).mp hzero

end

end Mixing
end

/- Source module Mixing.StrongMixing. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Strong mixing and its spectral disjointness criterion -/


open Filter Set
open scoped Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The free ultrafilters, written `G*` in the paper. -/
def freeUltrafilters (G : Type*) : Set (Ultrafilter G) := {p | (p : Filter G) ≤ cofinite}

/-- The weak coefficients converge to zero along every sequence escaping finite sets. -/
def IsStronglyMixing : Prop :=
  ∀ g : ℕ → G, Tendsto g atTop cofinite → ∀ x y : H,
    Tendsto (fun n => inner ℂ x (U (g n) y)) atTop (𝓝 0)

/-- Testing a cofinite limit on sequences escaping finite sets. -/
theorem tendsto_cofinite_iff_forall_escaping_sequences {G X : Type*} [TopologicalSpace X]
    (f : G → X) (x : X) :
    Tendsto f cofinite (𝓝 x) ↔ ∀ g : ℕ → G, Tendsto g atTop cofinite →
      Tendsto (f ∘ g) atTop (𝓝 x) := by
  constructor
  · intro h g hg
    exact h.comp hg
  · intro h
    by_contra hn
    obtain ⟨S, hS, hbad⟩ := not_tendsto_iff_exists_frequently_notMem.mp hn
    have hInf : {g | f g ∉ S}.Infinite := frequently_cofinite_iff_infinite.mp hbad
    let e := Set.Infinite.natEmbedding _ hInf
    let g : ℕ → G := fun n => (e n : G)
    have hg : Function.Injective g := Subtype.val_injective.comp e.injective
    have hlim := h g (Nat.cofinite_eq_atTop ▸ hg.tendsto_cofinite)
    have hEv : ∀ᶠ n in atTop, f (g n) ∈ S := hlim.eventually hS
    obtain ⟨n, hn⟩ := hEv.exists
    exact (e n).property hn

theorem isStronglyMixing_iff_isUMixing_free :
    IsStronglyMixing U ↔ IsUMixing U (freeUltrafilters G) := by
  constructor
  · intro h p hp
    apply ContinuousLinearMap.ext
    intro y
    apply ext_inner_left ℂ
    intro x
    have hC := (tendsto_cofinite_iff_forall_escaping_sequences
      (fun g => inner ℂ x (U g y)) 0).mpr fun g hg => h g hg x y
    simpa only [zero_apply, inner_zero_right] using
      tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p x y) (hC.mono_left hp)
  · intro h g hg x y
    have hC : Tendsto (fun a => inner ℂ x (U a y)) cofinite (𝓝 0) := by
      apply (Filter.tendsto_iff_ultrafilter _ _ _).mpr
      intro p hp
      have hlim := tendsto_ultrafilterOperator_coeff U p x y
      rw [h p hp, zero_apply, inner_zero_right] at hlim
      exact hlim
    exact hC.comp hg

/-- The iterates `Δ^n` in Proposition 6(i). -/
def ultrafilterDeltaIterate (P : Set (Ultrafilter G)) : ℕ → Set (Ultrafilter G)
  | 0 => P
  | n + 1 => ultrafilterDelta (ultrafilterDeltaIterate P n)

/-- Proposition 6(i), strong mixing can be tested using any iterate of Δ. -/
theorem isStronglyMixing_iff_isUMixing_deltaIterate (n : ℕ) :
    IsStronglyMixing U ↔ IsUMixing U (ultrafilterDeltaIterate (freeUltrafilters G) n) := by
  induction n with
  | zero => exact isStronglyMixing_iff_isUMixing_free U
  | succ n ih => exact ih.trans (isUMixing_iff_ultrafilterDelta U _)

variable [IsMulCommutative G]

/-- Proposition 6(ii), strong mixing can be tested on products of any fixed
positive number `n+1` of free ultrafilters. -/
theorem isStronglyMixing_iff_isUMixing_freeProducts (n : ℕ) :
    IsStronglyMixing U ↔ IsUMixing U (ultrafilterProductsSucc (freeUltrafilters G) n) :=
  (isStronglyMixing_iff_isUMixing_free U).trans (isUMixing_iff_ultrafilterProductsSucc U _ n)

universe u

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable (U₁ : G →* (H₁ ≃ₗᵢ[ℂ] H₁))

/-- Corollary 5(i). Generation by the free ultrafilters is equivalent to
spectral disjointness from all strongly mixing actions. -/
theorem generated_free_iff_spectrallyDisjoint_all_stronglyMixing :
    IsUGenerated U₁ (freeUltrafilters G) ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (V : G →* (K ≃ₗᵢ[ℂ] K)), IsStronglyMixing V → SpectrallyDisjoint U₁ V := by
  constructor
  · intro h K _ _ _ V hV
    have hd := (theorem3_1 U₁ (freeUltrafilters G)).2.mp h
    exact @hd K _ _ _ V ((isStronglyMixing_iff_isUMixing_free V).mp hV)
  · intro h
    apply (theorem3_1 U₁ (freeUltrafilters G)).2.mpr
    intro K _ _ _ V hV
    exact @h K _ _ _ V ((isStronglyMixing_iff_isUMixing_free V).mpr hV)

omit [IsMulCommutative G] in
/-- Corollary 5(ii). An injective ultrafilter operator is a sufficient condition
for disjointness from every action mixing along that ultrafilter. -/
theorem spectrallyDisjoint_of_ultrafilterOperator_injective {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : G →* (K ≃ₗᵢ[ℂ] K)) (p : Ultrafilter G)
    (hU : Function.Injective (ultrafilterOperator U p)) (hV : ultrafilterOperator V p = 0) :
    SpectrallyDisjoint U V := by
  intro J hJ
  apply ContinuousLinearMap.ext
  intro x
  apply hU
  rw [← hJ.ultrafilter, hV, zero_apply, map_zero, zero_apply, map_zero]

end Mixing
end

/- Source module Mixing.SpectralDual. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Spectral measures on the Pontryagin dual -/


open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Mixing Topology

namespace Mixing

variable {G : Type*} [Group G]

noncomputable section

/-- The Pontryagin dual endowed with its compact-open topology for discrete G. -/
abbrev DiscreteDual (G : Type*) [Group G] := @PontryaginDual G _ ⊥

instance : MeasurableSpace (DiscreteDual G) := borel _
instance : BorelSpace (DiscreteDual G) := ⟨rfl⟩

instance discreteDual_compactSpace : CompactSpace (DiscreteDual G) := by
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  change CompactSpace (G →ₜ* Circle)
  infer_instance

/-- Evaluation of a character at a fixed group element, as a circle-valued continuous map. -/
def dualEvaluation (g : G) : C(DiscreteDual G, Circle) := by
  let _ : TopologicalSpace G := ⊥
  exact (⟨fun χ : G →ₜ* Circle => χ g, continuous_eval_const g⟩ : C(G →ₜ* Circle, Circle))

variable {H : Type*} [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- A spectrum point gives a continuous character of discrete G. -/
def spectralPointDual (z : RepresentationSpectrum U) : DiscreteDual G := by
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  exact ⟨spectralPointCharacter U z, continuous_of_discreteTopology⟩

theorem spectralPointDual_continuous : Continuous (spectralPointDual U) := by
  let _ : TopologicalSpace G := ⊥
  let _ : DiscreteTopology G := ⟨rfl⟩
  change Continuous (fun z : RepresentationSpectrum U => (spectralPointDual U z : G →ₜ* Circle))
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  rw [continuous_iff_continuousAt]
  rintro ⟨z, g⟩
  have hg : ∀ᶠ t : RepresentationSpectrum U × G in 𝓝 (z, g), t.2 = g := by
    have h : ∀ᶠ g' in 𝓝 g, g' = g := (isOpen_discrete _).mem_nhds (Set.mem_singleton g)
    exact (continuous_snd.tendsto (z, g)).eventually h
  have hc : Continuous (fun z' : RepresentationSpectrum U => dualEvaluation g (spectralPointDual U z')) := by
    exact (spectralCoefficient U g).continuous.subtype_mk _
  have ht := (hc.comp continuous_fst).tendsto (z, g)
  apply ht.congr'
  filter_upwards [hg] with t ht
  change spectralPointCharacter U t.1 g = spectralPointCharacter U t.1 t.2
  rw [ht]

theorem spectralPointDual_injective : Function.Injective (spectralPointDual U) := by
  intro z w h
  apply spectralPointCharacter_injective U
  ext g
  exact congrArg (fun χ => (dualEvaluation g χ : ℂ)) h

/-- The spectral measure of the vector on the paper's common frequency space. -/
def dualVectorSpectralMeasure (x : H) : Measure (DiscreteDual G) :=
  (vectorSpectralMeasure U x).map (spectralPointDual U)

instance dualVectorSpectralMeasure_isFinite (x : H) : IsFiniteMeasure (dualVectorSpectralMeasure U x) :=
  Measure.isFiniteMeasure_map _ _

instance dualVectorSpectralMeasure_regular (x : H) : (dualVectorSpectralMeasure U x).Regular := by
  have : (dualVectorSpectralMeasure U x).InnerRegular :=
    Measure.InnerRegular.map_of_continuous (spectralPointDual_continuous U)
  infer_instance

/-- The Fourier coefficient at a group element, with the convention linear
in the acted-on vector. -/
def spectralFourier (μ : Measure (DiscreteDual G)) (g : G) : ℂ :=
  ∫ χ, (dualEvaluation g χ : ℂ) ∂μ

theorem spectralFourier_dualVectorSpectralMeasure (x : H) (g : G) :
    spectralFourier (dualVectorSpectralMeasure U x) g = ⟪x, U g x⟫_ℂ := by
  unfold spectralFourier dualVectorSpectralMeasure
  rw [integral_map (spectralPointDual_continuous U).measurable.aemeasurable]
  · calc
      _ = ∫ z, spectralCoefficient U g z ∂vectorSpectralMeasure U x :=
        integral_congr_ae (.of_forall fun _ => rfl)
      _ = _ := by
        rw [integral_vectorSpectralMeasure, spectralCalculus_spectralCoefficient]
        rfl
  · exact (continuous_subtype_val.comp (dualEvaluation g).continuous).aestronglyMeasurable

/-- The spectral Fourier formulation of ultrafilter mixing before passing to
a maximal spectral type. The tested family is `βG+P`. -/
theorem isUMixing_iff_all_vector_fourier_vanish (P : Set (Ultrafilter G)) :
    IsUMixing U P ↔ ∀ x : H, ∀ p ∈ P, ∀ q : Ultrafilter G,
      Tendsto (spectralFourier (dualVectorSpectralMeasure U x))
        ((q * p : Ultrafilter G) : Filter G) (𝓝 0) := by
  constructor
  · intro hU x p hp q
    have hzero : ultrafilterOperator U (q * p) = 0 := by
      rw [ultrafilterOperator_mul, hU p hp, mul_zero]
    rw [funext (spectralFourier_dualVectorSpectralMeasure U x)]
    simpa only [hzero, zero_apply, inner_zero_right] using
      tendsto_ultrafilterOperator_coeff U (q * p) x x
  · intro hU p hp
    apply ContinuousLinearMap.coe_injective
    rw [ContinuousLinearMap.toLinearMap_zero, ← inner_map_self_eq_zero]
    intro x
    have hlim := tendsto_ultrafilterOperator_coeff U (pure 1 * p) x x
    have heq : (pure 1 : Ultrafilter G) * p = p := by
      apply Ultrafilter.coe_inj.mp
      ext S
      change (∀ᶠ a in ((pure 1 * p : Ultrafilter G) : Filter G), a ∈ S) ↔
        ∀ᶠ a in (p : Filter G), a ∈ S
      simp [Ultrafilter.eventually_mul]
    have hlim' := hU x p hp (pure 1)
    rw [heq] at hlim
    rw [heq, funext (spectralFourier_dualVectorSpectralMeasure U x)] at hlim'
    have hzero := tendsto_nhds_unique hlim hlim'
    rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm, hzero, map_zero]

end

end Mixing
end

/- Source module SixProblems.NiceSpectral. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

noncomputable section

open MeasureTheory Mixing Set
open scoped Classical ENNReal InnerProductSpace ComplexConjugate Matrix

variable {G : Type} [Group G]

/-- The Fourier condition of Theorem 2.2(f), expressed with a positive error. -/
def NiceFCPlus (R : Set G) : Prop :=
  ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ], ∀ ε > 0,
    ∃ r ∈ R, τ.real {1} - ε ≤ ‖spectralFourier τ r‖

private def χeval (g : G) (χ : DiscreteDual G) : ℂ := dualEvaluation g χ

private theorem χeval_continuous (g : G) : Continuous (χeval g) :=
  continuous_subtype_val.comp (dualEvaluation g).continuous

@[simp] private theorem χeval_norm (g : G) (χ : DiscreteDual G) : ‖χeval g χ‖ = 1 :=
  Circle.norm_coe _

@[simp] private theorem χeval_trivial (g : G) : χeval g (1 : DiscreteDual G) = 1 := by
  rfl

private theorem χeval_mul_inv (g h : G) (χ : DiscreteDual G) :
    χeval (g*h⁻¹) χ = χeval g χ * conj (χeval h χ) := by
  change ((χ (g*h⁻¹) : Circle) : ℂ) = (χ g : ℂ) * conj (χ h : ℂ)
  rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv_eq_conj]

private theorem χeval_inv (g : G) (χ : DiscreteDual G) :
    χeval g⁻¹ χ = conj (χeval g χ) := by
  change ((χ g⁻¹ : Circle) : ℂ) = conj (χ g : ℂ)
  rw [map_inv, Circle.coe_inv_eq_conj]

private theorem χeval_integrable (τ : Measure (DiscreteDual G)) [IsFiniteMeasure τ] (g : G) :
    Integrable (χeval g) τ :=
  Integrable.of_bound (χeval_continuous g).aestronglyMeasurable 1
    (.of_forall fun χ ↦ (χeval_norm g χ).le)

private theorem spectralFourier_re (τ : Measure (DiscreteDual G)) [IsFiniteMeasure τ] (g : G) :
    (spectralFourier τ g).re = ∫ χ, (χeval g χ).re ∂τ :=
  (integral_re (χeval_integrable τ g)).symm

private theorem spectralFourier_inv (τ : Measure (DiscreteDual G)) (g : G) :
    spectralFourier τ g⁻¹ = conj (spectralFourier τ g) := by
  change (∫ χ, χeval g⁻¹ χ ∂τ) = conj (∫ χ, χeval g χ ∂τ)
  simp_rw [χeval_inv]
  exact integral_conj

theorem norm_spectralFourier_le (τ : Measure (DiscreteDual G)) (g : G) :
    ‖spectralFourier τ g‖ ≤ τ.real univ := by
  change ‖∫ χ, χeval g χ ∂τ‖ ≤ _
  exact (norm_integral_le_integral_norm _).trans_eq (by simp [measureReal_def])

/-- Real parts of Fourier coefficients of finite positive measures are positive definite. -/
theorem spectralFourier_realPositiveDefinite (τ : Measure (DiscreteDual G)) [IsFiniteMeasure τ] :
    RealPositiveDefinite (fun g ↦ (spectralFourier τ g).re) := by
  intro I
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    refine Matrix.IsSymm.ext fun i j ↦ ?_
    change (spectralFourier τ ((j : G)*(i : G)⁻¹)).re =
      (spectralFourier τ ((i : G)*(j : G)⁻¹)).re
    rw [show (j : G)*(i : G)⁻¹ = ((i : G)*(j : G)⁻¹)⁻¹ by group,
      spectralFourier_inv, Complex.conj_re]
  intro a
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  let v (i j : I) (χ : DiscreteDual G) := a i * ((χeval ((i : G)*(j : G)⁻¹) χ).re * a j)
  have hv i j : Integrable (v i j) τ := ((χeval_integrable τ _).re.mul_const _).const_mul _
  have hFin :
      (∫ χ, ∑ i, ∑ j, v i j χ ∂τ) =
        ∑ i : I, ∑ j : I, a i * ((spectralFourier τ ((i : G)*(j : G)⁻¹)).re * a j) := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hv i j))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ (fun j _ ↦ hv i j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show v i j = fun χ ↦ a i * ((χeval ((i : G)*(j : G)⁻¹) χ).re * a j) from rfl,
      integral_const_mul, integral_mul_const, ← spectralFourier_re]
  rw [← hFin]
  apply integral_nonneg
  intro χ
  change 0 ≤ ∑ i, ∑ j, v i j χ
  let : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal
  let u (i : I) := χeval (i : G) χ
  have hMat : (Matrix.of fun i j : I ↦ (χeval ((i : G)*(j : G)⁻¹) χ).re) = (Matrix.gram ℝ u)ᵀ := by
    ext i j
    change (χeval ((i : G)*(j : G)⁻¹) χ).re = (⟪u j, u i⟫_ℂ).re
    rw [χeval_mul_inv, RCLike.inner_apply', mul_comm]
  have hPos : (Matrix.gram ℝ u).PosSemidef := Matrix.posSemidef_gram ℝ u
  have h := hPos.transpose.dotProduct_mulVec_nonneg a
  rw [← hMat] at h
  simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, v, star_trivial] using h

/-- The supremum formulation of Theorem 2.2(f) on a nonempty testing set. -/
theorem niceFCPlus_iff_sSup {R : Set G} (hR : R.Nonempty) : NiceFCPlus R ↔
    ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ],
      τ.real {1} ≤ sSup ((fun g ↦ ‖spectralFourier τ g‖) '' R) := by
  constructor
  · intro h τ hτ
    by_contra! hn
    have hB : BddAbove ((fun g ↦ ‖spectralFourier τ g‖) '' R) :=
      ⟨τ.real univ, fun _ ⟨g, _, hg⟩ ↦ hg ▸ norm_spectralFourier_le τ g⟩
    obtain ⟨g, hg, hge⟩ := h τ _ (half_pos (sub_pos.mpr hn))
    have hle := le_csSup hB (Set.mem_image_of_mem _ hg)
    linarith
  · intro h τ hτ ε hε
    by_contra! hn
    have hle : sSup ((fun g ↦ ‖spectralFourier τ g‖) '' R) ≤ τ.real {1} - ε :=
      csSup_le (hR.image _) (by rintro _ ⟨g, hg, rfl⟩; exact (hn g hg).le)
    linarith [h τ]

private theorem spectralFourier_add_measures (τ σ : Measure (DiscreteDual G))
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] (g : G) :
    spectralFourier (τ + σ) g = spectralFourier τ g + spectralFourier σ g :=
  integral_add_measure (χeval_integrable τ g) (χeval_integrable σ g)

private theorem spectralFourier_smul_measure (τ : Measure (DiscreteDual G)) (c : ℝ≥0∞) (g : G) :
    spectralFourier (c • τ) g = c.toReal • spectralFourier τ g :=
  integral_smul_measure _ _

@[simp] private theorem spectralFourier_dirac_trivial (g : G) :
    spectralFourier (Measure.dirac (1 : DiscreteDual G)) g = 1 := by
  change ∫ χ, χeval g χ ∂Measure.dirac (1 : DiscreteDual G) = 1
  rw [integral_dirac' _ _ (χeval_continuous g).stronglyMeasurable, χeval_trivial]

theorem niceFCPlus_of_nonnegativePD {R : Set G} (h : NonnegativeOnPositiveDefinite R) :
    NiceFCPlus R := by
  intro τ hτ ε hε
  let A := ({1} : Set (DiscreteDual G))
  let ν := τ.restrict Aᶜ
  obtain ⟨r, hr, hneg⟩ := h _ (spectralFourier_realPositiveDefinite ν) ε hε
  refine ⟨r, hr, ?_⟩
  have hn := Complex.re_le_norm (spectralFourier τ r)
  have heq : spectralFourier τ r = spectralFourier ν r + (τ.real A : ℂ) := by
    have hm : MeasurableSet A := measurableSet_singleton _
    rw [← Measure.restrict_compl_add_restrict (μ := τ) hm, spectralFourier_add_measures]
    congr 1
    change spectralFourier (τ.restrict ({1} : Set (DiscreteDual G))) r = _
    rw [Measure.restrict_singleton, spectralFourier_smul_measure, spectralFourier_dirac_trivial]
    simp [measureReal_def, A]
  rw [heq, Complex.add_re, Complex.ofReal_re] at hn
  rw [← heq] at hn
  change τ.real A - ε ≤ _
  linarith

private theorem niceFCPlus_finite {R : Set G} (h : NiceFCPlus R)
    (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ r ∈ R, μ.real {1} - ε ≤ ‖spectralFourier μ r‖ := by
  let ν : FiniteMeasure (DiscreteDual G) := ⟨μ, inferInstance⟩
  let τ : Measure (DiscreteDual G) := ν.normalize
  have hμ : μ = (ν.mass : ℝ≥0∞) • τ :=
    congrArg (fun v : FiniteMeasure (DiscreteDual G) ↦ (v : Measure (DiscreteDual G)))
      ν.self_eq_mass_smul_normalize
  let c : ℝ := ν.mass
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have hε' : 0 < ε / (c + 1) := div_pos hε (by linarith)
  have : IsProbabilityMeasure τ := inferInstanceAs
    (IsProbabilityMeasure (ν.normalize : Measure (DiscreteDual G)))
  obtain ⟨r, hr, hb⟩ := h τ _ hε'
  refine ⟨r, hr, ?_⟩
  have hAtom : μ.real {1} = c * τ.real {1} := by
    rw [hμ]
    change (((ν.mass : ℝ≥0∞) • τ) {1}).toReal = _
    rw [smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rfl
  have hFourier : ‖spectralFourier μ r‖ = c * ‖spectralFourier τ r‖ := by
    rw [hμ, spectralFourier_smul_measure, norm_smul, ENNReal.coe_toReal, Real.norm_eq_abs,
      abs_of_nonneg hc]
  have hδ : c * (ε / (c+1)) ≤ ε := calc
    _ ≤ (c+1) * (ε / (c+1)) := mul_le_mul_of_nonneg_right (by linarith) hε'.le
    _ = ε := by field_simp
  rw [hAtom, hFourier]
  linarith [mul_le_mul_of_nonneg_left hb hc]

variable [Countable G] [IsMulCommutative G]

private theorem exists_spectralFourier_eq_realPD (φ : G → ℝ) (hφ : RealPositiveDefinite φ) :
    ∃ μ : Measure (DiscreteDual G), IsFiniteMeasure μ ∧ ∀ g, spectralFourier μ g = (φ g : ℂ) := by
  let S := gaussianPathSystem φ hφ
  let f : (G → ℝ) → ℂ := fun x ↦ (x 1 : ℂ)
  have hf : MemLp f 2 S.measure := (gaussianPath_coordinate_memLp φ hφ 1).ofReal
  let v := hf.toLp f
  let μ := dualVectorSpectralMeasure (systemKoopman S) v
  refine ⟨μ, inferInstance, fun g ↦ ?_⟩
  rw [show spectralFourier μ g = _ from spectralFourier_dualVectorSpectralMeasure
    (systemKoopman S) v g]
  rw [show ⟪v, systemKoopman S g v⟫_ℂ = _ from inner_systemKoopman_of_memLp S hf g]
  change (∫ x, (x ((g⁻¹)⁻¹ * 1) : ℂ) * conj (x 1 : ℂ) ∂S.measure) = _
  simp only [inv_inv, mul_one, Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal]
  exact congrArg Complex.ofReal ((gaussianPath_covariance φ hφ g 1).trans
    (by rw [mul_one, hφ.inv_eq]))

theorem nonnegativePD_of_niceFCPlus {R : Set G} (h : NiceFCPlus R) :
    NonnegativeOnPositiveDefinite R := by
  intro φ hφ ε hε
  obtain ⟨μ, hμ, hμFourier⟩ := exists_spectralFourier_eq_realPD φ hφ
  let c := (φ 1 + 1).toNNReal
  let δ : Measure (DiscreteDual G) := Measure.dirac 1
  let ν := μ + c • δ
  have hc : (c : ℝ) = φ 1 + 1 := Real.coe_toNNReal _ (by linarith [hφ.one_nonneg])
  have hc' : 0 ≤ (c : ℝ) := NNReal.coe_nonneg _
  have : IsFiniteMeasure δ := inferInstanceAs (IsFiniteMeasure (Measure.dirac (1 : DiscreteDual G)))
  have : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (μ + c • δ))
  have hAtom : (c : ℝ) ≤ ν.real {1} := by
    have hmn : (c • δ) {1} ≤ ν {1} := by
      change (c • δ) {1} ≤ (μ + c • δ) {1}
      rw [add_apply]
      exact le_add_self
    have ht := (ENNReal.toReal_le_toReal (measure_ne_top (c • δ) {1})
      (measure_ne_top ν {1})).mpr hmn
    have hδ : δ {1} = 1 := Measure.dirac_apply_of_mem (Set.mem_singleton _)
    simpa only [← Measure.coe_nnreal_smul, smul_apply, smul_eq_mul, hδ, mul_one,
      ENNReal.coe_toReal, measureReal_def] using ht
  obtain ⟨r, hr, hν⟩ := niceFCPlus_finite h ν ε hε
  refine ⟨r, hr, ?_⟩
  have hCalc : spectralFourier ν r = ((φ r + c : ℝ) : ℂ) := by
    change spectralFourier (μ + c • δ) r = _
    rw [spectralFourier_add_measures, hμFourier, ← Measure.coe_nnreal_smul,
      spectralFourier_smul_measure, ENNReal.coe_toReal, Complex.ofReal_add]
    change (φ r : ℂ) + (c : ℝ) • spectralFourier (Measure.dirac (1 : DiscreteDual G)) r = _
    rw [spectralFourier_dirac_trivial]
    simp
  have hpos : 0 ≤ φ r + c := by
    rw [hc]
    linarith [(abs_le.mp (hφ.abs_le_one r)).1]
  rw [hCalc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at hν
  linarith

/-- The abelian clause of Theorem 2.2 is equivalent to the real
    positive-definite condition. -/
theorem niceFCPlus_iff_nonnegativePD {R : Set G} :
    NiceFCPlus R ↔ NonnegativeOnPositiveDefinite R :=
  ⟨nonnegativePD_of_niceFCPlus, niceFCPlus_of_nonnegativePD⟩

/-- Theorem 2.2(d) and (f), both in the supremum form printed in the paper. -/
theorem theorem2_2_d_iff_f {R : Set G} (hR : R.Nonempty) :
    (∀ φ : G → ℝ, RealPositiveDefinite φ → 0 ≤ sSup (φ '' R)) ↔
      ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ],
        τ.real {1} ≤ sSup ((fun r ↦ ‖spectralFourier τ r‖) '' R) :=
  (nonnegativeOnPositiveDefinite_iff_sSup hR).symm.trans
    (niceFCPlus_iff_nonnegativePD.symm.trans (niceFCPlus_iff_sSup hR))

end

end SixProblems
end

/- Source module SixProblems.NiceEquivalence. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing

variable {G : Type} [Group G] [Countable G] [Infinite G]

theorem niceVdC_iff_nonnegativePD {R : Set G} : NiceVdC R ↔ NonnegativeOnPositiveDefinite R :=
  ⟨fun h ↦ nonnegativePD_of_ergodicNiceRecurrence hasBoundedErgodicPDApproximation
    (ergodicNiceRecurrence_of_niceRecurrence (niceRecurrence_of_niceVdC h)),
    fun h ↦ niceVdC_of_niceOperatorialRecurrence (niceOperatorialRecurrence_of_nonnegativePD h)⟩

/-- The five equivalent conditions of Theorem 2.2 for a countably infinite
group. Each condition is linked to condition (a). -/
theorem theorem2_2 (R : Set G) (hR : R.Nonempty) :
    (NiceRecurrence R ↔ ErgodicNiceRecurrence R) ∧
    (NiceRecurrence R ↔ NiceOperatorialRecurrence R) ∧
    (NiceRecurrence R ↔ ∀ φ : G → ℝ, RealPositiveDefinite φ → 0 ≤ sSup (φ '' R)) ∧
    (NiceRecurrence R ↔ NiceVdC R) := by
  have hab := ergodicNiceRecurrence_of_niceRecurrence (R := R)
  have hbd := nonnegativePD_of_ergodicNiceRecurrence hasBoundedErgodicPDApproximation (R := R)
  have hdc := niceOperatorialRecurrence_of_nonnegativePD (R := R)
  have hce := niceVdC_of_niceOperatorialRecurrence (R := R)
  have hea := niceRecurrence_of_niceVdC (R := R)
  exact ⟨⟨hab,fun h ↦ hea (hce (hdc (hbd h)))⟩,
    ⟨fun h ↦ hdc (hbd (hab h)),fun h ↦ hea (hce h)⟩,
    (show NiceRecurrence R ↔ NonnegativeOnPositiveDefinite R from
      ⟨fun h ↦ hbd (hab h),fun h ↦ hea (hce (hdc h))⟩).trans
        (nonnegativeOnPositiveDefinite_iff_sSup hR),
    ⟨fun h ↦ hce (hdc (hbd (hab h))),hea⟩⟩

/-- For an abelian acting group, the five conditions are also equivalent to
condition (f), the Fourier coefficient lower bound by the trivial atom. -/
theorem theorem2_2_abelian [IsMulCommutative G] (R : Set G) (hR : R.Nonempty) :
    NiceRecurrence R ↔ ∀ (τ : Measure (DiscreteDual G)) [IsProbabilityMeasure τ],
      τ.real {1} ≤ sSup ((fun r ↦ ‖spectralFourier τ r‖) '' R) :=
  (theorem2_2 R hR).2.2.1.trans (theorem2_2_d_iff_f hR)

end SixProblems
end

/- Source module SixProblems.PartitionRegularityTheorems. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Partition regularity of nice van der Corput sets -/


namespace SixProblems

variable {G : Type} [Group G] [Countable G] [Infinite G]

/-- **Theorem 3.3.** The union of two sets that fail the nice van der Corput
condition also fails that condition. -/
theorem theorem3_3 {A B : Set G} (hA : ¬ NiceVdC A) (hB : ¬ NiceVdC B) :
    ¬ NiceVdC (A ∪ B) := by
  intro h
  exact theorem3_3_positiveDefinite (hA ∘ niceVdC_iff_nonnegativePD.mpr)
    (hB ∘ niceVdC_iff_nonnegativePD.mpr) (niceVdC_iff_nonnegativePD.mp h)

/-- **Corollary 3.4.** A finite union that is nice van der Corput contains a
member of the union that is nice van der Corput. -/
theorem corollary3_4 {m : ℕ} (D : Fin m → Set G) (hD : NiceVdC (⋃ i, D i)) :
    ∃ i, NiceVdC (D i) := by
  have hPD : NonnegativeOnPositiveDefinite (⋃ i ∈ (Finset.univ : Finset (Fin m)), D i) := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using niceVdC_iff_nonnegativePD.mp hD
  obtain ⟨i, _, hi⟩ := corollary3_4_positiveDefinite Finset.univ D hPD
  exact ⟨i, niceVdC_iff_nonnegativePD.mpr hi⟩

/-- The consequence for nice recurrence stated in Remark 3.5. -/
theorem niceRecurrence_partitionRegular {m : ℕ} (D : Fin m → Set G)
    (hD : NiceRecurrence (⋃ i, D i)) : ∃ i, NiceRecurrence (D i) := by
  have hPD := nonnegativePD_of_ergodicNiceRecurrence hasBoundedErgodicPDApproximation
    (ergodicNiceRecurrence_of_niceRecurrence hD)
  obtain ⟨i, hi⟩ := corollary3_4 D (niceVdC_iff_nonnegativePD.mpr hPD)
  exact ⟨i, niceRecurrence_of_niceVdC hi⟩

end SixProblems
end

/- Source module SixProblems.BernoulliSigns. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-- A sign that is positive exactly below a given threshold. -/
def thresholdSign (a t : ℝ) : ℝ := if t ≤ a then 1 else -1

theorem measurable_thresholdSign (a : ℝ) : Measurable (thresholdSign a) :=
  measurable_const.ite measurableSet_Iic measurable_const

theorem norm_thresholdSign (a t : ℝ) : ‖thresholdSign a t‖ = 1 := by
  unfold thresholdSign
  split_ifs <;> simp

theorem integral_thresholdSign {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ t, thresholdSign a t ∂unitIntervalLaw = 2*a-1 := by
  let A := Iic a
  let h := A.indicator (fun _ : ℝ ↦ (1 : ℝ))
  have hm : MeasurableSet A := measurableSet_Iic
  have hh : Integrable h unitIntervalLaw := (integrable_const _).indicator hm
  have he (t : ℝ) : thresholdSign a t = 2*h t-1 := by
    by_cases ht : t ≤ a <;> norm_num [thresholdSign, h, A, ht]
  simp_rw [he]
  rw [integral_sub (hh.const_mul _) (integrable_const _), integral_const_mul,
    integral_indicator hm, setIntegral_const, integral_const]
  simp only [smul_eq_mul, mul_one, Measure.real_def, measure_univ, ENNReal.toReal_one]
  change 2 * (unitIntervalLaw (Iic a)).toReal - 1 = _
  rw [unitIntervalLaw_Iic ha0 ha1, ENNReal.toReal_ofReal ha0]

/-- Assign a sign using the identity coordinate of the independent Bernoulli
factor. A threshold in `[0,1]` gives the expected sign `2f-1`. -/
def bernoulliSign (f : X → ℝ) (z : X × (G → ℝ)) : ℝ := thresholdSign (f z.1) (z.2 1)

theorem measurable_bernoulliSign {f : X → ℝ} (hf : Measurable f) :
    Measurable (bernoulliSign (G := G) f) :=
  measurable_const.ite (measurableSet_bernoulliThreshold hf) measurable_const

theorem integral_bernoulliSign (S : System G X) {f : X → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    let T := S.prod (bernoulliShift G unitIntervalLaw)
    ∫ z, bernoulliSign f z ∂T.measure = ∫ x, 2*f x-1 ∂S.measure := by
  let m := Measure.infinitePi (fun _ : G ↦ unitIntervalLaw)
  let s := bernoulliSign (G := G) f
  have hs : Integrable s (S.measure.prod m) := Integrable.of_bound
    (measurable_bernoulliSign hf).aestronglyMeasurable 1 (ae_of_all _ fun z ↦
      (norm_thresholdSign (f z.1) (z.2 1)).le)
  change (∫ z, s z ∂S.measure.prod m) = _
  rw [integral_prod s hs]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  change (∫ t, thresholdSign (f x) (t 1) ∂m) = _
  have h := measurePreserving_eval_infinitePi (fun _ : G ↦ unitIntervalLaw) 1
  have hI := integral_map h.measurable.aemeasurable (μ := m) (f := thresholdSign (f x))
    (measurable_thresholdSign (f x)).aestronglyMeasurable
  rw [h.map_eq, integral_thresholdSign (hf0 x) (hf1 x)] at hI
  exact hI.symm

theorem integral_bernoulliSign_correlation (S : System G X) {f : X → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (g : G) (hg : g ≠ 1) :
    let T := S.prod (bernoulliShift G unitIntervalLaw)
    ∫ z, bernoulliSign f (T.act g z) * bernoulliSign f z ∂T.measure =
      ∫ x, (2*f (S.act g x)-1)*(2*f x-1) ∂S.measure := by
  let m := Measure.infinitePi (fun _ : G ↦ unitIntervalLaw)
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let s := bernoulliSign (G := G) f
  let q (z : X × (G → ℝ)) := s (T.act g z) * s z
  have hs := measurable_bernoulliSign (G := G) hf
  have hq : Integrable q (S.measure.prod m) := Integrable.of_bound
    ((hs.comp (T.preserves g).measurable).mul hs).aestronglyMeasurable 1
    (ae_of_all _ fun z ↦ by
      change ‖thresholdSign _ _ * thresholdSign _ _‖ ≤ 1
      rw [norm_mul, norm_thresholdSign, norm_thresholdSign, one_mul])
  change (∫ z, q z ∂S.measure.prod m) = _
  rw [integral_prod q hq]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  let u := thresholdSign (f (S.act g x))
  let v := thresholdSign (f x)
  let p (t : G → ℝ) := (t g,t 1)
  have hp : MeasurePreserving p m (unitIntervalLaw.prod unitIntervalLaw) :=
    ⟨(measurable_pi_apply g).prodMk (measurable_pi_apply 1),
      Measure.infinitePi_map_eval_prod (P := fun _ : G ↦ unitIntervalLaw) hg⟩
  let k (z : ℝ × ℝ) := u z.1 * v z.2
  have hk : Measurable k := ((measurable_thresholdSign _).comp measurable_fst).mul
    ((measurable_thresholdSign _).comp measurable_snd)
  have he := integral_map hp.aemeasurable (f := k) hk.aestronglyMeasurable
  rw [hp.map_eq] at he
  have hq' (t : G → ℝ) : q (x,t) = k (p t) := by
    change thresholdSign (f (S.act g x)) (t (1*g)) * thresholdSign (f x) (t 1) = _
    simp [k, p, u, v]
  simp_rw [hq']
  rw [← he]
  change (∫ z : ℝ × ℝ, u z.1 * v z.2 ∂unitIntervalLaw.prod unitIntervalLaw) = _
  rw [integral_prod_mul, integral_thresholdSign (hf0 _) (hf1 _),
    integral_thresholdSign (hf0 _) (hf1 _)]

end SixProblems
end

/- Source module SixProblems.FiniteScalarization. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped ENNReal InnerProductSpace

variable {G X I : Type*} [Group G] [MeasurableSpace X]

/-- The identity action on a probability space. -/
def identityAction (G : Type*) [Group G] {I : Type*} [MeasurableSpace I]
    (μ : Measure I) [IsProbabilityMeasure μ] : System G I where
  measure := μ
  probability := inferInstance
  act := fun _ ↦ id
  act_one := rfl
  act_mul _ _ := rfl
  preserves _ := MeasurePreserving.id μ

section Finite

variable [Fintype I] [Nonempty I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Uniform finite law, using the same weight at every index. -/
def uniformIndex (I : Type*) [Fintype I] [MeasurableSpace I] : Measure I :=
  (Fintype.card I : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure (uniformIndex I) := by
  constructor
  rw [uniformIndex, smul_apply, smul_eq_mul, Measure.count_univ]
  simp [ENNReal.inv_mul_cancel, Fintype.card_ne_zero]

omit [Nonempty I] in
theorem integral_uniformIndex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : I → E) :
    ∫ i, f i ∂uniformIndex I = (Fintype.card I : ℝ)⁻¹ • ∑ i, f i := by
  rw [uniformIndex, integral_smul_measure, integral_count, ENNReal.toReal_inv, ENNReal.toReal_natCast]

variable {𝕜 : Type*} [RCLike 𝕜]

omit [Nonempty I] in
theorem measurable_finiteSelection (v : X → I → 𝕜)
    (hv : ∀ i, Measurable (fun x ↦ v x i)) (s : I → Bool) :
    Measurable (fun z : X × I ↦ if s z.2 then -(v z.1 z.2) else v z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro i
  change Measurable (fun x ↦ if s i then -v x i else v x i)
  split_ifs
  · exact (hv i).neg
  · exact hv i

/-- Selecting one coordinate on a finite identity factor, with any choice
of signs, preserves the summed scalar correlations up to normalization. -/
theorem finiteSelection_correlation
    (S : System G X) (v : X → I → 𝕜) (hv : ∀ i, Measurable (fun x ↦ v x i))
    (C : ℝ) (hC : ∀ x i, ‖v x i‖ ≤ C) (s : I → Bool) (g : G) :
    let T := S.prod (identityAction G (uniformIndex I))
    let q (z : X × I) := if s z.2 then -(v z.1 z.2) else v z.1 z.2
    ∫ z, q (T.act g z) * (starRingEnd 𝕜) (q z) ∂T.measure =
      (Fintype.card I : ℝ)⁻¹ • ∑ i,
        ∫ x, v (S.act g x) i * (starRingEnd 𝕜) (v x i) ∂S.measure := by
  classical
  let f (z : X × I) := v (S.act g z.1) z.2 * (starRingEnd 𝕜) (v z.1 z.2)
  let T := S.prod (identityAction G (uniformIndex I))
  let q (z : X × I) := if s z.2 then -(v z.1 z.2) else v z.1 z.2
  change (∫ z, q (T.act g z) * (starRingEnd 𝕜) (q z) ∂T.measure) = _
  have hpt (z : X × I) : q (T.act g z) * (starRingEnd 𝕜) (q z) = f z := by
    change (if s z.2 then -v (S.act g z.1) z.2 else v (S.act g z.1) z.2) *
      (starRingEnd 𝕜) (if s z.2 then -v z.1 z.2 else v z.1 z.2) = f z
    split_ifs <;> simp [f]
  simp_rw [hpt]
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro i
    exact ((hv i).comp (S.preserves g).measurable).mul (RCLike.continuous_conj.measurable.comp (hv i))
  have hB : 0 ≤ C := (norm_nonneg (v (Classical.choice (nonempty_of_isProbabilityMeasure S.measure))
    (Classical.choice inferInstance))).trans (hC _ _)
  have hi : Integrable f T.measure := Integrable.of_bound hf.aestronglyMeasurable (C*C)
    (ae_of_all _ fun z ↦ by
      change ‖v (S.act g z.1) z.2 * (starRingEnd 𝕜) (v z.1 z.2)‖ ≤ _
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hC _ _) (hC _ _) (norm_nonneg _) hB)
  change (∫ z, f z ∂S.measure.prod (uniformIndex I)) = _
  change Integrable f (S.measure.prod (uniformIndex I)) at hi
  rw [integral_prod_symm f hi, integral_uniformIndex]

theorem finiteSelection_integral
    (S : System G X) (v : X → I → 𝕜) (hv : ∀ i, Measurable (fun x ↦ v x i))
    (C : ℝ) (hC : ∀ x i, ‖v x i‖ ≤ C) (s : I → Bool) :
    let T := S.prod (identityAction G (uniformIndex I))
    ∫ z : X × I, (if s z.2 then -(v z.1 z.2) else v z.1 z.2) ∂T.measure =
      (Fintype.card I : ℝ)⁻¹ • ∑ i, if s i then -(∫ x, v x i ∂S.measure) else ∫ x, v x i ∂S.measure := by
  let q (z : X × I) := if s z.2 then -(v z.1 z.2) else v z.1 z.2
  have hq : Measurable q := measurable_finiteSelection v hv s
  have hqB (z : X × I) : ‖q z‖ ≤ C := by
    unfold q
    split_ifs <;> simpa only [norm_neg] using hC z.1 z.2
  change (∫ z, q z ∂S.measure.prod (uniformIndex I)) = _
  rw [integral_prod_symm q (Integrable.of_bound hq.aestronglyMeasurable C (ae_of_all _ hqB)),
    integral_uniformIndex]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (∫ x, if s i then -v x i else v x i ∂S.measure) = _
  split_ifs with h
  · exact integral_neg (fun x ↦ v x i)
  · rfl

/-- If some coordinate mean is nonzero, at least one choice of signs has
nonzero mean after selection. Flipping one coordinate changes the sum by
twice that coordinate. -/
theorem exists_finiteSelection_nonzero_integral
    (S : System G X) (v : X → I → 𝕜) (hv : ∀ i, Measurable (fun x ↦ v x i))
    (C : ℝ) (hC : ∀ x i, ‖v x i‖ ≤ C) (j : I)
    (hj : ∫ x, v x j ∂S.measure ≠ 0) :
    ∃ s : I → Bool, let T := S.prod (identityAction G (uniformIndex I))
      (∫ z : X × I, (if s z.2 then -(v z.1 z.2) else v z.1 z.2) ∂T.measure) ≠ 0 := by
  classical
  by_contra! h
  let A (i : I) := ∫ x, v x i ∂S.measure
  have hWeight : (Fintype.card I : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hs (s : I → Bool) : (∑ i, if s i then -A i else A i) = 0 := by
    have he : (∫ z : X × I, (if s z.2 then -(v z.1 z.2) else v z.1 z.2)
        ∂(S.prod (identityAction G (uniformIndex I))).measure) = 0 := not_not.mp (h s)
    rw [finiteSelection_integral S v hv C hC s] at he
    exact (smul_eq_zero.mp he).resolve_left hWeight
  have hsum : ∑ i, A i = 0 := by simpa using hs (fun _ ↦ false)
  let s : I → Bool := fun i ↦ decide (i = j)
  have hdiff : (∑ i, ((if s i then -A i else A i) - A i)) = -A j - A j := by
    rw [Finset.sum_eq_single j]
    · simp [s]
    · intro i _ hi
      simp [s,hi]
    · simp
  rw [Finset.sum_sub_distrib, hs, hsum, sub_zero] at hdiff
  have he : (2 : 𝕜) * A j = 0 := calc
    _ = -(-A j - A j) := by ring
    _ = 0 := by rw [← hdiff, neg_zero]
  exact hj ((mul_eq_zero.mp he).resolve_left two_ne_zero)

end Finite

/-- Lemma 4.2. The scalar van der Corput test implies the finite-dimensional
test, including the zero-dimensional case. -/
theorem lemma4_2 {G X : Type} [Group G] [MeasurableSpace X] [StandardBorelSpace X]
    {R : Set G} (hR : IsVdC R) (S : System G X) {d : ℕ}
    (V : X → EuclideanSpace ℂ (Fin d)) (hV : Measurable V)
    (hB : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (hZero : ∀ r ∈ R, ∫ x, ⟪V x,V (S.act r x)⟫_ℂ ∂S.measure = 0) :
    (∫ x, V x ∂S.measure) = 0 := by
  classical
  obtain ⟨C,hC⟩ := hB
  let v (x : X) (i : Fin d) := V x i
  have hv (i : Fin d) : Measurable (fun x ↦ v x i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.measurable.comp hV
  have hvC (x : X) (i : Fin d) : ‖v x i‖ ≤ C :=
    (PiLp.norm_apply_le (V x) i).trans (hC x)
  have hInt : Integrable V S.measure := Integrable.of_bound hV.aestronglyMeasurable C (ae_of_all _ hC)
  ext i
  change EuclideanSpace.proj i (∫ x, V x ∂S.measure) = 0
  rw [← (EuclideanSpace.proj i).integral_comp_comm hInt]
  change ∫ x, v x i ∂S.measure = 0
  by_contra hi
  let : Nonempty (Fin d) := ⟨i⟩
  let T := S.prod (identityAction G (uniformIndex (Fin d)))
  obtain ⟨s, hs⟩ := exists_finiteSelection_nonzero_integral S v hv C hvC i hi
  let q (z : X × Fin d) : ℂ := if s z.2 then -v z.1 z.2 else v z.1 z.2
  have hqB (z : X × Fin d) : ‖q z‖ ≤ C := by
    unfold q
    split_ifs <;> simpa only [norm_neg] using hvC z.1 z.2
  apply hs
  apply hR T q (measurable_finiteSelection v hv s) ⟨C,hqB⟩
  intro r hr
  have hC0 : 0 ≤ C := (norm_nonneg (v (Classical.choice (nonempty_of_isProbabilityMeasure S.measure)) i)).trans (hvC _ _)
  rw [correlation, finiteSelection_correlation S v hv C hvC s r]
  have hi₀ (j : Fin d) : Integrable (fun x ↦ v (S.act r x) j * (starRingEnd ℂ) (v x j)) S.measure :=
    Integrable.of_bound (((hv j).comp (S.preserves r).measurable).mul
      (Complex.continuous_conj.measurable.comp (hv j))).aestronglyMeasurable
      (C*C) (ae_of_all _ fun x ↦ by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hvC _ _) (hvC _ _) (norm_nonneg _) hC0)
  rw [← integral_finsetSum _ (fun j _ ↦ hi₀ j)]
  have hsum (x : X) : (∑ j, v (S.act r x) j * (starRingEnd ℂ) (v x j)) = ⟪V x,V (S.act r x)⟫_ℂ := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [RCLike.inner_apply']
    exact mul_comm _ _
  simp_rw [hsum]
  rw [hZero r hr, smul_zero]

end SixProblems
end

/- Source module SixProblems.SignWitness. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory Mixing
open scoped InnerProductSpace

variable {G : Type} [Group G]

theorem isVdC_of_one_mem {R : Set G} (h : 1 ∈ R) : IsVdC R := by
  intro X _ _ S f hm hb hz
  let hf := bounded_measurable_memLp S hm hb
  have he := inner_systemKoopman_of_memLp S hf 1
  rw [map_one, inv_one, hz _ h] at he
  have hLp := inner_self_eq_zero.mp he
  apply integral_eq_zero_of_ae
  apply hf.coeFn_toLp.symm.trans
  rw [hLp]
  exact Lp.coeFn_zero _ _ _

/-- A complex counterexample to the dynamical van der Corput test gives
a real counterexample on a finite identity extension. -/
theorem exists_real_counterexample {R : Set G} (h : ¬ IsVdC R) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      Measurable f ∧ (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) ∧
      (∀ r ∈ R, ∫ x, f (S.act r x) * f x ∂S.measure = 0) ∧
      (∫ x, f x ∂S.measure) ≠ 0 := by
  classical
  by_contra hn
  apply h
  intro X mX hX S f hf hB hZ
  by_contra hM
  obtain ⟨C, hC⟩ := hB
  let v (x : X) (i : Bool) := if i then (f x).im else (f x).re
  have hv (i : Bool) : Measurable (fun x ↦ v x i) := by
    cases i
    · exact Complex.continuous_re.measurable.comp hf
    · exact Complex.continuous_im.measurable.comp hf
  have hvB (x : X) (i : Bool) : ‖v x i‖ ≤ C := by
    cases i
    · exact (Complex.abs_re_le_norm (f x)).trans (hC x)
    · exact (Complex.abs_im_le_norm (f x)).trans (hC x)
  have hInt : Integrable f S.measure :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hVMean : ∃ i : Bool, (∫ x, v x i ∂S.measure) ≠ 0 := by
    by_contra! hAll
    apply hM
    apply Complex.ext
    · have hr := Complex.reCLM.integral_comp_comm hInt
      change (∫ x, v x false ∂S.measure) = (∫ x, f x ∂S.measure).re at hr
      rw [← hr]
      exact hAll false
    · have hi := Complex.imCLM.integral_comp_comm hInt
      change (∫ x, v x true ∂S.measure) = (∫ x, f x ∂S.measure).im at hi
      rw [← hi]
      exact hAll true
  obtain ⟨i, hi⟩ := hVMean
  obtain ⟨s, hs⟩ := exists_finiteSelection_nonzero_integral S v hv C hvB i hi
  let T := S.prod (identityAction G (uniformIndex Bool))
  let q (z : X × Bool) : ℝ := if s z.2 then -v z.1 z.2 else v z.1 z.2
  refine hn ⟨X × Bool, inferInstance, inferInstance, T, q,
    measurable_finiteSelection v hv s, ⟨C, ?_⟩, ?_, hs⟩
  · intro z
    unfold q
    split_ifs <;> simpa only [norm_neg] using hvB z.1 z.2
  · intro r hr
    have hq := finiteSelection_correlation S v hv C hvB s r
    change (∫ z, q (T.act r z) * q z ∂T.measure) = _ at hq
    rw [hq]
    have hC0 : 0 ≤ C := (norm_nonneg (f (Classical.choice
      (nonempty_of_isProbabilityMeasure S.measure)))).trans (hC _)
    have hI (j : Bool) : Integrable (fun x ↦ v (S.act r x) j * v x j) S.measure :=
      Integrable.of_bound (((hv j).comp (S.preserves r).measurable).mul (hv j)).aestronglyMeasurable
        (C*C) (ae_of_all _ fun x ↦ by
          rw [norm_mul]
          exact mul_le_mul (hvB _ _) (hvB _ _) (norm_nonneg _) hC0)
    change (Fintype.card Bool : ℝ)⁻¹ • (∑ j, ∫ x, v (S.act r x) j * v x j ∂S.measure) = 0
    rw [← integral_finsetSum _ (fun j _ ↦ hI j)]
    let k (x : X) := f (S.act r x) * (starRingEnd ℂ) (f x)
    have hk : Integrable k S.measure := Integrable.of_bound
      ((hf.comp (S.preserves r).measurable).mul (Complex.continuous_conj.measurable.comp hf)).aestronglyMeasurable
      (C*C) (ae_of_all _ fun x ↦ by
        change ‖f (S.act r x) * (starRingEnd ℂ) (f x)‖ ≤ _
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0)
    have he (x : X) : (∑ j, v (S.act r x) j * v x j) = (k x).re := by
      have hu : (Finset.univ : Finset Bool) = {false,true} := by decide
      rw [hu, Finset.sum_insert (by decide), Finset.sum_singleton]
      simp [v, k, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    simp_rw [he]
    change (Fintype.card Bool : ℝ)⁻¹ • (∫ x, Complex.reCLM (k x) ∂S.measure) = 0
    rw [Complex.reCLM.integral_comp_comm hk]
    change (Fintype.card Bool : ℝ)⁻¹ • (correlation S f r).re = 0
    simp [hZ r hr]

/-- Lemma 4.3. Failure of the van der Corput test can be witnessed by a
two-valued observable. -/
theorem lemma4_3 [Countable G] {R : Set G} (h : ¬ IsVdC R) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      Measurable f ∧ (∀ x, f x = 1 ∨ f x = -1) ∧
      (∀ r ∈ R, ∫ x, f (S.act r x) * f x ∂S.measure = 0) ∧
      (∫ x, f x ∂S.measure) ≠ 0 := by
  obtain ⟨X, mX, hX, S, f, hf, ⟨C, hC⟩, hZ, hM⟩ := exists_real_counterexample h
  let := mX
  let := hX
  let B := |C| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let t (x : X) := (B⁻¹ * f x + 1) / 2
  have ht : Measurable t := ((measurable_const.mul hf).add measurable_const).div_const _
  have hb (x : X) : ‖B⁻¹ * f x‖ ≤ 1 := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB), ← div_eq_inv_mul]
    exact (div_le_iff₀ hB).2 (by
      rw [one_mul]
      exact (hC x).trans ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one)))
  have hb' (x : X) := abs_le.mp (show |B⁻¹ * f x| ≤ 1 from hb x)
  have ht0 (x : X) : 0 ≤ t x := by dsimp [t]; linarith [(hb' x).1]
  have ht1 (x : X) : t x ≤ 1 := by dsimp [t]; linarith [(hb' x).2]
  let T := S.prod (bernoulliShift G unitIntervalLaw)
  let s := bernoulliSign (G := G) t
  have he (x : X) : 2 * t x - 1 = B⁻¹ * f x := by dsimp [t]; ring
  refine ⟨X × (G → ℝ), inferInstance, inferInstance, T, s,
    measurable_bernoulliSign ht, ?_, ?_, ?_⟩
  · intro z
    unfold s bernoulliSign thresholdSign
    split_ifs <;> simp
  · intro r hr
    have hr1 : r ≠ 1 := fun e ↦ h (isVdC_of_one_mem (e ▸ hr))
    rw [integral_bernoulliSign_correlation S ht ht0 ht1 r hr1]
    simp_rw [he, show ∀ a b : ℝ, (B⁻¹ * a) * (B⁻¹ * b) = B⁻¹^2 * (a*b) by intro a b; ring]
    rw [integral_const_mul, hZ r hr, mul_zero]
  · rw [integral_bernoulliSign S ht ht0 ht1]
    simp_rw [he]
    rw [integral_const_mul]
    exact mul_ne_zero (inv_ne_zero hB.ne') hM

end SixProblems
end

/- Source module SixProblems.HaarDifferenceMixture. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {K : Type*} [Group K] [MeasurableSpace K]

omit [Group K] in
/-- Two distinct probability laws whose sum is twice Haar. Given a test set
of masses `a` and `b` on the two pieces, the laws have densities `1+b,b`
and `a,1+a`, respectively. -/
theorem exists_complementary_probability_laws (m : Measure K) [IsProbabilityMeasure m]
    (A : Set K) (hA : MeasurableSet A) (ha : m A ≠ 0) (hb : m Aᶜ ≠ 0) :
    ∃ p q : Measure K, IsProbabilityMeasure p ∧ IsProbabilityMeasure q ∧
      p + q = (2 : ℝ≥0∞) • m ∧ p A ≠ q A := by
  let a := m A
  let b := m Aᶜ
  have hab : a+b = 1 := by
    change m A + m Aᶜ = 1
    rw [measure_add_measure_compl hA, measure_univ]
  let p := (1+b) • m.restrict A + b • m.restrict Aᶜ
  let q := a • m.restrict A + (1+a) • m.restrict Aᶜ
  refine ⟨p,q,⟨?_⟩,⟨?_⟩,?_,?_⟩
  · change ((1+b) • m.restrict A + b • m.restrict Aᶜ) univ = 1
    simp only [add_apply, smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    change (1+b)*a+b*b = 1
    calc
      _ = a+b*(a+b) := by ring
      _ = 1 := by rw [hab, mul_one, hab]
  · change (a • m.restrict A + (1+a) • m.restrict Aᶜ) univ = 1
    simp only [add_apply, smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    change a*a+(1+a)*b = 1
    calc
      _ = a*(a+b)+b := by ring
      _ = 1 := by rw [hab, mul_one, hab]
  · change (1+b) • m.restrict A + b • m.restrict Aᶜ +
        (a • m.restrict A + (1+a) • m.restrict Aᶜ) = (2 : ℝ≥0∞) • m
    rw [add_add_add_comm, ← add_smul, ← add_smul,
      show 1+b+a = 2 from by rw [add_assoc, add_comm b a, hab, one_add_one_eq_two],
      show b+(1+a) = 2 from by rw [add_left_comm, add_comm b a, hab, one_add_one_eq_two],
      ← smul_add, Measure.restrict_add_restrict_compl hA]
  · have ha' : a.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨ha,measure_ne_top m _⟩
    have hb' : b.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hb,measure_ne_top m _⟩
    intro he
    have h := congrArg ENNReal.toReal he
    simp only [p, q, add_apply, smul_apply, smul_eq_mul, Measure.restrict_apply hA,
      inter_self, inter_compl_self, measure_empty, mul_zero, add_zero, ENNReal.toReal_mul] at h
    change (1+b).toReal * a.toReal = a.toReal * a.toReal at h
    rw [ENNReal.toReal_add ENNReal.one_ne_top (measure_ne_top m _), ENNReal.toReal_one] at h
    have hab' := congrArg ENNReal.toReal hab
    rw [ENNReal.toReal_add (measure_ne_top m _) (measure_ne_top m _), ENNReal.toReal_one] at hab'
    have h0 : 0 < a.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg ha'.symm
    have h1 : 0 < b.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg hb'.symm
    nlinarith [mul_pos h0 h1]

variable [MeasurableMul₂ K] [MeasurableInv K]

/-- Distribution of `k l⁻¹` under two independent laws. -/
def differenceLaw (a b : Measure K) : Measure K :=
  (a.prod b).map (fun z : K × K ↦ z.1 * z.2⁻¹)

theorem measurable_difference : Measurable (fun z : K × K ↦ z.1 * z.2⁻¹) :=
  measurable_fst.mul measurable_snd.inv

instance (a b : Measure K) [IsProbabilityMeasure a] [IsProbabilityMeasure b] :
    IsProbabilityMeasure (differenceLaw a b) :=
  (Measure.isProbabilityMeasure_map_iff measurable_difference.aemeasurable).mpr inferInstance

theorem differenceLaw_haar_left (m a : Measure K) [IsProbabilityMeasure a] [IsMulRightInvariant m]
    [SFinite m] : differenceLaw m a = m := by
  ext A hA
  rw [differenceLaw, Measure.map_apply measurable_difference hA,
    Measure.prod_apply_symm (measurable_difference hA)]
  have he (z : K) : m ((fun x ↦ (x,z)) ⁻¹' ((fun w : K × K ↦ w.1*w.2⁻¹) ⁻¹' A)) = m A := by
    change m ((fun x : K ↦ x*z⁻¹) ⁻¹' A) = m A
    exact (measurePreserving_mul_right m z⁻¹).measure_preimage hA.nullMeasurableSet
  simp_rw [he]
  rw [lintegral_const, measure_univ, mul_one]

theorem differenceLaw_haar_right (m a : Measure K) [IsProbabilityMeasure a]
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [IsInvInvariant m] : differenceLaw a m = m := by
  ext A hA
  rw [differenceLaw, Measure.map_apply measurable_difference hA,
    Measure.prod_apply (measurable_difference hA)]
  have he (z : K) : m ((fun x ↦ (z,x)) ⁻¹' ((fun w : K × K ↦ w.1*w.2⁻¹) ⁻¹' A)) = m A := by
    change m ((fun x : K ↦ z*x⁻¹) ⁻¹' A) = m A
    exact ((measurePreserving_mul_left m z).comp (measurePreserving_inv m)).measure_preimage hA.nullMeasurableSet
  simp_rw [he]
  rw [lintegral_const, measure_univ, mul_one]

theorem differenceLaw_add_left (a b c : Measure K) [SFinite a] [SFinite b] [SFinite c] :
    differenceLaw (a+b) c = differenceLaw a c + differenceLaw b c := by
  unfold differenceLaw
  rw [Measure.add_prod, Measure.map_add _ _ measurable_difference]

theorem differenceLaw_add_right (a b c : Measure K) [SFinite a] [SFinite b] [SFinite c] :
    differenceLaw a (b+c) = differenceLaw a b + differenceLaw a c := by
  unfold differenceLaw
  rw [Measure.prod_add, Measure.map_add _ _ measurable_difference]

/-- For complementary input laws, the output law depends only on whether the
two signs agree. The two possible output laws sum to twice Haar. -/
theorem differenceLaw_complementary (m p q : Measure K)
    [IsProbabilityMeasure m] [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    [IsMulLeftInvariant m] [IsMulRightInvariant m] [IsInvInvariant m]
    (hpq : p+q = (2 : ℝ≥0∞) • m) :
    differenceLaw p p = differenceLaw q q ∧
      differenceLaw p q = differenceLaw q p ∧
      differenceLaw p p + differenceLaw p q = (2 : ℝ≥0∞) • m := by
  have h₂ : p+q = m+m := hpq.trans (two_smul ℝ≥0∞ m)
  have hP : differenceLaw p p + differenceLaw p q = m+m := by
    rw [← differenceLaw_add_right, h₂, differenceLaw_add_right, differenceLaw_haar_right]
  have hQ : differenceLaw q p + differenceLaw q q = m+m := by
    rw [← differenceLaw_add_right, h₂, differenceLaw_add_right, differenceLaw_haar_right]
  have hL : differenceLaw p p + differenceLaw q p = m+m := by
    rw [← differenceLaw_add_left, h₂, differenceLaw_add_left, differenceLaw_haar_left]
  have hCancel (a b c : Measure K) [IsFiniteMeasure a] (h : a+b = a+c) : b = c := by
    ext A hA
    have h' := congrArg (fun v : Measure K ↦ v A) h
    simpa only [add_apply, ENNReal.add_right_inj (measure_ne_top a _)] using h'
  have hCross : differenceLaw p q = differenceLaw q p :=
    hCancel _ _ _ (hP.trans hL.symm)
  refine ⟨?_,hCross,hP.trans (two_smul ℝ≥0∞ m).symm⟩
  apply hCancel (differenceLaw p q)
  rw [add_comm (differenceLaw p q) (differenceLaw p p), hP, hCross, hQ]

end SixProblems
end

/- Source module SixProblems.CompactVdCReverse. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Mixing Set
open scoped Classical ENNReal

variable {G X K : Type} [Group G] [MeasurableSpace X] [Group K] [MeasurableSpace K]

omit [Group G] [Group K] [MeasurableSpace K] in
private theorem integral_sign (μ : Measure X) [IsProbabilityMeasure μ] (A : Set X)
    (hA : MeasurableSet A) :
    (∫ x, A.piecewise (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) x ∂μ) = 2 * (μ A).toReal - 1 := by
  classical
  rw [integral_piecewise hA (integrable_const _).integrableOn (integrable_const _).integrableOn,
    setIntegral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one, mul_neg, Measure.real_def]
  have h := congrArg ENNReal.toReal (measure_add_measure_compl (μ := μ) hA)
  rw [measure_univ, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h
  linarith

omit [Group G] [Group K] [MeasurableSpace K] in
private theorem lintegral_two_values (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (a b : ℝ≥0∞) : (∫⁻ x, (if x ∈ A then a else b) ∂μ) = a * μ A + b * μ Aᶜ := by
  classical
  change (∫⁻ x, A.piecewise (fun _ ↦ a) (fun _ ↦ b) x ∂μ) = _
  rw [lintegral_piecewise hA.nullMeasurableSet, lintegral_const, lintegral_const,
    Measure.restrict_apply_univ, Measure.restrict_apply_univ]

section Selection

variable (p q : Measure K) [IsProbabilityMeasure p] [IsProbabilityMeasure q]

/-- Select a coordinate from a pair of samples using a real sign. -/
private def signSelect (s : ℝ) (z : K × K) : K := if s = 1 then z.1 else z.2

omit [Group G] [Group K] in
private theorem measurable_signSelect (s : ℝ) : Measurable (signSelect (K := K) s) := by
  by_cases h : s = 1
  · rw [show signSelect (K := K) s = Prod.fst from funext fun z ↦ ite_eq_left h]
    exact measurable_fst
  · rw [show signSelect (K := K) s = Prod.snd from funext fun z ↦ ite_eq_right h]
    exact measurable_snd

omit [Group G] [Group K] in
private theorem signSelect_preserving (s : ℝ) :
    MeasurePreserving (signSelect (K := K) s) (p.prod q) (if s = 1 then p else q) := by
  by_cases h : s = 1
  · rw [ite_eq_left h, show signSelect (K := K) s = Prod.fst from funext fun z ↦ ite_eq_left h]
    exact measurePreserving_fst
  · rw [ite_eq_right h, show signSelect (K := K) s = Prod.snd from funext fun z ↦ ite_eq_right h]
    exact measurePreserving_snd

omit [Group G] [Group K] in
private theorem measurable_selectedCoordinate {s : X → ℝ} (hs : Measurable s) (g : G) :
    Measurable (fun z : X × (G → K × K) ↦ signSelect (s z.1) (z.2 g)) := by
  have h₁ : Measurable (fun z : X × (G → K × K) ↦ z.2 g) :=
    (measurable_pi_apply g).comp measurable_snd
  exact h₁.fst.ite ((hs.comp measurable_fst) (measurableSet_singleton (1 : ℝ))) h₁.snd

variable [MeasurableMul₂ K] [MeasurableInv K]

private theorem selectedDifference_fiber
    (a b : ℝ) {g : G} (hg : g ≠ 1) {B : Set K} (hB : MeasurableSet B) :
    (Measure.infinitePi fun _ : G ↦ p.prod q)
      ((fun t ↦ signSelect a (t g) * (signSelect b (t 1))⁻¹) ⁻¹' B) =
    differenceLaw (if a = 1 then p else q) (if b = 1 then p else q) B := by
  let h (t : G → K × K) := (t g,t 1)
  have hh : MeasurePreserving h (Measure.infinitePi fun _ : G ↦ p.prod q)
      ((p.prod q).prod (p.prod q)) :=
    ⟨(measurable_pi_apply g).prodMk (measurable_pi_apply 1),
      Measure.infinitePi_map_eval_prod (P := fun _ : G ↦ p.prod q) hg⟩
  let k := Prod.map (signSelect (K := K) a) (signSelect (K := K) b)
  have hk : MeasurePreserving k ((p.prod q).prod (p.prod q))
      ((if a = 1 then p else q).prod (if b = 1 then p else q)) :=
    (signSelect_preserving p q a).prod (signSelect_preserving p q b)
  let d (z : K × K) := z.1 * z.2⁻¹
  have he := (hk.comp hh).measure_preimage (measurable_difference hB).nullMeasurableSet
  change _ = ((if a = 1 then p else q).prod (if b = 1 then p else q)) (d ⁻¹' B) at he
  rw [differenceLaw, Measure.map_apply measurable_difference hB]
  exact he

end Selection

variable [TopologicalSpace K] [T2Space K] [IsTopologicalGroup K] [BorelSpace K] [SecondCountableTopology K]
  [StandardBorelSpace K] [Nontrivial K]

/-- The reverse implication of Theorem 4.6. From a sign witness, independently
sample one of two complementary Haar perturbations at each time. -/
theorem isVdC_of_measureTheoreticVdC [Countable G] {R : Set G} (m : Measure K)
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [IsMulRightInvariant m]
    [IsInvInvariant m] [m.IsOpenPosMeasure] (h : IsMeasureTheoreticVdC R m) : IsVdC R := by
  classical
  by_contra hv
  obtain ⟨Y,mY,hY,S,s,hs,hsign,hCorr,hMean⟩ := lemma4_3 hv
  let := mY
  let := hY
  obtain ⟨x,y,hxy⟩ := exists_pair_ne K
  obtain ⟨U,V,hU,hV,hx,hy,hUV⟩ := t2_separation hxy
  have ha : m U ≠ 0 := (hU.measure_pos m ⟨x,hx⟩).ne'
  have hb : m Uᶜ ≠ 0 := ((hV.measure_pos m ⟨y,hy⟩).trans_le
    (measure_mono (fun z hz ↦ disjoint_left.mp hUV.symm hz))).ne'
  obtain ⟨p,q,hp,hq,hpq,hDistinct⟩ := exists_complementary_probability_laws m U hU.measurableSet ha hb
  let := hp
  let := hq
  obtain ⟨hDiag,hCross,hSum⟩ := differenceLaw_complementary m p q hpq
  let law := Measure.infinitePi (fun _ : G ↦ p.prod q)
  let T := S.prod (bernoulliShift G (p.prod q))
  let F (z : Y × (G → K × K)) := signSelect (s z.1) (z.2 1)
  have hF : Measurable F := measurable_selectedCoordinate hs 1
  have hM := h T F hF ?_
  · let A : Set Y := {y | s y = 1}
    have hA : MeasurableSet A := hs (measurableSet_singleton 1)
    have he (y : Y) : s y = A.piecewise (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) y := by
      rcases hsign y with h | h <;> norm_num [A,h]
    have hMass : (S.measure A).toReal ≠ 1/2 := by
      intro ha
      apply hMean
      simp_rw [he]
      rw [integral_sign S.measure A hA, ha]
      norm_num
    have hFmeasure : T.measure.map F U = p U * S.measure A + q U * S.measure Aᶜ := by
      rw [Measure.map_apply hF hU.measurableSet]
      change (S.measure.prod law) (F ⁻¹' U) = _
      rw [Measure.prod_apply (hF hU.measurableSet)]
      have he' (y : Y) : law (Prod.mk y ⁻¹' (F ⁻¹' U)) =
          (if y ∈ A then p U else q U) := by
        have hEval := measurePreserving_eval_infinitePi (fun _ : G ↦ p.prod q) 1
        have hc := ((signSelect_preserving p q (s y)).comp hEval).measure_preimage
          hU.measurableSet.nullMeasurableSet
        change law (Prod.mk y ⁻¹' (F ⁻¹' U)) = (if s y = 1 then p else q) U at hc
        change _ = if s y = 1 then p U else q U
        split_ifs with hy <;> simp only [hy, ite_true, ite_false] at hc <;> exact hc
      simp_rw [he']
      exact lintegral_two_values S.measure A hA _ _
    rw [hM] at hFmeasure
    have hComp := congrArg (fun ρ : Measure K ↦ ρ U) hpq
    simp only [add_apply,smul_apply,smul_eq_mul] at hComp
    have htot := congrArg ENNReal.toReal (measure_add_measure_compl (μ := S.measure) hA)
    have hFreal := congrArg ENNReal.toReal hFmeasure
    have hCreal := congrArg ENNReal.toReal hComp
    simp only [measure_univ, ENNReal.toReal_one,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at htot
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
      ENNReal.toReal_mul, ENNReal.toReal_mul] at hFreal
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_mul,
      ENNReal.toReal_ofNat] at hCreal
    have hFactor : ((p U).toReal - (q U).toReal) * ((S.measure A).toReal - 1/2) = 0 := by
      have heq := congrArg ((q U).toReal * ·) htot
      linarith only [heq, hFreal, hCreal, show ((p U).toReal - (q U).toReal) *
        ((S.measure A).toReal - 1/2) = (p U).toReal * (S.measure A).toReal -
        (q U).toReal * (S.measure A).toReal - ((p U).toReal + (q U).toReal) / 2 + (q U).toReal by ring]
    rcases mul_eq_zero.mp hFactor with hpq' | hA'
    · exact hDistinct ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
        (sub_eq_zero.mp hpq'))
    · exact hMass (sub_eq_zero.mp hA')
  · intro g hg
    have hg1 : g ≠ 1 := fun e ↦ hv (isVdC_of_one_mem (e ▸ hg))
    let A : Set Y := {y | s (S.act g y) = s y}
    have hA : MeasurableSet A := measurableSet_eq_fun (hs.comp (S.preserves g).measurable) hs
    have he (y : Y) : s (S.act g y) * s y =
        A.piecewise (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) y := by
      rcases hsign (S.act g y) with h₁ | h₁ <;> rcases hsign y with h₂ | h₂ <;>
        norm_num [A,h₁,h₂]
    have hm : (S.measure A).toReal = 1/2 := by
      have hc := hCorr g hg
      simp_rw [he] at hc
      rw [integral_sign S.measure A hA] at hc
      linarith
    have hmc : (S.measure Aᶜ).toReal = 1/2 := by
      have hc := congrArg ENNReal.toReal (measure_add_measure_compl (μ := S.measure) hA)
      rw [measure_univ, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        ENNReal.toReal_one, hm] at hc
      linarith
    have hm' : S.measure A = 1/2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
      simpa using hm
    have hmc' : S.measure Aᶜ = 1/2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
      simpa using hmc
    ext B hB
    let d (z : Y × (G → K × K)) := F (T.act g z) * (F z)⁻¹
    have hd : Measurable d := (hF.comp (T.preserves g).measurable).mul hF.inv
    change T.measure.map d B = _
    rw [Measure.map_apply hd hB]
    change (S.measure.prod law) (d ⁻¹' B) = _
    rw [Measure.prod_apply (hd hB)]
    have hFiber (y : Y) : law (Prod.mk y ⁻¹' (d ⁻¹' B)) =
        (if y ∈ A then differenceLaw p p B else differenceLaw p q B) := by
      have hEq : Prod.mk y ⁻¹' (d ⁻¹' B) =
          (fun t : G → K × K ↦ signSelect (s (S.act g y)) (t g) * (signSelect (s y) (t 1))⁻¹) ⁻¹' B := by
        ext t
        simp [d, F, T, System.prod, System.prodAct, bernoulliShift, rightShift]
      rw [hEq, selectedDifference_fiber p q _ _ hg1 hB]
      rcases hsign (S.act g y) with h₁ | h₁ <;> rcases hsign y with h₂ | h₂ <;>
        norm_num [A,h₁,h₂,← hDiag,← hCross]
    simp_rw [hFiber]
    rw [lintegral_two_values S.measure A hA, hm', hmc', ← add_mul]
    have hsB := congrArg (fun ρ : Measure K ↦ ρ B) hSum
    simp only [add_apply, smul_apply, smul_eq_mul] at hsB
    rw [hsB, mul_right_comm, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

end SixProblems
end

/- Source module Mixing.CompactRepresentationAverage. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section
namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure InnerProductSpace Set
open scoped ComplexConjugate InnerProductSpace

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The average of the rank-one operators built from the orbit of a vector
in a strongly continuous unitary representation of a compact group. -/
def compactRepresentationAverage (μ : Measure K) (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    H →L[ℂ] H :=
  ∫ k, rankOne ℂ (ρ k x) (ρ k x) ∂μ

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [CompleteSpace H] in
private theorem continuous_rankOne_orbit (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hρ : Continuous fun k ↦ ρ k x) : Continuous (fun k ↦ rankOne ℂ (ρ k x) (ρ k x)) := by
  exact ((ContinuousLinearMap.smulRightL ℂ H H).continuous.comp
    ((innerSL ℂ).continuous.comp hρ)).clm_apply hρ

omit [IsTopologicalGroup K] [CompleteSpace H] in
private theorem integrable_rankOne_orbit (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    Integrable (fun k ↦ rankOne ℂ (ρ k x) (ρ k x)) μ :=
  (continuous_rankOne_orbit ρ x hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [CompleteSpace H] in
private theorem compact_rankOne_self (x : H) : IsCompactOperator (rankOne ℂ x x) := by
  let a := (1 : ℂ →L[ℂ] ℂ).smulRight x
  have hc : IsCompactOperator a := isCompactOperator_of_locallyCompactSpace_rng a
  have he : rankOne ℂ x x = a.comp (innerSL ℂ x) := by
    ext y
    simp [a]
  rw [he]
  exact hc.comp_clm (innerSL ℂ x)

omit [IsTopologicalGroup K] in
theorem isCompactOperator_compactRepresentationAverage (μ : Measure K) [IsProbabilityMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    IsCompactOperator (compactRepresentationAverage μ ρ x) := by
  let C := (compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ
  have hC : IsClosed (C : Set (H →L[ℂ] H)) := isClosed_setOfPred_isCompactOperator
  exact C.convex.integral_mem hC (ae_of_all _ fun k ↦ compact_rankOne_self (ρ k x))
    (integrable_rankOne_orbit μ ρ x hρ)

omit [IsTopologicalGroup K] in
theorem compactRepresentationAverage_apply (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) (y : H) :
    compactRepresentationAverage μ ρ x y = ∫ k, rankOne ℂ (ρ k x) (ρ k x) y ∂μ := by
  exact ((ContinuousLinearMap.apply ℂ H y).integral_comp_comm
    (integrable_rankOne_orbit μ ρ x hρ)).symm

omit [IsTopologicalGroup K] in
theorem inner_compactRepresentationAverage (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) (y z : H) :
    ⟪y, compactRepresentationAverage μ ρ x z⟫_ℂ =
      ∫ k, ⟪y, rankOne ℂ (ρ k x) (ρ k x) z⟫_ℂ ∂μ := by
  have hi := (ContinuousLinearMap.apply ℂ H z).integrable_comp
    (integrable_rankOne_orbit μ ρ x hρ)
  rw [compactRepresentationAverage_apply μ ρ x hρ]
  exact ((innerSL ℂ y).integral_comp_comm hi).symm

omit [IsTopologicalGroup K] in
theorem isSymmetric_compactRepresentationAverage (μ : Measure K) [IsFiniteMeasure μ]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hρ : Continuous fun k ↦ ρ k x) :
    (compactRepresentationAverage μ ρ x).IsSymmetric := by
  intro y z
  change ⟪compactRepresentationAverage μ ρ x y, z⟫_ℂ =
    ⟪y, compactRepresentationAverage μ ρ x z⟫_ℂ
  rw [← inner_conj_symm (compactRepresentationAverage μ ρ x y) z,
    inner_compactRepresentationAverage μ ρ x hρ, inner_compactRepresentationAverage μ ρ x hρ,
    ← integral_conj]
  apply integral_congr_ae
  exact ae_of_all _ fun k ↦
    (inner_conj_symm (rankOne ℂ (ρ k x) (ρ k x) y) z).trans
      (isSymmetric_rankOne_self (ρ k x) y z)

/-- The compact average commutes with the entire representation. -/
theorem compactRepresentationAverage_commutes (μ : Measure K) [IsFiniteMeasure μ]
    [IsMulLeftInvariant μ] (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (x : H)
    (hρ : Continuous fun k ↦ ρ k x) (a : K) (y : H) :
    ρ a (compactRepresentationAverage μ ρ x y) =
      compactRepresentationAverage μ ρ x (ρ a y) := by
  let v (k : K) := rankOne ℂ (ρ k x) (ρ k x) y
  let w (k : K) := rankOne ℂ (ρ k x) (ρ k x) (ρ a y)
  have hi := (ContinuousLinearMap.apply ℂ H y).integrable_comp (integrable_rankOne_orbit μ ρ x hρ)
  have hw := (ContinuousLinearMap.apply ℂ H (ρ a y)).integrable_comp
    (integrable_rankOne_orbit μ ρ x hρ)
  have he (k : K) : ρ a (v k) = w (a*k) := by
    simp only [v, w, rankOne_apply, map_mul]
    change ρ a (⟪ρ k x,y⟫_ℂ • ρ k x) =
      ⟪ρ a (ρ k x),ρ a y⟫_ℂ • ρ a (ρ k x)
    rw [map_smul, LinearIsometryEquiv.inner_map_map]
  rw [compactRepresentationAverage_apply μ ρ x hρ, compactRepresentationAverage_apply μ ρ x hρ]
  change ρ a (∫ k, v k ∂μ) = ∫ k, w k ∂μ
  calc
    _ = ∫ k, ρ a (v k) ∂μ :=
      ((ρ a).toLinearIsometry.toContinuousLinearMap.integral_comp_comm hi).symm
    _ = ∫ k, w (a*k) ∂μ := integral_congr_ae (ae_of_all _ he)
    _ = _ := by
      have ht := measurePreserving_mul_left μ a
      have hW : AEStronglyMeasurable w (μ.map (fun k ↦ a*k)) := by
        change AEStronglyMeasurable w (μ.map (a * ·))
        rw [ht.map_eq]
        exact hw.aestronglyMeasurable
      have he' := integral_map ht.aemeasurable hW
      rw [ht.map_eq] at he'
      exact he'.symm

omit [IsTopologicalGroup K] in
theorem compactRepresentationAverage_ne_zero (μ : Measure K) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (ρ : K →* (H ≃ₗᵢ[ℂ] H)) {x : H}
    (hx : x ≠ 0) (hρ : Continuous fun k ↦ ρ k x) :
    compactRepresentationAverage μ ρ x ≠ 0 := by
  let v (k : K) := ‖⟪ρ k x,x⟫_ℂ‖ ^ 2
  have hc : Continuous v := (hρ.inner continuous_const).norm.pow _
  have he : v 1 ≠ 0 := by
    have hOne : ρ 1 x = x := by rw [map_one]; rfl
    change ‖⟪ρ 1 x,x⟫_ℂ‖ ^ 2 ≠ 0
    rw [hOne]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (fun h ↦ hx (inner_self_eq_zero.mp h)))
  have hp : 0 < ∫ k, v k ∂μ :=
    hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (HasCompactSupport.of_compactSpace _)
      (fun _ ↦ sq_nonneg _) he
  have hi : Integrable (fun k ↦ ⟪x,rankOne ℂ (ρ k x) (ρ k x) x⟫_ℂ) μ :=
    (innerSL ℂ x).integrable_comp ((ContinuousLinearMap.apply ℂ H x).integrable_comp
      (integrable_rankOne_orbit μ ρ x hρ))
  have hReal : (⟪x, compactRepresentationAverage μ ρ x x⟫_ℂ).re = ∫ k, v k ∂μ := by
    change RCLike.re (⟪x, compactRepresentationAverage μ ρ x x⟫_ℂ) = _
    rw [inner_compactRepresentationAverage μ ρ x hρ, ← integral_re hi]
    apply integral_congr_ae
    refine ae_of_all _ fun k ↦ ?_
    change (⟪x, rankOne ℂ (ρ k x) (ρ k x) x⟫_ℂ).re = v k
    rw [rankOne_apply, inner_smul_right, mul_comm, ← inner_conj_symm (ρ k x) x, Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq, Complex.ofReal_re, norm_inner_symm]
  intro hz
  rw [hz, zero_apply, inner_zero_right, Complex.zero_re] at hReal
  exact hp.ne' hReal.symm

end Mixing
end

/- Source module Mixing.FourierUniqueness. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Fourier uniqueness on the compact dual -/


open Filter MeasureTheory Set TopologicalSpace
open scoped ComplexConjugate ENNReal Pointwise Topology

namespace Mixing

variable {G : Type*} [Group G]

noncomputable section

/-- The dual evaluation functions are a multiplicative family of complex continuous functions. -/
def dualCharacters : G →* C(DiscreteDual G, ℂ) where
  toFun g := ⟨fun χ => (dualEvaluation g χ : ℂ), continuous_subtype_val.comp (dualEvaluation g).continuous⟩
  map_one' := by
    let _ : TopologicalSpace G := ⊥
    ext χ
    change ((χ 1 : Circle) : ℂ) = 1
    rw [map_one, Circle.coe_one]
  map_mul' a b := by
    let _ : TopologicalSpace G := ⊥
    ext χ
    change ((χ (a * b) : Circle) : ℂ) = ((χ a : Circle) : ℂ) * ((χ b : Circle) : ℂ)
    rw [map_mul, Circle.coe_mul]

theorem dualCharacters_star (g : G) : star (dualCharacters g) = dualCharacters g⁻¹ := by
  let _ : TopologicalSpace G := ⊥
  ext χ
  change star ((χ g : Circle) : ℂ) = ((χ g⁻¹ : Circle) : ℂ)
  rw [map_inv, Circle.coe_inv_eq_conj, Complex.star_def]

/-- Trigonometric polynomials are dense in the continuous functions on the
compact dual. -/
theorem denseRange_dualCharacterSpan :
    Dense (((Submodule.span ℂ (Set.range (dualCharacters (G := G)))) : Submodule ℂ
      C(DiscreteDual G, ℂ)) : Set C(DiscreteDual G, ℂ)) := by
  let S : StarSubalgebra ℂ C(DiscreteDual G, ℂ) :=
    StarAlgebra.adjoin ℂ (Set.range (dualCharacters (G := G)))
  have hspan : S.toSubalgebra.toSubmodule = Submodule.span ℂ (Set.range (dualCharacters (G := G))) := by
    unfold S
    rw [StarAlgebra.adjoin_eq_span]
    have hStar : star (Set.range (dualCharacters (G := G))) ⊆
        Set.range (dualCharacters (G := G)) := by
      intro f hf
      obtain ⟨g, hg⟩ := Set.mem_star.mp hf
      exact ⟨g⁻¹, by rw [← dualCharacters_star, hg, star_star]⟩
    rw [union_eq_left.mpr hStar]
    let M : Submonoid C(DiscreteDual G, ℂ) := MonoidHom.mrange (dualCharacters (G := G))
    change Submodule.span ℂ
      (↑(Submonoid.closure (M : Set C(DiscreteDual G, ℂ))) : Set C(DiscreteDual G, ℂ)) = _
    rw [Submonoid.closure_eq]
    rfl
  have hSep : S.SeparatesPoints := by
    let _ : TopologicalSpace G := ⊥
    intro χ ψ hne
    have h : ∃ g : G, dualEvaluation g χ ≠ dualEvaluation g ψ := by
      by_contra! hh
      exact hne (PontryaginDual.ext hh)
    obtain ⟨g, hg⟩ := h
    have hMem : dualCharacters g ∈ S := StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g)
    refine ⟨dualCharacters g, ⟨dualCharacters g, hMem, rfl⟩, ?_⟩
    exact fun h => hg (Subtype.ext h)
  have hDense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hSep
  rw [← hspan, dense_iff_closure_eq]
  exact congrArg (fun A : StarSubalgebra ℂ C(DiscreteDual G, ℂ) => (A : Set C(DiscreteDual G, ℂ))) hDense

/-- Integration against a finite measure as a bounded functional on continuous tests. -/
def integralContinuousDual (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ] :
    C(DiscreteDual G, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

theorem integralContinuousDual_apply (μ : Measure (DiscreteDual G)) [IsFiniteMeasure μ]
    (f : C(DiscreteDual G, ℂ)) :
    integralContinuousDual μ f = ∫ χ, f χ ∂μ := by
  change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ f) = _
  rw [← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) μ f)

/-- Finite regular measures on the dual are determined by their Fourier coefficients. -/
theorem eq_of_spectralFourier_eq (μ ν : Measure (DiscreteDual G))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular]
    (h : ∀ g : G, spectralFourier μ g = spectralFourier ν g) : μ = ν := by
  let I := integralContinuousDual μ - integralContinuousDual ν
  have hLin : ∀ f : C(DiscreteDual G, ℂ), integralContinuousDual μ f = integralContinuousDual ν f := by
    intro f
    have hSub : Submodule.span ℂ (Set.range (dualCharacters (G := G))) ≤ I.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      change integralContinuousDual μ (dualCharacters g) - integralContinuousDual ν (dualCharacters g) = 0
      rw [sub_eq_zero, integralContinuousDual_apply, integralContinuousDual_apply]
      exact h g
    have hs : ((Submodule.span ℂ (Set.range (dualCharacters (G := G))) : Submodule ℂ
      C(DiscreteDual G, ℂ)) : Set C(DiscreteDual G, ℂ)) ⊆ (I.ker : Set C(DiscreteDual G, ℂ)) := hSub
    have hClosure := closure_minimal hs I.isClosed_ker
    have hMem : f ∈ I.ker :=
      hClosure ((denseRange_dualCharacterSpan (G := G)) f)
    exact sub_eq_zero.mp hMem
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have h' := hLin (complexify f.toContinuousMap)
  rw [integralContinuousDual_apply, integralContinuousDual_apply] at h'
  change (∫ χ, (f χ : ℂ) ∂μ) = (∫ χ, (f χ : ℂ) ∂ν) at h'
  have hμ := integral_ofReal (𝕜 := ℂ) (μ := μ) (f := ⇑f)
  have hν := integral_ofReal (𝕜 := ℂ) (μ := ν) (f := ⇑f)
  exact Complex.ofReal_injective (hμ.symm.trans (h'.trans hν))

instance discreteDual_metrizableSpace [Countable G] : MetrizableSpace (DiscreteDual G) := by
  let e (χ : DiscreteDual G) (g : G) := dualEvaluation g χ
  have hc : Continuous e := continuous_pi fun g => (dualEvaluation g).continuous
  have hi : Function.Injective e := by
    let _ : TopologicalSpace G := ⊥
    intro χ ψ h
    exact PontryaginDual.ext (congr_fun h)
  exact (hc.isClosedEmbedding hi).isEmbedding.metrizableSpace

/-- Convolution multiplies Fourier coefficients on the compact dual. -/
theorem spectralFourier_mconv [Countable G] (μ ν : Measure (DiscreteDual G))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (g : G) :
    spectralFourier (μ ∗ₘ ν) g = spectralFourier μ g * spectralFourier ν g := by
  let _ : TopologicalSpace G := ⊥
  have h_eval : Measurable (fun χ : DiscreteDual G => (dualEvaluation g χ : ℂ)) :=
    (continuous_subtype_val.comp (dualEvaluation g).continuous).measurable
  unfold spectralFourier Measure.mconv
  rw [integral_map (continuous_mul.measurable.aemeasurable) h_eval.aestronglyMeasurable]
  change (∫ z : DiscreteDual G × DiscreteDual G, (dualEvaluation g (z.1 * z.2) : ℂ) ∂μ.prod ν) = _
  calc
    _ = ∫ z : DiscreteDual G × DiscreteDual G,
      (dualEvaluation g z.1 : ℂ) * (dualEvaluation g z.2 : ℂ) ∂μ.prod ν := by
      apply integral_congr_ae
      exact .of_forall fun z => by
        change ((z.1 g * z.2 g : Circle) : ℂ) = ((z.1 g : Circle) : ℂ) * ((z.2 g : Circle) : ℂ)
        exact Circle.coe_mul _ _
    _ = _ := integral_prod_mul (μ := μ) (ν := ν)
      (fun χ => (dualEvaluation g χ : ℂ)) (fun χ => (dualEvaluation g χ : ℂ))

/-- Equality (18)'s spectral consequence. If the diagonal matrix coefficient
of a vector is the product of two other diagonal coefficients, its spectral
measure is the convolution of the two spectral measures. -/
theorem dualVectorSpectralMeasure_eq_mconv_of_coefficients [Countable G] [IsMulCommutative G]
    {H₁ H₂ H₃ : Type*} [NormedAddCommGroup H₁] [NormedAddCommGroup H₂] [NormedAddCommGroup H₃]
    [InnerProductSpace ℂ H₁] [InnerProductSpace ℂ H₂] [InnerProductSpace ℂ H₃]
    [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace H₃]
    (U₁ : G →* (H₁ ≃ₗᵢ[ℂ] H₁)) (U₂ : G →* (H₂ ≃ₗᵢ[ℂ] H₂)) (U₃ : G →* (H₃ ≃ₗᵢ[ℂ] H₃))
    (x₁ : H₁) (x₂ : H₂) (x₃ : H₃)
    (h : ∀ g : G, inner ℂ x₃ (U₃ g x₃) = inner ℂ x₁ (U₁ g x₁) * inner ℂ x₂ (U₂ g x₂)) :
    dualVectorSpectralMeasure U₃ x₃ = dualVectorSpectralMeasure U₁ x₁ ∗ₘ dualVectorSpectralMeasure U₂ x₂ := by
  let μ := dualVectorSpectralMeasure U₁ x₁
  let ν := dualVectorSpectralMeasure U₂ x₂
  have : IsFiniteMeasure (μ ∗ₘ ν) := Measure.isFiniteMeasure_map _ _
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_mconv, spectralFourier_dualVectorSpectralMeasure,
    spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure]
  exact h g

/-- An isometric intertwiner preserves vector spectral measures. -/
theorem dualVectorSpectralMeasure_eq_of_isometric_intertwiner [IsMulCommutative G]
    {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K))
    (J : H →ₗᵢ[ℂ] K) (hJ : ∀ g x, J (U g x) = V g (J x)) (x : H) :
    dualVectorSpectralMeasure V (J x) = dualVectorSpectralMeasure U x := by
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure, ← hJ]
  exact J.inner_map_map _ _

end

end Mixing
end

/- Source module Mixing.MildMixing. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Rigid vectors and mild mixing -/


open Filter Set
open scoped InnerProductSpace Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The free idempotents `E(G*)`. -/
def freeIdempotentUltrafilters (G : Type*) [Group G] : Set (Ultrafilter G) :=
  {p | p ∈ freeUltrafilters G ∧ p * p = p}

omit [Group G] in
theorem isClosed_freeUltrafilters : IsClosed (freeUltrafilters G) := by
  have h : freeUltrafilters G = ⋂ S : {S : Set G // S ∈ (cofinite : Filter G)}, {p | S.val ∈ p} := by
    ext p
    simp only [freeUltrafilters, Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
    rfl
  rw [h]
  exact isClosed_iInter fun S => ultrafilter_isClosed_basic S.val

theorem mul_mem_freeUltrafilters {p q : Ultrafilter G} (hq : q ∈ freeUltrafilters G) :
    p * q ∈ freeUltrafilters G := by
  intro S hS
  change ∀ᶠ a in ((p * q : Ultrafilter G) : Filter G), a ∈ S
  rw [Ultrafilter.eventually_mul]
  filter_upwards with a
  exact hq (((mul_right_injective a).tendsto_cofinite) hS)

/-- Weak convergence of the orbit of `x` to `x` along the displayed sequence. -/
def IsRigidAlong (g : ℕ → G) (x : H) : Prop :=
  ∀ y : H, Tendsto (fun n => ⟪y, U (g n) x⟫_ℂ) atTop (𝓝 ⟪y, x⟫_ℂ)

/-- A vector is rigid if its orbit returns weakly along a sequence escaping finite sets. -/
def IsRigidVector (x : H) : Prop :=
  ∃ g : ℕ → G, Tendsto g atTop cofinite ∧ IsRigidAlong U g x

/-- Mild mixing means that zero is the only rigid vector. -/
def IsMildlyMixing : Prop := ∀ x : H, IsRigidVector U x → x = 0

/-- Lemma 6. A rigid sequence yields a free idempotent ultrafilter fixing the vector. -/
theorem exists_freeIdempotent_fixed_of_rigidAlong (g : ℕ → G) (hg : Tendsto g atTop cofinite)
    (x : H) (hx : IsRigidAlong U g x) :
    ∃ p ∈ freeIdempotentUltrafilters G, ultrafilterOperator U p x = x := by
  let S : Set (Ultrafilter G) := {p | p ∈ freeUltrafilters G ∧ ultrafilterOperator U p x = x}
  have hNonempty : S.Nonempty := by
    obtain ⟨p, hp⟩ := exists_ultrafilter_le (Filter.map g atTop)
    refine ⟨p, hp.trans hg, ?_⟩
    apply ext_inner_left ℂ
    intro y
    have hlim : Tendsto (fun a : G => ⟪y, U a x⟫_ℂ) (Filter.map g atTop) (𝓝 ⟪y, x⟫_ℂ) :=
      Filter.tendsto_map'_iff.mpr (hx y)
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p y x)
      (hlim.mono_left hp)
  have hClosed : IsClosed S := by
    have hFix : IsClosed (⋂ y : H, {p | ⟪y, ultrafilterOperator U p x⟫_ℂ = ⟪y, x⟫_ℂ}) := by
      apply isClosed_iInter
      intro y
      exact isClosed_eq
        ((ContinuousLinearMapWOT.continuous_dual_apply x (InnerProductSpace.toDual ℂ H y)).comp
          (continuous_ultrafilterOperator_wot U)) continuous_const
    have he : S = freeUltrafilters G ∩ ⋂ y : H,
        {p | ⟪y, ultrafilterOperator U p x⟫_ℂ = ⟪y, x⟫_ℂ} := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact and_congr_right fun _ => ⟨fun h y => congrArg (inner ℂ y) h, ext_inner_left ℂ⟩
    rw [he]
    exact isClosed_freeUltrafilters.inter hFix
  have hMul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S := by
    rintro p ⟨_, hp⟩ q ⟨hq₁, hq₂⟩
    refine ⟨mul_mem_freeUltrafilters hq₁, ?_⟩
    rw [ultrafilterOperator_mul]
    change ultrafilterOperator U p (ultrafilterOperator U q x) = x
    rw [hq₂, hp]
  obtain ⟨p, ⟨hp, hfix⟩, hidem⟩ := exists_idempotent_in_compact_subsemigroup
    Ultrafilter.continuous_mul_left S hNonempty hClosed.isCompact hMul
  exact ⟨p, ⟨hp, hidem⟩, hfix⟩

/-- Lemma 7. A free idempotent acts as a self-adjoint idempotent. -/
theorem ultrafilterOperator_isOrthogonalProjection (p : Ultrafilter G)
    (hp : p ∈ freeIdempotentUltrafilters G) :
    ultrafilterOperator U p * ultrafilterOperator U p = ultrafilterOperator U p ∧
      IsSelfAdjoint (ultrafilterOperator U p) := by
  have hIdem : ultrafilterOperator U p * ultrafilterOperator U p = ultrafilterOperator U p := by
    rw [← ultrafilterOperator_mul, hp.2]
  exact ⟨hIdem, isSelfAdjoint_of_idempotent_contraction _ hIdem
    (ultrafilterOperator_norm_le_one U p)⟩

/-- If the weak ultrafilter limit of a vector equals the vector itself, then
the unitary orbit also converges to that vector in norm along the ultrafilter. -/
theorem tendsto_orbit_of_ultrafilter_fixed (p : Ultrafilter G) (x : H)
    (hx : ultrafilterOperator U p x = x) :
    Tendsto (fun g => U g x) (p : Filter G) (𝓝 x) := by
  have hCoeff := tendsto_ultrafilterOperator_coeff U p x x
  rw [hx] at hCoeff
  have hRe := (Complex.continuous_re.tendsto _).comp hCoeff
  have hSq : Tendsto (fun g => ‖U g x - x‖ ^ 2) (p : Filter G) (𝓝 (0 : ℝ)) := by
    have hRe' : Tendsto (fun g => (⟪x, U g x⟫_ℂ).re) (p : Filter G) (𝓝 (‖x‖ ^ 2)) := by
      have heq : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
      simpa only [Function.comp_def, heq] using hRe
    have hlim := (tendsto_const_nhds (x := ‖x‖ ^ 2 + ‖x‖ ^ 2)).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hRe')
    have hEq (g : G) : ‖U g x - x‖ ^ 2 = ‖x‖ ^ 2 + ‖x‖ ^ 2 - 2 * (⟪x, U g x⟫_ℂ).re := by
      rw [norm_sub_sq (𝕜 := ℂ), (U g).norm_map, ← inner_conj_symm (U g x) x]
      change ‖x‖ ^ 2 - 2 * (star (⟪x, U g x⟫_ℂ)).re + ‖x‖ ^ 2 = _
      rw [Complex.star_def, Complex.conj_re]
      ring
    have hz : ‖x‖ ^ 2 + ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 = 0 := by ring
    simpa only [hEq, hz] using hlim
  rw [Metric.tendsto_nhds] at hSq ⊢
  intro ε hε
  filter_upwards [hSq (ε ^ 2) (sq_pos_of_pos hε)] with g hg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at hg
  rw [dist_eq_norm]
  by_contra! h
  exact hg.not_ge (pow_le_pow_left₀ hε.le h 2)

/-- A vector fixed by a free ultrafilter is rigid along an escaping sequence. -/
theorem isRigidVector_of_ultrafilter_fixed [Countable G] (p : Ultrafilter G)
    (hp : p ∈ freeUltrafilters G) (x : H) (hx : ultrafilterOperator U p x = x) :
    IsRigidVector U x := by
  obtain ⟨e, he⟩ := exists_injective_nat G
  let _ : (cofinite : Filter G).IsCountablyGenerated := by
    rw [← he.comap_cofinite_eq, Nat.cofinite_eq_atTop]
    infer_instance
  let f := fun g : G => U g x
  let l : Filter G := cofinite ⊓ comap f (𝓝 x)
  have hpl : (p : Filter G) ≤ l :=
    le_inf hp (tendsto_orbit_of_ultrafilter_fixed U p x hx).le_comap
  let _ : NeBot l := neBot_of_le hpl
  obtain ⟨g, hg⟩ := Filter.exists_seq_tendsto l
  refine ⟨g, hg.mono_right inf_le_left, ?_⟩
  intro y
  have hnorm : Tendsto (f ∘ g) atTop (𝓝 x) := tendsto_comap.comp (hg.mono_right inf_le_right)
  exact ((InnerProductSpace.toDual ℂ H y).continuous.tendsto x).comp hnorm

/-- Proposition 5. Mild mixing is precisely mixing along all free idempotent
ultrafilters. -/
theorem isMildlyMixing_iff_isUMixing_freeIdempotents [Countable G] :
    IsMildlyMixing U ↔ IsUMixing U (freeIdempotentUltrafilters G) := by
  constructor
  · intro h p hp
    apply ContinuousLinearMap.ext
    intro x
    apply h
    have hIdem := (ultrafilterOperator_isOrthogonalProjection U p hp).1
    exact isRigidVector_of_ultrafilter_fixed U p hp.1 _
      (congrArg (fun T : H →L[ℂ] H => T x) hIdem)
  · rintro h x ⟨g, hg, hx⟩
    obtain ⟨p, hp, hfix⟩ := exists_freeIdempotent_fixed_of_rigidAlong U g hg x hx
    rw [h p hp, zero_apply] at hfix
    exact hfix.symm

end Mixing
end

/- Source module Mixing.SpectralMeasureClass. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Hilbert-space spectral criteria in the measure class -/


open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- Vanishing of the weak ultrafilter coefficient persists after multiplying
the spectral Fourier integrand by an arbitrary integrable scalar weight. -/
theorem tendsto_weighted_spectralCoefficient_zero (x : H) (p : Ultrafilter G)
    (hx : ultrafilterOperator U p x = 0)
    (w : RepresentationSpectrum U → ℂ) (hw : Measurable w)
    (hInt : Integrable w (vectorSpectralMeasure U x)) :
    Tendsto (fun g => ∫ z, w z * spectralCoefficient U g z ∂vectorSpectralMeasure U x)
      (p : Filter G) (𝓝 0) := by
  let μ := vectorSpectralMeasure U x
  let A (n : ℕ) : Set (RepresentationSpectrum U) := {z | ‖w z‖ ≤ n}
  let wN (n : ℕ) := (A n).indicator w
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le hw.norm measurable_const
  have hm (n : ℕ) : Measurable (wN n) := hw.indicator (hA n)
  have hBound (n : ℕ) (z : RepresentationSpectrum U) : ‖wN n z‖ ≤ n := by
    by_cases hz : z ∈ A n
    · change ‖(A n).indicator w z‖ ≤ n
      rw [Set.indicator_of_mem hz]
      exact hz
    · simp [wN, Set.indicator_of_notMem hz]
  have hiN (n : ℕ) : Integrable (wN n) μ :=
    Integrable.of_bound (hm n).aestronglyMeasurable n (.of_forall (hBound n))
  have hIntMul (g : G) (f : RepresentationSpectrum U → ℂ) (hf : Measurable f)
      (hi : Integrable f μ) : Integrable (fun z => f z * spectralCoefficient U g z) μ := by
    apply hi.norm.mono' (hf.mul (spectralCoefficient U g).continuous.measurable).aestronglyMeasurable
    exact .of_forall fun z => by
      rw [Pi.mul_apply, norm_mul, spectralCoefficient_apply, Circle.norm_coe, mul_one]
  have hCutLim (n : ℕ) : Tendsto (fun g => ∫ z, wN n z * spectralCoefficient U g z ∂μ)
      (p : Filter G) (𝓝 0) := by
    have hLp : MemLp (fun z => conj (wN n z)) 2 μ :=
      MemLp.of_bound (Complex.continuous_conj.measurable.comp (hm n)).aestronglyMeasurable n
        (.of_forall fun z => by simpa only [Complex.norm_conj] using hBound n z)
    let y := cyclicSpectralIsometry U x (hLp.toLp _)
    have hCoeff (g : G) : (∫ z, wN n z * spectralCoefficient U g z ∂μ) = ⟪y, U g x⟫_ℂ := by
      change _ = ⟪y, linearRepresentation U g x⟫_ℂ
      rw [← spectralCalculus_spectralCoefficient U g]
      change _ = ⟪cyclicSpectralIsometry U x (hLp.toLp _), spectralCalculus U (spectralCoefficient U g) x⟫_ℂ
      rw [inner_cyclicSpectralIsometry_spectralCalculus, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hLp.coeFn_toLp, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ
        (spectralCoefficient U g)] with z hz hz'
      rw [hz, hz', RCLike.inner_apply', starRingEnd_self_apply]
    have ht := tendsto_ultrafilterOperator_coeff U p y x
    rw [hx, inner_zero_right] at ht
    simpa only [hCoeff] using ht
  have hTail (n : ℕ) (z : RepresentationSpectrum U) : ‖w z - wN n z‖ ≤ ‖w z‖ := by
    by_cases hz : z ∈ A n
    · simp [wN, Set.indicator_of_mem hz]
    · simp [wN, Set.indicator_of_notMem hz]
  have hTailLim (z : RepresentationSpectrum U) : Tendsto (fun n => ‖w z - wN n z‖) atTop (𝓝 0) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖w z‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hz : z ∈ A n := hN.trans (by exact_mod_cast hn)
    simp [wN, Set.indicator_of_mem hz]
  have hL1 : Tendsto (fun n => ∫ z, ‖w z - wN n z‖ ∂μ) atTop (𝓝 0) := by
    simpa only [Pi.sub_apply, integral_zero] using
      tendsto_integral_of_dominated_convergence (μ := μ) (fun z => ‖w z‖)
        (fun n => ((hw.sub (hm n)).norm).aestronglyMeasurable) hInt.norm
        (fun n => .of_forall fun z => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          exact hTail n z) (.of_forall hTailLim)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (hL1.eventually_lt_const (half_pos hε)).exists
  filter_upwards [(hCutLim n).norm.eventually_lt_const (show ‖(0 : ℂ)‖ < ε / 2 by simpa using half_pos hε)]
    with g hg
  rw [dist_zero_right]
  have hErr : ‖(∫ z, w z * spectralCoefficient U g z ∂μ) -
      ∫ z, wN n z * spectralCoefficient U g z ∂μ‖ ≤ ∫ z, ‖w z - wN n z‖ ∂μ := by
    rw [← integral_sub' (hIntMul g w hw hInt) (hIntMul g (wN n) (hm n) (hiN n))]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    exact .of_forall fun z => by
      simp only [Pi.sub_apply]
      rw [← sub_mul, norm_mul, spectralCoefficient_apply, Circle.norm_coe, mul_one]
  let a := ∫ z, w z * spectralCoefficient U g z ∂μ
  let b := ∫ z, wN n z * spectralCoefficient U g z ∂μ
  have hTri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a - b) b
  have hTri' : ‖a‖ ≤ (∫ z, ‖w z - wN n z‖ ∂μ) + ‖b‖ :=
    hTri.trans (add_le_add hErr le_rfl)
  exact hTri'.trans_lt (by linarith [add_lt_add hn hg])

/-- Every finite positive measure absolutely continuous with respect to the
spectral measure of a vector in the ultrafilter kernel has a vanishing
Fourier transform along that ultrafilter. -/
theorem tendsto_spectralFourier_zero_of_ac (x : H) (p : Ultrafilter G)
    (hx : ultrafilterOperator U p x = 0) (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν]
    (hν : ν ≪ dualVectorSpectralMeasure U x) :
    Tendsto (spectralFourier ν) (p : Filter G) (𝓝 0) := by
  let σ := dualVectorSpectralMeasure U x
  let w (χ : DiscreteDual G) : ℂ := ((ν.rnDeriv σ χ).toReal : ℂ)
  have hw : Measurable w :=
    Complex.continuous_ofReal.measurable.comp ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
  have hwi : Integrable w σ :=
    (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := σ)).ofReal
  let f := spectralPointDual U
  have hf : Measurable f := (spectralPointDual_continuous U).measurable
  have hlim := tendsto_weighted_spectralCoefficient_zero U x p hx (w ∘ f) (hw.comp hf)
    (hwi.comp_measurable hf)
  refine hlim.congr' (.of_forall fun g => ?_)
  change (∫ z, w (f z) * spectralCoefficient U g z ∂vectorSpectralMeasure U x) =
    ∫ χ, (dualEvaluation g χ : ℂ) ∂ν
  have hIntegrand (z : RepresentationSpectrum U) :
      w (f z) * spectralCoefficient U g z = w (f z) * (dualEvaluation g (f z) : ℂ) := rfl
  simp_rw [hIntegrand]
  have hMeas : Measurable fun χ => w χ * (dualEvaluation g χ : ℂ) :=
    hw.mul (continuous_subtype_val.comp (dualEvaluation g).continuous).measurable
  calc
    _ = ∫ χ, w χ * (dualEvaluation g χ : ℂ) ∂σ :=
      (integral_map hf.aemeasurable hMeas.aestronglyMeasurable).symm
    _ = _ := integral_rnDeriv_smul hν

/-- A vector whose spectral measure dominates all vector spectral measures
represents the maximal spectral type. -/
def IsMaximalSpectralVector (x : H) : Prop :=
  ∀ y : H, dualVectorSpectralMeasure U y ≪ dualVectorSpectralMeasure U x

/-- The measure-class form of Theorem 6.1(ii) for finite positive measures.
The right side allows every measure dominated by the maximal spectral type,
which is stronger than testing only equivalent measures. -/
theorem theorem6_1_ii_positiveMeasureClass (P : Set (Ultrafilter G))
    (x : H) (hx : IsMaximalSpectralVector U x) :
    IsUMixing U P ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν], ν ≪ dualVectorSpectralMeasure U x →
        ∀ p ∈ P, ∀ q : Ultrafilter G,
          Tendsto (spectralFourier ν) ((q * p : Ultrafilter G) : Filter G) (𝓝 0) := by
  constructor
  · intro h ν _ hν p hp q
    apply tendsto_spectralFourier_zero_of_ac U x (q * p) _ ν hν
    rw [ultrafilterOperator_mul, h p hp, mul_zero, zero_apply]
  · intro h
    apply (isUMixing_iff_all_vector_fourier_vanish U P).mpr
    intro y p hp q
    exact @h (dualVectorSpectralMeasure U y) _ (hx y) p hp q

/-- Theorem 6.1(ii) phrased using exactly the mutually absolutely continuous
finite positive representatives of the maximal spectral type. -/
theorem theorem6_1_ii_equivalent_positiveMeasureClass (P : Set (Ultrafilter G))
    (x : H) (hx : IsMaximalSpectralVector U x) :
    IsUMixing U P ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν],
        ν ≪ dualVectorSpectralMeasure U x → dualVectorSpectralMeasure U x ≪ ν →
        ∀ p ∈ P, ∀ q : Ultrafilter G,
          Tendsto (spectralFourier ν) ((q * p : Ultrafilter G) : Filter G) (𝓝 0) := by
  constructor
  · intro h ν _ hν _
    have hm := (theorem6_1_ii_positiveMeasureClass U P x hx).mp h
    exact @hm ν _ hν
  · intro h
    apply (isUMixing_iff_all_vector_fourier_vanish U P).mpr
    intro y p hp q
    have hZero : ultrafilterOperator U p x = 0 := by
      let r := inverseUltrafilter p * p
      have hRefl := Measure.AbsolutelyContinuous.refl (dualVectorSpectralMeasure U x)
      have hFourier := @h (dualVectorSpectralMeasure U x) _ hRefl hRefl p hp (inverseUltrafilter p)
      rw [funext (spectralFourier_dualVectorSpectralMeasure U x)] at hFourier
      have he := tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U r x x) hFourier
      rw [show r = inverseUltrafilter p * p from rfl, ultrafilterOperator_mul,
        ultrafilterOperator_inverse] at he
      change ⟪x, (ultrafilterOperator U p).adjoint (ultrafilterOperator U p x)⟫_ℂ = 0 at he
      rw [ContinuousLinearMap.adjoint_inner_right] at he
      exact inner_self_eq_zero.mp he
    have hZero' : ultrafilterOperator U (q * p) x = 0 := by
      rw [ultrafilterOperator_mul]
      change ultrafilterOperator U q (ultrafilterOperator U p x) = _
      rw [hZero, map_zero]
    exact tendsto_spectralFourier_zero_of_ac U x (q * p) hZero' (dualVectorSpectralMeasure U y) (hx y)

/-- Theorem 6.1(iii). Every finite positive representative of the maximal
spectral type is Rajchman exactly when the representation is strongly mixing. -/
theorem theorem6_1_iii_equivalent_positiveMeasureClass
    (x : H) (hx : IsMaximalSpectralVector U x) :
    IsStronglyMixing U ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν],
        ν ≪ dualVectorSpectralMeasure U x → dualVectorSpectralMeasure U x ≪ ν →
        Tendsto (spectralFourier ν) cofinite (𝓝 0) := by
  rw [isStronglyMixing_iff_isUMixing_free U, theorem6_1_ii_equivalent_positiveMeasureClass U _ x hx]
  constructor
  · intro h ν _ hν hν'
    apply (Filter.tendsto_iff_ultrafilter _ _ _).mpr
    intro p hp
    have hlim := @h ν _ hν hν' p hp (pure 1)
    have heq : (pure 1 : Ultrafilter G) * p = p := by
      apply Ultrafilter.coe_inj.mp
      ext S
      change (∀ᶠ a in ((pure 1 * p : Ultrafilter G) : Filter G), a ∈ S) ↔
        ∀ᶠ a in (p : Filter G), a ∈ S
      simp [Ultrafilter.eventually_mul]
    rwa [heq] at hlim
  · intro h ν _ hν hν' p hp q
    exact (@h ν _ hν hν').mono_left (mul_mem_freeUltrafilters (p := q) hp)

/-- Theorem 6.1(iv). Set the reference measure to Haar measure to obtain the
absolutely continuous spectral criterion. -/
theorem theorem6_1_iv_equivalent_positiveMeasureClass (reference : Measure (DiscreteDual G))
    (x : H) (hx : IsMaximalSpectralVector U x) :
    (∀ y : H, dualVectorSpectralMeasure U y ≪ reference) ↔
      ∀ (ν : Measure (DiscreteDual G)) [IsFiniteMeasure ν],
        ν ≪ dualVectorSpectralMeasure U x → dualVectorSpectralMeasure U x ≪ ν → ν ≪ reference := by
  constructor
  · intro h ν _ hν _
    exact hν.trans (h x)
  · intro h y
    let σ := dualVectorSpectralMeasure U x
    have hσ := @h σ _ (Measure.AbsolutelyContinuous.refl σ) (Measure.AbsolutelyContinuous.refl σ)
    exact (hx y).trans hσ

end Mixing
end

/- Source module Mixing.SpectralOrthogonality. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Orthogonality from mutually singular spectral measures -/


open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

theorem spectralCalculus_complexify_adjoint (f : C(RepresentationSpectrum U, ℝ)) :
    (spectralCalculus U (complexify f)).adjoint = spectralCalculus U (complexify f) := by
  change star (spectralCalculus U (complexify f)) = _
  rw [← map_star, complexify_star]

theorem norm_spectralCalculus_complexify_sq (x : H) (f : C(RepresentationSpectrum U, ℝ)) :
    ‖spectralCalculus U (complexify f) x‖ ^ 2 =
      ∫ z, (f z) ^ 2 ∂vectorSpectralMeasure U x := by
  have hMul : complexify (f ^ 2) = complexify f * complexify f := by
    ext z
    simp only [complexify_apply, ContinuousMap.mul_apply, pow_two, Complex.ofReal_mul]
  have h := integral_vectorSpectralMeasure_real U x (f ^ 2)
  rw [hMul, map_mul] at h
  change (∫ z, (f z) ^ 2 ∂vectorSpectralMeasure U x) =
    (⟪x, spectralCalculus U (complexify f) (spectralCalculus U (complexify f) x)⟫_ℂ).re at h
  let A := spectralCalculus U (complexify f)
  have hInner := A.adjoint_inner_right x (A x)
  rw [show A.adjoint = A from spectralCalculus_complexify_adjoint U f] at hInner
  have hNorm : (⟪A x, A x⟫_ℂ).re = ‖A x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  exact (h.trans ((congrArg Complex.re hInner).trans hNorm)).symm

theorem norm_spectralCalculus_complexify_lt_of_zero_on (x : H)
    (f : C(RepresentationSpectrum U, ℝ)) {K : Set (RepresentationSpectrum U)}
    (hK : MeasurableSet K) (hf : ∀ z, f z ∈ Icc (0 : ℝ) 1) (hfK : Set.EqOn f 0 K)
    {ε : ℝ} (hε : 0 < ε) (hMass : vectorSpectralMeasure U x Kᶜ < ENNReal.ofReal (ε ^ 2)) :
    ‖spectralCalculus U (complexify f) x‖ < ε := by
  let μ := vectorSpectralMeasure U x
  have hi : Integrable (fun z => (f z) ^ 2) μ :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi' : Integrable (Kᶜ.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const _).indicator hK.compl
  have hBound : (∫ z, (f z) ^ 2 ∂μ) ≤ μ.real Kᶜ := by
    calc
      _ ≤ ∫ z, Kᶜ.indicator (fun _ => (1 : ℝ)) z ∂μ := by
        apply integral_mono hi hi'
        intro z
        by_cases hz : z ∈ K
        · have h0 : f z = 0 := hfK hz
          simp [h0, hz]
        · rw [Set.indicator_of_mem (show z ∈ Kᶜ from hz)]
          nlinarith [(hf z).1, (hf z).2, mul_nonneg (hf z).1 (sub_nonneg.mpr (hf z).2)]
      _ = _ := by rw [integral_indicator hK.compl, setIntegral_const, smul_eq_mul, mul_one]
  have hlt : μ.real Kᶜ < ε ^ 2 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ Kᶜ) ENNReal.ofReal_ne_top).mpr hMass
    rwa [ENNReal.toReal_ofReal (sq_nonneg ε)] at hh
  have hsq : ‖spectralCalculus U (complexify f) x‖ ^ 2 < ε ^ 2 :=
    (norm_spectralCalculus_complexify_sq U x f).trans_lt (hBound.trans_lt hlt)
  by_contra! h
  exact hsq.not_ge (pow_le_pow_left₀ hε.le h 2)

/-- The spectral orthogonality used in Theorem 6.2. The two vectors live in
the same representation, and singularity is tested on the common dual. -/
theorem inner_eq_zero_of_dualVectorSpectralMeasure_mutuallySingular (x y : H)
    (h : dualVectorSpectralMeasure U x ⟂ₘ dualVectorSpectralMeasure U y) : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨A, hA, hAx, hAy⟩ := h
  let z := spectralPointDual U
  let B := z ⁻¹' A
  let μ := vectorSpectralMeasure U x
  let ν := vectorSpectralMeasure U y
  have hz : Measurable z := (spectralPointDual_continuous U).measurable
  have hB : MeasurableSet B := hz hA
  have hBx : μ B = 0 := by
    rw [dualVectorSpectralMeasure, Measure.map_apply hz hA] at hAx
    exact hAx
  have hBy : ν Bᶜ = 0 := by
    rw [dualVectorSpectralMeasure, Measure.map_apply hz hA.compl] at hAy
    exact hAy
  by_contra hNonzero
  let ε := ‖⟪x, y⟫_ℂ‖ / (2 * (‖x‖ + ‖y‖ + 1))
  have hε : 0 < ε := div_pos (norm_pos_iff.mpr hNonzero) (by positivity)
  let δ := ENNReal.ofReal (ε ^ 2)
  have hδ : δ ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)).ne'
  obtain ⟨K, hK, hKc, hμK⟩ := hB.compl.exists_isCompact_sdiff_lt (measure_ne_top μ Bᶜ) hδ
  obtain ⟨L, hL, hLc, hνL⟩ := hB.exists_isCompact_sdiff_lt (measure_ne_top ν B) hδ
  have hμ : μ Kᶜ < δ := by
    have hs : Kᶜ ⊆ (Bᶜ \ K) ∪ B := fun t ht => by
      by_cases hb : t ∈ B
      · exact Or.inr hb
      · exact Or.inl ⟨hb, ht⟩
    exact (measure_mono hs).trans_lt ((measure_union_le _ _).trans_lt (by rwa [hBx, add_zero]))
  have hν : ν Lᶜ < δ := by
    have hs : Lᶜ ⊆ (B \ L) ∪ Bᶜ := fun t ht => by
      by_cases hb : t ∈ B
      · exact Or.inl ⟨hb, ht⟩
      · exact Or.inr hb
    exact (measure_mono hs).trans_lt ((measure_union_le _ _).trans_lt (by rwa [hBy, add_zero]))
  have hSep : _root_.Disjoint L K := Set.disjoint_left.mpr fun t ht hk => hK hk (hL ht)
  obtain ⟨f, hfL, hfK, hf⟩ :=
    exists_continuous_zero_one_of_isClosed hLc.isClosed hKc.isClosed hSep
  let P := spectralCalculus U (complexify f)
  have hX : ‖x - P x‖ < ε := by
    have hf' (z : RepresentationSpectrum U) : (1 - f) z ∈ Icc (0 : ℝ) 1 := by
      change 0 ≤ 1 - f z ∧ 1 - f z ≤ 1
      exact ⟨sub_nonneg.mpr (hf z).2, by linarith [(hf z).1]⟩
    have hfK' : Set.EqOn ((1 : C(RepresentationSpectrum U, ℝ)) - f)
        (0 : C(RepresentationSpectrum U, ℝ)) K := by
      intro z hz
      change 1 - f z = 0
      rw [hfK hz]
      exact sub_self 1
    have hlt := norm_spectralCalculus_complexify_lt_of_zero_on U x (1 - f)
      hKc.isClosed.measurableSet hf' hfK' hε hμ
    have hComp : complexify (1 - f) = 1 - complexify f := by
      ext z
      change Complex.ofReal (1 - f z) = 1 - Complex.ofReal (f z)
      simp
    rw [hComp, map_sub, map_one, sub_apply, one_apply_eq_self] at hlt
    exact hlt
  have hY : ‖P y‖ < ε :=
    norm_spectralCalculus_complexify_lt_of_zero_on U y f hLc.isClosed.measurableSet hf hfL hε hν
  have hInner : ⟪x, y⟫_ℂ = ⟪x - P x, y⟫_ℂ + ⟪x, P y⟫_ℂ := by
    have hAdj : ⟪x, P y⟫_ℂ = ⟪P x, y⟫_ℂ := by
      have hi := P.adjoint_inner_right x y
      rw [show P.adjoint = P from spectralCalculus_complexify_adjoint U f] at hi
      exact hi
    rw [hAdj, inner_sub_left, sub_add_cancel]
  have hEstimate : ‖⟪x, y⟫_ℂ‖ ≤ ε * (‖x‖ + ‖y‖) := by
    calc
      _ ≤ ‖⟪x - P x, y⟫_ℂ‖ + ‖⟪x, P y⟫_ℂ‖ := hInner ▸ norm_add_le _ _
      _ ≤ ‖x - P x‖ * ‖y‖ + ‖x‖ * ‖P y‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ε * (‖x‖ + ‖y‖) := by
        nlinarith [mul_le_mul_of_nonneg_right hX.le (norm_nonneg y),
          mul_le_mul_of_nonneg_left hY.le (norm_nonneg x)]
  have hεEq : ε * (2 * (‖x‖ + ‖y‖ + 1)) = ‖⟪x, y⟫_ℂ‖ :=
    div_mul_cancel₀ _ (by positivity)
  have hProd : 0 ≤ ε * (‖x‖ + ‖y‖) := by positivity
  nlinarith only [hEstimate, hεEq, hε, hProd]

end Mixing
end

/- Source module Mixing.SpectralMeasureSubmodule. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Absolute continuity of vector spectral measures -/


open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace Topology

namespace Mixing

section RegularOrder

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Order on finite regular measures can be tested by nonnegative continuous functions. -/
theorem measure_le_of_integral_nonnegative (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [μ.Regular] [ν.Regular]
    (h : ∀ f : C(X, ℝ), 0 ≤ f → ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν) : μ ≤ ν := by
  refine Measure.le_iff.mpr fun A hA => ?_
  by_contra! hNot
  obtain ⟨K, hKA, hK, hKt⟩ := hA.exists_lt_isCompact_of_ne_top (measure_ne_top μ A) hNot
  obtain ⟨O, hKO, hO, hOt⟩ := K.exists_isOpen_lt_of_lt (μ K) ((measure_mono hKA).trans_lt hKt)
  obtain ⟨f, hf1, _, hf2, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  have hLow (x : X) : K.indicator (fun _ => (1 : ℝ)) x ≤ f x := by
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, hf1 hx]
      exact le_rfl
    · rw [Set.indicator_of_notMem hx]
      exact (hf3 x).1
  have hHigh (x : X) : f x ≤ O.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ O
    · rw [Set.indicator_of_mem hx]
      exact (hf3 x).2
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport (fun h => hx (hf2 h))]
  have hiμ : Integrable (⇑f) μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiν : Integrable (⇑f) ν :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hReal : μ.real K ≤ ν.real O := calc
    _ = ∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂μ := (integral_indicator_one hK.measurableSet).symm
    _ ≤ ∫ x, f x ∂μ := integral_mono ((integrable_const _).indicator hK.measurableSet) hiμ hLow
    _ ≤ ∫ x, f x ∂ν := h f (fun x => (hf3 x).1)
    _ ≤ ∫ x, O.indicator (fun _ => (1 : ℝ)) x ∂ν :=
      integral_mono hiν ((integrable_const _).indicator hO.measurableSet) hHigh
    _ = _ := integral_indicator_one hO.measurableSet
  exact hOt.not_ge ((ENNReal.toReal_le_toReal (measure_ne_top μ K) (measure_ne_top ν O)).mp hReal)

end RegularOrder

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The integral of a nonnegative continuous spectral test is the squared norm of its
square-root multiplier on the vector. -/
theorem integral_vectorSpectralMeasure_eq_sqrt_norm (x : H)
    (f : C(RepresentationSpectrum U, ℝ)) (hf : 0 ≤ f) :
    (∫ z, f z ∂vectorSpectralMeasure U x) =
      ‖spectralCalculus U (complexify
        ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩) x‖ ^ 2 := by
  rw [norm_spectralCalculus_complexify_sq]
  apply integral_congr_ae
  exact .of_forall fun z => (Real.sq_sqrt (hf z)).symm

set_option maxHeartbeats 1200000 in
theorem vectorSpectralMeasure_add_le (x y : H) :
    vectorSpectralMeasure U (x + y) ≤ (2 : ℝ≥0∞) • (vectorSpectralMeasure U x + vectorSpectralMeasure U y) := by
  let μ := vectorSpectralMeasure U x + vectorSpectralMeasure U y
  have : IsFiniteMeasure ((2 : ℝ≥0∞) • μ) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top μ _)
  apply measure_le_of_integral_nonnegative
  intro f hf
  rw [integral_smul_measure, integral_add_measure]
  · rw [integral_vectorSpectralMeasure_eq_sqrt_norm U (x + y) f hf,
      integral_vectorSpectralMeasure_eq_sqrt_norm U x f hf,
      integral_vectorSpectralMeasure_eq_sqrt_norm U y f hf]
    simp only [map_add, ENNReal.toReal_ofNat, smul_eq_mul]
    let A := spectralCalculus U (complexify ⟨fun z => Real.sqrt (f z), Real.continuous_sqrt.comp f.continuous⟩)
    change ‖A x + A y‖ ^ 2 ≤ 2 * (‖A x‖ ^ 2 + ‖A y‖ ^ 2)
    have hTri := norm_add_le (A x) (A y)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hTri 2
    nlinarith only [hsq, sq_nonneg (‖A x‖ - ‖A y‖)]
  all_goals exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem dualVectorSpectralMeasure_add_le (x y : H) :
    dualVectorSpectralMeasure U (x + y) ≤
      (2 : ℝ≥0∞) • (dualVectorSpectralMeasure U x + dualVectorSpectralMeasure U y) := by
  have hf := (spectralPointDual_continuous U).measurable
  have hm := Measure.map_mono (vectorSpectralMeasure_add_le U x y) hf
  rw [Measure.map_smul (2 : ℝ≥0∞) hf.aemeasurable, Measure.map_add _ _ hf] at hm
  exact hm

theorem dualVectorSpectralMeasure_univ (x : H) :
    dualVectorSpectralMeasure U x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  unfold dualVectorSpectralMeasure
  rw [Measure.map_apply (spectralPointDual_continuous U).measurable MeasurableSet.univ, preimage_univ]
  conv_rhs => rw [← vectorSpectralMeasure_mass U x, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem dualVectorSpectralMeasure_map_unitary (g : G) (x : H) :
    dualVectorSpectralMeasure U (U g x) = dualVectorSpectralMeasure U x := by
  apply eq_of_spectralFourier_eq
  intro a
  rw [spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure]
  have hComm : U a (U g x) = U g (U a x) := by
    change (U a * U g) x = (U g * U a) x
    rw [← map_mul, ← map_mul, mul_comm' a g]
  rw [hComm, (U g).inner_map_map]

theorem dualVectorSpectralMeasure_smul (c : ℂ) (x : H) :
    dualVectorSpectralMeasure U (c • x) = ENNReal.ofReal (‖c‖ ^ 2) • dualVectorSpectralMeasure U x := by
  let μ := dualVectorSpectralMeasure U x
  have : IsFiniteMeasure (ENNReal.ofReal (‖c‖ ^ 2) • μ) := by
    constructor
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_dualVectorSpectralMeasure, (U g).map_smul, inner_smul_left, inner_smul_right]
  unfold spectralFourier
  rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _)]
  change star c * (c * ⟪x, U g x⟫_ℂ) =
    Complex.ofReal (‖c‖ ^ 2) * ∫ χ, (dualEvaluation g χ : ℂ) ∂μ
  rw [← mul_assoc, Complex.star_def, mul_comm (conj c) c, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact congrArg (Complex.ofReal (‖c‖ ^ 2) * ·) (spectralFourier_dualVectorSpectralMeasure U x g).symm

/-- The vectors whose spectral measure is absolutely continuous with respect
to a given measure form an invariant linear subspace. -/
noncomputable def spectralAbsoluteContinuousSubmodule (μ : Measure (DiscreteDual G)) : Submodule ℂ H where
  carrier := {x | dualVectorSpectralMeasure U x ≪ μ}
  zero_mem' := fun A _ => measure_mono_null (Set.subset_univ A) (by simp [dualVectorSpectralMeasure_univ])
  add_mem' := fun {x y} hx hy A hA => by
    apply le_antisymm ((dualVectorSpectralMeasure_add_le U x y) A |>.trans_eq ?_) bot_le
    simp only [smul_apply, add_apply, hx hA, hy hA, add_zero, smul_zero, bot_eq_zero]
  smul_mem' := fun c {x} hx A hA => by
    simp only [dualVectorSpectralMeasure_smul, smul_apply, hx hA, smul_zero]

theorem spectralAbsoluteContinuousSubmodule_invariant
    (μ : Measure (DiscreteDual G)) (g : G) (x : H)
    (hx : x ∈ spectralAbsoluteContinuousSubmodule U μ) :
    U g x ∈ spectralAbsoluteContinuousSubmodule U μ := by
  change dualVectorSpectralMeasure U (U g x) ≪ μ
  rw [dualVectorSpectralMeasure_map_unitary]
  exact hx

theorem spectralAbsoluteContinuousSubmodule_isClosed (μ : Measure (DiscreteDual G)) :
    IsClosed (spectralAbsoluteContinuousSubmodule U μ : Set H) := by
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  intro A hA
  have hbound (n : ℕ) : dualVectorSpectralMeasure U x A ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal (‖x - u n‖ ^ 2) := by
    have h := (dualVectorSpectralMeasure_add_le U (u n) (x - u n)) A
    rw [show u n + (x - u n) = x by abel, smul_apply, add_apply,
      (hu n : dualVectorSpectralMeasure U (u n) ≪ μ) hA, zero_add, smul_eq_mul] at h
    refine h.trans ?_
    gcongr
    exact (measure_mono (Set.subset_univ A)).trans_eq (dualVectorSpectralMeasure_univ U (x - u n))
  have h := (tendsto_const_nhds (x := x)).sub hlim
  rw [sub_self] at h
  have hh : Tendsto (fun n => (2 : ℝ≥0∞) * ENNReal.ofReal (‖x - u n‖ ^ 2)) atTop (𝓝 0) := by
    have h0 := (ENNReal.continuous_ofReal.tendsto _).comp (h.norm.pow 2)
    rw [norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero] at h0
    simpa only [Function.comp_def, mul_zero] using
      ENNReal.Tendsto.const_mul (a := 2) h0 (Or.inr ENNReal.ofNat_ne_top)
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hh hbound) bot_le

end Mixing
end

/- Source module Mixing.MaximalSpectralVector. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # A maximal spectral vector for a separable representation -/


open Filter MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal InnerProductSpace Topology

namespace Mixing

variable {G H : Type*} [Group G] [IsMulCommutative G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable section

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

def IsInvariantSubmodule (K : Submodule ℂ H) : Prop :=
  ∀ g : G, ∀ x ∈ K, U g x ∈ K

omit [IsMulCommutative G] [CompleteSpace H] in
theorem IsInvariantSubmodule.sup {U : G →* (H ≃ₗᵢ[ℂ] H)} {K L : Submodule ℂ H}
    (hK : IsInvariantSubmodule U K) (hL : IsInvariantSubmodule U L) :
    IsInvariantSubmodule U (K ⊔ L) := by
  intro g x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨U g a, hK g a ha, U g b, hL g b hb, rfl⟩

omit [IsMulCommutative G] [CompleteSpace H] in
theorem IsInvariantSubmodule.closure {U : G →* (H ≃ₗᵢ[ℂ] H)} {K : Submodule ℂ H}
    (hK : IsInvariantSubmodule U K) : IsInvariantSubmodule U K.topologicalClosure := by
  intro g x hx
  have hImage : U g '' (K : Set H) ⊆ K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hK g a ha
  exact closure_mono hImage (image_closure_subset_closure_image (U g).continuous ⟨x, hx, rfl⟩)

omit [IsMulCommutative G] [CompleteSpace H] in
theorem IsInvariantSubmodule.orthogonal {U : G →* (H ≃ₗᵢ[ℂ] H)} {K : Submodule ℂ H}
    (hK : IsInvariantSubmodule U K) : IsInvariantSubmodule U Kᗮ := by
  intro g x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  have hg : U g (U g⁻¹ y) = y := by
    change (U g * U g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  calc
    ⟪y, U g x⟫_ℂ = ⟪U g (U g⁻¹ y), U g x⟫_ℂ := by rw [hg]
    _ = ⟪U g⁻¹ y, x⟫_ℂ := (U g).inner_map_map _ _
    _ = 0 := hx _ (hK g⁻¹ y hy)

/-- The closed subspace generated by one orbit. -/
def cyclicClosedSubmodule (x : H) : ClosedSubmodule ℂ H :=
  (Submodule.span ℂ (Set.range fun g : G => U g x)).closure

omit [IsMulCommutative G] [CompleteSpace H] in
theorem mem_cyclicClosedSubmodule (x : H) : x ∈ cyclicClosedSubmodule U x := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  change U 1 x = x
  rw [map_one]
  rfl

omit [IsMulCommutative G] [CompleteSpace H] in
theorem cyclicClosedSubmodule_le (x : H) (K : ClosedSubmodule ℂ H) (hK : IsInvariantSubmodule U K)
    (hx : x ∈ K) : cyclicClosedSubmodule U x ≤ K := by
  change (Submodule.span ℂ (Set.range fun g : G => U g x)).closure ≤ K
  rw [Submodule.closure_le, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact hK g x hx

omit [IsMulCommutative G] [CompleteSpace H] in
theorem cyclicClosedSubmodule_invariant (x : H) : IsInvariantSubmodule U (cyclicClosedSubmodule U x) := by
  apply IsInvariantSubmodule.closure
  intro g y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨g * a, ?_⟩
    change U (g * a) x = U g (U a x)
    rw [map_mul]
    rfl
  | zero => simp
  | add y z _ _ hy hz => exact map_add (U g) y z ▸ Submodule.add_mem _ hy hz
  | smul c y _ hy => exact map_smul (U g) c y ▸ Submodule.smul_mem _ c hy

omit [IsMulCommutative G] [CompleteSpace H] in
theorem isInvariantSubmodule_closedSup (K L : ClosedSubmodule ℂ H)
    (hK : IsInvariantSubmodule U K) (hL : IsInvariantSubmodule U L) :
    IsInvariantSubmodule U (K ⊔ L : ClosedSubmodule ℂ H).toSubmodule := by
  rw [ClosedSubmodule.toSubmodule_sup]
  exact (hK.sup hL).closure

/-- Orthogonal projection onto an invariant closed subspace can only decrease a
vector spectral measure. -/
theorem dualVectorSpectralMeasure_starProjection_le (K : ClosedSubmodule ℂ H)
    (hK : IsInvariantSubmodule U K) (x : H) :
    dualVectorSpectralMeasure U (K.toSubmodule.starProjection x) ≤ dualVectorSpectralMeasure U x := by
  let y := K.toSubmodule.starProjection x
  let z := x - y
  have hy : y ∈ K := Submodule.starProjection_apply_mem _ _
  have hz : z ∈ K.toSubmoduleᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have he : x = y + z := by dsimp [z]; abel
  have hμ : dualVectorSpectralMeasure U x =
      dualVectorSpectralMeasure U y + dualVectorSpectralMeasure U z := by
    apply eq_of_spectralFourier_eq
    intro g
    have hiY : Integrable (fun χ => (dualEvaluation g χ : ℂ)) (dualVectorSpectralMeasure U y) :=
      (continuous_subtype_val.comp (dualEvaluation g).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hiZ : Integrable (fun χ => (dualEvaluation g χ : ℂ)) (dualVectorSpectralMeasure U z) :=
      (continuous_subtype_val.comp (dualEvaluation g).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hAdd : spectralFourier (dualVectorSpectralMeasure U y + dualVectorSpectralMeasure U z) g =
        spectralFourier (dualVectorSpectralMeasure U y) g + spectralFourier (dualVectorSpectralMeasure U z) g :=
      integral_add_measure hiY hiZ
    rw [hAdd, spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure,
      spectralFourier_dualVectorSpectralMeasure]
    have hOrth₁ : ⟪y, U g z⟫_ℂ = 0 := by
      have hh := hK.orthogonal g z hz
      rw [Submodule.mem_orthogonal] at hh
      exact hh y hy
    have hOrth₂ : ⟪z, U g y⟫_ℂ = 0 := by
      have hh := hz
      rw [Submodule.mem_orthogonal] at hh
      rw [← inner_conj_symm, hh _ (hK g y hy), map_zero]
    rw [he, map_add, inner_add_left, inner_add_right, inner_add_right, hOrth₁, hOrth₂, add_zero, zero_add]
  change dualVectorSpectralMeasure U y ≤ _
  rw [hμ]
  exact le_add_of_nonneg_right bot_le

/-- Start at zero and adjoin the cyclic orbit of each orthogonal residual in turn. -/
def partialCyclicSubmodule (v : ℕ → H) : ℕ → ClosedSubmodule ℂ H
  | 0 => ⊥
  | n + 1 =>
    let W := partialCyclicSubmodule v n
    W ⊔ cyclicClosedSubmodule U (v n - W.toSubmodule.starProjection (v n))

def orthogonalCyclicResidual (v : ℕ → H) (n : ℕ) : H :=
  v n - (partialCyclicSubmodule U v n).toSubmodule.starProjection (v n)

omit [IsMulCommutative G] in
theorem partialCyclicSubmodule_succ (v : ℕ → H) (n : ℕ) :
    partialCyclicSubmodule U v (n + 1) =
      partialCyclicSubmodule U v n ⊔ cyclicClosedSubmodule U (orthogonalCyclicResidual U v n) := rfl

omit [IsMulCommutative G] in
theorem partialCyclicSubmodule_monotone (v : ℕ → H) :
    Monotone (partialCyclicSubmodule U v) :=
  monotone_nat_of_le_succ fun n => partialCyclicSubmodule_succ U v n ▸ le_sup_left

omit [IsMulCommutative G] in
theorem partialCyclicSubmodule_invariant (v : ℕ → H) (n : ℕ) :
    IsInvariantSubmodule U (partialCyclicSubmodule U v n) := by
  induction n with
  | zero =>
    intro g x hx
    have hx' : x = 0 := hx
    simp [hx']
  | succ n ih =>
    rw [partialCyclicSubmodule_succ]
    exact isInvariantSubmodule_closedSup U _ _ ih (cyclicClosedSubmodule_invariant U _)

omit [IsMulCommutative G] in
theorem orthogonalCyclicResidual_mem_orthogonal (v : ℕ → H) (n : ℕ) :
    orthogonalCyclicResidual U v n ∈ (partialCyclicSubmodule U v n).toSubmoduleᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

omit [IsMulCommutative G] in
theorem cyclicClosedSubmodule_residual_le_orthogonal (v : ℕ → H) (n : ℕ) :
    (cyclicClosedSubmodule U (orthogonalCyclicResidual U v n)).toSubmodule ≤
      (partialCyclicSubmodule U v n).toSubmoduleᗮ := by
  let W : ClosedSubmodule ℂ H := ⟨(partialCyclicSubmodule U v n).toSubmoduleᗮ,
    Submodule.isClosed_orthogonal _⟩
  exact cyclicClosedSubmodule_le U _ W (partialCyclicSubmodule_invariant U v n).orthogonal
    (orthogonalCyclicResidual_mem_orthogonal U v n)

omit [IsMulCommutative G] in
theorem orthogonalCyclicResidual_orthogonal_to_other (v : ℕ → H) {n m : ℕ} (h : n ≠ m) :
    orthogonalCyclicResidual U v m ∈
      (cyclicClosedSubmodule U (orthogonalCyclicResidual U v n)).toSubmoduleᗮ := by
  have hBefore (i j : ℕ) (hij : i < j) :
      cyclicClosedSubmodule U (orthogonalCyclicResidual U v i) ≤ partialCyclicSubmodule U v j :=
    (show cyclicClosedSubmodule U (orthogonalCyclicResidual U v i) ≤ partialCyclicSubmodule U v (i + 1) by
      rw [partialCyclicSubmodule_succ]
      exact le_sup_right).trans (partialCyclicSubmodule_monotone U v (Nat.succ_le_of_lt hij))
  rcases lt_or_gt_of_ne h with hnm | hmn
  · exact Submodule.orthogonal_le (hBefore n m hnm) (orthogonalCyclicResidual_mem_orthogonal U v m)
  · rw [Submodule.mem_orthogonal]
    intro x hx
    have hx' := cyclicClosedSubmodule_residual_le_orthogonal U v n hx
    have hy := hBefore m n hmn (mem_cyclicClosedSubmodule U (orthogonalCyclicResidual U v m))
    rw [Submodule.mem_orthogonal] at hx'
    rw [← inner_conj_symm, hx' _ hy, map_zero]

/-- A geometrically weighted sum of the normalized orthogonal residuals has
each residual as a nonzero scalar multiple of one of its invariant projections. -/
theorem exists_vector_dominating_residual_measures (v : ℕ → H) :
    ∃ x : H, ∀ n, dualVectorSpectralMeasure U (orthogonalCyclicResidual U v n) ≪
      dualVectorSpectralMeasure U x := by
  let r := orthogonalCyclicResidual U v
  let c (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n / (‖r n‖ + 1)
  have hc (n : ℕ) : 0 < c n := by
    positivity
  let f (n : ℕ) : H := (c n : ℂ) • r n
  have hSumm : Summable f := by
    apply Summable.of_norm_bounded (g := fun n => (1 / 2 : ℝ) ^ n) (summable_geometric_of_lt_one
      (by norm_num) (by norm_num))
    intro n
    change ‖(c n : ℂ) • r n‖ ≤ _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (hc n).le]
    change ((1 / 2 : ℝ) ^ n / (‖r n‖ + 1)) * ‖r n‖ ≤ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) n]
  let x := ∑' n, f n
  refine ⟨x, fun n => ?_⟩
  let K := cyclicClosedSubmodule U (r n)
  let P := K.toSubmodule.starProjection
  have hP : P x = f n := by
    have hProj (m : ℕ) (hm : m ≠ n) : P (f m) = 0 := by
      change P ((c m : ℂ) • r m) = 0
      rw [map_smul]
      have hO := orthogonalCyclicResidual_orthogonal_to_other U v (Ne.symm hm)
      have hz : P (r m) = 0 := (Submodule.starProjection_apply_eq_zero_iff K.toSubmodule).mpr hO
      rw [hz, smul_zero]
    change P (∑' m, f m) = _
    rw [P.map_tsum hSumm, tsum_eq_single n hProj]
    apply Submodule.starProjection_eq_self_iff.mpr
    exact K.smul_mem _ (mem_cyclicClosedSubmodule U (r n))
  have hLe := dualVectorSpectralMeasure_starProjection_le U K (cyclicClosedSubmodule_invariant U _) x
  rw [show K.toSubmodule.starProjection x = f n from hP,
    show f n = (c n : ℂ) • r n from rfl, dualVectorSpectralMeasure_smul] at hLe
  intro A hA
  have h := hLe A
  rw [hA, smul_apply, smul_eq_mul] at h
  have hPos : 0 < ENNReal.ofReal (‖(c n : ℂ)‖ ^ 2) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (hc n).le]
    exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hc n))
  exact (mul_eq_zero.mp (le_antisymm h bot_le)).resolve_left hPos.ne'

/-- Existence of the dominating vector used to define a maximal spectral type
in §2.3. The dense sequence itself need not consist of cyclically orthogonal
vectors; their orthogonal residuals provide the required decomposition. -/
theorem exists_isMaximalSpectralVector [SeparableSpace H] :
    ∃ x : H, IsMaximalSpectralVector U x := by
  obtain ⟨v, hv⟩ := exists_dense_seq H
  obtain ⟨x, hx⟩ := exists_vector_dominating_residual_measures U v
  refine ⟨x, fun y => ?_⟩
  let D := spectralAbsoluteContinuousSubmodule U (dualVectorSpectralMeasure U x)
  have hD : IsClosed (D : Set H) := spectralAbsoluteContinuousSubmodule_isClosed U _
  let D' : ClosedSubmodule ℂ H := ⟨D, hD⟩
  have hInv : IsInvariantSubmodule U D := spectralAbsoluteContinuousSubmodule_invariant U _
  have hLe (n : ℕ) : partialCyclicSubmodule U v n ≤ D' := by
    induction n with
    | zero => exact bot_le
    | succ n ih =>
      rw [partialCyclicSubmodule_succ]
      exact sup_le ih (cyclicClosedSubmodule_le U _ D' hInv (hx n))
  have hRange : Set.range v ⊆ D := by
    rintro _ ⟨n, rfl⟩
    have hp : (partialCyclicSubmodule U v n).toSubmodule.starProjection (v n) ∈ D :=
      hLe n (Submodule.starProjection_apply_mem _ _)
    have hsum := D.add_mem hp (show orthogonalCyclicResidual U v n ∈ D from hx n)
    change (partialCyclicSubmodule U v n).toSubmodule.starProjection (v n) +
      (v n - (partialCyclicSubmodule U v n).toSubmodule.starProjection (v n)) ∈ D at hsum
    rwa [add_sub_cancel] at hsum
  have hy : y ∈ D := closure_minimal hRange hD (hv y)
  exact hy

end

end Mixing
end

/- Source module SixProblems.CompactRepresentationDensity. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure InnerProductSpace Mixing Module.End Set

variable {K H : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonzero strongly continuous unitary representation of a compact group
has a nonzero finite-dimensional invariant subspace. -/
theorem exists_finiteDimensional_invariantSubmodule_of_compact [Nontrivial H]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    ∃ W : Submodule ℂ H, W ≠ ⊥ ∧ FiniteDimensional ℂ W ∧ IsInvariantSubmodule ρ W := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let A := compactRepresentationAverage m ρ v
  have hA := isCompactOperator_compactRepresentationAverage m ρ v (hρ v)
  have hSym := isSymmetric_compactRepresentationAverage m ρ v (hρ v)
  have hne := compactRepresentationAverage_ne_zero m ρ hv (hρ v)
  have he : ¬ ∀ z, HasEigenvalue A.toLinearMap z → z = 0 :=
    fun h ↦ hne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hA hSym).mp h)
  push Not at he
  obtain ⟨z, hz, hzero⟩ := he
  let W := eigenspace A.toLinearMap z
  refine ⟨W, hasEigenvalue_iff.mp hz,
    ContinuousLinearMap.finite_dimensional_eigenspace hA z hzero, fun k w hw ↦ ?_⟩
  have hw' := mem_eigenspace_iff.mp hw
  apply mem_eigenspace_iff.mpr
  change A (ρ k w) = z • ρ k w
  rw [← compactRepresentationAverage_commutes m ρ v (hρ v), show A w = z • w from hw', map_smul]

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [TopologicalSpace K] [CompleteSpace H] in
/-- Irreducibility of an invariant submodule, expressed using submodules of
the ambient representation. -/
def IrreducibleInvariantSubmodule (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (W : Submodule ℂ H) : Prop :=
  W ≠ ⊥ ∧ IsInvariantSubmodule ρ W ∧
    ∀ L ≤ W, IsInvariantSubmodule ρ L → L = ⊥ ∨ L = W

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [TopologicalSpace K] [CompleteSpace H] in
theorem exists_irreducibleInvariantSubmodule_le (ρ : K →* (H ≃ₗᵢ[ℂ] H))
    (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hW : IsInvariantSubmodule ρ W) (hne : W ≠ ⊥) :
    ∃ L ≤ W, IrreducibleInvariantSubmodule ρ L := by
  classical
  let P (n : ℕ) := ∃ L ≤ W, L ≠ ⊥ ∧ IsInvariantSubmodule ρ L ∧ Module.finrank ℂ L = n
  have hp : ∃ n, P n := ⟨_, W, le_rfl, hne, hW, rfl⟩
  obtain ⟨L,hL,hLne,hLI,hfin⟩ := Nat.find_spec hp
  refine ⟨L,hL,hLne,hLI,fun V hV hVI ↦ ?_⟩
  let : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hL
  by_cases hb : V = ⊥
  · exact Or.inl hb
  · refine Or.inr (le_antisymm hV ?_)
    by_contra hVL
    have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hV hVL)
    exact Nat.find_min hp (hfin ▸ hlt) ⟨V,hV.trans hL,hb,hVI,rfl⟩

/-- Finite-dimensional invariant subspaces have dense linear span in a
strongly continuous unitary representation of a compact group. -/
theorem eq_top_of_contains_finiteInvariantSubmodules
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (P : Submodule ℂ H) (hP : IsClosed (P : Set H))
    (h : ∀ (V : Submodule ℂ H), FiniteDimensional ℂ V → IsInvariantSubmodule ρ V → V ≤ P) :
    P = ⊤ := by
  let A : Set H := {x | ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧ IsInvariantSubmodule ρ V ∧ x ∈ V}
  let Q := (Submodule.span ℂ A).topologicalClosure
  have hQP : Q ≤ P := Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro x ⟨V,hfin,hV,hx⟩; exact h V hfin hV hx)) hP
  have hQA (x : H) (hx : x ∈ A) : x ∈ Q :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hx)
  have hQinv : IsInvariantSubmodule ρ Q := by
    apply IsInvariantSubmodule.closure
    intro g x hmem
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨V,hfin,hV,hxV⟩ := hx
      exact Submodule.subset_span ⟨V,hfin,hV,hV g x hxV⟩
    | zero => simp
    | add x y _ _ hx hy => exact map_add (ρ g) x y ▸ Submodule.add_mem _ hx hy
    | smul c x _ hx => exact map_smul (ρ g) c x ▸ Submodule.smul_mem _ c hx
  have hQ : Q = ⊤ := by
    let : CompleteSpace Q := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let D := Qᗮ
    apply Submodule.orthogonal_eq_bot_iff.mp
    by_contra hD
    let : Nontrivial D := Submodule.nontrivial_iff_ne_bot.mpr hD
    let V := unitarySubmoduleAction ρ D hQinv.orthogonal
    have hV (x : D) : Continuous (fun k ↦ V k x) := (hρ x).subtype_mk _
    obtain ⟨W,hWne,hWfin,hWinv⟩ := exists_finiteDimensional_invariantSubmodule_of_compact m V hV
    obtain ⟨x,hx,hxne⟩ : ∃ x ∈ W, x ≠ 0 := by
      by_contra! he
      exact hWne ((Submodule.eq_bot_iff W).mpr he)
    let W' := W.map D.subtype
    have hWinv' : IsInvariantSubmodule ρ W' := by
      rintro k _ ⟨y,hy,rfl⟩
      exact ⟨V k y, hWinv k y hy, rfl⟩
    let : FiniteDimensional ℂ W := hWfin
    have he : (D.subtype.comp W.subtype).range = W' := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hWfin' : FiniteDimensional ℂ W' := he ▸ inferInstanceAs
      (FiniteDimensional ℂ (D.subtype.comp W.subtype).range)
    have hxQ : (x : H) ∈ Q := hQA x ⟨W',hWfin',hWinv',⟨x,hx,rfl⟩⟩
    exact hxne (Subtype.ext (inner_self_eq_zero.mp (x.property _ hxQ)))
  exact top_unique (hQ ▸ hQP)

omit [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [TopologicalSpace K] [CompleteSpace H] in
theorem finiteInvariantSubmodule_le_of_contains_irreducible (ρ : K →* (H ≃ₗᵢ[ℂ] H))
    (P : Submodule ℂ H)
    (hP : ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → IrreducibleInvariantSubmodule ρ W → W ≤ P)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] (hV : IsInvariantSubmodule ρ V) : V ≤ P := by
  suffices h : ∀ (n : ℕ) (L : Submodule ℂ H), FiniteDimensional ℂ L →
      Module.finrank ℂ L = n → IsInvariantSubmodule ρ L → L ≤ P from
    h _ V inferInstance rfl hV
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro L hfin hn hL
    let : FiniteDimensional ℂ L := hfin
    by_cases hL0 : L = ⊥
    · rw [hL0]; exact bot_le
    obtain ⟨W,hWL,hW⟩ := exists_irreducibleInvariantSubmodule_le ρ L hL hL0
    let : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWL
    let : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    let D := L ⊓ Wᗮ
    have hD : IsInvariantSubmodule ρ D := fun g x hx ↦
      ⟨hL g x hx.1, hW.2.1.orthogonal g x hx.2⟩
    have hDL : D < L := lt_of_le_of_ne inf_le_left fun he ↦ by
      apply hW.1
      apply (Submodule.eq_bot_iff W).mpr
      intro x hx
      have hx' : x ∈ D := he ▸ hWL hx
      exact inner_self_eq_zero.mp (hx'.2 x hx)
    have hd : D ≤ P := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hDL) D
      (Submodule.finiteDimensional_of_le hDL.le) rfl hD
    have hw : W ≤ P := hP W inferInstance hW
    intro x hx
    let w := W.starProjection x
    have hwW : w ∈ W := W.starProjection_apply_mem x
    have hdiff : x - w ∈ D :=
      ⟨L.sub_mem hx (hWL hwW), Submodule.sub_starProjection_mem_orthogonal x⟩
    have hsum := P.add_mem (hw hwW) (hd hdiff)
    rwa [add_sub_cancel] at hsum

/-- The finite-dimensional irreducible invariant subspaces of a strongly
continuous unitary representation of a compact group span a dense subspace. -/
theorem eq_top_of_contains_irreducibleInvariantSubmodules
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (P : Submodule ℂ H) (hP : IsClosed (P : Set H))
    (h : ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → IrreducibleInvariantSubmodule ρ W → W ≤ P) :
    P = ⊤ := by
  apply eq_top_of_contains_finiteInvariantSubmodules m ρ hρ P hP
  intro V hfin hV
  let : FiniteDimensional ℂ V := hfin
  exact finiteInvariantSubmodule_le_of_contains_irreducible ρ P h V hV

end SixProblems
end

/- Source module SixProblems.HaarRecognition. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Proposition 4.5: identifying Haar measure from matrix coefficients -/

noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Mixing
open scoped InnerProductSpace

universe u

variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] in
/-- An irreducible unitary representation has nonzero underlying space and has
only the zero and full invariant subspaces. -/
def UnitaryIrreducible (ρ : K →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  IrreducibleInvariantSubmodule ρ ⊤

omit [Group K] [IsTopologicalGroup K] in
private theorem integrable_of_continuous_on_compact {E : Type*} [NormedAddCommGroup E]
    (ν : Measure K) [IsFiniteMeasure ν] {g : K → E} (hg : Continuous g) : Integrable g ν :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

section HaarMean

variable [CompleteSpace H]

/-- Haar averaging in a nontrivial irreducible unitary representation is zero. -/
theorem integral_orbit_haar_eq_zero
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (hIrred : UnitaryIrreducible ρ) (hNontriv : ∃ k, ρ k ≠ 1) (y : H) :
    (∫ k, ρ k y ∂m) = 0 := by
  let V : Submodule ℂ H :=
    { carrier := {x | ∀ a : K, ρ a x = x}
      zero_mem' := by simp
      add_mem' := by
        intro x z hx hz a
        rw [map_add, hx a, hz a]
      smul_mem' := by
        intro c x hx a
        rw [map_smul, hx a] }
  have hVI : IsInvariantSubmodule ρ V := fun a x hx ↦ (hx a).symm ▸ hx
  have hV : V = ⊥ := by
    rcases hIrred.2.2 V le_top hVI with hz | ht
    · exact hz
    · obtain ⟨a, ha⟩ := hNontriv
      exfalso
      apply ha
      apply LinearIsometryEquiv.ext
      intro x
      have hx : x ∈ V := ht.symm ▸ Submodule.mem_top
      exact hx a
  apply (Submodule.mem_bot ℂ).mp
  rw [← hV]
  intro a
  have hi := integrable_of_continuous_on_compact m (hρ y)
  calc
    ρ a (∫ k, ρ k y ∂m) = ∫ k, ρ a (ρ k y) ∂m :=
      ((ρ a).toLinearIsometry.toContinuousLinearMap.integral_comp_comm hi).symm
    _ = ∫ k, ρ (a * k) y ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k ↦ by
        change ρ a (ρ k y) = ρ (a * k) y
        rw [map_mul]
        rfl
    _ = ∫ k, ρ k y ∂m := integral_mul_left_eq_self (fun k ↦ ρ k y) a

/-- The matrix coefficients of a nontrivial irreducible unitary representation
have zero Haar integral. -/
theorem integral_coefficient_haar_eq_zero
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x)
    (hIrred : UnitaryIrreducible ρ) (hNontriv : ∃ k, ρ k ≠ 1) (x y : H) :
    (∫ k, ⟪x, ρ k y⟫_ℂ ∂m) = 0 := by
  change (∫ k, innerSL ℂ x (ρ k y) ∂m) = 0
  rw [(innerSL ℂ x).integral_comp_comm (integrable_of_continuous_on_compact m (hρ y)),
    integral_orbit_haar_eq_zero m ρ hρ hIrred hNontriv y, map_zero]

end HaarMean

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] in
private theorem restrict_irreducible (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (W : Submodule ℂ H)
    (hW : IrreducibleInvariantSubmodule ρ W) :
    UnitaryIrreducible (unitarySubmoduleAction ρ W hW.2.1) := by
  let σ := unitarySubmoduleAction ρ W hW.2.1
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1
  refine ⟨top_ne_bot, fun _ _ _ ↦ Submodule.mem_top, fun L _ hL ↦ ?_⟩
  have hinj := Submodule.map_injective_of_injective W.subtype_injective
  have hLW : L.map W.subtype ≤ W := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hLI : IsInvariantSubmodule ρ (L.map W.subtype) := by
    intro a _ hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    exact ⟨σ a x, hL a x hx, rfl⟩
  rcases hW.2.2 _ hLW hLI with hz | ht
  · exact Or.inl (hinj (hz.trans (Submodule.map_bot _).symm))
  · right
    apply hinj
    simpa only [Submodule.map_top, Submodule.range_subtype] using ht

omit [IsTopologicalGroup K] in
/-- Integration of an orbit of a strongly continuous unitary representation
defines a bounded linear operator. -/
def integratedUnitary (ν : Measure K) [IsProbabilityMeasure ν]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ∫ k, ρ k x ∂ν
      map_add' := fun x y ↦ by
        simp only [map_add]
        exact integral_add (integrable_of_continuous_on_compact ν (hρ x))
          (integrable_of_continuous_on_compact ν (hρ y))
      map_smul' := fun c x ↦ by simp only [map_smul, integral_smul, RingHom.id_apply] }
    1 fun x ↦ by
    change ‖∫ k, ρ k x ∂ν‖ ≤ 1 * ‖x‖
    simpa only [LinearIsometryEquiv.norm_map, integral_const, probReal_univ, one_smul, one_mul]
      using norm_integral_le_integral_norm (μ := ν) (fun k ↦ ρ k x)

omit [IsTopologicalGroup K] in
theorem integratedUnitary_apply (ν : Measure K) [IsProbabilityMeasure ν]
    (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) (x : H) :
    integratedUnitary ν ρ hρ x = ∫ k, ρ k x ∂ν := rfl

/-- Vanishing of the nontrivial irreducible matrix coefficients of a measure. -/
def VanishesOnNontrivialIrreducibleCoefficients (ν : Measure K) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : K →* (E ≃ₗᵢ[ℂ] E)), (∀ x, Continuous fun k ↦ ρ k x) →
    UnitaryIrreducible ρ → (∃ k, ρ k ≠ 1) →
    ∀ x y, (∫ k, ⟪x, ρ k y⟫_ℂ ∂ν) = 0

private theorem integratedUnitary_eq_haar (m ν : Measure K)
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure] [IsProbabilityMeasure ν]
    (hν : VanishesOnNontrivialIrreducibleCoefficients ν)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (ρ : K →* (V ≃ₗᵢ[ℂ] V)) (hρ : ∀ x, Continuous fun k ↦ ρ k x) :
    integratedUnitary ν ρ hρ = integratedUnitary m ρ hρ := by
  let D := integratedUnitary ν ρ hρ - integratedUnitary m ρ hρ
  have hker : D.ker = ⊤ := by
    apply eq_top_of_contains_irreducibleInvariantSubmodules m ρ hρ D.ker D.isClosed_ker
    intro W hfin hW y hy
    let : FiniteDimensional ℂ W := hfin
    let : CompleteSpace W := FiniteDimensional.completeSpace ℂ W
    let σ := unitarySubmoduleAction ρ W hW.2.1
    have hσ (x : W) : Continuous fun k ↦ σ k x := (hρ x).subtype_mk _
    let z : W := ⟨y, hy⟩
    have hrestrict : ∀ (μ : Measure K) [IsProbabilityMeasure μ],
        W.subtypeL (∫ k, σ k z ∂μ) = integratedUnitary μ ρ hρ y := fun μ _ ↦
      (W.subtypeL.integral_comp_comm (integrable_of_continuous_on_compact μ (hσ z))).symm
    apply LinearMap.mem_ker.mpr
    change integratedUnitary ν ρ hρ y - integratedUnitary m ρ hρ y = 0
    apply sub_eq_zero.mpr
    rw [← hrestrict ν, ← hrestrict m]
    congr 1
    by_cases hnon : ∃ k, σ k ≠ 1
    · have hσI := restrict_irreducible ρ W hW
      rw [integral_orbit_haar_eq_zero m σ hσ hσI hnon z]
      apply ext_inner_left ℂ
      intro x
      change innerSL ℂ x (∫ k, σ k z ∂ν) = ⟪x, 0⟫_ℂ
      rw [← (innerSL ℂ x).integral_comp_comm (integrable_of_continuous_on_compact ν (hσ z)), inner_zero_right]
      exact hν W σ hσ hσI hnon x z
    · push Not at hnon
      have hz (k : K) : σ k z = z := by rw [hnon k]; rfl
      simp only [hz, integral_const, probReal_univ, one_smul]
  ext x
  have hx : x ∈ D.ker := hker.symm ▸ Submodule.mem_top
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp hx)

variable [SecondCountableTopology K] [T2Space K]

/-- **Proposition 4.5.** A probability on a compact metrizable group equals its
normalized Haar measure iff the indicated matrix coefficients have zero integral. -/
theorem proposition4_5 (m ν : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    [m.IsOpenPosMeasure] [IsProbabilityMeasure ν] :
    ν = m ↔ VanishesOnNontrivialIrreducibleCoefficients ν := by
  constructor
  · intro he
    subst ν
    intro E _ _ _ ρ hρ hIrred hNontriv x y
    let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
    exact integral_coefficient_haar_eq_zero m ρ hρ hIrred hNontriv x y
  · intro hν
    let hInv (k : K) : MeasurePreserving (fun x : K ↦ k • x) m m :=
      measurePreserving_mul_left m k
    let ρ := inverseActionKoopmanRep m hInv
    have hρ := continuous_inverseActionKoopmanRep m hInv
    have hA := integratedUnitary_eq_haar m ν hν ρ hρ
    have hComplex (f : C(K, ℂ)) : (∫ k, f k⁻¹ ∂ν) = ∫ k, f k⁻¹ ∂m := by
      let F (k : K) : C(K, ℂ) := ⟨fun x ↦ f (k⁻¹ * x),
        f.continuous.comp (continuous_const.mul continuous_id)⟩
      have hF : Continuous F := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact f.continuous.comp (continuous_fst.inv.mul continuous_snd)
      let J : C(K, ℂ) →L[ℂ] Lp ℂ 2 m := ContinuousMap.toLp 2 m ℂ
      have hJ (k : K) : J (F k) = ρ k (J f) := by
        apply Lp.ext
        refine (ContinuousMap.coeFn_toLp m (F k)).trans ?_
        refine Filter.EventuallyEq.trans ?_ (ae_inverseActionKoopmanRep_apply m hInv k (J f)).symm
        exact ((hInv k⁻¹).quasiMeasurePreserving.ae_eq_comp (ContinuousMap.coeFn_toLp m f)).symm
      have hIntegrals : (∫ k, F k ∂ν) = ∫ k, F k ∂m := by
        apply ContinuousMap.toLp_injective (𝕜 := ℂ) (p := 2) m
        rw [← J.integral_comp_comm (integrable_of_continuous_on_compact ν hF),
          ← J.integral_comp_comm (integrable_of_continuous_on_compact m hF)]
        simp_rw [hJ]
        exact DFunLike.congr_fun hA (J f)
      let ev := ContinuousMap.evalCLM ℂ (1 : K) (M := ℂ)
      simpa only [ev, ContinuousMap.evalCLM_apply, F, ContinuousMap.coe_mk, mul_one] using
        calc
          (∫ k, ev (F k) ∂ν) = ev (∫ k, F k ∂ν) :=
            ev.integral_comp_comm (integrable_of_continuous_on_compact ν hF)
          _ = ev (∫ k, F k ∂m) := congrArg ev hIntegrals
          _ = ∫ k, ev (F k) ∂m :=
            (ev.integral_comp_comm (integrable_of_continuous_on_compact m hF)).symm
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    let g : C(K, ℂ) := ⟨fun k ↦ (f k⁻¹ : ℂ), Complex.continuous_ofReal.comp (f.continuous.comp continuous_inv)⟩
    have hg := hComplex g
    have he : (∫ k, (f k : ℂ) ∂ν) = ∫ k, (f k : ℂ) ∂m := by
      simpa only [g, ContinuousMap.coe_mk, inv_inv] using hg
    exact Complex.ofReal_injective (by simpa only [integral_complex_ofReal] using he)

/-- **Proposition 4.5**, with the representation space written as `ℂᵈ` as in
the paper. The converse transfers the test through an orthonormal basis. -/
theorem proposition4_5_euclidean (m ν : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    [m.IsOpenPosMeasure] [IsProbabilityMeasure ν] :
    ν = m ↔ ∀ (d : ℕ) (ρ : K →* (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d))),
      (∀ x, Continuous fun k ↦ ρ k x) → UnitaryIrreducible ρ → (∃ k, ρ k ≠ 1) →
      ∀ x y, (∫ k, ⟪x, ρ k y⟫_ℂ ∂ν) = 0 := by
  constructor
  · intro he d ρ hρ hI hN x y
    subst ν
    exact integral_coefficient_haar_eq_zero m ρ hρ hI hN x y
  · intro hν
    apply (proposition4_5 m ν).mpr
    intro E _ _ _ ρ hρ hI hN x y
    let d := Module.finrank ℂ E
    let F := EuclideanSpace ℂ (Fin d)
    let e : E ≃ₗᵢ[ℂ] F := (stdOrthonormalBasis ℂ E).repr
    let σ : K →* (F ≃ₗᵢ[ℂ] F) :=
      { toFun := fun k ↦ (e.symm.trans (ρ k)).trans e
        map_one' := by
          apply LinearIsometryEquiv.ext
          intro v
          change e (ρ 1 (e.symm v)) = v
          rw [map_one]
          exact e.apply_symm_apply v
        map_mul' := by
          intro a b
          apply LinearIsometryEquiv.ext
          intro v
          change e (ρ (a * b) (e.symm v)) = e (ρ a (e.symm (e (ρ b (e.symm v)))))
          rw [map_mul, e.symm_apply_apply]
          rfl }
    have he (k : K) (v : E) : σ k (e v) = e (ρ k v) := by
      change e (ρ k (e.symm (e v))) = e (ρ k v)
      rw [e.symm_apply_apply]
    have hσ (v : F) : Continuous fun k ↦ σ k v := e.continuous.comp (hρ (e.symm v))
    have hσI : UnitaryIrreducible σ := by
      let : Nontrivial (⊤ : Submodule ℂ E) := Submodule.nontrivial_iff_ne_bot.mpr hI.1
      let : Nontrivial E := (⊤ : Submodule ℂ E).subtype_injective.nontrivial
      let : Nontrivial F := e.injective.nontrivial
      refine ⟨top_ne_bot, fun _ _ _ ↦ Submodule.mem_top, fun L _ hL ↦ ?_⟩
      let eL := e.toLinearEquiv.toLinearMap
      have hLI : IsInvariantSubmodule ρ (L.comap eL) := by
        intro a v hv
        change e v ∈ L at hv
        change e (ρ a v) ∈ L
        rw [← he]
        exact hL a _ hv
      have hinj := Submodule.comap_injective_of_surjective (f := eL) e.surjective
      rcases hI.2.2 _ le_top hLI with hz | ht
      · refine Or.inl (hinj ?_)
        rwa [Submodule.comap_bot, LinearMap.ker_eq_bot.mpr e.injective]
      · refine Or.inr (hinj ?_)
        rwa [Submodule.comap_top]
    have hσN : ∃ k, σ k ≠ 1 := by
      obtain ⟨k,hk⟩ := hN
      refine ⟨k, fun htriv ↦ hk ?_⟩
      apply LinearIsometryEquiv.ext
      intro v
      apply e.injective
      rw [← he, htriv]
      rfl
    have h := hν d σ hσ hσI hσN (e x) (e y)
    simpa only [he, e.inner_map_map] using h

end SixProblems
end

/- Source module SixProblems.CompactVdC. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open MeasureTheory MeasureTheory.Measure Mixing
open scoped InnerProductSpace

theorem integral_eq_zero_of_isVdC_vector {G X E : Type} [Group G] [MeasurableSpace X]
    [StandardBorelSpace X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {R : Set G} (hR : IsVdC R) (S : System G X) (V : X → E) (hV : StronglyMeasurable V)
    (hB : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (hZero : ∀ r ∈ R, ∫ x, ⟪V x,V (S.act r x)⟫_ℂ ∂S.measure = 0) :
    (∫ x, V x ∂S.measure) = 0 := by
  let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
  let e := (stdOrthonormalBasis ℂ E).repr
  have hZ := lemma4_2 hR S (fun x ↦ e (V x)) (e.continuous.comp_stronglyMeasurable hV).measurable
    (by obtain ⟨C,hC⟩ := hB; exact ⟨C,fun x ↦ (e.norm_map _).trans_le (hC x)⟩)
    (by intro r hr; simp_rw [e.inner_map_map]; exact hZero r hr)
  obtain ⟨C,hC⟩ := hB
  have hi := Integrable.of_bound (μ := S.measure) hV.aestronglyMeasurable C (ae_of_all _ hC)
  change ∫ x, e.toLinearIsometry.toContinuousLinearMap (V x) ∂S.measure = _ at hZ
  rw [e.toLinearIsometry.toContinuousLinearMap.integral_comp_comm hi] at hZ
  change e (∫ x, V x ∂S.measure) = 0 at hZ
  apply e.injective
  simpa only [map_zero] using hZ

variable {G K : Type} [Group G] [Group K] [TopologicalSpace K] [T2Space K]
  [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

/-- The forward implication of Theorem 4.6, using the Hilbert-space observable
obtained by applying a unitary representation to the inverse value. -/
theorem measureTheoreticVdC_of_isVdC {R : Set G} (hR : IsVdC R) (m : Measure K)
    [IsProbabilityMeasure m] [IsMulLeftInvariant m] [m.IsOpenPosMeasure] [IsInvInvariant m] :
    IsMeasureTheoreticVdC R m := by
  intro X _ _ S F hF hDiff
  let F' (x : X) := (F x)⁻¹
  have hF' : Measurable F' := hF.inv
  let ν := S.measure.map F'
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hF'.aemeasurable).mpr inferInstance
  have hν : ν = m := (proposition4_5 m ν).2 (by
    intro E _ _ _ ρ hρ hI hN ξ η
    let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
    let V (x : X) := ρ (F' x) η
    have hV : StronglyMeasurable V := (hρ η).stronglyMeasurable.comp_measurable hF'
    have hB (x : X) : ‖V x‖ ≤ ‖η‖ := (LinearIsometryEquiv.norm_map _ _).le
    have hW : ∫ x, V x ∂S.measure = 0 := by
      apply integral_eq_zero_of_isVdC_vector hR S V hV ⟨_,hB⟩
      intro g hg
      let d (x : X) := F (S.act g x) * (F x)⁻¹
      have hd : Measurable d := (hF.comp (S.preserves g).measurable).mul hF.inv
      let c (k : K) := ⟪η,ρ k η⟫_ℂ
      have hc : Continuous c := continuous_const.inner (hρ η)
      have he (x : X) : ⟪V x,V (S.act g x)⟫_ℂ = c (d x)⁻¹ := by
        rw [← (ρ (F x)).inner_map_map]
        change ⟪(ρ (F x) * ρ (F x)⁻¹) η,(ρ (F x) * ρ (F (S.act g x))⁻¹) η⟫_ℂ = _
        rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
        simp [c, d, mul_inv_rev]
      have hInv := measurePreserving_inv m
      have hm : S.measure.map (Inv.inv ∘ d) = m := by
        rw [← Measure.map_map measurable_inv hd, hDiff g hg, hInv.map_eq]
      simp_rw [he]
      change (∫ x, c ((Inv.inv ∘ d) x) ∂S.measure) = 0
      rw [← integral_map (measurable_inv.comp hd).aemeasurable hc.aestronglyMeasurable, hm]
      exact integral_coefficient_haar_eq_zero m ρ hρ hI hN η η
    change ∫ k, ⟪ξ,ρ k η⟫_ℂ ∂ν = 0
    rw [integral_map hF'.aemeasurable (continuous_const.inner (hρ η)).aestronglyMeasurable]
    have hi := Integrable.of_bound (μ := S.measure) hV.aestronglyMeasurable ‖η‖ (ae_of_all _ hB)
    change ∫ x, innerSL ℂ ξ (V x) ∂S.measure = 0
    rw [(innerSL ℂ ξ).integral_comp_comm hi, hW, map_zero])
  have he : Inv.inv ∘ F' = F := by funext x; exact inv_inv _
  rw [← he, ← Measure.map_map measurable_inv hF', show S.measure.map F' = ν from rfl,
    hν, (measurePreserving_inv m).map_eq]

/-- Theorem 4.6 at the normalized Haar measure of a nontrivial compact
metrizable group. -/
theorem theorem4_6 [Countable G] [StandardBorelSpace K] [Nontrivial K] (R : Set G)
    (m : Measure K) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    IsVdC R ↔ IsMeasureTheoreticVdC R m := by
  let : IsMulRightInvariant m := ⟨fun k ↦ by
    let : IsProbabilityMeasure (m.map (· * k)) :=
      (Measure.isProbabilityMeasure_map_iff (continuous_mul_const k).measurable.aemeasurable).mpr inferInstance
    exact isHaarMeasure_eq_of_isProbabilityMeasure (m.map (· * k)) m⟩
  let : IsInvInvariant m := ⟨by
    let : IsProbabilityMeasure m.inv :=
      (Measure.isProbabilityMeasure_map_iff continuous_inv.measurable.aemeasurable).mpr inferInstance
    let : m.inv.IsHaarMeasure := isHaarMeasure_of_isCompact_nonempty_interior m.inv
      Set.univ isCompact_univ (by simp) (by simp) (by simp)
    exact isHaarMeasure_eq_of_isProbabilityMeasure m.inv m⟩
  constructor
  · intro h
    exact measureTheoreticVdC_of_isVdC h m
  · intro h
    exact isVdC_of_measureTheoreticVdC m h

end SixProblems
end

/- Source module SixProblems.CorrespondenceAverages. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter MeasureTheory
open scoped Topology symmDiff ENNReal

/-- An average over a finite set, with the conventional value zero at the empty set. -/
def finiteAverage {ι E : Type*} [AddCommMonoid E] [Module ℝ E] (A : Finset ι) (f : ι → E) : E :=
  (A.card : ℝ)⁻¹ • ∑ i ∈ A, f i

/-- A left Følner sequence of nonempty finite subsets of a group. -/
structure LeftFolnerSequence (G : Type*) [Group G] [DecidableEq G] where
  blocks : ℕ → Finset G
  nonempty : ∀ n, (blocks n).Nonempty
  tendsto_defect (a : G) :
    Tendsto (fun n ↦ ((blocks n).image (a * ·) ∆ blocks n).card / ((blocks n).card : ℝ))
      atTop (𝓝 0)

private theorem norm_sum_sub_sum_bound {ι : Type*} [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] (A B : Finset ι) (f : ι → E)
    {C : ℝ} (hC : ∀ i, ‖f i‖ ≤ C) :
    ‖(∑ i ∈ A, f i) - ∑ i ∈ B, f i‖ ≤ ((A ∆ B).card : ℝ) * C := by
  have hA := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : A ∩ B ⊆ A)
  have hB := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : A ∩ B ⊆ B)
  have hdiffA : A \ (A ∩ B) = A \ B := by ext; simp
  have hdiffB : B \ (A ∩ B) = B \ A := by ext; simp
  rw [hdiffA] at hA
  rw [hdiffB] at hB
  rw [← hA, ← hB, add_sub_add_right_eq_sub]
  calc
    _ ≤ ‖∑ i ∈ A \ B, f i‖ + ‖∑ i ∈ B \ A, f i‖ := norm_sub_le _ _
    _ ≤ (∑ i ∈ A \ B, C) + ∑ i ∈ B \ A, C :=
      add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hC i))
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hC i))
    _ = _ := by
      rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
      · simp [add_mul]
      · rw [Finset.disjoint_left]
        intro i hi hj
        exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

/-- Left shifts do not affect a limit of bounded Følner averages. -/
theorem LeftFolnerSequence.tendsto_average_sub_translate {G : Type*} [Group G] [DecidableEq G]
    (F : LeftFolnerSequence G) (a : G) (f : G → ℝ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C) :
    Tendsto (fun n ↦ finiteAverage (F.blocks n) (fun g ↦ f (a * g)) -
      finiteAverage (F.blocks n) f) atTop (𝓝 0) := by
  have h := (F.tendsto_defect a).mul_const C
  rw [zero_mul] at h
  apply squeeze_zero_norm _ h
  intro n
  let A := F.blocks n
  have hinj : Function.Injective (a * ·) := fun _ _ h ↦ mul_left_cancel h
  have hs := Finset.sum_image (f := f) (s := A) (g := (a * ·))
    (fun _ _ _ _ he ↦ hinj he)
  simp only [finiteAverage, smul_eq_mul, ← mul_sub, norm_mul]
  rw [← hs, Real.norm_of_nonneg (by positivity)]
  convert mul_le_mul_of_nonneg_left (norm_sum_sub_sum_bound (A.image (a * ·)) A f hC)
    (inv_nonneg.mpr (Nat.cast_nonneg A.card)) using 1
  rw [div_eq_mul_inv]
  ring

/-- The probability law of a map on a uniformly distributed finite index set. -/
def finiteEmpiricalLaw {ι E : Type*} [MeasurableSpace E] (A : Finset ι) (hA : A.Nonempty)
    (f : ι → E) : ProbabilityMeasure E :=
  ⟨(A.card : ℝ≥0∞)⁻¹ • ∑ i ∈ A, Measure.dirac (f i), ⟨by
    simp [ENNReal.inv_mul_cancel, Finset.Nonempty.card_ne_zero hA]⟩⟩

theorem integral_finiteEmpiricalLaw {ι E B : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] (A : Finset ι) (hA : A.Nonempty) (f : ι → E) (k : E → B) :
    ∫ x, k x ∂(finiteEmpiricalLaw A hA f : Measure E) = finiteAverage A (k ∘ f) := by
  change ∫ x, k x ∂((A.card : ℝ≥0∞)⁻¹ • ∑ i ∈ A, Measure.dirac (f i)) = _
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [finiteAverage]
  · exact fun i _ ↦ integrable_dirac (f := k) (by simp)

end SixProblems
end

/- Source module SixProblems.CorrespondenceTiling. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter
open scoped Topology symmDiff

variable {G : Type*} [Group G] [DecidableEq G]

/-- The points of `A` that leave `A` after at least one left shift from `D`. -/
def leftBoundary (D A : Finset G) : Finset G := by
  classical
  exact A.filter fun g ↦ ∃ d ∈ D, d * g ∉ A

theorem mem_leftBoundary {D A : Finset G} {g : G} :
    g ∈ leftBoundary D A ↔ g ∈ A ∧ ∃ d ∈ D, d * g ∉ A := by
  simp [leftBoundary]

private theorem leftBoundary_subset_union (D A : Finset G) :
    leftBoundary D A ⊆ D.biUnion (fun d ↦ (A.image (d⁻¹ * ·)) ∆ A) := by
  intro g hg
  obtain ⟨hgA, d, hd, hdg⟩ := mem_leftBoundary.mp hg
  refine Finset.mem_biUnion.mpr ⟨d, hd, Finset.symmDiff_subset_sdiff' ?_⟩
  refine Finset.mem_sdiff.mpr ⟨hgA, fun hm ↦ ?_⟩
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hm
  apply hdg
  have : z = d * g := by rw [← he, mul_inv_cancel_left]
  simpa [← this] using hz

/-- The fraction of points in the boundary for any fixed finite set of shifts tends to zero. -/
theorem LeftFolnerSequence.tendsto_leftBoundary (F : LeftFolnerSequence G) (D : Finset G) :
    Tendsto (fun n ↦ ((leftBoundary D (F.blocks n)).card : ℝ) / (F.blocks n).card)
      atTop (𝓝 0) := by
  let defect (d : G) (n : ℕ) :=
    ((F.blocks n).image (d⁻¹ * ·) ∆ F.blocks n).card / ((F.blocks n).card : ℝ)
  have hsum : Tendsto (fun n ↦ ∑ d ∈ D, defect d n) atTop (𝓝 0) := by
    induction D using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using tendsto_const_nhds
    | insert d D hd hD =>
      simp only [Finset.sum_insert hd]
      simpa only [zero_add] using (F.tendsto_defect d⁻¹).add hD
  apply squeeze_zero (fun _ ↦ by positivity) _ hsum
  intro n
  rw [← Finset.sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.card_le_card (leftBoundary_subset_union D (F.blocks n))).trans
    Finset.card_biUnion_le

/-- An arbitrary Følner sequence in an infinite group eventually has at least any given size. -/
theorem LeftFolnerSequence.tendsto_card [Infinite G] (F : LeftFolnerSequence G) :
    Tendsto (fun n ↦ (F.blocks n).card) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  obtain ⟨D, hD⟩ := Infinite.exists_subset_card_eq G k
  filter_upwards [(F.tendsto_leftBoundary D).eventually_lt_const (zero_lt_one' ℝ)] with n hn
  let A := F.blocks n
  have hA : (0 : ℝ) < A.card := by exact_mod_cast (F.nonempty n).card_pos
  have hlt : (leftBoundary D A).card < A.card := by
    have h := (div_lt_iff₀ hA).mp hn
    rw [one_mul] at h
    exact_mod_cast h
  have hNot : ¬ A ⊆ leftBoundary D A := fun h ↦ (Finset.card_le_card h).not_gt hlt
  obtain ⟨g, hg, hgB⟩ := Finset.not_subset.mp hNot
  have hgD (d : G) (hd : d ∈ D) : d * g ∈ A := by
    by_contra hdg
    exact hgB (mem_leftBoundary.mpr ⟨hg, d, hd, hdg⟩)
  have hsub : D.image (· * g) ⊆ A := Finset.image_subset_iff.mpr hgD
  have hinj : Function.Injective ((· * g) : G → G) := fun _ _ h ↦ mul_right_cancel h
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective D hinj, hD] at hcard

/-- A partition of the group into finite cells, with a uniform finite bound on the left
displacements between elements of each cell. A tiling with finitely many right-translate
shapes has this property. -/
structure BoundedTilePartition (G : Type*) [Group G] [DecidableEq G] where
  cell : G → Finset G
  mem_cell (g : G) : g ∈ cell g
  cell_eq {g h : G} (hh : h ∈ cell g) : cell h = cell g
  displacements : Finset G
  mem_displacements {g h : G} (hh : h ∈ cell g) : h * g⁻¹ ∈ displacements

/-- Boundary points whose partition cell is not contained in the block. -/
def tileBoundary (T : G → Finset G) (A : Finset G) : Finset G :=
  A.filter fun g ↦ ¬ T g ⊆ A

omit [Group G] [DecidableEq G] in
/-- The proportion of a block that belongs to a specified set. -/
def blockProportion (A : Finset G) (E : Set G) : ℝ := by
  classical
  exact ((A.filter (· ∈ E)).card : ℝ) / A.card

private theorem coherentTilePartitions_monotone (P : ℕ → BoundedTilePartition G)
    (hP : ∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g) (g : G) :
    Monotone (fun k ↦ (P k).cell g) := monotone_nat_of_le_succ fun k ↦ hP k g

/-- From congruent tilings and a prescribed Følner sequence, choose a single partition
using finitely many cells from each level, such that almost every point of a late block
belongs to a cell entirely inside the block. This is the diagonal partition step in the
inverse correspondence argument. -/
theorem exists_mixedTilePartition [Countable G] [Infinite G] (F : LeftFolnerSequence G)
    (P : ℕ → BoundedTilePartition G)
    (hP : ∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g)
    (bad : ℕ → Set G) (δs : ℕ → ℝ) (hδs : ∀ k, 0 ≤ δs k) (hSum : Summable δs)
    (hSparse : ∀ k, ∀ᶠ n in atTop, blockProportion (F.blocks n) (bad k) ≤ δs k) :
    ∃ level : G → ℕ,
      (∀ g h, h ∈ (P (level g)).cell g → level h = level g) ∧
      (∀ k, {g | level g ≤ k}.Finite) ∧
      Tendsto (fun n ↦ ((tileBoundary (fun g ↦ (P (level g)).cell g) (F.blocks n)).card : ℝ) /
        (F.blocks n).card) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ blockProportion (F.blocks n) {g | g ∈ bad (level g)}) atTop (𝓝 0) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let moves (k : ℕ) := (Finset.range (k + 1)).biUnion (fun j ↦ (P j).displacements)
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hThreshold (k : ℕ) : ∃ N, ∀ n ≥ N,
      ((leftBoundary (moves (k + 1)) (F.blocks n)).card : ℝ) / (F.blocks n).card < ε k ∧
      ∀ j ∈ Finset.range (k+2), blockProportion (F.blocks n) (bad j) ≤ δs j := by
    apply eventually_atTop.1
    exact ((F.tendsto_leftBoundary (moves (k+1))).eventually_lt_const (hε k)).and
      ((eventually_all_finset (Finset.range (k+2))).mpr (fun j _ ↦ hSparse j))
  choose N hN using hThreshold
  let cutoff : ℕ → ℕ := Nat.rec (N 0) (fun k c ↦ max (c + 1) (N (k + 1)))
  have hCut (k : ℕ) : N k ≤ cutoff k := by cases k <;> simp [cutoff]
  have hCutMono : Monotone cutoff := monotone_nat_of_le_succ fun k ↦ by
    show cutoff k ≤ max (cutoff k + 1) (N (k + 1))
    exact (Nat.le_succ _).trans (le_max_left _ _)
  have hCutLarge (k : ℕ) : k ≤ cutoff k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k hk =>
      show k + 1 ≤ max (cutoff k + 1) (N (k + 1))
      exact (Nat.succ_le_succ hk).trans (le_max_left _ _)
  let seeds (k : ℕ) := ((Finset.range (cutoff k + 1)).biUnion F.blocks) ∪
    ((Finset.range (k + 1)).image e)
  let D (k : ℕ) := (seeds k).biUnion (P (k + 1)).cell
  have hSeeds {j k : ℕ} (hjk : j ≤ k) : seeds j ⊆ seeds k := by
    apply Finset.union_subset_union
    · exact Finset.biUnion_subset_biUnion_of_subset_left _
        (Finset.range_mono (Nat.succ_le_succ (hCutMono hjk)))
    · exact Finset.image_subset_image (Finset.range_mono (Nat.succ_le_succ hjk))
  have hDMono : Monotone D := by
    intro j k hjk g hg
    obtain ⟨z, hz, hgz⟩ := Finset.mem_biUnion.mp hg
    exact Finset.mem_biUnion.mpr ⟨z, hSeeds hjk hz,
      coherentTilePartitions_monotone P hP z (Nat.succ_le_succ hjk) hgz⟩
  have hSeedD (k : ℕ) : seeds k ⊆ D k := fun g hg ↦
    Finset.mem_biUnion.mpr ⟨g, hg, (P (k + 1)).mem_cell g⟩
  have hDClose {k : ℕ} {g h : G} (hg : g ∈ D k) (hh : h ∈ (P (k + 1)).cell g) : h ∈ D k := by
    obtain ⟨z, hz, hgz⟩ := Finset.mem_biUnion.mp hg
    exact Finset.mem_biUnion.mpr ⟨z, hz, (P (k + 1)).cell_eq hgz ▸ hh⟩
  have hBlocksIn {n k : ℕ} (hn : n ≤ cutoff k) : F.blocks n ⊆ D k := fun g hg ↦
    hSeedD k (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨n,
      Finset.mem_range.mpr (Nat.lt_succ_of_le hn), hg⟩))
  have hExhaust (g : G) : ∃ k, g ∈ D k := by
    obtain ⟨k, rfl⟩ := he g
    exact ⟨k, hSeedD k (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩))⟩
  let level (g : G) := Nat.find (hExhaust g)
  have hLevelMem (g : G) : g ∈ D (level g) := Nat.find_spec (hExhaust g)
  have hLevelLe {g : G} {k : ℕ} (h : g ∈ D k) : level g ≤ k := Nat.find_min' (hExhaust g) h
  have hSameLevel (g h : G) (hh : h ∈ (P (level g)).cell g) : level h = level g := by
    have hle : level h ≤ level g :=
      hLevelLe (hDClose (hLevelMem g) (hP (level g) g hh))
    apply Nat.le_antisymm hle
    by_contra hng
    have hlt : level h < level g := Nat.lt_of_not_ge hng
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hlt)
    rw [hk] at hh hlt
    have hg : g ∈ (P (k + 1)).cell h := by
      rw [(P (k + 1)).cell_eq hh]
      exact (P (k + 1)).mem_cell g
    have hhD : h ∈ D k := hDMono (Nat.le_of_lt_succ hlt) (hLevelMem h)
    have hgLe := hLevelLe (hDClose hhD hg)
    omega
  let T (g : G) := (P (level g)).cell g
  have hBound {n k : ℕ} (hn : n ≤ cutoff k) :
      tileBoundary T (F.blocks n) ⊆ leftBoundary (moves k) (F.blocks n) := by
    intro g hg
    obtain ⟨hg, hNot⟩ := Finset.mem_filter.mp hg
    obtain ⟨h, hh, hhNot⟩ := Finset.not_subset.mp hNot
    have hk : level g ≤ k := hLevelLe (hBlocksIn hn hg)
    have hMove := (P (level g)).mem_displacements hh
    exact mem_leftBoundary.mpr ⟨hg, h * g⁻¹, Finset.mem_biUnion.mpr
      ⟨level g, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hMove⟩, by simpa using hhNot⟩
  have hIndex {J n : ℕ} (hn : cutoff J < n) :
      ∃ j, J ≤ j ∧ n ≤ cutoff (j+1) ∧ cutoff j < n := by
    have hex : ∃ k, n ≤ cutoff k := ⟨n, hCutLarge n⟩
    let dec : DecidablePred (fun a ↦ n ≤ cutoff a) := fun a ↦ Nat.decLe n (cutoff a)
    let k := @Nat.find _ dec hex
    have hk : n ≤ cutoff k := @Nat.find_spec _ dec hex
    have hJk : J < k := Nat.lt_of_not_ge (fun h ↦ hn.not_ge (hk.trans (hCutMono h)))
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hJk)
    have hnj : cutoff j < n := Nat.lt_of_not_ge
      (@Nat.find_min _ dec hex j (by omega : j < k))
    exact ⟨j,by omega,by rw [show j+1 = k from hj.symm]; exact hk,hnj⟩
  refine ⟨level, hSameLevel, fun k ↦ (D k).finite_toSet.subset ?_, ?_, ?_⟩
  · exact fun g hg ↦ hDMono hg (hLevelMem g)
  · apply Metric.tendsto_nhds.2
    intro δ hδ
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hεlim.eventually_lt_const hδ)
    filter_upwards [eventually_ge_atTop (cutoff J + 1)] with n hn
    obtain ⟨j,hj,hk,hnj⟩ := hIndex (by omega : cutoff J < n)
    have hSmall := (hN j n ((hCut j).trans hnj.le)).1
    have hCompare : ((tileBoundary T (F.blocks n)).card : ℝ) / (F.blocks n).card ≤
        ((leftBoundary (moves (j + 1)) (F.blocks n)).card : ℝ) / (F.blocks n).card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (hBound hk)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    exact hCompare.trans_lt (hSmall.trans (hJ j hj))
  · apply Metric.tendsto_nhds.2
    intro r hr
    obtain ⟨J,hJ⟩ := ((_root_.tendsto_sum_nat_add δs).eventually_lt_const (half_pos hr)).exists
    have hSize : Tendsto (fun n ↦ ((F.blocks n).card : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp F.tendsto_card
    have hSmallD : Tendsto (fun n ↦ ((D J).card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := by
      simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using
        (tendsto_inv_atTop_zero.comp hSize).const_mul ((D J).card : ℝ)
    filter_upwards [eventually_ge_atTop (cutoff J+1), hSmallD.eventually_lt_const (half_pos hr)] with n hn hnD
    obtain ⟨j,hj,hk,hnj⟩ := hIndex (by omega : cutoff J < n)
    let A := F.blocks n
    let I := Finset.range (j+2-J)
    let B (l : ℕ) := A.filter (· ∈ bad (l+J))
    have hSub : A.filter (fun g ↦ g ∈ bad (level g)) ⊆ D J ∪ I.biUnion B := by
      intro g hg
      obtain ⟨hgn,hgb⟩ := Finset.mem_filter.mp hg
      by_cases hle : level g ≤ J
      · exact Finset.mem_union_left _ (hDMono hle (hLevelMem g))
      · have hUpper := hLevelLe (hBlocksIn (k := j+1) hk hgn)
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨level g-J,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨hgn,?_⟩⟩)
        simpa only [Nat.sub_add_cancel (by omega : J ≤ level g)] using hgb
    have hSumI : (∑ l ∈ I, ((B l).card : ℝ) / A.card) ≤ ∑ l ∈ I, δs (l+J) := by
      apply Finset.sum_le_sum
      intro l hl
      have hL : l+J ∈ Finset.range (j+2) := Finset.mem_range.mpr (by
        have := Finset.mem_range.mp hl
        omega)
      exact (hN j n ((hCut j).trans hnj.le)).2 _ hL
    have hTail : (∑ l ∈ I, δs (l+J)) ≤ ∑' l, δs (l+J) :=
      ((summable_nat_add_iff J).mpr hSum).sum_le_tsum I (fun l _ ↦ hδs (l+J))
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by unfold blockProportion; positivity),blockProportion]
    change (((A.filter (fun g ↦ g ∈ bad (level g))).card : ℝ) / A.card) < r
    calc
      _ ≤ (((D J).card : ℝ) + ∑ l ∈ I, ((B l).card : ℝ)) / A.card := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (Finset.card_le_card hSub).trans
          (Finset.card_union_le _ _ |>.trans (Nat.add_le_add_left Finset.card_biUnion_le _))
      _ = _ := by rw [add_div, Finset.sum_div]
      _ < r := by
        change ((D J).card : ℝ) / A.card + ∑ l ∈ I, ((B l).card : ℝ) / A.card < r
        linarith [hSumI,hTail]

omit [Group G] in
private theorem norm_finiteAverage_le_sparse {A B : Finset G} (hA : A.Nonempty)
    {f : G → ℝ} {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hBound : ∀ g ∈ A, ‖f g‖ ≤ c) (hSparse : ∀ g ∈ A, g ∉ B → ‖f g‖ ≤ d) :
    ‖finiteAverage A f‖ ≤ ((B.card : ℝ) / A.card) * c + d := by
  have hSize : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hsum : ‖∑ g ∈ A, f g‖ ≤ (B.card : ℝ) * c + A.card * d := by
    calc
      _ ≤ ∑ g ∈ A, ‖f g‖ := norm_sum_le _ _
      _ ≤ ∑ g ∈ A, ((if g ∈ B then c else 0) + d) := by
        apply Finset.sum_le_sum
        intro g hg
        split_ifs with h
        · exact (hBound g hg).trans (le_add_of_nonneg_right hd)
        · simpa only [zero_add] using hSparse g hg h
      _ = ((A.filter (· ∈ B)).card : ℝ) * c + A.card * d := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        refine add_le_add (mul_le_mul_of_nonneg_right ?_ hc) (le_refl _)
        exact_mod_cast Finset.card_le_card fun g hg ↦ (Finset.mem_filter.mp hg).2
  simp only [finiteAverage, smul_eq_mul, norm_mul,
    Real.norm_of_nonneg (inv_nonneg.mpr hSize.le)]
  calc
    _ ≤ (A.card : ℝ)⁻¹ * ((B.card : ℝ) * c + A.card * d) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hSize.le)
    _ = _ := by field_simp

omit [Group G] [DecidableEq G] in
private theorem finiteAverage_sub (A : Finset G) (f q : G → ℝ) :
    finiteAverage A (fun g ↦ f g - q g) = finiteAverage A f - finiteAverage A q := by
  simp [finiteAverage, Finset.sum_sub_distrib, mul_sub]

omit [Group G] in
private theorem sum_cell_averages (A : Finset G) (T : G → Finset G) (f : G → ℝ)
    (hMem : ∀ g, g ∈ T g) (hEq : ∀ {g h}, h ∈ T g → T h = T g)
    (hClosed : ∀ g ∈ A, T g ⊆ A) :
    ∑ g ∈ A, finiteAverage (T g) f = ∑ h ∈ A, f h := by
  have hFilter (g : G) (hg : g ∈ A) : A.filter (· ∈ T g) = T g := by
    ext h
    exact Finset.mem_filter.trans ⟨And.right, fun hh ↦ ⟨hClosed g hg hh, hh⟩⟩
  calc
    _ = ∑ g ∈ A, ∑ h ∈ A, if h ∈ T g then ((T g).card : ℝ)⁻¹ * f h else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [← Finset.sum_filter, hFilter g hg, ← Finset.mul_sum]
      rfl
    _ = ∑ h ∈ A, ∑ g ∈ A, if h ∈ T g then ((T g).card : ℝ)⁻¹ * f h else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [← Finset.sum_filter]
      have hFilter' : A.filter (fun g ↦ h ∈ T g) = T h := by
        ext g
        rw [Finset.mem_filter]
        refine ⟨fun ⟨_, hg⟩ ↦ ?_, fun hg ↦ ⟨hClosed h hh hg, ?_⟩⟩
        · rw [hEq hg]
          exact hMem g
        · rw [hEq hg]
          exact hMem h
      rw [hFilter']
      have hSize : (T h).card ≠ 0 := Finset.Nonempty.card_ne_zero ⟨h, hMem h⟩
      calc
        _ = ∑ g ∈ T h, ((T h).card : ℝ)⁻¹ * f h := by
          exact Finset.sum_congr rfl fun g hg ↦ by rw [hEq hg]
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          field_simp

/-- Glue the supplied finite-tile approximations into one configuration. Each centered
test depends on finitely many translate coordinates. The conclusion uses every block
of the prescribed Følner sequence. -/
theorem exists_tendsto_finiteTimeTests_of_tiledApproximations [Countable G] [Infinite G]
    {K : Type*} (F : LeftFolnerSequence G) (P : ℕ → BoundedTilePartition G)
    (hP : ∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g)
    (badCell : ℕ → Set G)
    (hBadCell : ∀ k g h, h ∈ (P k).cell g → (h ∈ badCell k ↔ g ∈ badCell k))
    (δs : ℕ → ℝ) (hδs : ∀ k, 0 ≤ δs k) (hSum : Summable δs)
    (hSparse : ∀ k, ∀ᶠ n in atTop, blockProportion (F.blocks n) (badCell k) ≤ δs k)
    (support : ℕ → Finset G) (q : ℕ → (G → K) → G → ℝ) (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hNorm : ∀ i x g, ‖q i x g‖ ≤ C i)
    (hLocal : ∀ i x y g, (∀ a ∈ support i, x (a * g) = y (a * g)) → q i x g = q i y g)
    (sample : ℕ → Finset G → G → K)
    (hApprox : ∀ k g i, i ≤ k → g ∉ badCell k →
      ‖finiteAverage ((P k).cell g) (q i (sample k ((P k).cell g)))‖ ≤ 1 / ((k : ℝ) + 1))
    (hSmallBoundary : ∀ k g i, i ≤ k → g ∉ badCell k →
      ((leftBoundary (support i) ((P k).cell g)).card : ℝ) / ((P k).cell g).card ≤
        1 / ((k : ℝ) + 1)) :
    ∃ x : G → K, ∀ i, Tendsto (fun n ↦ finiteAverage (F.blocks n) (q i x)) atTop (𝓝 0) := by
  classical
  obtain ⟨level, hLevel, hFinite, hBoundary, hBad⟩ :=
    exists_mixedTilePartition F P hP badCell δs hδs hSum hSparse
  let T (g : G) := (P (level g)).cell g
  let x (g : G) := sample (level g) (T g) g
  have hMem (g : G) : g ∈ T g := (P (level g)).mem_cell g
  have hEq {g h : G} (hh : h ∈ T g) : T h = T g := by
    simp only [T, hLevel g h hh]
    exact (P (level g)).cell_eq hh
  have hSample {g h : G} (hh : h ∈ T g) : x h = sample (level g) (T g) h := by
    rw [show x h = sample (level h) (T h) h from rfl, hEq hh, hLevel g h hh]
  have hTile (i : ℕ) (g : G) (hi : i ≤ level g) (hg : g ∉ badCell (level g)) :
      ‖finiteAverage (T g) (q i x)‖ ≤ (2 * C i + 1) * (1 / ((level g : ℝ) + 1)) := by
    let y := sample (level g) (T g)
    let A := T g
    let B := leftBoundary (support i) A
    have hc : 0 ≤ 2 * C i := mul_nonneg (by norm_num) (hC i)
    have hDiff : ‖finiteAverage A (q i x) - finiteAverage A (q i y)‖ ≤
        ((B.card : ℝ) / A.card) * (2 * C i) := by
      rw [← finiteAverage_sub]
      have h := norm_finiteAverage_le_sparse (A := A) (B := B) (f := fun z ↦ q i x z - q i y z)
        ⟨g, hMem g⟩ hc (le_refl 0)
      rw [add_zero] at h
      apply h
      · intro z _
        calc
          _ ≤ ‖q i x z‖ + ‖q i y z‖ := norm_sub_le _ _
          _ ≤ 2 * C i := by linarith [hNorm i x z, hNorm i y z]
      · intro z hz hzB
        have heq : q i x z = q i y z := by
          apply hLocal
          intro a ha
          apply hSample
          by_contra hn
          exact hzB (mem_leftBoundary.mpr ⟨hz, a, ha, hn⟩)
        simp [heq]
    calc
      _ = ‖(finiteAverage A (q i x) - finiteAverage A (q i y)) +
          finiteAverage A (q i y)‖ := by rw [sub_add_cancel]
      _ ≤ ‖finiteAverage A (q i x) - finiteAverage A (q i y)‖ +
          ‖finiteAverage A (q i y)‖ := norm_add_le _ _
      _ ≤ ((B.card : ℝ) / A.card) * (2 * C i) + 1 / ((level g : ℝ) + 1) :=
        add_le_add hDiff (hApprox (level g) g i hi hg)
      _ ≤ (1 / ((level g : ℝ) + 1)) * (2 * C i) + 1 / ((level g : ℝ) + 1) :=
        add_le_add (mul_le_mul_of_nonneg_right (hSmallBoundary (level g) g i hi hg) hc) (le_refl _)
      _ = _ := by ring
  refine ⟨x, fun i ↦ Metric.tendsto_nhds.2 ?_⟩
  intro δ hδ
  have hlim : Tendsto (fun k : ℕ ↦ (2 * C i + 1) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C i + 1)
  obtain ⟨j, hj⟩ := eventually_atTop.1 (hlim.eventually_lt_const (half_pos hδ))
  let J := max i j
  let E := (hFinite J).toFinset
  let B (n : ℕ) := (F.blocks n).filter (fun g ↦ g ∈ badCell (level g))
  let bad (n : ℕ) := tileBoundary T (F.blocks n) ∪ E ∪ B n
  let good (n : ℕ) := F.blocks n \ bad n
  have hGood (n : ℕ) {g : G} (hg : g ∈ good n) :
      J < level g ∧ T g ⊆ F.blocks n ∧ g ∉ badCell (level g) := by
    obtain ⟨hgA, hgBad⟩ := Finset.mem_sdiff.mp hg
    refine ⟨Nat.lt_of_not_ge (fun h ↦ hgBad (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))), ?_, ?_⟩
    · exact (Set.Finite.mem_toFinset (hFinite J)).mpr h
    · by_contra hn
      exact hgBad (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgA, hn⟩)))
    · intro hb
      exact hgBad (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hgA,hb⟩))
  have hClosed (n : ℕ) (g : G) (hg : g ∈ good n) : T g ⊆ good n := by
    intro h hh
    have hgGood := hGood n hg
    refine Finset.mem_sdiff.mpr ⟨hgGood.2.1 hh, fun hBad ↦ ?_⟩
    rcases Finset.mem_union.mp hBad with hBE | hB
    · rcases Finset.mem_union.mp hBE with hBoundary | hE
      · exact (Finset.mem_filter.mp hBoundary).2 ((hEq hh).symm ▸ hgGood.2.1)
      · have hle : level h ≤ J := (Set.Finite.mem_toFinset (hFinite J)).mp hE
        exact hgGood.1.not_ge ((hLevel g h hh) ▸ hle)
    · apply hgGood.2.2
      apply (hBadCell (level g) g h hh).mp
      exact (hLevel g h hh) ▸ (Finset.mem_filter.mp hB).2
  let mixed (n : ℕ) (g : G) : ℝ :=
    if g ∈ good n then finiteAverage (T g) (q i x) else q i x g
  have hAverage (n : ℕ) : finiteAverage (F.blocks n) (mixed n) =
      finiteAverage (F.blocks n) (q i x) := by
    simp only [finiteAverage]
    congr 1
    have hsub : good n ⊆ F.blocks n := Finset.sdiff_subset
    rw [← Finset.sum_sdiff (f := mixed n) hsub, ← Finset.sum_sdiff (f := q i x) hsub]
    congr 1
    · apply Finset.sum_congr rfl
      intro g hg
      simp [mixed, (Finset.mem_sdiff.mp hg).2]
    · calc
        _ = ∑ g ∈ good n, finiteAverage (T g) (q i x) :=
          Finset.sum_congr rfl fun g hg ↦ by simp [mixed, hg]
        _ = _ := sum_cell_averages (good n) T (q i x) hMem (fun hg ↦ hEq hg) (hClosed n)
  have hSize : Tendsto (fun n ↦ ((F.blocks n).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.tendsto_card
  have hEden : Tendsto (fun n ↦ (E.card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hSize).const_mul (E.card : ℝ)
  have hBadDen : Tendsto (fun n ↦ ((bad n).card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := by
    have hBd : Tendsto (fun n ↦ ((B n).card : ℝ) / (F.blocks n).card) atTop (𝓝 0) := hBad
    have hBound := (hBoundary.add hEden).add hBd
    simp only [zero_add] at hBound
    apply squeeze_zero (fun _ ↦ by positivity) _ hBound
    intro n
    rw [← add_div, ← add_div, ← Nat.cast_add, ← Nat.cast_add]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hSmall := hBadDen.mul_const (C i)
  rw [zero_mul] at hSmall
  filter_upwards [hSmall.eventually_lt_const (half_pos hδ)] with n hn
  have hGoodNorm {g : G} (hg : g ∈ good n) : ‖mixed n g‖ < δ / 2 := by
    simp only [mixed, hg, ite_true]
    have hlg := (hGood n hg).1
    exact (hTile i g ((le_max_left i j).trans hlg.le) (hGood n hg).2.2).trans_lt
      (hj (level g) ((le_max_right i j).trans hlg.le))
  have hMixed (g : G) (_hg : g ∈ F.blocks n) : ‖mixed n g‖ ≤ C i := by
    by_cases h : g ∈ good n
    · simp only [mixed, h, ite_true]
      simpa only [Finset.card_empty, Nat.cast_zero, zero_div, zero_mul, zero_add] using
        norm_finiteAverage_le_sparse (A := T g) (B := ∅) ⟨g, hMem g⟩ (hC i) (hC i)
          (fun z _ ↦ hNorm i x z) (fun z _ _ ↦ hNorm i x z)
    · simp only [mixed, h, ite_false]
      exact hNorm i x g
  rw [dist_zero_right, ← hAverage n]
  have hBound := norm_finiteAverage_le_sparse (F.nonempty n) (B := bad n)
    (hC i) (half_pos hδ).le hMixed
    (fun g hg hbad ↦ (hGoodNorm (Finset.mem_sdiff.mpr ⟨hg, hbad⟩)).le)
  exact hBound.trans_lt (by linarith)

end SixProblems
end

/- Source module SixProblems.CorrespondenceQuasiTiling. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open scoped Classical
open Filter
open scoped Topology

variable {G : Type*} [Group G] [DecidableEq G]

/-- Right translate of a finite shape, consistent with left-invariance of the blocks. -/
def tileTranslate (S : Finset G) (center : G) : Finset G := S.image (· * center)

@[simp] theorem card_tileTranslate (S : Finset G) (center : G) :
    (tileTranslate S center).card = S.card :=
  Finset.card_image_of_injective _ fun _ _ h ↦ mul_right_cancel h

theorem mem_tileTranslate {S : Finset G} {c g : G} :
    g ∈ tileTranslate S c ↔ g * c⁻¹ ∈ S := by
  constructor
  · intro h
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp h
    simpa using hd
  · intro h
    exact Finset.mem_image.mpr ⟨g * c⁻¹, h, by simp⟩

/-- Sites of a translate available before adding it to the covered set. -/
private def availableSites (S : Finset G) (center : G) (U : Set G) : Finset G :=
  (tileTranslate S center).filter (· ∉ U)

private theorem availableSites_antitone (S : Finset G) (center : G) :
    Antitone (availableSites S center) := by
  intro U V hUV g hg
  obtain ⟨hTile, hOut⟩ := Finset.mem_filter.mp hg
  exact Finset.mem_filter.mpr ⟨hTile, fun h ↦ hOut (hUV h)⟩

/-- Scan an enumeration of centers, retaining a translate if it contributes at
least `b` sites outside the set already covered. -/
private def greedyCoverStage (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) : ℕ → Set G :=
  Nat.rec U (fun n C ↦
    if b ≤ (availableSites S (e n) C).card then C ∪ ↑(tileTranslate S (e n)) else C)

private theorem greedyCoverStage_monotone (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) :
    Monotone (greedyCoverStage S e b U) := by
  apply monotone_nat_of_le_succ
  intro n
  change greedyCoverStage S e b U n ⊆ if b ≤ _ then _ ∪ _ else _
  split_ifs
  · exact Set.subset_union_left
  · exact Set.Subset.rfl

/-- Covered sites after scanning all centers. -/
private def greedyCover (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) : Set G :=
  ⋃ n, greedyCoverStage S e b U n

private theorem greedyCover_subset (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) (n : ℕ) :
    greedyCoverStage S e b U n ⊆ greedyCover S e b U :=
  Set.subset_iUnion _ n

/-- The part of the current translate that newly contributes to the cover. -/
private def greedyCore (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) (n : ℕ) : Finset G :=
  let C := greedyCoverStage S e b U n
  if b ≤ (availableSites S (e n) C).card then availableSites S (e n) C else ∅

private theorem greedyCoverStage_succ_eq_union_core (S : Finset G) (e : ℕ → G) (b : ℕ)
    (U : Set G) (n : ℕ) :
    greedyCoverStage S e b U (n + 1) = greedyCoverStage S e b U n ∪ ↑(greedyCore S e b U n) := by
  let C := greedyCoverStage S e b U n
  change (if b ≤ (availableSites S (e n) C).card then C ∪ ↑(tileTranslate S (e n)) else C) = _
  by_cases h : b ≤ (availableSites S (e n) C).card
  · simp only [greedyCore, ← show C = greedyCoverStage S e b U n from rfl, h, ite_true]
    ext g
    change (g ∈ C ∨ g ∈ tileTranslate S (e n)) ↔ g ∈ C ∨ g ∈ availableSites S (e n) C
    rw [availableSites, Finset.mem_filter]
    tauto
  · simp [greedyCore, ← show C = greedyCoverStage S e b U n from rfl, h]

private theorem greedyCore_subset_tile (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) (n : ℕ) :
    greedyCore S e b U n ⊆ tileTranslate S (e n) := by
  dsimp only [greedyCore]
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

private theorem greedyCore_disjoint_stage (S : Finset G) (e : ℕ → G) (b : ℕ)
    (U : Set G) (n : ℕ) :
    Disjoint (↑(greedyCore S e b U n) : Set G) (greedyCoverStage S e b U n) := by
  rw [Set.disjoint_left]
  intro g hg hStage
  dsimp only [greedyCore] at hg
  split_ifs at hg
  · exact (Finset.mem_filter.mp hg).2 hStage
  · simp at hg

private theorem greedyCore_disjoint (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) :
    Pairwise (fun i j ↦ Disjoint (greedyCore S e b U i) (greedyCore S e b U j)) := by
  have hLt {i j : ℕ} (hij : i < j) : Disjoint (greedyCore S e b U i) (greedyCore S e b U j) := by
    rw [← Finset.disjoint_coe]
    apply (greedyCore_disjoint_stage S e b U j).symm.mono_left
    exact (Set.subset_union_right.trans (greedyCoverStage_succ_eq_union_core S e b U i).symm.subset).trans
      (greedyCoverStage_monotone S e b U (Nat.succ_le_of_lt hij))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hLt h
  · exact (hLt h).symm

private theorem greedyCover_eq_union_cores (S : Finset G) (e : ℕ → G) (b : ℕ) (U : Set G) :
    greedyCover S e b U = U ∪ ⋃ n, ↑(greedyCore S e b U n) := by
  apply Set.Subset.antisymm
  · apply Set.iUnion_subset
    intro n
    induction n with
    | zero => exact Set.subset_union_left
    | succ n hn =>
      rw [greedyCoverStage_succ_eq_union_core]
      exact Set.union_subset hn ((Set.subset_iUnion
        (fun i ↦ (↑(greedyCore S e b U i) : Set G)) n).trans Set.subset_union_right)
  · apply Set.union_subset (greedyCover_subset S e b U 0)
    apply Set.iUnion_subset
    intro n
    exact (Set.subset_union_right.trans (greedyCoverStage_succ_eq_union_core S e b U n).symm.subset).trans
      (greedyCover_subset S e b U (n + 1))

private theorem availableSites_greedyCover_card_lt (S : Finset G) (e : ℕ → G)
    (he : Function.Surjective e) {b : ℕ} (hb : 0 < b) (U : Set G) (c : G) :
    (availableSites S c (greedyCover S e b U)).card < b := by
  obtain ⟨n, rfl⟩ := he c
  by_cases h : b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card
  · have hg : ↑(tileTranslate S (e n)) ⊆ greedyCover S e b U := by
      apply Set.Subset.trans _ (greedyCover_subset S e b U (n + 1))
      change (↑(tileTranslate S (e n)) : Set G) ⊆
        if b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card then
          greedyCoverStage S e b U n ∪ ↑(tileTranslate S (e n)) else greedyCoverStage S e b U n
      simp only [h, ite_true]
      exact Set.subset_union_right
    have hEmpty : availableSites S (e n) (greedyCover S e b U) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro g hmem
      exact (Finset.mem_filter.mp hmem).2 (hg (Finset.mem_filter.mp hmem).1)
    simpa [hEmpty] using hb
  · exact (Finset.card_le_card (availableSites_antitone S (e n) (greedyCover_subset S e b U n))).trans_lt
      (Nat.lt_of_not_ge h)

/-- One maximal greedy layer produces disjoint cores of approved translates.
Every translate of the chosen shape has fewer than `b` sites outside the enlarged cover. -/
theorem exists_greedyCover [Countable G] (S : Finset G) {b : ℕ} (hb : 0 < b) (U : Set G) :
    ∃ (V : Set G) (e : ℕ → G) (R : ℕ → Finset G),
      V = U ∪ ⋃ n, ↑(R n) ∧
      Pairwise (fun i j ↦ Disjoint (R i) (R j)) ∧
      (∀ n, Disjoint (↑(R n) : Set G) U) ∧
      (∀ n, R n ⊆ tileTranslate S (e n) ∧ (R n = ∅ ∨ b ≤ (R n).card)) ∧
      (∀ n, (R n).Nonempty → ↑(tileTranslate S (e n)) ⊆ V) ∧
      (∀ c : G, ((tileTranslate S c).filter (· ∉ V)).card < b) := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  refine ⟨greedyCover S e b U, e, greedyCore S e b U,
    greedyCover_eq_union_cores S e b U, greedyCore_disjoint S e b U, ?_, ?_, ?_,
    availableSites_greedyCover_card_lt S e he hb U⟩
  · intro n
    exact (greedyCore_disjoint_stage S e b U n).mono_right
      (greedyCoverStage_monotone S e b U (Nat.zero_le n))
  · intro n
    refine ⟨greedyCore_subset_tile S e b U n, ?_⟩
    dsimp only [greedyCore]
    split_ifs with h
    · exact Or.inr h
    · exact Or.inl rfl
  · intro n hn
    have h : b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card := by
      by_contra h
      simp [greedyCore, h] at hn
    apply Set.Subset.trans _ (greedyCover_subset S e b U (n + 1))
    change (↑(tileTranslate S (e n)) : Set G) ⊆
      if b ≤ (availableSites S (e n) (greedyCoverStage S e b U n)).card then
        greedyCoverStage S e b U n ∪ ↑(tileTranslate S (e n)) else greedyCoverStage S e b U n
    simp only [h, ite_true]
    exact Set.subset_union_right

/-- Count selected pairs `(shape element, center)` to bound from below the coverage of a
maximal greedy layer inside a finite region. The centers tested here have their entire
translate in that region and outside the prior covered set. -/
theorem card_greedyCover_layer (S centers region : Finset G) {U V : Set G} {b : ℕ}
    (hMaximal : ∀ c : G, ((tileTranslate S c).filter (· ∉ V)).card < b)
    (hInside : ∀ c ∈ centers, tileTranslate S c ⊆ region)
    (hOutside : ∀ c ∈ centers, ∀ g ∈ tileTranslate S c, g ∉ U) :
    centers.card * (S.card + 1 - b) ≤
      S.card * (region.filter (fun g ↦ g ∈ V ∧ g ∉ U)).card := by
  let newSites := region.filter (fun g ↦ g ∈ V ∧ g ∉ U)
  have hLower (c : G) : S.card + 1 - b ≤ (S.filter (fun s ↦ s * c ∈ V)).card := by
    have hImage : ((S.filter (fun s ↦ s * c ∉ V)).image (· * c)) =
        (tileTranslate S c).filter (· ∉ V) := by
      ext g
      simp only [Finset.mem_image, Finset.mem_filter, tileTranslate]
      constructor
      · rintro ⟨s, ⟨hs, hV⟩, rfl⟩
        exact ⟨⟨s, hs, rfl⟩, hV⟩
      · rintro ⟨⟨s, hs, rfl⟩, hV⟩
        exact ⟨s, ⟨hs, hV⟩, rfl⟩
    have hsmall := hMaximal c
    rw [← hImage, Finset.card_image_of_injective _
      (show Function.Injective ((· * c) : G → G) from fun _ _ h ↦ mul_right_cancel h)] at hsmall
    have hsum := Finset.card_filter_add_card_filter_not (s := S) (fun s ↦ s * c ∈ V)
    omega
  have hUpper (s : G) (hs : s ∈ S) : (centers.filter (fun c ↦ s * c ∈ V)).card ≤ newSites.card := by
    rw [← Finset.card_image_of_injective _
      (show Function.Injective ((s * ·) : G → G) from fun _ _ h ↦ mul_left_cancel h)]
    apply Finset.card_le_card
    intro g hg
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hC, hV⟩ := Finset.mem_filter.mp hc
    have hmem : s * c ∈ tileTranslate S c := Finset.mem_image.mpr ⟨s, hs, rfl⟩
    exact Finset.mem_filter.mpr ⟨hInside c hC hmem, hV, hOutside c hC _ hmem⟩
  calc
    _ = ∑ c ∈ centers, (S.card + 1 - b) := by simp
    _ ≤ ∑ c ∈ centers, (S.filter (fun s ↦ s * c ∈ V)).card :=
      Finset.sum_le_sum fun c _ ↦ hLower c
    _ = ∑ s ∈ S, (centers.filter (fun c ↦ s * c ∈ V)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ s ∈ S, newSites.card := Finset.sum_le_sum hUpper
    _ = _ := by simp [newSites]

omit [Group G] [DecidableEq G] in
private theorem finiteAverage_sum (A D : Finset G) (w : G → G → ℝ) :
    finiteAverage A (fun g ↦ ∑ d ∈ D, w d g) = ∑ d ∈ D, finiteAverage A (w d) := by
  simp only [finiteAverage, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- For a bounded transport by finitely many left displacements, the difference between
averaged outgoing and incoming mass vanishes along the prescribed Følner sequence. -/
theorem LeftFolnerSequence.tendsto_transport_balance (F : LeftFolnerSequence G) (D : Finset G)
    (w : G → G → ℝ) (C : ℝ) (hBound : ∀ d ∈ D, ∀ g, ‖w d g‖ ≤ C) :
    Tendsto (fun n ↦ finiteAverage (F.blocks n) (fun g ↦ ∑ d ∈ D, w d g) -
      finiteAverage (F.blocks n) (fun g ↦ ∑ d ∈ D, w d (d⁻¹ * g))) atTop (𝓝 0) := by
  simp_rw [finiteAverage_sum, ← Finset.sum_sub_distrib]
  induction D using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using tendsto_const_nhds
  | insert d D hd ih =>
    have hD : ∀ x ∈ D, ∀ g, ‖w x g‖ ≤ C := fun x hx ↦ hBound x (Finset.mem_insert_of_mem hx)
    have h := (F.tendsto_average_sub_translate d⁻¹ (w d) C (hBound d (Finset.mem_insert_self _ _))).neg
    simp only [neg_zero, neg_sub] at h
    simpa only [Finset.sum_insert hd, zero_add] using h.add (ih hD)

omit [Group G] [DecidableEq G] in
private theorem finiteAverage_indicator (A : Finset G) (B : Set G) :
    finiteAverage A (fun g ↦ if g ∈ B then (1 : ℝ) else 0) = ((A.filter (· ∈ B)).card : ℝ) / A.card := by
  rw [finiteAverage, smul_eq_mul, ← Finset.sum_filter]
  simp [div_eq_mul_inv, mul_comm]

/-- If the sites of `B` each send one unit, the other sites send zero, and each
site receives at most `ρ` units, then `ρ` bounds the eventual upper density of `B`. -/
theorem LeftFolnerSequence.eventually_density_le_of_transport (F : LeftFolnerSequence G)
    (D : Finset G) (w : G → G → ℝ) (C : ℝ) (hBound : ∀ d ∈ D, ∀ g, ‖w d g‖ ≤ C)
    (B : Set G) (ρ : ℝ) (hOut : ∀ g, (∑ d ∈ D, w d g) = if g ∈ B then 1 else 0)
    (hIn : ∀ g, ∑ d ∈ D, w d (d⁻¹ * g) ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (((F.blocks n).filter (· ∈ B)).card : ℝ) / (F.blocks n).card < ρ + ε := by
  have hb := F.tendsto_transport_balance D w C hBound
  simp_rw [hOut, finiteAverage_indicator] at hb
  filter_upwards [hb.eventually_lt_const hε] with n hn
  let A := F.blocks n
  have hCard : 0 < (A.card : ℝ) := by exact_mod_cast (F.nonempty n).card_pos
  have hAvg : finiteAverage A (fun g ↦ ∑ d ∈ D, w d (d⁻¹ * g)) ≤ ρ := by
    simp only [finiteAverage, smul_eq_mul]
    calc
      _ ≤ (A.card : ℝ)⁻¹ * ∑ g ∈ A, ρ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ ↦ hIn g) (inv_nonneg.mpr hCard.le)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ hCard.ne', one_mul]
  linarith

/-- The points outside `A` which enter `A` after some left shift from `Q`. -/
def externalBoundary (Q A : Finset G) : Finset G :=
  (Q.biUnion fun a ↦ A.image (a⁻¹ * ·)) \ A

theorem mem_externalBoundary {Q A : Finset G} {g : G} :
    g ∈ externalBoundary Q A ↔ g ∉ A ∧ ∃ q ∈ Q, q * g ∈ A := by
  simp only [externalBoundary, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_image]
  refine ⟨fun ⟨⟨q, hq, x, hx, he⟩, hg⟩ ↦ ⟨hg, q, hq, ?_⟩,
    fun ⟨hg, q, hq, hx⟩ ↦ ⟨⟨q, hq, q * g, hx, inv_mul_cancel_left _ _⟩, hg⟩⟩
  rwa [← he, mul_inv_cancel_left]

theorem externalBoundary_tileTranslate (Q A : Finset G) (c : G) :
    externalBoundary Q (tileTranslate A c) = tileTranslate (externalBoundary Q A) c := by
  ext g
  simp only [mem_externalBoundary, mem_tileTranslate, mul_assoc]

theorem externalBoundary_mono {P Q : Finset G} (hPQ : P ⊆ Q) (A : Finset G) :
    externalBoundary P A ⊆ externalBoundary Q A := by
  intro g hg
  obtain ⟨hOut, a, ha, hIn⟩ := mem_externalBoundary.mp hg
  exact mem_externalBoundary.mpr ⟨hOut, a, hPQ ha, hIn⟩

/-- The external boundary of a fixed finite collection of shifts has vanishing
relative cardinality on a left Følner sequence. -/
theorem LeftFolnerSequence.tendsto_externalBoundary (F : LeftFolnerSequence G) (Q : Finset G) :
    Tendsto (fun n ↦ ((externalBoundary Q (F.blocks n)).card : ℝ) / (F.blocks n).card)
      atTop (𝓝 0) := by
  let P := Q.image Inv.inv
  have hCard (A : Finset G) : (externalBoundary Q A).card ≤ Q.card * (leftBoundary P A).card := by
    have hSub : externalBoundary Q A ⊆ Q.biUnion (fun q ↦ (leftBoundary P A).image (q⁻¹ * ·)) := by
      intro g hg
      obtain ⟨hOut, q, hq, hIn⟩ := mem_externalBoundary.mp hg
      exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image.mpr ⟨q * g,
        mem_leftBoundary.mpr ⟨hIn, q⁻¹, Finset.mem_image_of_mem _ hq, by simpa using hOut⟩,
        inv_mul_cancel_left _ _⟩⟩
    exact (Finset.card_le_card hSub).trans (Finset.card_biUnion_le_card_mul _ _ _
      fun q _ ↦ Finset.card_image_le)
  have h := (F.tendsto_leftBoundary P).const_mul (Q.card : ℝ)
  rw [mul_zero] at h
  apply squeeze_zero (fun _ ↦ by positivity) _ h
  intro n
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hCard (F.blocks n)) (Nat.cast_nonneg _)

/-- A union of disjoint trimmed cores inherits a small external boundary when the whole
original translates have small boundaries compared with their cores. -/
theorem LeftFolnerSequence.eventually_externalCoverBoundary_le {ι : Type*}
    (F : LeftFolnerSequence G) (Q D : Finset G) (U : Set G) (A R : ι → Finset G)
    (hR : ∀ i, R i ⊆ A i) (hU : ∀ i, (R i).Nonempty → ↑(A i) ⊆ U)
    (hCover : ∀ g ∈ U, ∃ i, g ∈ R i) (hPair : Pairwise (fun i j ↦ Disjoint (R i) (R j)))
    (hD : ∀ i, ∀ g ∈ externalBoundary Q (A i), ∀ y ∈ R i, y * g⁻¹ ∈ D)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hSmall : ∀ i, (R i).Nonempty → ((externalBoundary Q (A i)).card : ℝ) ≤ ρ * (R i).card)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (((F.blocks n).filter (fun g ↦ g ∉ U ∧ ∃ q ∈ Q, q * g ∈ U)).card : ℝ) /
      (F.blocks n).card < ρ + ε := by
  let B : Set G := {g | g ∉ U ∧ ∃ q ∈ Q, q * g ∈ U}
  have pick (g : B) : ∃ i, (R i).Nonempty ∧ (g : G) ∈ externalBoundary Q (A i) := by
    obtain ⟨hg, q, hq, hqU⟩ := g.property
    obtain ⟨i, hi⟩ := hCover (q * (g : G)) hqU
    have hn : (R i).Nonempty := ⟨_, hi⟩
    exact ⟨i, hn, mem_externalBoundary.mpr ⟨fun h ↦ hg (hU i hn h), q, hq, hR i hi⟩⟩
  choose loc hLoc using pick
  let w (d g : G) : ℝ :=
    if hg : g ∈ B then
      let i := loc ⟨g, hg⟩
      if d * g ∈ R i then ((R i).card : ℝ)⁻¹ else 0
    else 0
  have hSize (g : B) : 0 < ((R (loc g)).card : ℝ) := by
    exact_mod_cast (hLoc g).1.card_pos
  have hw (d : G) (_hd : d ∈ D) (g : G) : ‖w d g‖ ≤ 1 := by
    by_cases hg : g ∈ B
    · simp only [w, hg, dite_true]
      split_ifs
      · rw [Real.norm_of_nonneg (inv_nonneg.mpr (hSize ⟨g, hg⟩).le),
          inv_le_one₀ (hSize ⟨g, hg⟩)]
        exact_mod_cast (hLoc ⟨g, hg⟩).1.card_pos
      · simp
    · simp [w, hg]
  have hOut (g : G) : (∑ d ∈ D, w d g) = if g ∈ B then 1 else 0 := by
    by_cases hg : g ∈ B
    · let i := loc ⟨g, hg⟩
      let C := D.filter (fun d ↦ d * g ∈ R i)
      have hImage : C.image (· * g) = R i := by
        ext y
        constructor
        · intro hy
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_filter.mp hd).2
        · intro hy
          refine Finset.mem_image.mpr ⟨y * g⁻¹, Finset.mem_filter.mpr
            ⟨hD i g (hLoc ⟨g, hg⟩).2 y hy, ?_⟩, by simp⟩
          simpa using hy
      have hCard : C.card = (R i).card := by
        rw [← hImage, Finset.card_image_of_injective _
          (show Function.Injective ((· * g) : G → G) from fun _ _ h ↦ mul_right_cancel h)]
      simp only [w, hg, dite_true, ite_true, ← Finset.sum_filter]
      change (∑ d ∈ C, ((R i).card : ℝ)⁻¹) = 1
      simp only [Finset.sum_const, nsmul_eq_mul, hCard]
      exact mul_inv_cancel₀ (hSize ⟨g, hg⟩).ne'
    · simp [w, hg]
  have hIn (g : G) : ∑ d ∈ D, w d (d⁻¹ * g) ≤ ρ := by
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hCover g hg
      let C := D.filter (fun d ↦ d⁻¹ * g ∈ externalBoundary Q (A i))
      have hCard : C.card ≤ (externalBoundary Q (A i)).card := by
        rw [← Finset.card_image_of_injective _ (show Function.Injective (fun d : G ↦ d⁻¹ * g) from
          fun _ _ h ↦ inv_injective (mul_right_cancel h))]
        exact Finset.card_le_card (Finset.image_subset_iff.mpr fun _ h ↦ (Finset.mem_filter.mp h).2)
      have hSize : 0 < ((R i).card : ℝ) := by exact_mod_cast (show (R i).Nonempty from ⟨g, hi⟩).card_pos
      calc
        _ ≤ ∑ d ∈ D, if d⁻¹ * g ∈ externalBoundary Q (A i) then ((R i).card : ℝ)⁻¹ else 0 := by
          apply Finset.sum_le_sum
          intro d _
          by_cases hx : d⁻¹ * g ∈ B
          · simp only [w, hx, dite_true, mul_inv_cancel_left]
            split_ifs with hy hz hz
            · have hEq : loc ⟨d⁻¹ * g, hx⟩ = i := by
                by_contra hn
                exact Finset.disjoint_left.mp (hPair hn) hy hi
              rw [hEq]
            · exfalso
              have hEq : loc ⟨d⁻¹ * g, hx⟩ = i := by
                by_contra hn
                exact Finset.disjoint_left.mp (hPair hn) hy hi
              exact hz (hEq ▸ (hLoc ⟨d⁻¹ * g, hx⟩).2)
            · exact inv_nonneg.mpr hSize.le
            · rfl
          · simp only [w, hx, dite_false]
            split_ifs
            · exact inv_nonneg.mpr hSize.le
            · rfl
        _ = (C.card : ℝ) * ((R i).card : ℝ)⁻¹ := by
          rw [← Finset.sum_filter]
          simp [C]
        _ ≤ ((externalBoundary Q (A i)).card : ℝ) * ((R i).card : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) (inv_nonneg.mpr hSize.le)
        _ ≤ ρ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hSize]
          exact hSmall i ⟨g, hi⟩
    · have hZero (d : G) : w d (d⁻¹ * g) = 0 := by
        by_cases hx : d⁻¹ * g ∈ B
        · have hy : g ∉ R (loc ⟨d⁻¹ * g, hx⟩) := fun h ↦
            hg (hU _ (hLoc ⟨d⁻¹ * g, hx⟩).1 (hR _ h))
          simp [w, hx, hy]
        · simp [w, hx]
      simpa [hZero] using hρ
  have hOut' (g : G) : (∑ d ∈ D, w d g) = @ite ℝ (g ∈ B) (Classical.propDecidable _) 1 0 := by
    have h := hOut g
    by_cases hg : g ∈ B <;> simpa [hg] using h
  filter_upwards [F.eventually_density_le_of_transport D w 1 hw B ρ hOut' hIn hε] with n hn
  have he : @Finset.filter G (· ∈ B) (fun g ↦ Classical.propDecidable (g ∈ B)) (F.blocks n) =
      (F.blocks n).filter (fun g ↦ g ∉ U ∧ ∃ q ∈ Q, q * g ∈ U) := by
    ext g
    simp only [Finset.mem_filter, B, Set.mem_ofPred_eq]
  rwa [he] at hn

/-- Fraction of a finite region lying in a specified set. -/
def finiteFraction (A : Finset G) (U : Set G) : ℝ :=
  ((A.filter (· ∈ U)).card : ℝ) / A.card

omit [Group G] [DecidableEq G] in
theorem finiteFraction_eq_blockProportion (A : Finset G) (U : Set G) :
    finiteFraction A U = blockProportion A U := rfl

omit [Group G] [DecidableEq G] in
theorem finiteFraction_eq_filter (A : Finset G) (U : Set G) (d : DecidablePred (· ∈ U)) :
    finiteFraction A U = ((@Finset.filter G (· ∈ U) d A).card : ℝ) / A.card := by
  unfold finiteFraction
  apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / A.card)
  ext g
  simp only [Finset.mem_filter]

omit [Group G] [DecidableEq G] in
theorem finiteFraction_setOf (A : Finset G) (p : G → Prop) :
    finiteFraction A {g | p g} = ((A.filter p).card : ℝ) / A.card := by
  unfold finiteFraction
  apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / A.card)
  ext g
  simp only [Finset.mem_filter, Set.mem_ofPred_eq]

/-- A greedy layer reduces the uncovered fraction by a fixed proportion, allowing for
centers whose translates meet the outside of the region or the previous cover. -/
theorem finiteFraction_complement_le_of_greedyLayer (S A : Finset G) (hS : S.Nonempty)
    {U V : Set G} (hUV : U ⊆ V) {b : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hηb : η * S.card ≤ ((S.card + 1 - b : ℕ) : ℝ))
    (hMaximal : ∀ c : G, ((tileTranslate S c).filter (· ∉ V)).card < b) :
    finiteFraction A Vᶜ ≤ (1 - η) * finiteFraction A Uᶜ +
      η * (finiteFraction A {g | ∃ s ∈ S, s * g ∉ A} +
        finiteFraction A {g | g ∉ U ∧ ∃ s ∈ S, s * g ∈ U}) := by
  let Z := A.filter (· ∉ U)
  let C := Z.filter (fun c ↦ ∀ s ∈ S, s * c ∈ A ∧ s * c ∉ U)
  let B := leftBoundary S A
  let E := A.filter (fun g ↦ g ∉ U ∧ ∃ s ∈ S, s * g ∈ U)
  let W := A.filter (fun g ↦ g ∈ V ∧ g ∉ U)
  have hBlame : Z \ C ⊆ B ∪ E := by
    intro g hg
    obtain ⟨hZ, hNC⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨hA, hU⟩ := Finset.mem_filter.mp hZ
    have hFail : ¬ ∀ s ∈ S, s * g ∈ A ∧ s * g ∉ U :=
      fun h ↦ hNC (Finset.mem_filter.mpr ⟨hZ, h⟩)
    push Not at hFail
    obtain ⟨s, hs, h⟩ := hFail
    by_cases hIn : s * g ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, hU, s, hs, h hIn⟩)
    · exact Finset.mem_union_left _ (mem_leftBoundary.mpr ⟨hA, s, hs, hIn⟩)
  have hZ : Z.card ≤ C.card + B.card + E.card := by
    have hle : (Z \ C).card ≤ B.card + E.card :=
      (Finset.card_le_card hBlame).trans (Finset.card_union_le _ _)
    have hsub : C ⊆ Z := Finset.filter_subset _ _
    have he := Finset.card_sdiff_add_card_eq_card hsub
    omega
  have hNew : (η * (C.card : ℝ)) ≤ W.card := by
    have hCount := card_greedyCover_layer S C A hMaximal
      (fun c hc g hg ↦ by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
        exact ((Finset.mem_filter.mp hc).2 s hs).1)
      (fun c hc g hg ↦ by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hg
        exact ((Finset.mem_filter.mp hc).2 s hs).2)
    have hCountR : (C.card : ℝ) * ((S.card + 1 - b : ℕ) : ℝ) ≤ S.card * (W.card : ℝ) := by
      exact_mod_cast hCount
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    refine (mul_le_mul_iff_right₀ hSpos).mp ?_
    calc
      (S.card : ℝ) * (η * (C.card : ℝ)) = (C.card : ℝ) * (η * S.card) := by ring
      _ ≤ (C.card : ℝ) * ((S.card + 1 - b : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hηb (Nat.cast_nonneg _)
      _ ≤ S.card * (W.card : ℝ) := hCountR
  have hcard : (A.filter (· ∉ V)).card + W.card = Z.card := by
    have h₁ : Z.filter (· ∈ V) = W := by
      ext g
      simp [Z, W, and_assoc, and_comm]
    have h₂ : Z.filter (· ∉ V) = A.filter (· ∉ V) := by
      ext g
      simp only [Z, Finset.mem_filter]
      exact ⟨fun ⟨⟨hA, _⟩, hV⟩ ↦ ⟨hA, hV⟩, fun ⟨hA, hV⟩ ↦ ⟨⟨hA, fun hu ↦ hV (hUV hu)⟩, hV⟩⟩
    rw [← h₁, ← h₂, add_comm, Finset.card_filter_add_card_filter_not]
  have hZr : (Z.card : ℝ) ≤ C.card + B.card + E.card := by exact_mod_cast hZ
  have hCardR : ((A.filter (· ∉ V)).card : ℝ) + W.card = Z.card := by exact_mod_cast hcard
  have he : ((A.filter (· ∉ V)).card : ℝ) ≤ (1 - η) * Z.card + η * (B.card + E.card) := by
    linarith [mul_le_mul_of_nonneg_left hZr hη]
  have hdiv := div_le_div_of_nonneg_right he (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  rw [add_div, mul_div_assoc, mul_div_assoc, add_div] at hdiv
  have hfrac (U : Set G) (p : G → Prop) [DecidablePred p] (h : ∀ g ∈ A, g ∈ U ↔ p g) :
      finiteFraction A U = ((A.filter p).card : ℝ) / A.card := by
    unfold finiteFraction
    rw [Finset.filter_congr h]
  have hB : A.filter (fun g ↦ ∃ s ∈ S, s * g ∉ A) = B := by
    ext g
    exact Finset.mem_filter.trans mem_leftBoundary.symm
  rw [hfrac Vᶜ (· ∉ V) (fun _ _ ↦ Iff.rfl), hfrac Uᶜ (· ∉ U) (fun _ _ ↦ Iff.rfl),
    hfrac _ (fun g ↦ ∃ s ∈ S, s * g ∉ A) (fun _ _ ↦ Iff.rfl), hB,
    hfrac _ (fun g ↦ g ∉ U ∧ ∃ s ∈ S, s * g ∈ U) (fun _ _ ↦ Iff.rfl)]
  exact hdiv

end SixProblems
end

/- Source module SixProblems.CorrespondenceQuasiTilingCover. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter
open scoped Classical Topology

universe u
variable {G : Type u} [Group G] [DecidableEq G]

/-- A finite-shape family of translates with pairwise disjoint trimmed cores.
The cores cover exactly the set occupied by all translates with nonempty cores. -/
structure PartialQuasiTiling (G : Type u) [Group G] [DecidableEq G] (η : ℝ) where
  index : Type u
  shapes : Finset (Finset G)
  shape : index → Finset G
  shape_mem (i : index) : shape i ∈ shapes
  center : index → G
  core : index → Finset G
  covered : Set G
  covered_eq : covered = ⋃ i, ↑(core i)
  disjoint_core : Pairwise (fun i j ↦ Disjoint (core i) (core j))
  core_subset (i : index) : core i ⊆ tileTranslate (shape i) (center i)
  tile_subset (i : index) : (core i).Nonempty → ↑(tileTranslate (shape i) (center i)) ⊆ covered
  core_card (i : index) : (core i).Nonempty → (1 - η) * (shape i).card ≤ ((core i).card : ℝ)

namespace PartialQuasiTiling

variable {η : ℝ}

theorem core_subset_covered (T : PartialQuasiTiling G η) (i : T.index) : ↑(T.core i) ⊆ T.covered := by
  rw [T.covered_eq]
  exact Set.subset_iUnion (fun j ↦ (↑(T.core j) : Set G)) i

/-- Empty cover before the first greedy layer. -/
def empty : PartialQuasiTiling G η where
  index := PEmpty
  shapes := ∅
  shape := fun i ↦ i.elim
  shape_mem := fun i ↦ i.elim
  center := fun i ↦ i.elim
  core := fun i ↦ i.elim
  covered := ∅
  covered_eq := by simp
  disjoint_core := fun i ↦ i.elim
  core_subset := fun i ↦ i.elim
  tile_subset := fun i ↦ i.elim
  core_card := fun i ↦ i.elim

/-- Extend the finite family by one maximal layer, retaining at least the prescribed
proportion in each new nonempty core. -/
theorem exists_extend [Countable G] (T : PartialQuasiTiling G η) (S : Finset G)
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) :
    ∃ (T' : PartialQuasiTiling G η) (b : ℕ),
      T'.shapes = insert S T.shapes ∧ T.covered ⊆ T'.covered ∧
      η * (S.card : ℝ) ≤ ((S.card + 1 - b : ℕ) : ℝ) ∧
      (∀ c : G, ((tileTranslate S c).filter (· ∉ T'.covered)).card < b) := by
  let r := ⌈η * (S.card : ℝ)⌉₊
  have hr : r ≤ S.card := Nat.ceil_le.mpr (by
    calc
      η * (S.card : ℝ) ≤ 1 * (S.card : ℝ) := mul_le_mul_of_nonneg_right hη₁ (Nat.cast_nonneg _)
      _ = _ := one_mul _)
  let b := S.card + 1 - r
  have hb : 0 < b := by dsimp [b]; omega
  have hηb : η * (S.card : ℝ) ≤ ((S.card + 1 - b : ℕ) : ℝ) := by
    rw [show S.card + 1 - b = r by dsimp [b]; omega]
    exact Nat.le_ceil _
  have hηb' : (1 - η) * (S.card : ℝ) ≤ (b : ℝ) := by
    have hr' : (r : ℝ) < η * (S.card : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    dsimp only [b]
    rw [Nat.cast_sub (by omega : r ≤ S.card + 1), Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨V, e, R, hV, hDis, hNewDis, hNewCore, hNewTile, hMax⟩ :=
    exists_greedyCover S hb T.covered
  have hUV : T.covered ⊆ V := hV ▸ Set.subset_union_left
  let T' : PartialQuasiTiling G η :=
    { index := T.index ⊕ ℕ,
      shapes := insert S T.shapes,
      shape := Sum.elim T.shape (fun _ ↦ S),
      shape_mem := fun i ↦ match i with
        | .inl j => Finset.mem_insert_of_mem (T.shape_mem j)
        | .inr _ => Finset.mem_insert_self _ _,
      center := Sum.elim T.center e,
      core := Sum.elim T.core R,
      covered := V,
      covered_eq := by rw [hV, T.covered_eq, Set.iUnion_sum]; rfl,
      disjoint_core := by
        intro i j hne
        cases i with
        | inl i =>
          cases j with
          | inl j => exact T.disjoint_core (fun h ↦ hne (congrArg Sum.inl h))
          | inr j =>
            rw [← Finset.disjoint_coe]
            exact (hNewDis j).symm.mono_left (T.core_subset_covered i)
        | inr i =>
          cases j with
          | inl j =>
            rw [← Finset.disjoint_coe]
            exact (hNewDis i).mono_right (T.core_subset_covered j)
          | inr j => exact hDis (fun h ↦ hne (congrArg Sum.inr h)),
      core_subset := fun i ↦ match i with
        | .inl j => T.core_subset j
        | .inr j => (hNewCore j).1,
      tile_subset := fun i ↦ match i with
        | .inl j => fun hj ↦ (T.tile_subset j hj).trans hUV
        | .inr j => hNewTile j,
      core_card := fun i ↦ match i with
        | .inl j => T.core_card j
        | .inr j => fun hj ↦ hηb'.trans (Nat.cast_le.mpr ((hNewCore j).2.resolve_left hj.ne_empty)) }
  exact ⟨T', b, rfl, hUV, hηb, hMax⟩

/-- Boundary of a partial cover, using only the finitely many possible tile shapes. -/
theorem eventually_externalBoundary (T : PartialQuasiTiling G η) (F : LeftFolnerSequence G)
    (Q : Finset G) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hShapes : ∀ S ∈ T.shapes, ((externalBoundary Q S).card : ℝ) ≤ ρ * (1 - η) * S.card)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, finiteFraction (F.blocks n) {g | g ∉ T.covered ∧ ∃ q ∈ Q, q * g ∈ T.covered} < ρ + ε := by
  let M := T.shapes.biUnion (fun S ↦ S.biUnion (fun y ↦ S.image (fun x ↦ y * x⁻¹)))
  let D := M.biUnion (fun d ↦ Q.image (d * ·))
  let A (i : T.index) := tileTranslate (T.shape i) (T.center i)
  have hD (i : T.index) (g : G) (hg : g ∈ externalBoundary Q (A i))
      (y : G) (hy : y ∈ T.core i) : y * g⁻¹ ∈ D := by
    obtain ⟨_, q, hq, hqA⟩ := mem_externalBoundary.mp hg
    have hyS := mem_tileTranslate.mp (T.core_subset i hy)
    have hqS : q * g * (T.center i)⁻¹ ∈ T.shape i := mem_tileTranslate.mp hqA
    let d := (y * (T.center i)⁻¹) * (q * g * (T.center i)⁻¹)⁻¹
    have hd : d ∈ M := Finset.mem_biUnion.mpr ⟨T.shape i, T.shape_mem i,
      Finset.mem_biUnion.mpr ⟨y * (T.center i)⁻¹, hyS, Finset.mem_image.mpr ⟨_, hqS, rfl⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨q, hq, by simp [d, mul_assoc]⟩⟩
  have hSmall (i : T.index) (hi : (T.core i).Nonempty) :
      ((externalBoundary Q (A i)).card : ℝ) ≤ ρ * (T.core i).card := by
    rw [show A i = _ from rfl, externalBoundary_tileTranslate, card_tileTranslate]
    have hs := hShapes (T.shape i) (T.shape_mem i)
    rw [mul_assoc] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left (T.core_card i hi) hρ)
  have hCover (g : G) (hg : g ∈ T.covered) : ∃ i, g ∈ T.core i := by
    rw [T.covered_eq, Set.mem_iUnion] at hg
    exact hg
  have h := F.eventually_externalCoverBoundary_le Q D T.covered A T.core T.core_subset T.tile_subset
    hCover T.disjoint_core hD ρ hρ hSmall hε
  filter_upwards [h] with n hn
  have he : finiteFraction (F.blocks n) {g | g ∉ T.covered ∧ ∃ q ∈ Q, q * g ∈ T.covered} =
      (((F.blocks n).filter (fun g ↦ g ∉ T.covered ∧ ∃ q ∈ Q, q * g ∈ T.covered)).card : ℝ) /
        (F.blocks n).card := by
    unfold finiteFraction
    apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / (F.blocks n).card)
    ext g
    simp only [Finset.mem_filter, Set.mem_ofPred_eq]
  rwa [he]

/-- Greedy layers with progressively less invariant shapes give a finite-shape cover
whose uncovered fraction is eventually below the prescribed tolerance. The allowable
shapes can impose additional conditions, provided arbitrarily invariant shapes are available. -/
theorem exists_eventually_cover [Countable G] (F : LeftFolnerSequence G) (allowed : Set (Finset G))
    {η δ : ℝ} (hη : 0 < η) (hη₁ : η < 1) (hδ : 0 < δ)
    (hAvailable : ∀ (Q : Finset G) (ε : ℝ), 0 < ε →
      ∃ S ∈ allowed, S.Nonempty ∧ ((externalBoundary Q S).card : ℝ) ≤ ε * S.card) :
    ∃ T : PartialQuasiTiling G η, (∀ S ∈ T.shapes, S ∈ allowed) ∧
      ∀ᶠ n in atTop, finiteFraction (F.blocks n) T.coveredᶜ < δ := by
  let ρ : ℝ := δ / 8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hOneη : 0 ≤ 1 - η := sub_nonneg.mpr hη₁.le
  have hL (m : ℕ) (Q : Finset G) : ∃ T : PartialQuasiTiling G η,
      (∀ S ∈ T.shapes, S ∈ allowed) ∧
      (∀ S ∈ T.shapes, ((externalBoundary Q S).card : ℝ) ≤ ρ * (1 - η) * S.card) ∧
      ∀ᶠ n in atTop, finiteFraction (F.blocks n) T.coveredᶜ ≤ (1 - η) ^ m + δ / 2 := by
    induction m generalizing Q with
    | zero =>
      let T : PartialQuasiTiling G η := empty
      refine ⟨T, by simp [T, empty], by simp [T, empty], Filter.Eventually.of_forall fun n ↦ ?_⟩
      have hCard : ((F.blocks n).card : ℝ) ≠ 0 := by exact_mod_cast (F.nonempty n).card_ne_zero
      simp only [T, empty, Set.compl_empty, finiteFraction, Set.mem_univ, Finset.filter_true,
        div_self hCard, pow_zero]
      linarith
    | succ m ih =>
      obtain ⟨S, hSAllow, hS, hSBoundary⟩ := hAvailable Q (ρ * (1 - η))
        (mul_pos hρ (sub_pos.mpr hη₁))
      obtain ⟨T, hAllow, hShape, hOldDensity⟩ := ih (Q ∪ S)
      obtain ⟨T', b, hShapes, hUV, hηb, hMaximal⟩ := T.exists_extend S hη.le hη₁.le
      refine ⟨T', ?_, ?_, ?_⟩
      · intro A hA
        rw [hShapes, Finset.mem_insert] at hA
        rcases hA with rfl | hA
        · exact hSAllow
        · exact hAllow A hA
      · intro A hA
        rw [hShapes, Finset.mem_insert] at hA
        rcases hA with rfl | hA
        · exact hSBoundary
        · exact (Nat.cast_le.mpr (Finset.card_le_card
            (externalBoundary_mono Finset.subset_union_left A))).trans (hShape A hA)
      have hShapeOld (A : Finset G) (hA : A ∈ T.shapes) :
          ((externalBoundary S A).card : ℝ) ≤ ρ * (1 - η) * A.card :=
        (Nat.cast_le.mpr (Finset.card_le_card
          (externalBoundary_mono Finset.subset_union_right A))).trans (hShape A hA)
      have hSmallU := T.eventually_externalBoundary F S hρ.le hShapeOld hρ
      have hSmallA := (F.tendsto_leftBoundary S).eventually_lt_const (show 0 < δ / 4 by positivity)
      filter_upwards [hOldDensity, hSmallU, hSmallA] with n hOld hU hA
      have hB := finiteFraction_complement_le_of_greedyLayer S (F.blocks n) hS hUV hη.le hηb hMaximal
      have hFrac : finiteFraction (F.blocks n) {g | ∃ s ∈ S, s * g ∉ F.blocks n} =
          ((leftBoundary S (F.blocks n)).card : ℝ) / (F.blocks n).card := by
        unfold finiteFraction
        apply congrArg (fun t : Finset G ↦ (t.card : ℝ) / (F.blocks n).card)
        ext g
        simp only [Finset.mem_filter, Set.mem_ofPred_eq, mem_leftBoundary]
      rw [hFrac] at hB
      rw [pow_succ]
      calc
        _ ≤ (1 - η) * ((1 - η) ^ m + δ / 2) + η * (δ / 2) := by
          refine hB.trans (add_le_add (mul_le_mul_of_nonneg_left hOld hOneη)
            (mul_le_mul_of_nonneg_left ?_ hη.le))
          dsimp [ρ] at hU
          linarith
        _ = _ := by ring
  have hPow : Tendsto (fun m : ℕ ↦ (1 - η) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hOneη (by linarith)
  obtain ⟨m, hm⟩ := (hPow.eventually_lt_const (half_pos hδ)).exists
  obtain ⟨T, hT, _, hDensity⟩ := hL m ∅
  exact ⟨T, hT, hDensity.mono fun n hn ↦ hn.trans_lt (by linarith)⟩

end PartialQuasiTiling

end SixProblems
end

/- Source module SixProblems.CorrespondenceQuasiTilingCoarsen. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter
open scoped Classical Topology

variable {G : Type*} [Group G] [DecidableEq G]

/-- The union of the cells of `P` entirely contained in `A`. -/
def BoundedTilePartition.interior (P : BoundedTilePartition G) (A : Finset G) : Finset G :=
  A.filter fun g ↦ P.cell g ⊆ A

theorem BoundedTilePartition.mem_interior_iff (P : BoundedTilePartition G) {A : Finset G} {g : G} :
    g ∈ P.interior A ↔ P.cell g ⊆ A :=
  ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun h ↦ Finset.mem_filter.mpr ⟨h (P.mem_cell g), h⟩⟩

theorem BoundedTilePartition.interior_subset (P : BoundedTilePartition G) (A : Finset G) :
    P.interior A ⊆ A := Finset.filter_subset _ _

theorem leftBoundary_tileTranslate (Q A : Finset G) (c : G) :
    leftBoundary Q (tileTranslate A c) = tileTranslate (leftBoundary Q A) c := by
  ext g
  simp only [mem_leftBoundary, mem_tileTranslate, mul_assoc]

/-- Restricting a finite set creates additional boundary only near the sites removed. -/
theorem card_leftBoundary_le_of_subset (D : Finset G) {A B : Finset G} (hBA : B ⊆ A) :
    (leftBoundary D B).card ≤ (leftBoundary D A).card + D.card * (A \ B).card := by
  let C := D.biUnion (fun d ↦ (A \ B).image (d⁻¹ * ·))
  have hSub : leftBoundary D B ⊆ leftBoundary D A ∪ C := by
    intro g hg
    obtain ⟨hgB, d, hd, hdB⟩ := mem_leftBoundary.mp hg
    by_cases hdA : d * g ∈ A
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr
        ⟨d * g, Finset.mem_sdiff.mpr ⟨hdA, hdB⟩, inv_mul_cancel_left _ _⟩⟩)
    · exact Finset.mem_union_left _ (mem_leftBoundary.mpr ⟨hBA hgB, d, hd, hdA⟩)
  have hC : C.card ≤ D.card * (A \ B).card :=
    Finset.card_biUnion_le_card_mul _ _ _ fun _ _ ↦ Finset.card_image_le
  exact (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans (add_le_add (le_refl _) hC))

omit [Group G] in
/-- Removing a fraction of a block perturbs a bounded real average by at most
twice the bound times that fraction. -/
theorem norm_finiteAverage_sub_of_subset {A B : Finset G} (hBA : B ⊆ A) (hB : B.Nonempty)
    (f : G → ℝ) {C : ℝ} (hf : ∀ g, ‖f g‖ ≤ C) :
    ‖finiteAverage A f - finiteAverage B f‖ ≤ 2 * C * (((A \ B).card : ℝ) / A.card) := by
  have hA := hB.mono hBA
  have hCount (I : Finset G) (hI : I.Nonempty) : 0 < (I.card : ℝ) := by exact_mod_cast hI.card_pos
  have hMean : ‖finiteAverage B f‖ ≤ C := by
    rw [finiteAverage, smul_eq_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (hCount B hB).le)]
    have hSum : ‖∑ g ∈ B, f g‖ ≤ (B.card : ℝ) * C := by
      apply (norm_sum_le _ _).trans
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun (g : G) (_hg : g ∈ B) ↦ hf g)
    calc
      _ ≤ (B.card : ℝ)⁻¹ * ((B.card : ℝ) * C) := mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (hCount B hB).ne', one_mul]
  have hSumEq (I : Finset G) (hI : I.Nonempty) :
      (I.card : ℝ) * finiteAverage I f = ∑ g ∈ I, f g := by
    rw [finiteAverage, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (hCount I hI).ne', one_mul]
  have hSize : (A.card : ℝ) = ((A \ B).card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hBA).symm
  have hIdentity : (A.card : ℝ) * (finiteAverage A f - finiteAverage B f) =
      ∑ g ∈ A \ B, (f g - finiteAverage B f) := by
    rw [mul_sub, hSumEq A hA, ← Finset.sum_sdiff hBA (f := f), hSize, add_mul, hSumEq B hB,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have hEq : finiteAverage A f - finiteAverage B f =
      (∑ g ∈ A \ B, (f g - finiteAverage B f)) / (A.card : ℝ) :=
    (eq_div_iff (hCount A hA).ne').mpr (by rwa [mul_comm])
  rw [hEq, norm_div, Real.norm_of_nonneg (hCount A hA).le]
  have hNorm : ‖∑ g ∈ A \ B, (f g - finiteAverage B f)‖ ≤ ((A \ B).card : ℝ) * (2 * C) := by
    calc
      _ ≤ ∑ g ∈ A \ B, ‖f g - finiteAverage B f‖ := norm_sum_le _ _
      _ ≤ ∑ g ∈ A \ B, 2 * C := Finset.sum_le_sum fun g _ ↦ (norm_sub_le _ _).trans (by linarith [hf g])
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (((A \ B).card : ℝ) * (2 * C)) / (A.card : ℝ) :=
      div_le_div_of_nonneg_right hNorm (hCount A hA).le
    _ = _ := by rw [mul_comm (((A \ B).card : ℝ)), mul_div_assoc]

namespace PartialQuasiTiling

variable {η : ℝ}

/-- A finite set containing differences between any two sites of any original tile. -/
def displacements (T : PartialQuasiTiling G η) : Finset G :=
  T.shapes.biUnion (fun A ↦ A.biUnion (fun y ↦ A.image (fun x ↦ y * x⁻¹)))

theorem mem_displacements (T : PartialQuasiTiling G η) (i : T.index) {x y : G}
    (hx : x ∈ tileTranslate (T.shape i) (T.center i))
    (hy : y ∈ tileTranslate (T.shape i) (T.center i)) : y * x⁻¹ ∈ T.displacements := by
  have hx' := mem_tileTranslate.mp hx
  have hy' := mem_tileTranslate.mp hy
  refine Finset.mem_biUnion.mpr ⟨T.shape i, T.shape_mem i, Finset.mem_biUnion.mpr
    ⟨y * (T.center i)⁻¹, hy', Finset.mem_image.mpr ⟨x * (T.center i)⁻¹, hx', ?_⟩⟩⟩
  simp [mul_assoc]

/-- Sites in prior cells which cannot be assigned whole to any one trimmed core. -/
def exceptional (T : PartialQuasiTiling G η) (P : BoundedTilePartition G) : Set G :=
  {g | ¬ ∃ i, g ∈ P.interior (T.core i)}

/-- Turn the trimmed cores into cells of a coarser partition. Any former cell
that is outside these cores survives as an exceptional cell. -/
theorem exists_coarsening (T : PartialQuasiTiling G η) (P : BoundedTilePartition G) :
    ∃ Q : BoundedTilePartition G,
      (∀ g, P.cell g ⊆ Q.cell g) ∧
      (∀ g h, h ∈ Q.cell g → (g ∈ T.exceptional P ↔ h ∈ T.exceptional P)) ∧
      (∀ g ∉ T.exceptional P, ∃ i, g ∈ P.interior (T.core i) ∧ Q.cell g = P.interior (T.core i)) := by
  let S := fun i : T.index ↦ P.interior (T.core i)
  let U : Set G := {g | ∃ i, g ∈ S i}
  have hex (g : U) : ∃ i, (g : G) ∈ S i := g.property
  choose label hLabel using hex
  let cell (g : G) := if hg : g ∈ U then S (label ⟨g, hg⟩) else P.cell g
  have hAssign (i : T.index) {g : G} (hg : g ∈ S i) : cell g = S i := by
    have hU : g ∈ U := ⟨i, hg⟩
    simp only [cell, hU, dite_true]
    have heq : label ⟨g, hU⟩ = i := by
      by_contra hn
      exact Finset.disjoint_left.mp (T.disjoint_core hn)
        (P.interior_subset _ (hLabel ⟨g, hU⟩)) (P.interior_subset _ hg)
    rw [heq]
  have hOutside {g h : G} (hg : g ∉ U) (hh : h ∈ P.cell g) : h ∉ U := by
    rintro ⟨i, hi⟩
    apply hg
    refine ⟨i, (P.mem_interior_iff).mpr ?_⟩
    rw [← P.cell_eq hh]
    exact P.mem_interior_iff.mp hi
  have hCoarsen (g : G) : P.cell g ⊆ cell g := by
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hg
      rw [hAssign i hi]
      intro h hh
      exact P.mem_interior_iff.mpr ((P.cell_eq hh).symm ▸ P.mem_interior_iff.mp hi)
    · simp [cell, hg]
  have hMem (g : G) : g ∈ cell g := hCoarsen g (P.mem_cell g)
  have hSame {g h : G} (hh : h ∈ cell g) : cell h = cell g := by
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hg
      rw [hAssign i hi] at hh ⊢
      exact hAssign i hh
    · have hhP : h ∈ P.cell g := by simpa [cell, hg] using hh
      simpa [cell, hg, hOutside hg hhP] using P.cell_eq hhP
  let Q : BoundedTilePartition G :=
    { cell := cell, mem_cell := hMem, cell_eq := hSame,
      displacements := P.displacements ∪ T.displacements,
      mem_displacements := by
        intro g h hh
        by_cases hg : g ∈ U
        · obtain ⟨i, hi⟩ := hg
          rw [hAssign i hi] at hh
          exact Finset.mem_union_right _ (T.mem_displacements i (T.core_subset i (P.interior_subset _ hi))
            (T.core_subset i (P.interior_subset _ hh)))
        · exact Finset.mem_union_left _ (P.mem_displacements (by simpa [cell, hg] using hh)) }
  refine ⟨Q, hCoarsen, ?_, ?_⟩
  · intro g h hh
    change g ∉ U ↔ h ∉ U
    by_cases hg : g ∈ U
    · obtain ⟨i, hi⟩ := hg
      change h ∈ cell g at hh
      rw [hAssign i hi] at hh
      exact ⟨fun hn ↦ (hn ⟨i, hi⟩).elim, fun hn ↦ (hn ⟨i, hh⟩).elim⟩
    · exact ⟨fun hng ↦ hOutside hng (by simpa [Q, cell, hg] using hh), fun _ ↦ hg⟩
  · intro g hg
    have hg' : g ∈ U := Classical.not_not.mp hg
    obtain ⟨i, hi⟩ := hg'
    exact ⟨i, hi, hAssign i hi⟩

/-- Discarding old cells that cross a core boundary loses only near-boundary sites or
sites near a point removed in the original trimming. -/
theorem card_sdiff_interior_le (T : PartialQuasiTiling G η) (P : BoundedTilePartition G)
    (i : T.index) (hi : (T.core i).Nonempty) :
    (((tileTranslate (T.shape i) (T.center i)) \ P.interior (T.core i)).card : ℝ) ≤
      ((1 + P.displacements.card) * η) * (T.shape i).card +
        ((leftBoundary P.displacements (T.shape i)).card : ℝ) := by
  let A := tileTranslate (T.shape i) (T.center i)
  let R := T.core i
  let B := A \ R
  let L := leftBoundary P.displacements A
  let E := P.displacements.biUnion (fun d ↦ B.image (d⁻¹ * ·))
  have hSub : A \ P.interior R ⊆ (B ∪ E) ∪ L := by
    intro g hg
    obtain ⟨hgA, hgLost⟩ := Finset.mem_sdiff.mp hg
    by_cases hR : g ∈ R
    · obtain ⟨h, hhP, hhR⟩ := Finset.not_subset.mp (fun h ↦ hgLost (P.mem_interior_iff.mpr h))
      have hMove := P.mem_displacements hhP
      by_cases hhA : h ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨h * g⁻¹, hMove, Finset.mem_image.mpr ⟨h, Finset.mem_sdiff.mpr ⟨hhA, hhR⟩, by simp⟩⟩))
      · exact Finset.mem_union_right _ (mem_leftBoundary.mpr
          ⟨hgA, h * g⁻¹, hMove, by simpa using hhA⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hgA, hR⟩))
  have hCard : (A \ P.interior R).card ≤ B.card + P.displacements.card * B.card + L.card := by
    have hE : E.card ≤ P.displacements.card * B.card :=
      Finset.card_biUnion_le_card_mul _ _ _ fun _ _ ↦ Finset.card_image_le
    exact (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_union_le _ _) (le_refl _)) |>.trans
      (add_le_add (add_le_add (le_refl _) hE) (le_refl _)))
  have hB : (B.card : ℝ) ≤ η * (T.shape i).card := by
    have he := Finset.card_sdiff_add_card_eq_card (T.core_subset i)
    rw [card_tileTranslate] at he
    have he' : (B.card : ℝ) + (R.card : ℝ) = (T.shape i).card := by exact_mod_cast he
    linarith [T.core_card i hi]
  have hL : L.card = (leftBoundary P.displacements (T.shape i)).card := by
    simp only [L, A, leftBoundary_tileTranslate, card_tileTranslate]
  have hCardR : ((A \ P.interior R).card : ℝ) ≤ B.card + P.displacements.card * (B.card : ℝ) + L.card := by
    exact_mod_cast hCard
  rw [hL] at hCardR
  linarith [mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg P.displacements.card : (0 : ℝ) ≤ _)]

/-- Compare the loss from coarsening on a finite region with the total loss of the
cores contained in the region. Cores crossing the region boundary are counted separately. -/
theorem finiteFraction_exceptional_le (T : PartialQuasiTiling G η) (P : BoundedTilePartition G)
    (A : Finset G) (hA : A.Nonempty) {loss : ℝ} (hloss : 0 ≤ loss)
    (hLoss : ∀ i, (T.core i).Nonempty →
      (((T.core i) \ P.interior (T.core i)).card : ℝ) ≤ loss * (T.core i).card) :
    finiteFraction A (T.exceptional P) ≤ finiteFraction A T.coveredᶜ +
      ((leftBoundary T.displacements A).card : ℝ) / A.card + loss := by
  let B := leftBoundary T.displacements A
  let W := (A \ B).filter (· ∈ T.covered)
  have hex (g : W) : ∃ i, (g : G) ∈ T.core i := by
    have hg : (g : G) ∈ T.covered := (Finset.mem_filter.mp g.property).2
    rw [T.covered_eq, Set.mem_iUnion] at hg
    exact hg
  choose label hLabel using hex
  let cores := W.attach.image (fun g : W ↦ T.core (label g))
  have hActive (R : Finset G) (hR : R ∈ cores) : ∃ i, R = T.core i ∧ R.Nonempty ∧ R ⊆ A := by
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hR
    have hg := (Finset.mem_filter.mp g.property).1
    refine ⟨label g, rfl, ⟨_, hLabel g⟩, fun z hz ↦ ?_⟩
    by_contra hOut
    have hMove := T.mem_displacements (label g) (T.core_subset _ (hLabel g)) (T.core_subset _ hz)
    exact (Finset.mem_sdiff.mp hg).2 (mem_leftBoundary.mpr
      ⟨(Finset.mem_sdiff.mp hg).1, z * (g : G)⁻¹, hMove, by simpa using hOut⟩)
  have hPair : (↑cores : Set (Finset G)).PairwiseDisjoint id := by
    intro R hR S hS hne
    obtain ⟨i, rfl, _, _⟩ := hActive R hR
    obtain ⟨j, rfl, _, _⟩ := hActive S hS
    exact T.disjoint_core (fun he ↦ hne (congrArg T.core he))
  have hSum : (∑ R ∈ cores, R.card) ≤ A.card := by
    have he := Finset.card_biUnion hPair
    change (cores.biUnion id).card = ∑ R ∈ cores, R.card at he
    rw [← he]
    refine Finset.card_le_card (Finset.biUnion_subset.mpr ?_)
    intro R hR
    obtain ⟨_, _, _, hSub⟩ := hActive R hR
    exact hSub
  let E := A.filter (· ∈ T.coveredᶜ)
  let L := cores.biUnion (fun R ↦ R \ P.interior R)
  have hSub : A.filter (· ∈ T.exceptional P) ⊆ (E ∪ B) ∪ L := by
    intro g hg
    obtain ⟨hgA, hgBad⟩ := Finset.mem_filter.mp hg
    by_cases hgU : g ∈ T.covered
    · by_cases hgB : g ∈ B
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hgB)
      · let x : W := ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hgA, hgB⟩, hgU⟩⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨T.core (label x), Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩,
            Finset.mem_sdiff.mpr ⟨hLabel x, fun hd ↦ hgBad ⟨label x, hd⟩⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgA, hgU⟩))
  have hLCast : (L.card : ℝ) ≤ loss * (A.card : ℝ) := by
    calc
      _ ≤ ∑ R ∈ cores, (((R \ P.interior R).card : ℕ) : ℝ) := by
        exact_mod_cast (show L.card ≤ ∑ R ∈ cores, (R \ P.interior R).card from Finset.card_biUnion_le)
      _ ≤ ∑ R ∈ cores, loss * (R.card : ℝ) := by
        refine Finset.sum_le_sum fun R hR ↦ ?_
        obtain ⟨i, rfl, hn, _⟩ := hActive R hR
        exact hLoss i hn
      _ = loss * ∑ R ∈ cores, (R.card : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hSum) hloss
  have hNat : (A.filter (· ∈ T.exceptional P)).card ≤ E.card + B.card + L.card :=
    (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_union_le _ _) (le_refl _)))
  have hReal : ((A.filter (· ∈ T.exceptional P)).card : ℝ) ≤ E.card + B.card + L.card := by
    exact_mod_cast hNat
  have hCard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  have h := div_le_div_of_nonneg_right (hReal.trans (add_le_add (le_refl _) hLCast))
    (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
  rw [add_div, add_div, mul_div_assoc, div_self hCard, mul_one] at h
  rw [finiteFraction_eq_filter A (T.exceptional P) (fun _ ↦ inferInstance),
    finiteFraction_eq_filter A T.coveredᶜ (fun _ ↦ inferInstance)]
  exact h

/-- Prescribing a small loss in each core and a small uncovered fraction gives a small
eventual density for the exceptional cells of the coarsened partition. -/
theorem eventually_exceptional (T : PartialQuasiTiling G η) (P : BoundedTilePartition G)
    (F : LeftFolnerSequence G) {a loss ε : ℝ} (hloss : 0 ≤ loss) (hε : 0 < ε)
    (hLoss : ∀ i, (T.core i).Nonempty →
      (((T.core i) \ P.interior (T.core i)).card : ℝ) ≤ loss * (T.core i).card)
    (hCovered : ∀ᶠ n in atTop, finiteFraction (F.blocks n) T.coveredᶜ < a) :
    ∀ᶠ n in atTop, finiteFraction (F.blocks n) (T.exceptional P) < a + loss + ε := by
  filter_upwards [hCovered, (F.tendsto_leftBoundary T.displacements).eventually_lt_const hε] with n hC hB
  exact (T.finiteFraction_exceptional_le P _ (F.nonempty n) hloss hLoss).trans_lt (by linarith)

end PartialQuasiTiling

end SixProblems
end

/- Source module SixProblems.CorrespondenceModelCoarsening. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter
open scoped Classical Topology

variable {G K : Type*} [Group G] [DecidableEq G] [Countable G] [Nonempty K]

omit [Countable G] in
private theorem leftBoundary_mono_support (A : Finset G) {D E : Finset G} (h : D ⊆ E) :
    leftBoundary D A ⊆ leftBoundary E A := by
  intro g hg
  obtain ⟨hgA, d, hd, hdA⟩ := mem_leftBoundary.mp hg
  exact mem_leftBoundary.mpr ⟨hgA, d, h hd, hdA⟩

/-- Refine the approximation accuracy by grouping whole prior cells. Large Følner
blocks bearing local models become the shapes of the new cells. Cells that could
not be grouped are allowed on a set of arbitrarily small eventual density. -/
theorem exists_modelCoarsening {ι : Type*} (F : LeftFolnerSequence G) (P : BoundedTilePartition G)
    (I : Finset ι) (support : ι → Finset G) (q : ι → (G → K) → G → ℝ) {C τ δ : ℝ}
    (hC : 0 ≤ C) (hτ : 0 < τ) (hδ : 0 < δ)
    (hBound : ∀ i ∈ I, ∀ x g, ‖q i x g‖ ≤ C)
    (hTranslate : ∀ i ∈ I, ∀ c (x : G → K) g, q i (fun h ↦ x (h * c⁻¹)) (g * c) = q i x g)
    (hModels : ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ∈ I,
      ‖finiteAverage (F.blocks n) (q i x)‖ ≤ τ / 2) :
    ∃ (Q : BoundedTilePartition G) (bad : Set G) (sample : Finset G → G → K),
      (∀ g, P.cell g ⊆ Q.cell g) ∧
      (∀ g h, h ∈ Q.cell g → (g ∈ bad ↔ h ∈ bad)) ∧
      (∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ δ) ∧
      (∀ g ∉ bad, ∀ i ∈ I, ‖finiteAverage (Q.cell g) (q i (sample (Q.cell g)))‖ ≤ τ) ∧
      (∀ g ∉ bad, ∀ i ∈ I, ((leftBoundary (support i) (Q.cell g)).card : ℝ) / (Q.cell g).card ≤ τ) := by
  let D := I.biUnion support
  let E := D ∪ P.displacements
  let c : ℝ := 1 + C + D.card
  have hc : 0 < c := by dsimp [c]; positivity
  let r := min (1 / 4 : ℝ) (min (δ / 8) (τ / (4 * c)))
  have hr : 0 < r := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hrOne : r ≤ 1 / 4 := min_le_left _ _
  have hrδ : r ≤ δ / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hrτ : r * (4 * c) ≤ τ := (le_div_iff₀ (by positivity : 0 < 4 * c)).mp
    ((min_le_right _ _).trans (min_le_right _ _))
  let η := r / (2 * (1 + (P.displacements.card : ℝ)))
  let θ := r / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηHalf : η ≤ 1 / 2 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + (P.displacements.card : ℝ)))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) P.displacements.card]
  have hθ : 0 < θ := half_pos hr
  have hIdentity : (1 + (P.displacements.card : ℝ)) * η + θ = r := by
    dsimp [η, θ]
    field_simp
    norm_num
  let allowed : Set (Finset G) := {S | S.Nonempty ∧
    ((leftBoundary E S).card : ℝ) ≤ θ * S.card ∧
    ∃ x : G → K, ∀ i ∈ I, ‖finiteAverage S (q i x)‖ ≤ τ / 2}
  have hAvailable (A : Finset G) (ε : ℝ) (hε : 0 < ε) : ∃ S ∈ allowed, S.Nonempty ∧
      ((externalBoundary A S).card : ℝ) ≤ ε * S.card := by
    obtain ⟨n, hmodel, hLeft, hExt⟩ :=
      (hModels.and (((F.tendsto_leftBoundary E).eventually_lt_const hθ).and
        ((F.tendsto_externalBoundary A).eventually_lt_const hε))).exists
    have hn : (0 : ℝ) < (F.blocks n).card := by exact_mod_cast (F.nonempty n).card_pos
    exact ⟨F.blocks n, ⟨F.nonempty n, ((div_lt_iff₀ hn).mp hLeft).le, hmodel⟩,
      F.nonempty n, ((div_lt_iff₀ hn).mp hExt).le⟩
  obtain ⟨T, hAllowed, hCovered⟩ := PartialQuasiTiling.exists_eventually_cover F allowed hη
    (by linarith : η < 1) (by positivity : 0 < δ / 4) hAvailable
  let excess (i : T.index) := tileTranslate (T.shape i) (T.center i) \ P.interior (T.core i)
  have hExcess (i : T.index) (hi : (T.core i).Nonempty) :
      ((excess i).card : ℝ) ≤ r * (T.shape i).card := by
    have he := T.card_sdiff_interior_le P i hi
    have hLeft : ((leftBoundary P.displacements (T.shape i)).card : ℝ) ≤ θ * (T.shape i).card :=
      (Nat.cast_le.mpr (Finset.card_le_card
        (leftBoundary_mono_support (T.shape i) (Finset.subset_union_right : P.displacements ⊆ E)))).trans
          (hAllowed (T.shape i) (T.shape_mem i)).2.1
    calc
      _ ≤ ((1 + (P.displacements.card : ℝ)) * η) * (T.shape i).card + θ * (T.shape i).card :=
        he.trans (add_le_add (le_refl _) hLeft)
      _ = _ := by rw [← add_mul, hIdentity]
  have hLoss (i : T.index) (hi : (T.core i).Nonempty) :
      (((T.core i) \ P.interior (T.core i)).card : ℝ) ≤ (2 * r) * (T.core i).card := by
    have hCore : (T.shape i).card ≤ 2 * ((T.core i).card : ℝ) := by
      linarith [T.core_card i hi, mul_le_mul_of_nonneg_right hηHalf (Nat.cast_nonneg (α := ℝ) (T.shape i).card)]
    calc
      _ ≤ ((excess i).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card (fun g hg ↦ by
        obtain ⟨hgR, hgOut⟩ := Finset.mem_sdiff.mp hg
        exact Finset.mem_sdiff.mpr ⟨T.core_subset i hgR, hgOut⟩))
      _ ≤ r * (T.shape i).card := hExcess i hi
      _ ≤ r * (2 * ((T.core i).card : ℝ)) := mul_le_mul_of_nonneg_left hCore hr.le
      _ = _ := by ring
  obtain ⟨Q, hCoarsen, hConstant, hGood⟩ := T.exists_coarsening P
  let bad := T.exceptional P
  have hBad : ∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ δ := by
    have h := T.eventually_exceptional P F (a := δ / 4) (loss := 2 * r) (ε := δ / 4)
      (by positivity) (by positivity) hLoss hCovered
    exact h.mono fun n hn ↦ hn.le.trans (by linarith)
  have hModel (g : G) (hg : g ∉ bad) :
      (∃ x, ∀ j ∈ I, ‖finiteAverage (Q.cell g) (q j x)‖ ≤ τ) ∧
      ∀ j ∈ I, ((leftBoundary (support j) (Q.cell g)).card : ℝ) / (Q.cell g).card ≤ τ := by
    obtain ⟨i, hgi, hCell⟩ := hGood g hg
    let S := T.shape i
    let A := tileTranslate S (T.center i)
    let B := P.interior (T.core i)
    have hB : B.Nonempty := ⟨g, hgi⟩
    have hBA : B ⊆ A := (P.interior_subset _).trans (T.core_subset i)
    have hAS : A.card = S.card := card_tileTranslate _ _
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast (hB.mono hBA).card_pos
    have hi : (T.core i).Nonempty := ⟨g, P.interior_subset _ hgi⟩
    have hAB : (((A \ B).card : ℕ) : ℝ) ≤ r * A.card := by rw [hAS]; exact hExcess i hi
    have hABden : (((A \ B).card : ℕ) : ℝ) / A.card ≤ r := (div_le_iff₀ hApos).mpr hAB
    have hSize : ((A.card : ℕ) : ℝ) ≤ 2 * (B.card : ℝ) := by
      have he : (((A \ B).card : ℕ) : ℝ) + B.card = A.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hBA
      linarith [mul_le_mul_of_nonneg_right hrOne hApos.le]
    obtain ⟨_, hBoundary, x, hx⟩ := hAllowed S (T.shape_mem i)
    let z : G → K := fun a ↦ x (a * (T.center i)⁻¹)
    rw [hCell]
    refine ⟨⟨z, ?_⟩, ?_⟩
    · intro j hj
      have hAvgEq : finiteAverage A (q j z) = finiteAverage S (q j x) := by
        rw [finiteAverage, finiteAverage, hAS]
        congr 1
        change (∑ a ∈ S.image (· * T.center i), q j z a) = ∑ a ∈ S, q j x a
        rw [Finset.sum_image (fun _ _ _ _ he ↦ mul_right_cancel he)]
        exact Finset.sum_congr rfl fun a _ ↦ hTranslate j hj (T.center i) x a
      have hDist := (norm_finiteAverage_sub_of_subset hBA hB (q j z) (hBound j hj z)).trans
        (mul_le_mul_of_nonneg_left hABden (mul_nonneg (by norm_num) hC))
      have hComp : 2 * C * r ≤ τ / 2 := by
        dsimp [c] at hrτ
        nlinarith [mul_nonneg hr.le (Nat.cast_nonneg (α := ℝ) D.card)]
      calc
        _ = ‖(finiteAverage B (q j z) - finiteAverage A (q j z)) +
            finiteAverage A (q j z)‖ := by rw [sub_add_cancel]
        _ ≤ ‖finiteAverage B (q j z) - finiteAverage A (q j z)‖ +
            ‖finiteAverage A (q j z)‖ := norm_add_le _ _
        _ ≤ 2 * C * r + τ / 2 := by
          apply add_le_add
          · rw [norm_sub_rev]
            exact hDist
          · rw [hAvgEq]
            exact hx j hj
        _ ≤ τ := by linarith
    · intro j hj
      have hDE : support j ⊆ D := fun d hd ↦ Finset.mem_biUnion.mpr ⟨j, hj, hd⟩
      have hDcard : ((support j).card : ℝ) ≤ D.card := Nat.cast_le.mpr (Finset.card_le_card hDE)
      have hAleft : ((leftBoundary (support j) A).card : ℝ) ≤ θ * A.card := by
        rw [show A = _ from rfl, leftBoundary_tileTranslate, card_tileTranslate, card_tileTranslate]
        exact (Nat.cast_le.mpr (Finset.card_le_card (leftBoundary_mono_support S
          (hDE.trans (Finset.subset_union_left : D ⊆ E))))).trans hBoundary
      have hBorder : ((leftBoundary (support j) B).card : ℝ) ≤
          θ * A.card + (D.card : ℝ) * (r * A.card) := by
        have hNat := card_leftBoundary_le_of_subset (support j) hBA
        have hCast : ((leftBoundary (support j) B).card : ℝ) ≤
            (leftBoundary (support j) A).card + (support j).card * (((A \ B).card : ℕ) : ℝ) := by
          exact_mod_cast hNat
        exact hCast.trans (add_le_add hAleft (mul_le_mul hDcard hAB (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      apply (div_le_iff₀ hBpos).mpr
      have hLast : 2 * (θ + (D.card : ℝ) * r) ≤ τ := by
        dsimp [θ, c] at *
        nlinarith [mul_nonneg hr.le hC, mul_nonneg hr.le (Nat.cast_nonneg (α := ℝ) D.card)]
      calc
        _ ≤ (θ + (D.card : ℝ) * r) * A.card := hBorder.trans (le_of_eq (by ring))
        _ ≤ (θ + (D.card : ℝ) * r) * (2 * (B.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hSize (by positivity)
        _ = (2 * (θ + (D.card : ℝ) * r)) * (B.card : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hLast hBpos.le
  let sample (B : Finset G) : G → K :=
    if h : ∃ x, ∀ j ∈ I, ‖finiteAverage B (q j x)‖ ≤ τ then Classical.choose h else fun _ ↦ Classical.ofNonempty
  refine ⟨Q, bad, sample, hCoarsen, hConstant, hBad, ?_, fun g hg ↦ (hModel g hg).2⟩
  intro g hg
  have h := (hModel g hg).1
  simpa only [sample, h, dite_true] using Classical.choose_spec h

omit [Countable G] in
/-- The finest partition, used to start a sequence of coarsenings. -/
def singletonTilePartition (G : Type*) [Group G] [DecidableEq G] : BoundedTilePartition G where
  cell g := {g}
  mem_cell g := Finset.mem_singleton_self g
  cell_eq h := by rw [Finset.mem_singleton.mp h]
  displacements := {1}
  mem_displacements h := by rw [Finset.mem_singleton.mp h]; simp

/-- A bounded partition with small cylinder boundaries apart from exceptional
cells of arbitrarily small eventual density. The construction starts from singletons
and uses the coarsening theorem with a zero observable. -/
theorem exists_smallBoundaryTilePartition {ι : Type*} (F : LeftFolnerSequence G)
    (I : Finset ι) (support : ι → Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : BoundedTilePartition G) (bad : Set G),
      (∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ ε) ∧
      (∀ i ∈ I, ∀ g ∉ bad,
        ((leftBoundary (support i) (P.cell g)).card : ℝ) ≤ ε * (P.cell g).card) := by
  have hModels : ∀ᶠ n in atTop, ∃ x : G → Unit, ∀ i ∈ I,
      ‖finiteAverage (F.blocks n) (fun _ ↦ (0 : ℝ))‖ ≤ ε / 2 :=
    Filter.Eventually.of_forall fun _ ↦ ⟨fun _ ↦ (), fun _ _ ↦ by
      simpa [finiteAverage] using (half_pos hε).le⟩
  obtain ⟨P, bad, _, _, _, hBad, _, hBoundary⟩ := exists_modelCoarsening F
    (singletonTilePartition G) I support (fun _ (_ : G → Unit) _ ↦ 0) (C := 0) (τ := ε) (δ := ε)
    (le_refl 0) hε hε (by simp) (by simp) hModels
  refine ⟨P, bad, hBad, fun i hi g hg ↦ ?_⟩
  have hCard : (0 : ℝ) < (P.cell g).card := by
    exact_mod_cast (Finset.Nonempty.card_pos ⟨g, P.mem_cell g⟩)
  exact (div_le_iff₀ hCard).mp (hBoundary g hg i hi)

/-- Iterate the coarsening construction so that both the model accuracies and the
exceptional-site bounds have the required decay as the number of tests grows. -/
theorem exists_congruentModelCoarsenings (F : LeftFolnerSequence G)
    (support : ℕ → Finset G) (q : ℕ → (G → K) → G → ℝ) (C : ℕ → ℝ)
    (hC : ∀ k, 0 ≤ C k)
    (hNorm : ∀ k i, i ≤ k → ∀ x g, ‖q i x g‖ ≤ C k)
    (hTranslate : ∀ i c (x : G → K) g, q i (fun h ↦ x (h * c⁻¹)) (g * c) = q i x g)
    (hModels : ∀ k, ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ≤ k,
      ‖finiteAverage (F.blocks n) (q i x)‖ ≤ (1 / ((k : ℝ) + 1)) / 2) :
    ∃ (P : ℕ → BoundedTilePartition G) (bad : ℕ → Set G) (sample : ℕ → Finset G → G → K),
      (∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g) ∧
      (∀ k g h, h ∈ (P k).cell g → (g ∈ bad k ↔ h ∈ bad k)) ∧
      (∀ k, ∀ᶠ n in atTop, finiteFraction (F.blocks n) (bad k) ≤ (1 / 2 : ℝ) ^ k) ∧
      (∀ k g, g ∉ bad k → ∀ i ≤ k,
        ‖finiteAverage ((P k).cell g) (q i (sample k ((P k).cell g)))‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ k g, g ∉ bad k → ∀ i ≤ k,
        ((leftBoundary (support i) ((P k).cell g)).card : ℝ) / ((P k).cell g).card ≤ 1 / ((k : ℝ) + 1)) := by
  let τ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let δ (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
  have hStep (k : ℕ) (P : BoundedTilePartition G) :
      ∃ (Q : BoundedTilePartition G) (bad : Set G) (sample : Finset G → G → K),
        (∀ g, P.cell g ⊆ Q.cell g) ∧
        (∀ g h, h ∈ Q.cell g → (g ∈ bad ↔ h ∈ bad)) ∧
        (∀ᶠ n in atTop, finiteFraction (F.blocks n) bad ≤ δ k) ∧
        (∀ g ∉ bad, ∀ i ≤ k, ‖finiteAverage (Q.cell g) (q i (sample (Q.cell g)))‖ ≤ τ k) ∧
        (∀ g ∉ bad, ∀ i ≤ k, ((leftBoundary (support i) (Q.cell g)).card : ℝ) / (Q.cell g).card ≤ τ k) := by
    have hRange (i : ℕ) : i ∈ Finset.range (k + 1) ↔ i ≤ k := Finset.mem_range.trans Nat.lt_succ_iff
    have hInput : ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ∈ Finset.range (k + 1),
        ‖finiteAverage (F.blocks n) (q i x)‖ ≤ τ k / 2 :=
      (hModels k).mono fun _ ⟨x, hx⟩ ↦ ⟨x, fun i hi ↦ hx i ((hRange i).mp hi)⟩
    obtain ⟨Q, bad, sample, hCoarsen, hConstant, hDensity, hTest, hBorder⟩ :=
      exists_modelCoarsening F P (Finset.range (k + 1)) support q (hC k)
        (show 0 < τ k by dsimp [τ]; positivity) (show 0 < δ k by dsimp [δ]; positivity)
        (fun i hi ↦ hNorm k i ((hRange i).mp hi)) (fun i _ ↦ hTranslate i) hInput
    exact ⟨Q, bad, sample, hCoarsen, hConstant, hDensity,
      fun g hg i hi ↦ hTest g hg i ((hRange i).mpr hi),
      fun g hg i hi ↦ hBorder g hg i ((hRange i).mpr hi)⟩
  choose next bad sample hCoarsen hConstant hDensity hTest hBorder using hStep
  let prev : ℕ → BoundedTilePartition G := Nat.rec (singletonTilePartition G) next
  let P (k : ℕ) := next k (prev k)
  exact ⟨P, fun k ↦ bad k (prev k), fun k ↦ sample k (prev k),
    fun k ↦ hCoarsen (k + 1) (prev (k + 1)), fun k ↦ hConstant k (prev k),
    fun k ↦ hDensity k (prev k), fun k ↦ hTest k (prev k), fun k ↦ hBorder k (prev k)⟩

end SixProblems
end

/- Source module SixProblems.Correspondence. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter MeasureTheory Mixing
open scoped Topology BoundedContinuousFunction

variable {G K : Type} [Group G] [DecidableEq G]
variable [Group K] [MetricSpace K] [CompactSpace K] [IsTopologicalGroup K]
variable [MeasurableSpace K] [BorelSpace K]

/-- Uniform distribution of a configuration along the prescribed Følner sequence.
Real tests suffice since a complex test splits into its real and imaginary parts. -/
def IsFolnerUniformlyDistributed (F : LeftFolnerSequence G) (x : G → K)
    (m : Measure K) : Prop :=
  ∀ f : C(K, ℝ), Tendsto (fun n ↦ finiteAverage (F.blocks n) (f ∘ x))
    atTop (𝓝 (∫ k, f k ∂m))

omit [Group K] [IsTopologicalGroup K] in
private theorem empiricalLaw_tendsto_iff_distribution_tests (𝕜 : Type*) [RCLike 𝕜]
    (F : LeftFolnerSequence G) (x : G → K) (m : ProbabilityMeasure K) :
    Tendsto (fun n ↦ finiteEmpiricalLaw (F.blocks n) (F.nonempty n) x) atTop (𝓝 m) ↔
    ∀ f : C(K, 𝕜), Tendsto (fun n ↦ finiteAverage (F.blocks n) (f ∘ x))
      atTop (𝓝 (∫ k, f k ∂(m : Measure K))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜]
  simp only [integral_finiteEmpiricalLaw]
  constructor
  · intro h f
    exact h (BoundedContinuousFunction.mkOfCompact f)
  · intro h f
    exact h f.toContinuousMap

omit [Group K] [IsTopologicalGroup K] in
/-- Testing real continuous functions is equivalent to the paper's complex test convention. -/
theorem isFolnerUniformlyDistributed_iff_complex_tests (F : LeftFolnerSequence G) (x : G → K)
    (m : Measure K) [IsProbabilityMeasure m] :
    IsFolnerUniformlyDistributed F x m ↔
    ∀ f : C(K, ℂ), Tendsto (fun n ↦ finiteAverage (F.blocks n) (f ∘ x))
      atTop (𝓝 (∫ k, f k ∂m)) := by
  let ν : ProbabilityMeasure K := ⟨m, inferInstance⟩
  exact (empiricalLaw_tendsto_iff_distribution_tests ℝ F x ν).symm.trans
    (empiricalLaw_tendsto_iff_distribution_tests ℂ F x ν)

/-- The sequence formulation of compact-group van der Corput sets, Definition 4.7. -/
def IsFolnerVdC (F : LeftFolnerSequence G) (R : Set G) (m : Measure K) : Prop :=
  ∀ x : G → K, (∀ h ∈ R, IsFolnerUniformlyDistributed F (fun g ↦ x (h * g) * (x g)⁻¹) m) →
    IsFolnerUniformlyDistributed F x m

/-- The continuous left action on the full shift, expressed by right multiplication
on the coordinates. -/
def correspondenceShift (a : G) : C(G → K, G → K) :=
  ⟨fun x b ↦ x (b * a), continuous_pi fun b ↦ continuous_apply (b * a)⟩

omit [DecidableEq G] [Group K] [CompactSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
  [BorelSpace K] in
@[simp] theorem correspondenceShift_apply (a b : G) (x : G → K) :
    correspondenceShift a x b = x (b * a) := rfl

/-- The identity-coordinate factor on the full shift of the group. -/
def correspondenceOrigin : C(G → K, K) :=
  ⟨fun x ↦ x 1, continuous_apply 1⟩

/-- The pair correlation coordinate with the article's order of multiplication. -/
def correspondenceDifference (h : G) : C(G → K, K) :=
  ⟨fun x ↦ x h * (x 1)⁻¹, (continuous_apply h).mul (continuous_apply 1).inv⟩

private theorem measure_eq_of_continuous_tests {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure Y) [μ.Regular] [ν.Regular]
    (h : ∀ f : C(Y, ℝ), ∫ y, f y ∂μ = ∫ y, f y ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact h f.toContinuousMap

variable [Countable G]

/-- The empirical probability measures of a configuration on the given left Følner blocks. -/
def correspondenceOrbitLaw (F : LeftFolnerSequence G) (x : G → K) (n : ℕ) :
    ProbabilityMeasure (G → K) :=
  finiteEmpiricalLaw (F.blocks n) (F.nonempty n) (fun g ↦ correspondenceShift g x)

omit [Group K] [IsTopologicalGroup K] in
private theorem correspondenceShift_invariant_of_limit (F : LeftFolnerSequence G) (x : G → K)
    {p : Ultrafilter ℕ} (hp : (p : Filter ℕ) ≤ atTop) {ν : ProbabilityMeasure (G → K)}
    (hν : Tendsto (correspondenceOrbitLaw F x) p (𝓝 ν)) (a : G) :
    MeasurePreserving (correspondenceShift a) (ν : Measure (G → K)) (ν : Measure (G → K)) := by
  have hcont : Continuous (correspondenceShift a : (G → K) → (G → K)) :=
    (correspondenceShift a).continuous
  refine ⟨hcont.measurable, ?_⟩
  apply measure_eq_of_continuous_tests
  intro f
  rw [integral_map hcont.aemeasurable f.continuous.aestronglyMeasurable]
  let b : (G → K) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact f
  have hcl : MapClusterPt ν atTop (correspondenceOrbitLaw F x) :=
    mapClusterPt_iff_ultrafilter.mpr ⟨p, hp, hν⟩
  apply ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt hcont hcl (g := b)
  let w : G → ℝ := fun g ↦ f (correspondenceShift g x)
  have hw (g : G) : ‖w g‖ ≤ ‖f‖ := ContinuousMap.norm_coe_le_norm f _
  have h := F.tendsto_average_sub_translate a w ‖f‖ hw
  refine h.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  simp only [correspondenceOrbitLaw, integral_finiteEmpiricalLaw]
  congr 2
  · funext g
    change f (correspondenceShift (a * g) x) = f (correspondenceShift a (correspondenceShift g x))
    congr 1
    funext j
    simp [mul_assoc]

private def correspondenceShiftSystem (ν : ProbabilityMeasure (G → K))
    (hν : ∀ a : G, MeasurePreserving (correspondenceShift a)
      (ν : Measure (G → K)) (ν : Measure (G → K))) : System G (G → K) where
  measure := ν
  probability := inferInstance
  act := fun a ↦ correspondenceShift a
  act_one := by funext x b; simp
  act_mul := by
    intro g h
    funext x b
    simp [mul_assoc]
  preserves := hν

/-- Every empirical limit of the coordinate (x_h x_1^{-1}) has the prescribed law
if the difference configuration is uniformly distributed. -/
private theorem correspondenceDifference_map_of_limit
    (F : LeftFolnerSequence G) (x : G → K) (m : Measure K) [IsProbabilityMeasure m] (h : G)
    (hx : IsFolnerUniformlyDistributed F (fun g ↦ x (h * g) * (x g)⁻¹) m)
    {p : Ultrafilter ℕ} (hp : (p : Filter ℕ) ≤ atTop) {ν : ProbabilityMeasure (G → K)}
    (hν : Tendsto (correspondenceOrbitLaw F x) p (𝓝 ν)) :
    (ν : Measure (G → K)).map (correspondenceDifference h) = m := by
  have hc : Continuous (correspondenceDifference h : (G → K) → K) :=
    (correspondenceDifference h).continuous
  apply measure_eq_of_continuous_tests
  intro f
  let b : (G → K) →ᵇ ℝ := (BoundedContinuousFunction.mkOfCompact f).compContinuous
    (correspondenceDifference h)
  rw [integral_map hc.aemeasurable f.continuous.aestronglyMeasurable]
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) b
  have htest := (hx f).mono_left hp
  apply tendsto_nhds_unique _ htest
  refine hw.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  rw [correspondenceOrbitLaw, integral_finiteEmpiricalLaw]
  congr 1
  funext g
  change f (x (h * g) * (x (1 * g))⁻¹) = _
  simp only [one_mul, Function.comp_apply]

/-- The measure-theoretic formulation implies the Følner-sequence formulation.
This is the compactness direction of Theorem 4.8. -/
theorem folnerVdC_of_measureTheoretic (F : LeftFolnerSequence G) (R : Set G)
    (m : Measure K) [IsProbabilityMeasure m] (hm : IsMeasureTheoreticVdC R m) :
    IsFolnerVdC F R m := by
  intro x hx f
  rw [tendsto_iff_ultrafilter]
  intro p hp
  let v := correspondenceOrbitLaw F x
  let ν := (p.map v).lim
  have hν : Tendsto v p (𝓝 ν) := (p.map v).le_nhds_lim
  let S := correspondenceShiftSystem ν
    (correspondenceShift_invariant_of_limit F x hp hν)
  have hLaw : (ν : Measure (G → K)).map correspondenceOrigin = m := by
    apply hm S correspondenceOrigin correspondenceOrigin.continuous.measurable
    intro h hr
    have hfun : (fun x ↦ correspondenceOrigin (S.act h x) * (correspondenceOrigin x)⁻¹) =
        (correspondenceDifference h : (G → K) → K) := by funext y; simp [S, correspondenceShiftSystem,
      correspondenceOrigin, correspondenceDifference]
    rw [hfun]
    exact correspondenceDifference_map_of_limit F x m h (hx h hr) hp hν
  let b : (G → K) →ᵇ ℝ := (BoundedContinuousFunction.mkOfCompact f).compContinuous
    (correspondenceOrigin : C(G → K, K))
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) b
  have he : (∫ y, b y ∂(ν : Measure (G → K))) = ∫ y, f y ∂m := by
    change (∫ y, f (correspondenceOrigin y) ∂(ν : Measure (G → K))) = _
    rw [← integral_map correspondenceOrigin.continuous.aemeasurable
      f.continuous.aestronglyMeasurable, hLaw]
  rw [← he]
  refine hw.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  change (∫ y, b y ∂(correspondenceOrbitLaw F x n : Measure (G → K))) = _
  rw [correspondenceOrbitLaw, integral_finiteEmpiricalLaw]
  congr 1
  funext g
  change f (x (1 * g)) = _
  simp only [one_mul, Function.comp_apply]

end SixProblems
end

/- Source module SixProblems.CorrespondenceInverse. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter MeasureTheory Mixing
open scoped Topology BoundedContinuousFunction

variable {G K : Type} [Group G] [DecidableEq G] [Countable G]
variable [Group K] [MetricSpace K] [CompactSpace K] [IsTopologicalGroup K]
variable [MeasurableSpace K] [BorelSpace K]

/-- The inverse correspondence property of the full shift along a fixed sequence.
This asks for convergence along the entire sequence of Følner blocks. -/
def HasFolnerGenericRealizations (F : LeftFolnerSequence G) (K : Type) [TopologicalSpace K]
    [SecondCountableTopology K] [MeasurableSpace K] [OpensMeasurableSpace K] : Prop :=
  ∀ ν : ProbabilityMeasure (G → K),
    (∀ a : G, (ν : Measure (G → K)).map (fun x j ↦ x (j * a)) = (ν : Measure (G → K))) →
    ∃ x : G → K, Tendsto
      (fun n ↦ finiteEmpiricalLaw (F.blocks n) (F.nonempty n) (fun g j ↦ x (j * g)))
      atTop (𝓝 ν)

/-- The correspondence direction of Theorem 4.8, with the generic-realization
property stated explicitly. The property is used on the shift law of the
coordinate process associated to the proposed observable. -/
theorem measureTheoreticVdC_of_folnerVdC_of_genericRealizations (F : LeftFolnerSequence G)
    (hGen : HasFolnerGenericRealizations F K) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] (hm : IsFolnerVdC F R m) :
    IsMeasureTheoreticVdC R m := by
  intro X _ _ S f hf hDif
  let p : X → G → K := fun x g ↦ f (S.act g x)
  have hp : Measurable p := Measurable.of_eval fun g ↦ hf.comp (S.preserves g).measurable
  let μ := S.measure.map p
  let hProb : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  let ν : ProbabilityMeasure (G → K) := ⟨μ, hProb⟩
  have hInvariant (a : G) : μ.map (fun x j ↦ x (j * a)) = μ := by
    have hpShift : correspondenceShift (K := K) a ∘ p = p ∘ S.act a := by
      funext x g
      simp [p, S.act_mul]
    change (S.measure.map p).map (⇑(correspondenceShift (K := K) a)) = μ
    rw [Measure.map_map (correspondenceShift (K := K) a).continuous.measurable hp,
      hpShift, ← Measure.map_map hp (S.preserves a).measurable, (S.preserves a).map_eq]
  obtain ⟨x, hx⟩ := hGen ν hInvariant
  have : IsProbabilityMeasure (S.measure.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have hTest (u : C(G → K, ℝ)) : Tendsto
      (fun n ↦ finiteAverage (F.blocks n) (fun g ↦ u (correspondenceShift g x)))
      atTop (𝓝 (∫ y, u y ∂μ)) := by
    have hu := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hx)
      (BoundedContinuousFunction.mkOfCompact u)
    refine hu.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    rw [integral_finiteEmpiricalLaw]
    rfl
  have hGe (h : G) (hr : h ∈ R) :
      IsFolnerUniformlyDistributed F (fun g ↦ x (h * g) * (x g)⁻¹) m := by
    intro v
    have hv := hTest (v.comp (correspondenceDifference h))
    have hMap : μ.map (correspondenceDifference h) = m := by
      unfold μ
      rw [Measure.map_map (correspondenceDifference h).continuous.measurable hp]
      convert hDif h hr using 2
      funext y
      simp [p, correspondenceDifference, S.act_one]
    have hEnd : (∫ y, v (correspondenceDifference h y) ∂μ) = ∫ y, v y ∂m := by
      rw [← integral_map (correspondenceDifference h).continuous.aemeasurable
        v.continuous.aestronglyMeasurable, hMap]
    change Tendsto _ _ (𝓝 (∫ y, v (correspondenceDifference h y) ∂μ)) at hv
    rw [hEnd] at hv
    refine hv.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    congr 1
    funext g
    change v (x (h * g) * (x (1 * g))⁻¹) = _
    simp only [one_mul, Function.comp_apply]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro v
  have hv := hTest ((v.toContinuousMap).comp (correspondenceOrigin (G := G) (K := K)))
  have hMap : μ.map (correspondenceOrigin (G := G) (K := K)) = S.measure.map f := by
    unfold μ
    rw [Measure.map_map (correspondenceOrigin (G := G) (K := K)).continuous.measurable hp]
    congr 1
    funext y
    simp [p, correspondenceOrigin, S.act_one]
  have hEnd : (∫ y, v (correspondenceOrigin y) ∂μ) = ∫ y, v y ∂(S.measure.map f) := by
    change (∫ y, v.toContinuousMap (correspondenceOrigin y) ∂μ) =
      ∫ y, v.toContinuousMap y ∂(S.measure.map f)
    rw [← integral_map (correspondenceOrigin (G := G) (K := K)).continuous.aemeasurable
      v.continuous.aestronglyMeasurable, hMap]
  change Tendsto _ _ (𝓝 (∫ y, v (correspondenceOrigin y) ∂μ)) at hv
  rw [hEnd] at hv
  apply tendsto_nhds_unique _ (hm x hGe v.toContinuousMap)
  refine hv.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  congr 1
  funext g
  change v (x (1 * g)) = _
  rw [one_mul]
  rfl

/-- Theorem 4.8 under its explicit inverse-correspondence input. -/
theorem folnerVdC_iff_measureTheoretic_of_genericRealizations (F : LeftFolnerSequence G)
    (hGen : HasFolnerGenericRealizations F K) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] :
    IsFolnerVdC F R m ↔ IsMeasureTheoreticVdC R m :=
  ⟨measureTheoreticVdC_of_folnerVdC_of_genericRealizations F hGen R m,
    folnerVdC_of_measureTheoretic F R m⟩

end SixProblems
end

/- Source module SixProblems.CorrespondenceCylinder. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

variable {G K : Type} [DecidableEq G] [MetricSpace K] [CompactSpace K]

/-- Two configurations agreeing on `D` have the same value under this test. -/
def IsCylinderOn (D : Finset G) (f : C(G → K, ℝ)) : Prop :=
  ∀ x y, (∀ g ∈ D, x g = y g) → f x = f y

private def cylinderAlgebra : Subalgebra ℝ C(G → K, ℝ) where
  carrier := {f | ∃ D, IsCylinderOn D f}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A ∪ B, fun x y h ↦ ?_⟩
    change f x * g x = f y * g y
    rw [hA x y (fun a ha ↦ h a (Finset.mem_union_left _ ha)),
      hB x y (fun b hb ↦ h b (Finset.mem_union_right _ hb))]
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A ∪ B, fun x y h ↦ ?_⟩
    change f x + g x = f y + g y
    rw [hA x y (fun a ha ↦ h a (Finset.mem_union_left _ ha)),
      hB x y (fun b hb ↦ h b (Finset.mem_union_right _ hb))]
  algebraMap_mem' := fun _ ↦ ⟨∅, fun _ _ _ ↦ rfl⟩

private theorem cylinderAlgebra_dense :
    Dense (↑(cylinderAlgebra (G := G) (K := K)) : Set C(G → K, ℝ)) := by
  have hsep : (cylinderAlgebra : Subalgebra ℝ C(G → K, ℝ)).SeparatesPoints := by
    intro x y hxy
    have hex : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := hex
    let f : C(G → K, ℝ) := ⟨fun z ↦ dist (z i) (x i), (continuous_apply i).dist continuous_const⟩
    refine ⟨f, ⟨f, ⟨{i}, fun a b h ↦ ?_⟩, rfl⟩, ?_⟩
    · change dist (a i) (x i) = dist (b i) (x i)
      rw [h i (Finset.mem_singleton_self i)]
    · change dist (x i) (x i) ≠ dist (y i) (x i)
      rw [dist_self]
      exact (dist_ne_zero.mpr hi.symm).symm
  intro f
  exact ContinuousMap.continuousMap_mem_subalgebra_closure_of_separatesPoints cylinderAlgebra hsep f

variable [Countable G]

/-- A countable family of continuous tests, each depending on finitely many
coordinates, is uniformly dense in the real continuous functions on the shift. -/
theorem exists_dense_cylinderTests : ∃ (f : ℕ → C(G → K, ℝ)) (D : ℕ → Finset G),
    DenseRange f ∧ ∀ i, IsCylinderOn (D i) (f i) := by
  obtain ⟨t, ht, htc, htd⟩ := (cylinderAlgebra_dense (G := G) (K := K)).exists_countable_dense_subset
  have : Countable t := htc.to_subtype
  have : Nonempty t := htd.nonempty.to_subtype
  obtain ⟨enum, hEnum⟩ := exists_surjective_nat t
  let f : ℕ → C(G → K, ℝ) := fun i ↦ (enum i).val
  have hf : ∀ i, ∃ D, IsCylinderOn D (f i) := fun i ↦ ht (enum i).property
  choose D hD using hf
  refine ⟨f, D, ?_, hD⟩
  have hr : Set.range f = t := by
    ext u
    refine ⟨?_, fun hu ↦ ?_⟩
    · rintro ⟨i, rfl⟩
      exact (enum i).property
    · obtain ⟨i, hi⟩ := hEnum ⟨u, hu⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  rw [DenseRange, hr]
  exact htd

variable [MeasurableSpace K] [BorelSpace K]

omit [DecidableEq G] in
private theorem continuous_testIntegral (ν : ProbabilityMeasure (G → K)) :
    Continuous (fun f : C(G → K, ℝ) ↦ ∫ z, f z ∂(ν : Measure (G → K))) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f h
  have hintegrable (u : C(G → K, ℝ)) : Integrable u (ν : Measure (G → K)) :=
    u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Real.dist_eq, ← integral_sub (hintegrable f) (hintegrable h), dist_eq_norm]
  simpa using norm_integral_le_of_norm_le_const (μ := (ν : Measure (G → K)))
    (C := ‖f - h‖) (Eventually.of_forall fun z ↦ ContinuousMap.norm_coe_le_norm (f - h) z)

variable [Group G] [Infinite G]

/-- Local finite models on congruent tiling cells. The boundary condition lets
the local tests be transferred to a single configuration across the cells. -/
def HasTiledCylinderApproximations (K : Type) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] {G : Type} [Group G] [DecidableEq G]
    (F : LeftFolnerSequence G) : Prop :=
  ∀ (ν : ProbabilityMeasure (G → K)) (f : ℕ → C(G → K, ℝ)) (D : ℕ → Finset G),
    (∀ a : G, (ν : Measure (G → K)).map (fun x j ↦ x (j * a)) = (ν : Measure (G → K))) →
    (∀ i, IsCylinderOn (D i) (f i)) →
    ∃ (P : ℕ → BoundedTilePartition G) (sample : ℕ → Finset G → G → K)
      (bad : ℕ → Set G) (δs : ℕ → ℝ),
      (∀ k g, (P k).cell g ⊆ (P (k + 1)).cell g) ∧
      (∀ k g h, h ∈ (P k).cell g → (h ∈ bad k ↔ g ∈ bad k)) ∧
      (∀ k, 0 ≤ δs k) ∧ Summable δs ∧
      (∀ k, ∀ᶠ n in atTop, blockProportion (F.blocks n) (bad k) ≤ δs k) ∧
      (∀ k g i, i ≤ k → g ∉ bad k →
        ‖finiteAverage ((P k).cell g) (fun a ↦ f i (correspondenceShift a (sample k ((P k).cell g))) -
          ∫ z, f i z ∂(ν : Measure (G → K)))‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      (∀ k g i, i ≤ k → g ∉ bad k →
        ((leftBoundary (D i) ((P k).cell g)).card : ℝ) / ((P k).cell g).card ≤
          1 / ((k : ℝ) + 1))

omit [Countable G] [Group G] [Infinite G] [DecidableEq G] in
private theorem finiteAverage_sub_constant {A : Finset G} (hA : A.Nonempty) (f : G → ℝ) (c : ℝ) :
    finiteAverage A (fun g ↦ f g - c) = finiteAverage A f - c := by
  have hc : ((A.card : ℝ)) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  simp only [finiteAverage, smul_eq_mul, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Finite models on congruent tilings yield a generic configuration for every
invariant full-shift measure along the prescribed Følner sequence. -/
theorem hasFolnerGenericRealizations_of_tiledCylinderApproximations (F : LeftFolnerSequence G)
    (hTiles : HasTiledCylinderApproximations K F) : HasFolnerGenericRealizations F K := by
  intro ν hInvariant
  obtain ⟨f, D, hDense, hD⟩ := exists_dense_cylinderTests (G := G) (K := K)
  obtain ⟨P, sample, bad, δs, hP, hBad, hδs, hSum, hSparse, hTest, hSmall⟩ :=
    hTiles ν f D hInvariant hD
  let m (i : ℕ) := ∫ z, f i z ∂(ν : Measure (G → K))
  let C (i : ℕ) := ‖f i‖ + ‖m i‖
  let q (i : ℕ) (x : G → K) (a : G) := f i (correspondenceShift a x) - m i
  have hC (i : ℕ) : 0 ≤ C i := by dsimp [C]; positivity
  have hNorm (i : ℕ) (x : G → K) (a : G) : ‖q i x a‖ ≤ C i :=
    (norm_sub_le _ _).trans (add_le_add (ContinuousMap.norm_coe_le_norm (f i) _) (le_refl _))
  have hLocal (i : ℕ) (x y : G → K) (a : G) (h : ∀ g ∈ D i, x (g * a) = y (g * a)) :
      q i x a = q i y a := by
    change f i (fun g ↦ x (g * a)) - m i = f i (fun g ↦ y (g * a)) - m i
    rw [hD i _ _ fun g hg ↦ h g hg]
  obtain ⟨x, hx⟩ := exists_tendsto_finiteTimeTests_of_tiledApproximations F P hP bad hBad δs hδs hSum hSparse D q C
    hC hNorm hLocal sample hTest hSmall
  let v := correspondenceOrbitLaw F x
  have hTests (i : ℕ) : Tendsto
      (fun n ↦ ∫ z, f i z ∂(v n : Measure (G → K))) atTop (𝓝 (m i)) := by
    have h := (hx i).add_const (m i)
    rw [zero_add] at h
    refine h.congr (fun n ↦ ?_)
    change finiteAverage (F.blocks n) (fun a ↦ f i (correspondenceShift a x) - m i) + m i =
      ∫ z, f i z ∂(correspondenceOrbitLaw F x n : Measure (G → K))
    rw [finiteAverage_sub_constant (F.nonempty n), sub_add_cancel, correspondenceOrbitLaw,
      integral_finiteEmpiricalLaw]
    rfl
  refine ⟨x, ?_⟩
  change Tendsto v atTop (𝓝 ν)
  rw [tendsto_iff_ultrafilter]
  intro p hp
  let μ := (p.map v).lim
  have hμ : Tendsto v p (𝓝 μ) := (p.map v).le_nhds_lim
  have hAgree (i : ℕ) : (∫ z, f i z ∂(μ : Measure (G → K))) = m i :=
    tendsto_nhds_unique
      (((ProbabilityMeasure.continuous_integral_continuousMap (f i)).tendsto μ).comp hμ)
      ((hTests i).mono_left hp)
  have hClosed : IsClosed {u : C(G → K, ℝ) |
      (∫ z, u z ∂(μ : Measure (G → K))) = ∫ z, u z ∂(ν : Measure (G → K))} :=
    isClosed_eq (continuous_testIntegral μ) (continuous_testIntegral ν)
  have hEq : μ = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro u
    apply closure_minimal _ hClosed (hDense u.toContinuousMap)
    rintro v ⟨i, rfl⟩
    exact hAgree i
  exact hEq ▸ hμ

end SixProblems
end

/- Source module SixProblems.CorrespondenceSampling. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical Topology ProbabilityTheory

section Sampling

variable {A B I X : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Fintype I] [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
/-- Independent samples for a finite set of labels simultaneously control all
    centered test sums. The squared error bound is linear in the number of
    terms and in the largest label class. -/
theorem exists_small_groupedSums (μ : Measure X) [IsProbabilityMeasure μ]
    (label : A → B) (q : I → A → X → ℝ) (C : I → ℝ)
    (hBound : ∀ i a x, ‖q i a x‖ ≤ C i)
    (hMeas : ∀ i a, Measurable (q i a)) (hMean : ∀ i a, (∫ x, q i a x ∂μ) = 0)
    (M : ℕ) (hM : ∀ b, (Finset.univ.filter (fun a ↦ label a = b)).card ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (hSmall : (Fintype.card A : ℝ) * M * (∑ i, C i ^ 2) < ε ^ 2) :
    ∃ y : B → X, ∀ i, ‖∑ a, q i a (y (label a))‖ < ε := by
  let fiber (b : B) := Finset.univ.filter (fun a ↦ label a = b)
  let ν : Measure (B → X) := Measure.pi (fun _ : B ↦ μ)
  let Z (i : I) (b : B) (x : X) := ∑ a ∈ fiber b, q i a x
  let Y (i : I) (y : B → X) := ∑ b, Z i b (y b)
  have hZMeas (i : I) (b : B) : Measurable (Z i b) :=
    Finset.measurable_sum _ fun a _ ↦ hMeas i a
  have hZBound (i : I) (b : B) (x : X) : ‖Z i b x‖ ≤ ((fiber b).card : ℝ) * C i := calc
    _ ≤ ∑ a ∈ fiber b, ‖q i a x‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ fiber b, C i := Finset.sum_le_sum fun a _ ↦ hBound i a x
    _ = _ := by simp [nsmul_eq_mul]
  have hZLp (i : I) (b : B) : MemLp (Z i b) 2 μ :=
    MemLp.of_bound (hZMeas i b).aestronglyMeasurable _ (.of_forall fun x ↦ hZBound i b x)
  have hZMean (i : I) (b : B) : (∫ x, Z i b x ∂μ) = 0 := by
    have hInt (a : A) : Integrable (q i a) μ :=
      Integrable.of_bound (hMeas i a).aestronglyMeasurable _ (.of_forall (hBound i a))
    unfold Z
    rw [integral_finsetSum _ (fun a _ ↦ hInt a)]
    simp [hMean]
  have hYInt (i : I) (b : B) : Integrable (fun y : B → X ↦ Z i b (y b)) ν :=
    (measurePreserving_eval (fun _ : B ↦ μ) b).integrable_comp_of_integrable
      ((hZLp i b).integrable (by norm_num))
  have hYLp (i : I) : MemLp (Y i) 2 ν :=
    memLp_finsetSum _ fun b _ ↦ (hZLp i b).comp_measurePreserving
      (measurePreserving_eval (fun _ : B ↦ μ) b)
  have hYMean (i : I) : (∫ y, Y i y ∂ν) = 0 := by
    unfold Y
    rw [integral_finsetSum _ (fun b _ ↦ hYInt i b)]
    apply Finset.sum_eq_zero
    intro b _
    have hp := measurePreserving_eval (fun _ : B ↦ μ) b
    rw [← hZMean i b, ← hp.map_eq, integral_map hp.measurable.aemeasurable
      (hZMeas i b).aestronglyMeasurable]
  have hSize : ∑ b, ((fiber b).card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A)) (t := (Finset.univ : Finset B))
      (f := label) (fun _ _ ↦ Finset.mem_univ _)).symm
  have hVar (i : I) : (∫ y, Y i y ^ 2 ∂ν) ≤ (Fintype.card A : ℝ) * M * C i ^ 2 := by
    have hv₁ : variance (Y i) ν = ∫ y, Y i y ^ 2 ∂ν := by
      rw [variance_eq_sub (hYLp i), hYMean i]
      simp [Pi.pow_apply]
    have hv₂ : variance (Y i) ν = ∑ b, variance (Z i b) μ := by
      have hYEq : Y i = ∑ b, (fun y : B → X ↦ Z i b (y b)) := by
        funext y
        simp only [Y, Finset.sum_apply]
      rw [hYEq]
      exact variance_sum_pi (μ := fun _ : B ↦ μ) (hZLp i)
    rw [← hv₁, hv₂, ← hSize, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    let c := ((fiber b).card : ℝ) * C i
    have hb : ∀ᵐ x ∂μ, Z i b x ∈ Icc (-c) c := .of_forall fun x ↦
      abs_le.mp (hZBound i b x)
    calc
      _ ≤ ((c - -c) / 2) ^ 2 := variance_le_sq_of_bounded hb (hZMeas i b).aemeasurable
      _ = ((fiber b).card : ℝ) ^ 2 * C i ^ 2 := by dsimp [c]; ring
      _ ≤ ((fiber b).card : ℝ) * M * C i ^ 2 := by
        rw [pow_two ((fiber b).card : ℝ)]
        gcongr
        exact_mod_cast hM b
  let loss (y : B → X) := ∑ i, Y i y ^ 2
  have hLossInt : Integrable loss ν :=
    integrable_finsetSum _ fun i _ ↦ (hYLp i).integrable_sq
  have hLoss : (∫ y, loss y ∂ν) < ε ^ 2 := by
    refine lt_of_le_of_lt ?_ hSmall
    unfold loss
    rw [integral_finsetSum _ (fun i _ ↦ (hYLp i).integrable_sq), Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hVar i
  obtain ⟨y, hy⟩ : ∃ y, loss y < ε ^ 2 := by
    by_contra! hn
    have hge : ε ^ 2 ≤ ∫ y, loss y ∂ν := by
      simpa using integral_mono (integrable_const (ε ^ 2)) hLossInt hn
    exact (not_lt_of_ge hge) hLoss
  refine ⟨y, fun i ↦ ?_⟩
  have hYi : Y i y ^ 2 ≤ loss y :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (Y j y)) (Finset.mem_univ i)
  have hI : ‖Y i y‖ < ε := by
    rw [Real.norm_eq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) hε.le).mp (by simpa only [sq_abs] using hYi.trans_lt hy)
  have hsum : Y i y = ∑ a, q i a (y (label a)) := by
    unfold Y Z
    calc
      _ = ∑ b, ∑ a ∈ fiber b, q i a (y (label a)) := by
        refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a ha ↦ ?_
        rw [(Finset.mem_filter.mp ha).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset A))
        (t := (Finset.univ : Finset B)) (g := label) (fun _ _ ↦ Finset.mem_univ _)
        (fun a ↦ q i a (y (label a)))
  rwa [← hsum]

end Sampling

end

end SixProblems
end

/- Source module SixProblems.CorrespondenceLocalModels. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical Topology ProbabilityTheory

section LocalPatterns

variable {G : Type*} [Group G] [DecidableEq G]

/-- Points in the block whose test coordinates cross a boundary of the partition. -/
def tileTestBoundary (P : BoundedTilePartition G) (D A : Finset G) : Finset G :=
  A.filter fun g ↦ g ∈ leftBoundary D (P.cell g)

/-- Cells crossing the block boundary are detected by the finitely many
    possible displacements inside a partition cell. -/
theorem tileBoundary_subset_displacements (P : BoundedTilePartition G) (A : Finset G) :
    tileBoundary P.cell A ⊆ leftBoundary P.displacements A := by
  intro g hg
  obtain ⟨hgA, hgP⟩ := Finset.mem_filter.mp hg
  obtain ⟨a, ha, haA⟩ := Finset.not_subset.mp hgP
  exact mem_leftBoundary.mpr ⟨hgA, a*g⁻¹, P.mem_displacements ha, by simpa using haA⟩

/-- The test boundary is bounded by the bad sites, the sites in incomplete
    cells, and the sum of the internal boundaries of the remaining cells. -/
theorem tileTestBoundary_card_le (P : BoundedTilePartition G) (D A : Finset G)
    (bad : Set G) (η : ℝ) (hη : 0 ≤ η)
    (hRel : ∀ a ∉ bad, ((leftBoundary D (P.cell a)).card : ℝ) ≤ η * (P.cell a).card) :
    ((tileTestBoundary P D A).card : ℝ) ≤
      ((A.filter (· ∈ bad)).card : ℝ) + (leftBoundary P.displacements A).card + η * A.card := by
  let R := (A.filter fun g ↦ g ∉ bad ∧ P.cell g ⊆ A).image P.cell
  have hDisjoint : (↑R : Set (Finset G)).PairwiseDisjoint id := by
    intro U hU V hV hUV
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hV
    exact Finset.disjoint_left.mpr fun a hua hva ↦ hUV ((P.cell_eq hua).symm.trans (P.cell_eq hva))
  have hCover : R.biUnion id ⊆ A := by
    intro a ha
    obtain ⟨U, hU, haU⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hU
    exact (Finset.mem_filter.mp hu).2.2 haU
  have hSum : ∑ U ∈ R, (U.card : ℝ) ≤ A.card := by
    have he := Finset.card_biUnion hDisjoint
    simp only [id_eq] at he
    rw [← Nat.cast_sum, ← he]
    exact_mod_cast Finset.card_le_card hCover
  have hInternal : ((R.biUnion (leftBoundary D)).card : ℝ) ≤ η * A.card := calc
    _ ≤ ∑ U ∈ R, ((leftBoundary D U).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ U ∈ R, η * (U.card : ℝ) := by
      apply Finset.sum_le_sum
      intro U hU
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hU
      exact hRel u (Finset.mem_filter.mp hu).2.1
    _ ≤ η * A.card := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hSum hη
  have hSite : tileTestBoundary P D A ⊆
      ((A.filter (· ∈ bad)) ∪ leftBoundary P.displacements A) ∪ R.biUnion (leftBoundary D) := by
    intro a ha
    obtain ⟨haA, haD⟩ := Finset.mem_filter.mp ha
    by_cases hb : a ∈ bad
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haA, hb⟩))
    by_cases hP : P.cell a ⊆ A
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨P.cell a, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨haA, hb, hP⟩), haD⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (tileBoundary_subset_displacements P A (Finset.mem_filter.mpr ⟨haA, hP⟩)))
  refine le_trans ?_ (add_le_add le_rfl hInternal)
  norm_cast
  exact (Finset.card_le_card hSite).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))

set_option maxHeartbeats 1000000 in
/-- Glue independent configurations on the cells meeting a finite block. The
    variance term depends on the largest cell, while the deterministic error
    comes from the sites whose test coordinates cross cell boundaries. -/
theorem exists_localPattern_of_tileVariance {K I : Type*}
    [MeasurableSpace K] [Nonempty K] [Fintype I]
    (μ : Measure (G → K)) [IsProbabilityMeasure μ] (P : BoundedTilePartition G)
    (A : Finset G) (hA : A.Nonempty) (M : ℕ) (hM : ∀ a ∈ A, (P.cell a).card ≤ M)
    (D : I → Finset G) (q : I → (G → K) → G → ℝ) (C : I → ℝ)
    (hBound : ∀ i x a, ‖q i x a‖ ≤ C i)
    (hMeas : ∀ i a, Measurable (fun x ↦ q i x a))
    (hMean : ∀ i a, (∫ x, q i x a ∂μ) = 0)
    (hLocal : ∀ i x y a, (∀ d ∈ D i, x (d*a) = y (d*a)) → q i x a = q i y a)
    (ε : ℝ) (hε : 0 < ε) (hSmall : (M : ℝ) * (∑ i, C i ^ 2) < (A.card : ℝ) * ε ^ 2) :
    ∃ x : G → K, ∀ i,
      ‖finiteAverage A (q i x)‖ <
        ε + ((tileTestBoundary P (D i) A).card : ℝ) / A.card * (2 * C i) := by
  let B := A.image P.cell
  let : DecidableEq B := inferInstance
  let label (a : A) : B := ⟨P.cell a, Finset.mem_image_of_mem _ a.property⟩
  have hFiber (b : B) : (Finset.univ.filter (fun a ↦ label a = b)).card ≤ M := by
    obtain ⟨g, hg, hgb⟩ := Finset.mem_image.mp b.property
    have hSub (a : A) (ha : a ∈ Finset.univ.filter (fun a ↦ label a = b)) :
        (a : G) ∈ P.cell g := by
      have he : P.cell a = P.cell g :=
        (congrArg Subtype.val (Finset.mem_filter.mp ha).2).trans hgb.symm
      rw [← he]
      exact P.mem_cell a
    exact (Finset.card_le_card_of_injOn Subtype.val hSub Subtype.val_injective.injOn).trans (hM g hg)
  have hcard : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hCount : (Fintype.card A : ℝ) * M * (∑ i, C i ^ 2) < (ε * (A.card : ℝ)) ^ 2 := by
    have h := mul_lt_mul_of_pos_left hSmall hcard
    rw [Fintype.card_coe]
    convert h using 1 <;> ring
  obtain ⟨y, hy⟩ := exists_small_groupedSums μ label (fun i (a : A) x ↦ q i x a) C
    (fun i a x ↦ hBound i x a) (fun i a ↦ hMeas i a) (fun i a ↦ hMean i a)
    M hFiber (ε * A.card) (mul_pos hε hcard) hCount
  let x (g : G) := if hg : P.cell g ∈ B then y ⟨P.cell g, hg⟩ g else Classical.choice ‹Nonempty K›
  refine ⟨x, fun i ↦ ?_⟩
  let E := tileTestBoundary P (D i) A
  let total := ∑ a : A, q i (y (label a)) a
  have hAgree (a : A) (ha : (a : G) ∉ E) : q i x a = q i (y (label a)) a := by
    apply hLocal
    intro d hd
    have hg : d * (a : G) ∈ P.cell a := by
      by_contra h
      exact ha (Finset.mem_filter.mpr ⟨a.property,
        mem_leftBoundary.mpr ⟨P.mem_cell a, d, hd, h⟩⟩)
    have he := P.cell_eq hg
    have hb : P.cell (d * (a : G)) ∈ B := he.symm ▸ (label a).property
    simp only [x, dite_eq_left hb]
    exact congrArg (fun b : B ↦ y b (d * (a : G))) (Subtype.ext he)
  have hDiff : ‖(∑ a ∈ A, q i x a) - total‖ ≤ (E.card : ℝ) * (2 * C i) := by
    have hSum : (∑ a : A, q i x a) = ∑ a ∈ A, q i x a := Finset.sum_attach _ _
    rw [← hSum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ a : A, ‖q i x a - q i (y (label a)) a‖ := norm_sum_le _ _
      _ ≤ ∑ a : A, if (a : G) ∈ E then 2 * C i else 0 := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · exact (norm_sub_le _ _).trans (by linarith [hBound i x a, hBound i (y (label a)) a])
        · simp [hAgree a ha]
      _ = _ := by
        have hSum' : (∑ a : A, if (a : G) ∈ E then 2 * C i else 0) =
            ∑ a ∈ A, if a ∈ E then 2 * C i else 0 :=
          Finset.sum_attach A (fun a : G ↦ if a ∈ E then 2 * C i else 0)
        rw [hSum', ← Finset.sum_filter]
        have hFilter : A.filter (· ∈ E) = E := by
          ext a
          exact Finset.mem_filter.trans ⟨And.right, fun ha ↦
            ⟨(Finset.mem_filter.mp ha).1, ha⟩⟩
        rw [hFilter, Finset.sum_const, nsmul_eq_mul]
  have hApprox : ‖∑ a ∈ A, q i x a‖ < (E.card : ℝ) * (2 * C i) + ε * A.card := by
    calc
      _ = ‖((∑ a ∈ A, q i x a) - total) + total‖ := by rw [sub_add_cancel]
      _ ≤ ‖(∑ a ∈ A, q i x a) - total‖ + ‖total‖ := norm_add_le _ _
      _ < _ := add_lt_add_of_le_of_lt hDiff (hy i)
  calc
    _ = (A.card : ℝ)⁻¹ * ‖∑ a ∈ A, q i x a‖ := by
      simp [finiteAverage, smul_eq_mul, norm_mul, Real.norm_eq_abs]
    _ < (A.card : ℝ)⁻¹ * ((E.card : ℝ) * (2 * C i) + ε * A.card) :=
      mul_lt_mul_of_pos_left hApprox (inv_pos.mpr hcard)
    _ = _ := by field_simp; ring

/-- A fixed bounded partition gives local models throughout the tail of the
    prescribed Følner sequence, with errors controlled by the exceptional
    sites and the relative test boundaries on the other cells. -/
theorem eventually_exists_localPattern_of_tileDensity {K I : Type*}
    [Infinite G] [MeasurableSpace K] [Nonempty K] [Fintype I]
    (μ : Measure (G → K)) [IsProbabilityMeasure μ] (F : LeftFolnerSequence G)
    (P : BoundedTilePartition G) (bad : Set G) (η : ℝ) (hη : 0 ≤ η)
    (hBad : ∀ᶠ n in atTop,
      (((F.blocks n).filter (· ∈ bad)).card : ℝ) / (F.blocks n).card ≤ η)
    (D : I → Finset G) (q : I → (G → K) → G → ℝ) (C : I → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hBound : ∀ i x a, ‖q i x a‖ ≤ C i)
    (hMeas : ∀ i a, Measurable (fun x ↦ q i x a))
    (hMean : ∀ i a, (∫ x, q i x a ∂μ) = 0)
    (hLocal : ∀ i x y a, (∀ d ∈ D i, x (d*a) = y (d*a)) → q i x a = q i y a)
    (hRel : ∀ i a, a ∉ bad → ((leftBoundary (D i) (P.cell a)).card : ℝ) ≤ η * (P.cell a).card)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ x : G → K, ∀ i,
      ‖finiteAverage (F.blocks n) (q i x)‖ < ε + (2*η + ε)*(2*C i) := by
  let M := P.displacements.card
  have hCard (a : G) : (P.cell a).card ≤ M :=
    Finset.card_le_card_of_injOn (fun b ↦ b*a⁻¹) (fun b hb ↦ P.mem_displacements hb)
      (fun b _ c _ heq ↦ mul_right_cancel heq)
  have hSize : Tendsto (fun n ↦ ((F.blocks n).card : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp F.tendsto_card
  have hSmall : ∀ᶠ n in atTop, (M : ℝ) * (∑ i, C i ^ 2) < ((F.blocks n).card : ℝ) * ε^2 := by
    have hp : 0 < ε^2 := pow_pos hε 2
    filter_upwards [tendsto_atTop.1 hSize ((M : ℝ) * (∑ i, C i ^ 2) / ε^2 + 1)]
      with n hn
    exact (div_lt_iff₀ hp).mp ((lt_add_one _).trans_le hn)
  filter_upwards [hBad, hSmall, (F.tendsto_leftBoundary P.displacements).eventually_lt_const hε]
    with n hn hV hBoundary
  obtain ⟨x, hx⟩ := exists_localPattern_of_tileVariance μ P (F.blocks n) (F.nonempty n)
    M (fun g _ ↦ hCard g) D q C hBound hMeas hMean hLocal ε hε hV
  have hCoef (i : I) : 0 ≤ 2*C i := mul_nonneg (by norm_num) (hC i)
  refine ⟨x, fun i ↦ (hx i).trans_le (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right ?_ (hCoef i)))⟩
  let A := F.blocks n
  have hA : 0 < (A.card : ℝ) := by exact_mod_cast (F.nonempty n).card_pos
  have hDiv := div_le_div_of_nonneg_right
    (tileTestBoundary_card_le P (D i) A bad η hη (hRel i)) hA.le
  rw [add_div, add_div, mul_div_cancel_right₀ _ hA.ne'] at hDiv
  exact hDiv.trans (by linarith)

end LocalPatterns

section CylinderPatterns

variable {G K : Type} [Group G] [DecidableEq G] [Countable G] [Infinite G]
  [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K]

set_option maxHeartbeats 1000000 in
/-- A sufficiently sparse test boundary gives finite models for a prescribed
    finite family of cylinder tests of an invariant shift law. -/
theorem eventually_exists_localCylinderPattern (F : LeftFolnerSequence G)
    (ν : ProbabilityMeasure (G → K))
    (hInvariant : ∀ a : G, (ν : Measure (G → K)).map (fun x g ↦ x (g * a)) = ν)
    (f : ℕ → C(G → K, ℝ)) (D : ℕ → Finset G) (I : Finset ℕ)
    (hD : ∀ i ∈ I, IsCylinderOn (D i) (f i))
    (P : BoundedTilePartition G) (bad : Set G) (η : ℝ) (hη : 0 ≤ η)
    (hBad : ∀ᶠ n in atTop,
      (((F.blocks n).filter (· ∈ bad)).card : ℝ) / (F.blocks n).card ≤ η)
    (hRel : ∀ i ∈ I, ∀ a ∉ bad,
      ((leftBoundary (D i) (P.cell a)).card : ℝ) ≤ η * (P.cell a).card)
    (τ : ℝ) (hτ : 0 < τ) (hBudget : 8*η*(∑ i ∈ I, ‖f i‖) ≤ τ / 4) :
    ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ∈ I, ‖finiteAverage (F.blocks n)
      (fun a ↦ f i (correspondenceShift a x) - ∫ y, f i y ∂(ν : Measure (G → K)))‖ ≤ τ / 2 := by
  let μ : Measure (G → K) := ν
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (ν : Measure (G → K)))
  let C (i : I) : ℝ := 2 * ‖f i‖
  let m (i : I) : ℝ := ∫ y, f i y ∂μ
  let q (i : I) (x : G → K) (a : G) := f i (correspondenceShift a x) - m i
  have hC (i : I) : 0 ≤ C i := by dsimp [C]; positivity
  have hBound (i : I) (x : G → K) (a : G) : ‖q i x a‖ ≤ C i := by
    have hm : ‖m i‖ ≤ ‖f i‖ := by
      simpa [Measure.real, m] using norm_integral_le_of_norm_le_const (μ := μ)
        (.of_forall (ContinuousMap.norm_coe_le_norm (f i)))
    have hf := ContinuousMap.norm_coe_le_norm (f i) (correspondenceShift a x)
    calc
      _ ≤ ‖f i (correspondenceShift a x)‖ + ‖m i‖ := norm_sub_le _ _
      _ ≤ ‖f i‖ + ‖f i‖ := add_le_add hf hm
      _ = C i := (two_mul _).symm
  have hMeas (i : I) (a : G) : Measurable (fun x ↦ q i x a) :=
    ((f i).continuous.comp (correspondenceShift a).continuous).measurable.sub measurable_const
  have hMean (i : I) (a : G) : (∫ x, q i x a ∂μ) = 0 := by
    have hp : MeasurePreserving (correspondenceShift (K := K) a) μ μ :=
      ⟨(correspondenceShift a).continuous.measurable, hInvariant a⟩
    have hi : Integrable (f i) μ :=
      (f i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hShift : (∫ x, f i (correspondenceShift a x) ∂μ) = m i := by
      have h := integral_map (μ := μ) hp.measurable.aemeasurable
        (f i).continuous.aestronglyMeasurable
      rw [hp.map_eq] at h
      exact h.symm
    have ha : Integrable (fun x ↦ f i (correspondenceShift a x)) μ :=
      hp.integrable_comp_of_integrable hi
    have hk : Integrable (fun _ : G → K ↦ m i) μ := integrable_const _
    change (∫ x, f i (correspondenceShift a x) - m i ∂μ) = _
    rw [integral_sub ha hk, hShift]
    simp [Measure.real]
  have hLocal (i : I) (x y : G → K) (a : G)
      (h : ∀ d ∈ D i, x (d*a) = y (d*a)) : q i x a = q i y a :=
    congrArg (· - m i) (hD i i.property _ _ h)
  let B : ℝ := ∑ i ∈ I, ‖f i‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ ↦ norm_nonneg (f i)
  let ε := τ / (4*(1+4*B))
  have hε : 0 < ε := div_pos hτ (by positivity)
  have hEq : ε * (1+4*B) = τ / 4 := by
    have hb : 0 < 1+4*B := by positivity
    dsimp [ε]
    field_simp
  have ht := eventually_exists_localPattern_of_tileDensity μ F P bad η hη hBad
    (fun i : I ↦ D i) q C hC hBound hMeas hMean hLocal
    (fun i ↦ hRel i i.property) ε hε
  filter_upwards [ht] with n hn
  obtain ⟨x, hx⟩ := hn
  refine ⟨x, fun i hi ↦ (hx ⟨i, hi⟩).le.trans ?_⟩
  have hNorm : ‖f i‖ ≤ B :=
    Finset.single_le_sum (fun j _ ↦ norm_nonneg (f j)) hi
  change ε + (2*η+ε)*(2*(2*‖f i‖)) ≤ τ / 2
  calc
    _ ≤ ε + (2*η+ε)*(2*(2*B)) := by gcongr
    _ = ε*(1+4*B) + 8*η*B := by ring
    _ ≤ _ := by
      rw [hEq]
      change 8*η*B ≤ τ / 4 at hBudget
      linarith

end CylinderPatterns

end

end SixProblems
end

/- Source module SixProblems.CorrespondenceTheorem. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


noncomputable section

namespace SixProblems

open Filter MeasureTheory
open scoped Topology

variable {G K : Type} [Group G] [DecidableEq G] [Countable G] [Infinite G]
  [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Finite local models, coarsened partitions and the exceptional-density
bounds needed by the diagonal gluing argument. -/
theorem hasTiledCylinderApproximations [Nonempty K] (F : LeftFolnerSequence G) :
    HasTiledCylinderApproximations K F := by
  classical
  intro ν f D hInvariant hD
  let μ : Measure (G → K) := ν
  have : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (ν : Measure (G → K)))
  let m (i : ℕ) := ∫ x, f i x ∂μ
  let q (i : ℕ) (x : G → K) (a : G) := f i (correspondenceShift a x) - m i
  let B (k : ℕ) := ∑ i ∈ Finset.range (k+1), ‖f i‖
  have hB (k : ℕ) : 0 ≤ B k := Finset.sum_nonneg (fun i _ ↦ norm_nonneg (f i))
  have hNorm (k i : ℕ) (hi : i ≤ k) (x : G → K) (g : G) : ‖q i x g‖ ≤ 2*B k := by
    have hMi : ‖m i‖ ≤ ‖f i‖ := by
      simpa [m, Measure.real] using norm_integral_le_of_norm_le_const (μ := μ)
        (.of_forall (ContinuousMap.norm_coe_le_norm (f i)))
    have hFi : ‖f i‖ ≤ B k := Finset.single_le_sum (fun j _ ↦ norm_nonneg (f j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact (norm_sub_le _ _).trans (by linarith [ContinuousMap.norm_coe_le_norm (f i) (correspondenceShift g x)])
  have hTranslate (i : ℕ) (c : G) (x : G → K) (a : G) :
      q i (fun h ↦ x (h*c⁻¹)) (a*c) = q i x a := by
    have he : correspondenceShift (a * c) (fun h ↦ x (h * c⁻¹)) = correspondenceShift a x := by
      funext g
      simp [mul_assoc]
    simp [q, he]
  have hModels (k : ℕ) : ∀ᶠ n in atTop, ∃ x : G → K, ∀ i ≤ k,
      ‖finiteAverage (F.blocks n) (q i x)‖ ≤ (1 / ((k : ℝ) + 1)) / 2 := by
    let I := Finset.range (k+1)
    let τ : ℝ := 1 / ((k : ℝ) + 1)
    have hτ : 0 < τ := by dsimp [τ]; positivity
    let η := τ / (32*(1+B k))
    have hη : 0 < η := div_pos hτ (by linarith [hB k])
    obtain ⟨P,bad,hSparse,hRel⟩ := exists_smallBoundaryTilePartition F I D hη
    have hSparse' : ∀ᶠ n in atTop, (((F.blocks n).filter (· ∈ bad)).card : ℝ) / (F.blocks n).card ≤ η := by
      simpa only [finiteFraction] using hSparse
    have hBudget : 8*η*B k ≤ τ/4 := by
      have hEq : η * (32*(1+B k)) = τ :=
        div_mul_cancel₀ _ (by linarith [hB k])
      nlinarith only [hEq,hη.le]
    filter_upwards [eventually_exists_localCylinderPattern F ν hInvariant f D I
      (fun i _ ↦ hD i) P bad η hη.le hSparse' hRel τ hτ hBudget] with n hn
    obtain ⟨x,hx⟩ := hn
    exact ⟨x,fun i hi ↦ hx i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))⟩
  obtain ⟨P,bad,sample,hP,hBad,hSparse,hApprox,hRel⟩ := exists_congruentModelCoarsenings F D q
    (fun k ↦ 2*B k) (fun k ↦ by linarith [hB k]) hNorm hTranslate hModels
  let δ (k : ℕ) : ℝ := (1/2)^k
  have hδ (k : ℕ) : 0 ≤ δ k := pow_nonneg (by norm_num) _
  have hSum : Summable δ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact ⟨P,sample,bad,δ,hP,fun k g h hh ↦ (hBad k g h hh).symm,hδ,hSum,
    (fun k ↦ by simpa only [finiteFraction_eq_blockProportion] using hSparse k),
    fun k g i hi hg ↦ hApprox k g hg i hi,fun k g i hi hg ↦ hRel k g hg i hi⟩

/-- Inverse correspondence along the given left Følner sequence. Every
invariant law on the full shift is realized by one configuration along all
blocks of that sequence. -/
theorem hasFolnerGenericRealizations [Nonempty K] (F : LeftFolnerSequence G) :
    HasFolnerGenericRealizations F K :=
  hasFolnerGenericRealizations_of_tiledCylinderApproximations F (hasTiledCylinderApproximations F)

variable [Group K] [IsTopologicalGroup K]

/-- Theorem 4.8. Sequential and measure-theoretic compact-group van der
Corput agree along any given left Følner sequence. This includes the case
where `m` is normalized Haar measure. -/
theorem theorem4_8 (F : LeftFolnerSequence G) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] : IsFolnerVdC F R m ↔ IsMeasureTheoreticVdC R m := by
  exact folnerVdC_iff_measureTheoretic_of_genericRealizations F (hasFolnerGenericRealizations F) R m

end SixProblems
end

/- Source module SixProblems.BoundedObservableRepresentative. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/


/-! # Essentially bounded observables and bounded measurable representatives -/

noncomputable section

namespace SixProblems

open MeasureTheory Mixing Set
open scoped ENNReal

theorem MemLp_exists_measurable_bounded_aeEq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : MemLp f ∞ μ) :
    ∃ b : X → ℂ, Measurable b ∧ f =ᵐ[μ] b ∧ ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C := by
  let f' := hf.aestronglyMeasurable.mk f
  let C := lpNorm f ∞ μ
  let A : Set X := {x | ‖f' x‖ ≤ C}
  let b := A.indicator f'
  have hf' : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hm : MeasurableSet A := measurableSet_le hf'.norm measurable_const
  refine ⟨b, hf'.indicator hm, ?_, C, fun x ↦ ?_⟩
  · filter_upwards [hf.aestronglyMeasurable.ae_eq_mk, ae_le_lpNorm_exponent_top hf] with x hx hb
    have hAx : x ∈ A := by
      change ‖f' x‖ ≤ C
      have he : f x = f' x := hx
      rw [← he]
      exact hb
    exact hx.trans (indicator_of_mem hAx f').symm
  · by_cases hx : x ∈ A
    · simpa only [b, indicator_of_mem hx] using (show ‖f' x‖ ≤ C from hx)
    · simpa only [b, indicator_of_notMem hx, norm_zero] using
        (lpNorm_nonneg (f := f) (p := ∞) (μ := μ))

theorem correlation_congr_ae {G X : Type*} [Group G] [MeasurableSpace X] (S : System G X)
    {f b : X → ℂ} (hEq : f =ᵐ[S.measure] b) (g : G) : correlation S f g = correlation S b g := by
  apply integral_congr_ae
  filter_upwards [hEq, (S.preserves g).quasiMeasurePreserving.ae_eq_comp hEq] with x hx hg
  exact congrArg₂ (· * ·) hg (congrArg (starRingEnd ℂ) hx)

/-- Condition (e) of Theorem 2.2 can be tested on all `L∞` observables. -/
theorem niceVdC_iff_memLp_top {G : Type} [Group G] {R : Set G} : NiceVdC R ↔
    ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X] (S : System G X) (f : X → ℂ),
      MemLp f ∞ S.measure → ∀ ε : ℝ, 0 < ε → ∃ r ∈ R,
        ‖∫ x, f x ∂S.measure‖ ^ 2 - ε ≤ ‖correlation S f r⁻¹‖ := by
  constructor
  · intro h X _ _ S f hf ε hε
    obtain ⟨b,hb,hEq,hBound⟩ := MemLp_exists_measurable_bounded_aeEq hf
    obtain ⟨r,hr,hI⟩ := h S b hb hBound ε hε
    exact ⟨r,hr, by rwa [integral_congr_ae hEq, correlation_congr_ae S hEq]⟩
  · intro h X _ _ S f hf ⟨C, hC⟩ ε hε
    exact h S f (memLp_top_of_bound hf.aestronglyMeasurable C (.of_forall hC)) ε hε

end SixProblems
end

/- Source module SixProblems.OperatorialRecurrence. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

noncomputable section

open MeasureTheory Mixing Set Matrix
open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal

variable {G : Type} [Group G]

/-- The measurable bounded representatives in Definition 4.1 give the same test
    as the essentially bounded functions in the paper. -/
theorem isVdC_iff_memLp_top {H : Set G} : IsVdC H ↔
    ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X] (S : System G X) (f : X → ℂ),
      MemLp f ∞ S.measure → (∀ h ∈ H, correlation S f h = 0) → ∫ x, f x ∂S.measure = 0 := by
  constructor
  · intro h X _ _ S f hf hc
    obtain ⟨b,hb,hEq,hB⟩ := MemLp_exists_measurable_bounded_aeEq hf
    exact (integral_congr_ae hEq).trans
      (h S b hb hB (fun g hg ↦ (correlation_congr_ae S hEq g).symm.trans (hc g hg)))
  · intro h X _ _ S f hf ⟨C, hC⟩ hc
    exact h S f (memLp_top_of_bound hf.aestronglyMeasurable C (.of_forall hC)) hc

/-- Complex positive definiteness is tested on finite group-indexed matrices. -/
def ComplexPositiveDefinite (φ : G → ℂ) : Prop :=
  ∀ I : Finset G, (Matrix.of fun i j : I ↦ φ ((i : G) * (j : G)⁻¹)).PosSemidef

theorem ComplexPositiveDefinite.realPart {φ : G → ℂ} (hφ : ComplexPositiveDefinite φ) :
    RealPositiveDefinite (fun g ↦ (φ g).re) := by
  intro I
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    exact Matrix.IsSymm.ext fun i j ↦ by
      have he := congrArg Complex.re ((hφ I).isHermitian.apply i j)
      simpa only [Matrix.of_apply, Complex.star_def, Complex.conj_re] using he
  intro a
  have h := (hφ I).re_dotProduct_nonneg (fun i ↦ (a i : ℂ))
  change 0 ≤ Complex.re _ at h
  have hSum (f : I → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reAddGroupHom f Finset.univ
  simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, hSum, star_trivial,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] using h

/-- The correlation of an L² observable is positive definite, with no commutativity
    assumption on the group. -/
theorem correlation_complexPositiveDefinite {X : Type*} [MeasurableSpace X]
    (S : System G X) {f : X → ℂ} (hf : MemLp f 2 S.measure) :
    ComplexPositiveDefinite (correlation S f) := by
  intro I
  let U := systemKoopman S
  let x := hf.toLp f
  let v (i : I) := U ((i : G)⁻¹) x
  convert (Matrix.posSemidef_gram ℂ v).transpose using 1
  ext i j
  change correlation S f ((i : G) * (j : G)⁻¹) = ⟪v j, v i⟫_ℂ
  symm
  rw [← (U (j : G)).inner_map_map]
  change ⟪(U (j : G) * U ((j : G)⁻¹)) x, (U (j : G) * U ((i : G)⁻¹)) x⟫_ℂ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  change ⟪x, U ((j : G)*(i : G)⁻¹) x⟫_ℂ = _
  rw [inner_systemKoopman_of_memLp, _root_.mul_inv_rev, inv_inv]

/-- The L² correlation test for operatorial recurrence in Theorem 5.3(b). -/
def IsOperatoriallyRecurrent (H : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (f : X → ℂ), MemLp f 2 S.measure →
      (∀ h ∈ H, correlation S f h = 0) → ∫ x, f x ∂S.measure = 0

/-- The positive-definite obstruction in Theorem 5.3(c). -/
def NoConstantNegativePositiveDefinite (H : Set G) : Prop :=
  ¬∃ (φ : G → ℂ), ComplexPositiveDefinite φ ∧
    ∃ r : ℝ, r < 0 ∧ ∀ h ∈ H, φ h = r

theorem IsOperatoriallyRecurrent.isVdC {H : Set G} (hH : IsOperatoriallyRecurrent H) : IsVdC H :=
  fun S f hf hB hC ↦ hH S f (bounded_measurable_memLp S hf hB) hC

private theorem correlation_add_const_of_mean_zero {X : Type*} [MeasurableSpace X]
    (S : System G X) {f : X → ℂ} (hf : MemLp f 2 S.measure)
    (hm : (∫ x, f x ∂S.measure) = 0) (c : ℂ) (g : G) :
    correlation S (fun x ↦ f x + c) g = correlation S f g + (‖c‖ ^ 2 : ℝ) := by
  have hfg := hf.comp_measurePreserving (S.preserves g)
  have hs : MemLp (fun x ↦ conj (f x)) 2 S.measure := hf.star
  have h₁ : Integrable (fun x ↦ f (S.act g x) * conj (f x)) S.measure := hfg.integrable_mul hs
  have h₂ : Integrable (fun x ↦ f (S.act g x) * conj c) S.measure :=
    (hfg.integrable (by norm_num)).mul_const _
  have h₃ : Integrable (fun x ↦ c * conj (f x)) S.measure :=
    (hs.integrable (by norm_num)).const_mul _
  have hj : (∫ x, f (S.act g x) ∂S.measure) = 0 :=
    (integral_comp_preserving (S.preserves g) hf.aestronglyMeasurable).trans hm
  unfold correlation
  have hExp : (fun x ↦ (f (S.act g x) + c) * conj (f x + c)) =
      fun x ↦ (f (S.act g x) * conj (f x) + f (S.act g x) * conj c) +
        (c * conj (f x) + c * conj c) := funext fun _ ↦ by rw [map_add]; ring
  have hk : Integrable (fun _ : X ↦ c * conj c) S.measure := integrable_const _
  rw [hExp, integral_add (h₁.fun_add h₂) (h₃.fun_add hk), integral_add h₁ h₂,
    integral_add h₃ hk, integral_mul_const, integral_const_mul,
    integral_conj, hj, hm, map_zero, zero_mul, mul_zero, add_zero, zero_add, integral_const,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [Measure.real]

theorem operatorial_of_noConstantNegativePD {H : Set G}
    (hh : NoConstantNegativePositiveDefinite H) : IsOperatoriallyRecurrent H := by
  intro X _ _ S f hf hcorr
  set a := ∫ x, f x ∂S.measure with ha
  by_contra hne
  let f₀ : X → ℂ := fun x ↦ f x - a
  have hf₀ : MemLp f₀ 2 S.measure := hf.sub (memLp_const a)
  have hm : (∫ x, f₀ x ∂S.measure) = 0 := by
    unfold f₀
    rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _), integral_const, ← ha]
    simp [Measure.real]
  apply hh
  refine ⟨correlation S f₀, correlation_complexPositiveDefinite S hf₀, -(‖a‖ ^ 2),
    neg_lt_zero.mpr (pow_pos (norm_pos_iff.mpr hne) 2), fun g hg ↦ ?_⟩
  have h := correlation_add_const_of_mean_zero S hf₀ hm a g
  have he : (fun x ↦ f₀ x + a) = f := funext fun x ↦ sub_add_cancel _ _
  rw [he, hcorr g hg] at h
  push_cast
  push_cast at h
  linear_combination -h

theorem noConstantNegativePD_of_vdC [Countable G] {H : Set G} (hne : H.Nonempty)
    (hH : IsVdC H) : NoConstantNegativePositiveDefinite H := by
  rintro ⟨φ, hφ, r, hr, hneg⟩
  exact not_vdC_of_negative_constant_real hne (fun g ↦ (φ g).re) hφ.realPart r hr
    (fun g hg ↦ by rw [hneg g hg, Complex.ofReal_re]) hH

/-- Theorem 5.3. The bounded and square-integrable tests are equivalent, and each
    is equivalent to the absence of a constant negative positive-definite witness. -/
theorem theorem5_3 [Countable G] {H : Set G} (hne : H.Nonempty) :
    (IsVdC H ↔ IsOperatoriallyRecurrent H) ∧
      (IsVdC H ↔ NoConstantNegativePositiveDefinite H) := by
  have hac := noConstantNegativePD_of_vdC hne
  exact ⟨⟨fun h ↦ operatorial_of_noConstantNegativePD (hac h),
    IsOperatoriallyRecurrent.isVdC⟩,
    ⟨hac, fun h ↦ IsOperatoriallyRecurrent.isVdC (operatorial_of_noConstantNegativePD h)⟩⟩

end

end SixProblems
end

/- Source module SixProblems.OperatorialRecurrenceHilbert. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems

noncomputable section

open MeasureTheory Mixing Set
open scoped InnerProductSpace ComplexOrder

variable {G : Type} [Group G]

/-- Operatorial recurrence stated in terms of the invariant projection of a unitary
    representation, as in the introduction. -/
def IsHilbertOperatoriallyRecurrent (H : Set G) : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : G →* (E ≃ₗᵢ[ℂ] E)) (x : E),
    (∀ h ∈ H, ⟪U h x, x⟫_ℂ = 0) → invariantProjection U x = 0

theorem complexPositiveDefinite_coefficient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* (E ≃ₗᵢ[ℂ] E)) (x : E) :
    ComplexPositiveDefinite (fun g ↦ ⟪x, U g x⟫_ℂ) := by
  intro I
  let v (i : I) := U ((i : G)⁻¹) x
  convert Matrix.posSemidef_gram ℂ v using 1
  ext i j
  change ⟪x, U ((i : G) * (j : G)⁻¹) x⟫_ℂ = ⟪v i, v j⟫_ℂ
  symm
  rw [← (U (i : G)).inner_map_map]
  change ⟪(U (i : G) * U ((i : G)⁻¹)) x, (U (i : G) * U ((j : G)⁻¹)) x⟫_ℂ = _
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem hilbertOperatorial_of_noConstantNegativePD {H : Set G}
    (hH : NoConstantNegativePositiveDefinite H) : IsHilbertOperatoriallyRecurrent H := by
  intro E _ _ _ U x hx
  let P := invariantVectors U
  let u := P.starProjection x
  let v := x - u
  have hu : u ∈ P := P.starProjection_apply_mem x
  have hv : v ∈ Pᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have huv : ⟪v, u⟫_ℂ = 0 := inner_eq_zero_symm.mp (hv _ hu)
  change u = 0
  by_contra hne
  apply hH
  refine ⟨fun g ↦ ⟪v, U g v⟫_ℂ, complexPositiveDefinite_coefficient U v, -(‖u‖ ^ 2),
    neg_lt_zero.mpr (pow_pos (norm_pos_iff.mpr hne) 2), fun g hg ↦ ?_⟩
  have hgu : U g u = u := hu g
  have hOrtho : ⟪u, U g v⟫_ℂ = 0 := by
    rw [← hgu, (U g).inner_map_map]
    exact hv _ hu
  have hSplit : ⟪x, U g x⟫_ℂ = ⟪u, u⟫_ℂ + ⟪v, U g v⟫_ℂ := by
    rw [show x = u + v from (add_sub_cancel u x).symm, map_add, hgu,
      inner_add_left, inner_add_right, inner_add_right, hOrtho, huv, add_zero, zero_add]
  rw [inner_eq_zero_symm.mpr (hx g hg), inner_self_eq_norm_sq_to_K] at hSplit
  change 0 = (‖u‖ : ℂ) ^ 2 + ⟪v, U g v⟫_ℂ at hSplit
  push_cast
  linear_combination -hSplit

theorem operatorial_of_hilbertOperatorial {H : Set G}
    (hH : IsHilbertOperatoriallyRecurrent H) : IsOperatoriallyRecurrent H := by
  intro X _ _ S f hf hcorr
  let U := systemKoopman S
  let v := hf.toLp f
  let one := constantOne S.measure
  have hOne : one ∈ invariantVectors U := systemKoopman_constantOne S
  have hp := hH U v (fun h hh ↦ by
    have he := inner_systemKoopman_of_memLp S hf h⁻¹
    rw [inv_inv, hcorr h hh] at he
    change ⟪v, U h⁻¹ v⟫_ℂ = 0 at he
    rw [← (U h).inner_map_map] at he
    change ⟪U h v, (U h * U h⁻¹) v⟫_ℂ = 0 at he
    rw [← map_mul, mul_inv_cancel, map_one] at he
    exact he)
  have hv := (invariantVectors U).sub_starProjection_mem_orthogonal v
  change v - invariantProjection U v ∈ (invariantVectors U)ᗮ at hv
  rw [hp, sub_zero] at hv
  exact (integral_congr_ae hf.coeFn_toLp).symm.trans
    ((inner_constantOne_left S.measure v).symm.trans (hv _ hOne))

/-- The introductory invariant-projection test and the L² test of Theorem 5.3(b)
    are equivalent. -/
theorem hilbertOperatorial_iff_operatorial [Countable G] {H : Set G} (hne : H.Nonempty) :
    IsHilbertOperatoriallyRecurrent H ↔ IsOperatoriallyRecurrent H :=
  ⟨operatorial_of_hilbertOperatorial, fun h ↦ hilbertOperatorial_of_noConstantNegativePD
    (noConstantNegativePD_of_vdC hne (IsOperatoriallyRecurrent.isVdC h))⟩

end

end SixProblems
end

/- Source module SixProblems.OperatorialRecurrencePolar. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems.Gaussian

noncomputable section

open MeasureTheory ProbabilityTheory Set Real ENNReal
open scoped ENNReal Real

/-- The joint law of two independent standard real Gaussians. -/
def standardPlane : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure standardPlane := by
  unfold standardPlane
  infer_instance

private def planeDensity (x : ℝ × ℝ) : ℝ≥0∞ := gaussianPDF 0 1 x.1 * gaussianPDF 0 1 x.2

private theorem standardPlane_eq_density : standardPlane = volume.withDensity planeDensity := by
  unfold standardPlane
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  rfl

private theorem planeDensity_polar (r θ : ℝ) :
    planeDensity (polarCoord.symm (r, θ)) = planeDensity (r, 0) := by
  simp only [planeDensity, polarCoord_symm_apply, gaussianPDF, gaussianPDFReal_def,
    NNReal.coe_one, mul_one, sub_zero, zero_pow (by decide : 2 ≠ 0), zero_div, neg_zero, Real.exp_zero]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_mul_mul_comm, ← Real.exp_add, mul_right_comm]
  have hsq : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
    linear_combination r^2 * (cos_sq_add_sin_sq θ)
  have he : -(r * cos θ) ^ 2 / 2 + -(r * sin θ) ^ 2 / 2 = -r ^ 2 / 2 := by linarith
  rw [he]

private def radialMass : ℝ≥0∞ := ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * planeDensity (r, 0)

private theorem sector_mass_factor {E : Set (ℝ × ℝ)} {A : Set ℝ}
    (hE : MeasurableSet E) (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (-π) π)
    (hSector : ∀ r > 0, ∀ θ ∈ Ioo (-π) π, polarCoord.symm (r, θ) ∈ E ↔ θ ∈ A) :
    standardPlane E = radialMass * volume A := by
  rw [standardPlane_eq_density, withDensity_apply _ hE, ← lintegral_indicator hE,
    ← lintegral_comp_polarCoord_symm]
  let f (r : ℝ) := ENNReal.ofReal r * planeDensity (r, 0)
  let g : ℝ → ℝ≥0∞ := A.indicator fun _ ↦ 1
  have hf : Measurable f := by
    change Measurable fun r ↦ ENNReal.ofReal r * (gaussianPDF 0 1 r * gaussianPDF 0 1 0)
    exact measurable_ofReal.mul ((measurable_gaussianPDF 0 1).mul measurable_const)
  have hg : Measurable g := measurable_const.indicator hA
  rw [polarCoord_target]
  calc
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, f p.1 * g p.2 := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      rintro ⟨r, θ⟩ ⟨hr, hθ⟩
      change ENNReal.ofReal r * E.indicator planeDensity (polarCoord.symm (r, θ)) = f r * g θ
      by_cases hθA : θ ∈ A
      · simp only [indicator_of_mem ((hSector r hr θ hθ).mpr hθA), f, g, indicator_of_mem hθA,
          mul_one, planeDensity_polar]
      · have hn : polarCoord.symm (r, θ) ∉ E := fun h ↦ hθA ((hSector r hr θ hθ).mp h)
        simp only [indicator_of_notMem hn, g, indicator_of_notMem hθA, mul_zero]
    _ = _ := by
      change (∫⁻ p : ℝ × ℝ, f p.1 * g p.2 ∂((volume : Measure ℝ).prod volume).restrict
        (Ioi 0 ×ˢ Ioo (-π) π)) = _
      rw [← Measure.prod_restrict, lintegral_prod_mul hf.aemeasurable hg.aemeasurable]
      have hAz : (∫⁻ θ in Ioo (-π) π, g θ) = volume A := by
        rw [show g = A.indicator (fun _ ↦ 1) from rfl, lintegral_indicator hA, lintegral_const,
          one_mul, Measure.restrict_restrict_of_subset hAsub, Measure.restrict_apply_univ]
      rw [hAz]
      rfl

private theorem radialMass_normalized : radialMass.toReal * (2 * π) = 1 := by
  have h := sector_mass_factor (E := univ) (A := Ioo (-π) π) MeasurableSet.univ
    measurableSet_Ioo (Subset.refl _) (fun _ _ _ hθ ↦ iff_of_true (mem_univ _) hθ)
  rw [measure_univ, Real.volume_Ioo, show π - -π = 2 * π by ring] at h
  have he := congrArg ENNReal.toReal h.symm
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_one] at he

/-- The angular part of a standard planar Gaussian is uniform on its full circle. -/
theorem standardPlane_sector {E : Set (ℝ × ℝ)} {A : Set ℝ}
    (hE : MeasurableSet E) (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (-π) π)
    (hSector : ∀ r > 0, ∀ θ ∈ Ioo (-π) π, polarCoord.symm (r, θ) ∈ E ↔ θ ∈ A) :
    (standardPlane E).toReal = (volume A).toReal / (2 * π) := by
  rw [sector_mass_factor hE hA hAsub hSector, ENNReal.toReal_mul,
    eq_div_iff (show 2 * π ≠ 0 by positivity), mul_right_comm, radialMass_normalized, one_mul]

private theorem cos_pos_iff_of_angle_range {θ : ℝ} (hl : -(π + π/2) ≤ θ) (hu : θ ≤ π + π/2) :
    0 < cos θ ↔ θ ∈ Ioo (-(π/2)) (π/2) := by
  constructor
  · intro h
    constructor
    · by_contra! ht
      have hn := cos_nonpos_of_pi_div_two_le_of_le (show π / 2 ≤ -θ by linarith) (by linarith : -θ ≤ π+π/2)
      rw [cos_neg] at hn
      linarith
    · by_contra! ht
      linarith [cos_nonpos_of_pi_div_two_le_of_le ht hu]
  · exact fun h ↦ cos_pos_of_mem_Ioo h

/-- The probability that a standard Gaussian lies in the two indicated positive
    half-planes is the angle between their boundary rays divided by `2π`. -/
theorem standardPlane_positive_wedge (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ π) :
    (standardPlane {x | 0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2}).toReal =
      (π - α) / (2 * π) := by
  have hm : MeasurableSet {x : ℝ × ℝ | 0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const ((measurable_fst.const_mul _).add (measurable_snd.const_mul _)))
  rw [standardPlane_sector (A := Ioo (α-π/2) (π/2)) hm measurableSet_Ioo]
  · rw [Real.volume_Ioo, show π/2 - (α-π/2) = π-α by ring,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hα₁)]
  · intro θ hθ
    exact ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2, pi_pos]⟩
  · intro r hr θ hθ
    change (0 < r * cos θ ∧ 0 < cos α * (r * cos θ) + sin α * (r * sin θ)) ↔ _
    have he : cos α * (r * cos θ) + sin α * (r * sin θ) = r * cos (θ - α) := by
      rw [cos_sub]
      ring
    rw [he, mul_pos_iff_of_pos_left hr, mul_pos_iff_of_pos_left hr,
      cos_pos_iff_of_angle_range (by linarith [hθ.1, pi_pos]) (by linarith [hθ.2, pi_pos])]
    constructor
    · rintro ⟨ht, hs⟩
      rw [cos_pos_iff_of_angle_range (by linarith [ht.1]) (by linarith [ht.2, pi_pos])] at hs
      exact ⟨by linarith [hs.1], ht.2⟩
    · intro h
      have ht : θ ∈ Ioo (-(π/2)) (π/2) := ⟨by linarith [h.1], h.2⟩
      refine ⟨ht, ?_⟩
      apply cos_pos_of_mem_Ioo
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

end

end SixProblems.Gaussian
end

/- Source module SixProblems.OperatorialRecurrenceSheppard. -/
section
/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/



namespace SixProblems.Gaussian

noncomputable section

open MeasureTheory ProbabilityTheory Set Real Matrix WithLp
open scoped ENNReal Real RealInnerProductSpace Matrix

/-- Applying a matrix to a standard Gaussian gives covariance `A * Aᴴ`.
    The proof does not require the matrix to be invertible. -/
theorem map_stdGaussian_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (Matrix.toEuclideanCLM (𝕜 := ℝ) A) =
      multivariateGaussian (0 : EuclideanSpace ℝ ι) (A * Aᴴ) := by
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  change (stdGaussian (EuclideanSpace ℝ ι)).map L = _
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map, integral_id_stdGaussian, map_zero,
      integral_id_multivariateGaussian]
    exact IsGaussian.integrable_id
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  have hAdj : L.adjoint = Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ :=
    (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ)) A).symm
  calc
    _ = ⟪L.adjoint x, L.adjoint y⟫ := by
      rw [covarianceBilin_map IsGaussian.memLp_two_id L, covarianceBilin_stdGaussian,
        innerSL_apply_apply]
    _ = ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) (A*Aᴴ)) y⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_left, map_mul, mul_apply_eq_comp, ← hAdj]
    _ = _ := by
      rw [Matrix.inner_toEuclideanCLM,
        covarianceBilin_multivariateGaussian (Matrix.posSemidef_self_mul_conjTranspose A)]

private def pairToEuclidean (x : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  toLp 2 ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).symm x)

private theorem pairToEuclidean_preserving :
    MeasurePreserving pairToEuclidean standardPlane (stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have h₁ : MeasurePreserving e (Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1)) standardPlane :=
    measurePreserving_piFinTwo _
  have h₂ : MeasurePreserving (toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
      (Measure.pi (fun _ : Fin 2 ↦ gaussianReal 0 1)) (stdGaussian _) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact h₂.comp h₁.symm

@[simp] private theorem pairToEuclidean_zero (x : ℝ × ℝ) : pairToEuclidean x 0 = x.1 := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  exact congrArg Prod.fst (e.apply_symm_apply x)

@[simp] private theorem pairToEuclidean_one (x : ℝ × ℝ) : pairToEuclidean x 1 = x.2 := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  exact congrArg Prod.snd (e.apply_symm_apply x)

private theorem standardPlane_neg_preserving :
    MeasurePreserving (fun x : ℝ × ℝ ↦ (-x.1, -x.2)) standardPlane standardPlane := by
  have hn : MeasurePreserving (fun z : ℝ ↦ -z) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
  exact hn.prod hn

private theorem standardPlane_product_positive (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ π) :
    (standardPlane {x | 0 < x.1 * (cos α * x.1 + sin α * x.2)}).toReal = (π - α) / π := by
  let E : Set (ℝ × ℝ) := {x | 0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2}
  let N : ℝ × ℝ → ℝ × ℝ := fun x ↦ (-x.1, -x.2)
  have hm : MeasurableSet E := (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_const ((measurable_fst.const_mul _).add (measurable_snd.const_mul _)))
  have hN : MeasurableSet (N ⁻¹' E) := hm.preimage standardPlane_neg_preserving.measurable
  have hd : Disjoint E (N ⁻¹' E) := Set.disjoint_left.mpr (fun x hx hy ↦ by
    have h1 : 0 < x.1 := hx.1
    have h2 : 0 < -x.1 := hy.1
    linarith)
  have hU : {x : ℝ × ℝ | 0 < x.1 * (cos α * x.1 + sin α * x.2)} = E ∪ N ⁻¹' E := by
    ext x
    change 0 < x.1 * (cos α * x.1 + sin α * x.2) ↔
      (0 < x.1 ∧ 0 < cos α * x.1 + sin α * x.2) ∨
      (0 < -x.1 ∧ 0 < cos α * (-x.1) + sin α * (-x.2))
    rw [mul_pos_iff]
    simp only [neg_pos, mul_neg, ← neg_add_rev, add_comm (sin α * x.2)]
  rw [hU, measure_union hd hN,
    standardPlane_neg_preserving.measure_preimage hm.nullMeasurableSet, ENNReal.toReal_add
      (measure_ne_top standardPlane E) (measure_ne_top standardPlane E),
    show (standardPlane E).toReal = _ from standardPlane_positive_wedge α hα₀ hα₁]
  ring

/-- Lemma 5.2 (Sheppard's formula), including both singular endpoint covariances. -/
theorem lemma5_2 (a b d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hS : (!![a,b; b,d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![a,b; b,d])
      {x | 0 < x 0 * x 1}).toReal = 1/2 + (1/π) * arcsin (b / √(a*d)) := by
  let A₀ : Matrix (Fin 2) (Fin 2) ℝ := !![a,b; b,d]
  let t := √(a*d)
  let r := b/t
  let α := arccos r
  have ht : 0 < t := sqrt_pos.mpr (mul_pos ha hd)
  have hdet : 0 ≤ a*d - b*b := by
    simpa only [Matrix.det_fin_two_of] using hS.det_nonneg
  have hbb : b^2 ≤ a*d := by nlinarith only [hdet]
  have habs : |b| ≤ t := by
    rw [← sqrt_sq_eq_abs]
    exact sqrt_le_sqrt hbb
  have hr : |r| ≤ 1 := by
    change |b/t| ≤ 1
    rw [abs_div, abs_of_pos ht, div_le_iff₀ ht, one_mul]
    exact habs
  have hα₀ : 0 ≤ α := arccos_nonneg r
  have hα₁ : α ≤ π := arccos_le_pi r
  have hcos : cos α = r := cos_arccos (abs_le.mp hr).1 (abs_le.mp hr).2
  have hAB : √a * (√d * cos α) = b := by
    rw [← mul_assoc, ← sqrt_mul ha.le, hcos]
    change t * (b/t) = b
    field_simp
  let A : Matrix (Fin 2) (Fin 2) ℝ := !![√a,0; √d * cos α, √d * sin α]
  have hA : A*Aᴴ = A₀ := by
    ext i j
    fin_cases i <;> fin_cases j
      <;> simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        star_trivial]
    · change √a * √a + 0*0 = a
      rw [mul_zero, add_zero, mul_self_sqrt ha.le]
    · change √a * (√d * cos α) + 0 * (√d * sin α) = b
      rw [zero_mul, add_zero, hAB]
    · change (√d * cos α) * √a + (√d * sin α) * 0 = b
      rw [mul_comm _ (√a), mul_zero, add_zero, hAB]
    · change (√d * cos α)*(√d * cos α) + (√d * sin α)*(√d * sin α) = d
      calc
        _ = √d * √d * (cos α ^ 2 + sin α ^ 2) := by ring
        _ = d := by rw [cos_sq_add_sin_sq, mul_one, mul_self_sqrt hd.le]
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let P : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := L ∘ pairToEuclidean
  have hmap : MeasurePreserving P standardPlane (multivariateGaussian 0 A₀) :=
    (show MeasurePreserving L (stdGaussian _) (multivariateGaussian 0 A₀) from
      ⟨L.continuous.measurable, by rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) A from rfl,
        map_stdGaussian_matrix, hA]⟩).comp pairToEuclidean_preserving
  have hx (z : ℝ × ℝ) : P z 0 = √a * z.1 := by
    change (L (toLp 2 ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).symm z))) 0 = _
    rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) A from rfl, Matrix.toEuclideanCLM_toLp]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A]
  have hy (z : ℝ × ℝ) : P z 1 = √d * (cos α * z.1 + sin α * z.2) := by
    change (L (toLp 2 ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)).symm z))) 1 = _
    rw [show L = Matrix.toEuclideanCLM (𝕜 := ℝ) A from rfl, Matrix.toEuclideanCLM_toLp]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A, mul_add, mul_assoc]
  let F : Set (EuclideanSpace ℝ (Fin 2)) := {x | 0 < x 0 * x 1}
  have hF : MeasurableSet F := measurableSet_lt measurable_const
    (((EuclideanSpace.proj 0).continuous.measurable).mul ((EuclideanSpace.proj 1).continuous.measurable))
  change ((multivariateGaussian 0 A₀) F).toReal = _
  rw [← hmap.map_eq, Measure.map_apply hmap.measurable hF]
  have hEq : P ⁻¹' F = {x | 0 < x.1 * (cos α * x.1 + sin α * x.2)} := by
    ext z
    change 0 < P z 0 * P z 1 ↔ _
    rw [hx, hy, mul_mul_mul_comm, mul_pos_iff_of_pos_left (mul_pos (sqrt_pos.mpr ha) (sqrt_pos.mpr hd))]
    rfl
  rw [hEq, standardPlane_product_positive α hα₀ hα₁]
  change (π - arccos r) / π = _
  rw [arccos_eq_pi_div_two_sub_arcsin]
  have hne : π ≠ 0 := pi_pos.ne'
  change (π - (π/2 - arcsin r)) / π = 1/2 + (1/π) * arcsin r
  field_simp
  ring

end

end SixProblems.Gaussian
end
