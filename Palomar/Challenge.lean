module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.Algebra.PontryaginDual

@[expose] public section
noncomputable section
open Filter MeasureTheory MeasureTheory.Measure ProbabilityTheory Set WithLp
open scoped Topology symmDiff ENNReal InnerProductSpace ProbabilityTheory ComplexOrder


namespace Mixing

/-- A probability-preserving action, with the probability space left explicit. -/
structure System (G X : Type*) [Group G] [MeasurableSpace X] where
  measure : Measure X
  probability : IsProbabilityMeasure measure
  act : G → X → X
  act_one : act 1 = id
  act_mul : ∀ g h, act (g * h) = act g ∘ act h
  preserves : ∀ g, MeasurePreserving (act g) measure measure

attribute [instance] System.probability

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-- Ergodicity with respect to the entire acting group. -/
def System.IsErgodic (S : System G X) : Prop :=
  ∀ A : Set X, MeasurableSet A →
    (∀ g, S.act g ⁻¹' A =ᵐ[S.measure] A) → EventuallyEmptyOrUniv A (ae S.measure)

end Mixing

namespace SixProblems
open Mixing

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

section
variable {G : Type*} [Group G]

/-- A real positive-definite function on a group. Right differences make
each covariance matrix invariant under simultaneous right translation. -/
def RealPositiveDefinite (φ : G → ℝ) : Prop :=
  ∀ I : Finset G, (Matrix.of fun i j : I ↦ φ ((i : G) * (j : G)⁻¹)).PosSemidef

end
section
variable {G : Type} [Group G]

/-- Complex positive definiteness is tested on finite group-indexed matrices. -/
def ComplexPositiveDefinite (φ : G → ℂ) : Prop :=
  ∀ I : Finset G, (Matrix.of fun i j : I ↦ φ ((i : G) * (j : G)⁻¹)).PosSemidef

/-- The L² correlation test for operatorial recurrence in Theorem 5.3(b). -/
def IsOperatoriallyRecurrent (H : Set G) : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (S : System G X) (f : X → ℂ), MemLp f 2 S.measure →
      (∀ h ∈ H, correlation S f h = 0) → ∫ x, f x ∂S.measure = 0

/-- The positive-definite obstruction in Theorem 5.3(c). -/
def NoConstantNegativePositiveDefinite (H : Set G) : Prop :=
  ¬∃ (φ : G → ℂ), ComplexPositiveDefinite φ ∧
    ∃ r : ℝ, r < 0 ∧ ∀ h ∈ H, φ h = r

end
section
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

end
section
variable {G : Type*} [Group G]

/-- The left shift on group-indexed real paths. -/
def gaussianShift (g : G) (x : G → ℝ) (i : G) : ℝ := x (g⁻¹ * i)

end

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

section
variable {G K : Type} [Group G] [DecidableEq G]
  [Group K] [MetricSpace K] [CompactSpace K] [IsTopologicalGroup K]
  [MeasurableSpace K] [BorelSpace K]

/-- Uniform distribution of a configuration along the prescribed Følner sequence.
Real tests suffice since a complex test splits into its real and imaginary parts. -/
def IsFolnerUniformlyDistributed (F : LeftFolnerSequence G) (x : G → K)
    (m : Measure K) : Prop :=
  ∀ f : C(K, ℝ), Tendsto (fun n ↦ finiteAverage (F.blocks n) (f ∘ x))
    atTop (𝓝 (∫ k, f k ∂m))

/-- The sequence formulation of compact-group van der Corput sets, Definition 4.7. -/
def IsFolnerVdC (F : LeftFolnerSequence G) (R : Set G) (m : Measure K) : Prop :=
  ∀ x : G → K, (∀ h ∈ R, IsFolnerUniformlyDistributed F (fun g ↦ x (h * g) * (x g)⁻¹) m) →
    IsFolnerUniformlyDistributed F x m

end
end SixProblems

namespace SixProblems.Submission
open Mixing

universe u

/-- A nonzero Euclidean representation with no proper nonzero invariant subspace. -/
def IrreducibleEuclidean {K : Type u} [Group K] {d : ℕ}
    (ρ : K →* (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d))) : Prop :=
  (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin d))) ≠ ⊥ ∧
    ∀ W : Submodule ℂ (EuclideanSpace ℂ (Fin d)),
      (∀ k x, x ∈ W → ρ k x ∈ W) → W = ⊥ ∨ W = ⊤

section

/-- Paper result 2.1. -/
theorem paper_proposition2_1 {G X : Type} [Group G] [Countable G] [Infinite G]
    [MeasurableSpace X] [StandardBorelSpace X] (S : System G X)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ∃ (Y : Type) (mY : MeasurableSpace Y) (_ : @StandardBorelSpace Y mY)
      (T : @System G Y _ mY) (C : Set Y),
      MeasurableSet C ∧
      (∀ J : Finset G, (T.measure {y | ∀ g ∈ J, y ∈ T.act g ⁻¹' C}).toReal =
        ∫ x, ∏ g ∈ J, f (S.act g x) ∂S.measure) ∧
      (S.IsErgodic → T.IsErgodic) := by
  sorry

end

section
variable {G : Type} [Group G] [Countable G] [Infinite G]

/-- Paper result 2.2(a–e). -/
theorem paper_theorem2_2 (R : Set G) (hR : R.Nonempty) :
    (NiceRecurrence R ↔ ErgodicNiceRecurrence R) ∧
    (NiceRecurrence R ↔ NiceOperatorialRecurrence R) ∧
    (NiceRecurrence R ↔ ∀ φ : G → ℝ, RealPositiveDefinite φ → 0 ≤ sSup (φ '' R)) ∧
    (NiceRecurrence R ↔ NiceVdC R) := by
  sorry

/-- Paper result 2.2(f). -/
theorem paper_theorem2_2_abelian [IsMulCommutative G] (R : Set G) (hR : R.Nonempty) :
    NiceRecurrence R ↔
      let : TopologicalSpace G := ⊥
      let : MeasurableSpace (PontryaginDual G) := borel _
      ∀ (τ : Measure (PontryaginDual G)) [IsProbabilityMeasure τ],
        τ.real {1} ≤ sSup ((fun r ↦ ‖∫ χ : PontryaginDual G, (χ r : ℂ) ∂τ‖) '' R) := by
  sorry

/-- Paper result 3.3. -/
theorem paper_theorem3_3 {A B : Set G} (hA : ¬ NiceVdC A) (hB : ¬ NiceVdC B) :
    ¬ NiceVdC (A ∪ B) := by
  sorry

/-- Paper result 3.4. -/
theorem paper_corollary3_4 {m : ℕ} (D : Fin m → Set G) (hD : NiceVdC (⋃ i, D i)) :
    ∃ i, NiceVdC (D i) := by
  sorry

end

section
variable {G : Type*} [Group G]

/-- Paper result 3.1. -/
theorem paper_lemma3_1 {I : Type*} (F : I → G → ℝ) (hF : ∀ i, RealPositiveDefinite (F i))
    (p : MvPolynomial I ℝ) (hp : ∀ d, 0 ≤ p.coeff d) :
    RealPositiveDefinite (fun g ↦ MvPolynomial.eval (fun i ↦ F i g) p) := by
  sorry

/-- Paper result 3.2. -/
theorem paper_lemma3_2 {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M) :
    ∃ δ > 0, ∃ K : ℕ, ∀ x y : ℝ, x ∈ Set.Icc (-M) M → y ∈ Set.Icc (-M) M →
      (x < -ε ∨ y < -ε) → x * (2 * M + y) ^ K + y * (2 * M + x) ^ K ≤ -δ := by
  sorry

end

section

/-- Paper result 4.2. -/
theorem paper_lemma4_2 {G X : Type} [Group G] [MeasurableSpace X] [StandardBorelSpace X]
    {R : Set G} (hR : IsVdC R) (S : System G X) {d : ℕ}
    (V : X → EuclideanSpace ℂ (Fin d)) (hV : Measurable V)
    (hB : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (hZero : ∀ r ∈ R, ∫ x, ⟪V x,V (S.act r x)⟫_ℂ ∂S.measure = 0) :
    (∫ x, V x ∂S.measure) = 0 := by
  sorry

end

section
variable {G : Type} [Group G]

/-- Paper result 4.3. -/
theorem paper_lemma4_3 [Countable G] {R : Set G} (h : ¬ IsVdC R) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      Measurable f ∧ (∀ x, f x = 1 ∨ f x = -1) ∧
      (∀ r ∈ R, ∫ x, f (S.act r x) * f x ∂S.measure = 0) ∧
      (∫ x, f x ∂S.measure) ≠ 0 := by
  sorry

/-- Paper result 5.3. -/
theorem paper_theorem5_3 [Countable G] {H : Set G} (hne : H.Nonempty) :
    (IsVdC H ↔ IsOperatoriallyRecurrent H) ∧
      (IsVdC H ↔ NoConstantNegativePositiveDefinite H) := by
  sorry

end

section
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] [T2Space K]

/-- Paper result 4.5. -/
theorem paper_proposition4_5_euclidean (m ν : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    [m.IsOpenPosMeasure] [IsProbabilityMeasure ν] :
    ν = m ↔ ∀ (d : ℕ) (ρ : K →* (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d))),
      (∀ x, Continuous fun k ↦ ρ k x) → IrreducibleEuclidean ρ → (∃ k, ρ k ≠ 1) →
      ∀ x y, (∫ k, ⟪x, ρ k y⟫_ℂ ∂ν) = 0 := by
  sorry

end

section
variable {G K : Type} [Group G] [Group K] [TopologicalSpace K] [T2Space K]
  [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

/-- Paper result 4.6. -/
theorem paper_theorem4_6 [Countable G] [StandardBorelSpace K] [Nontrivial K] (R : Set G)
    (m : Measure K) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    IsVdC R ↔ IsMeasureTheoreticVdC R m := by
  sorry

end

section
variable {G : Type} [Group G] [Countable G]

/-- Paper result 5.1. -/
theorem paper_lemma5_1 (φ : G → ℝ) (hφ : RealPositiveDefinite φ) :
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
  sorry

end

section
open Real

/-- Paper result 5.2. -/
theorem paper_lemma5_2 (a b d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hS : (!![a,b; b,d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![a,b; b,d])
      {x | 0 < x 0 * x 1}).toReal = 1/2 + (1/π) * arcsin (b / √(a*d)) := by
  sorry

end

section
variable {G K : Type} [Group G] [DecidableEq G] [Countable G] [Infinite G]
  [Group K] [MetricSpace K] [CompactSpace K] [IsTopologicalGroup K]
  [MeasurableSpace K] [BorelSpace K]

/-- Paper result 4.8. -/
theorem paper_theorem4_8 (F : LeftFolnerSequence G) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] : IsFolnerVdC F R m ↔ IsMeasureTheoreticVdC R m := by
  sorry

end
end SixProblems.Submission
