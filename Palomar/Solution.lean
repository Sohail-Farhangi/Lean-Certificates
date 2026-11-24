module

public import SixProblems

@[expose] public section
noncomputable section
open Filter MeasureTheory MeasureTheory.Measure ProbabilityTheory Set WithLp
open scoped Topology symmDiff ENNReal InnerProductSpace ProbabilityTheory ComplexOrder


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
      (S.IsErgodic → T.IsErgodic) :=
  SixProblems.proposition2_1 S f hf hf0 hf1

end

section
variable {G : Type} [Group G] [Countable G] [Infinite G]

/-- Paper result 2.2(a–e). -/
theorem paper_theorem2_2 (R : Set G) (hR : R.Nonempty) :
    (NiceRecurrence R ↔ ErgodicNiceRecurrence R) ∧
    (NiceRecurrence R ↔ NiceOperatorialRecurrence R) ∧
    (NiceRecurrence R ↔ ∀ φ : G → ℝ, RealPositiveDefinite φ → 0 ≤ sSup (φ '' R)) ∧
    (NiceRecurrence R ↔ NiceVdC R) :=
  SixProblems.theorem2_2 R hR

/-- Paper result 2.2(f). -/
theorem paper_theorem2_2_abelian [IsMulCommutative G] (R : Set G) (hR : R.Nonempty) :
    NiceRecurrence R ↔
      let : TopologicalSpace G := ⊥
      let : MeasurableSpace (PontryaginDual G) := borel _
      ∀ (τ : Measure (PontryaginDual G)) [IsProbabilityMeasure τ],
        τ.real {1} ≤ sSup ((fun r ↦ ‖∫ χ : PontryaginDual G, (χ r : ℂ) ∂τ‖) '' R) :=
  SixProblems.theorem2_2_abelian R hR

/-- Paper result 3.3. -/
theorem paper_theorem3_3 {A B : Set G} (hA : ¬ NiceVdC A) (hB : ¬ NiceVdC B) :
    ¬ NiceVdC (A ∪ B) :=
  SixProblems.theorem3_3 hA hB

/-- Paper result 3.4. -/
theorem paper_corollary3_4 {m : ℕ} (D : Fin m → Set G) (hD : NiceVdC (⋃ i, D i)) :
    ∃ i, NiceVdC (D i) :=
  SixProblems.corollary3_4 D hD

end

section
variable {G : Type*} [Group G]

/-- Paper result 3.1. -/
theorem paper_lemma3_1 {I : Type*} (F : I → G → ℝ) (hF : ∀ i, RealPositiveDefinite (F i))
    (p : MvPolynomial I ℝ) (hp : ∀ d, 0 ≤ p.coeff d) :
    RealPositiveDefinite (fun g ↦ MvPolynomial.eval (fun i ↦ F i g) p) :=
  SixProblems.lemma3_1 F hF p hp

/-- Paper result 3.2. -/
theorem paper_lemma3_2 {ε M : ℝ} (hε : 0 < ε) (hεM : ε < M) :
    ∃ δ > 0, ∃ K : ℕ, ∀ x y : ℝ, x ∈ Set.Icc (-M) M → y ∈ Set.Icc (-M) M →
      (x < -ε ∨ y < -ε) → x * (2 * M + y) ^ K + y * (2 * M + x) ^ K ≤ -δ :=
  SixProblems.lemma3_2 hε hεM

end

section

/-- Paper result 4.2. -/
theorem paper_lemma4_2 {G X : Type} [Group G] [MeasurableSpace X] [StandardBorelSpace X]
    {R : Set G} (hR : IsVdC R) (S : System G X) {d : ℕ}
    (V : X → EuclideanSpace ℂ (Fin d)) (hV : Measurable V)
    (hB : ∃ C : ℝ, ∀ x, ‖V x‖ ≤ C)
    (hZero : ∀ r ∈ R, ∫ x, ⟪V x,V (S.act r x)⟫_ℂ ∂S.measure = 0) :
    (∫ x, V x ∂S.measure) = 0 :=
  SixProblems.lemma4_2 hR S V hV hB hZero

end

section
variable {G : Type} [Group G]

/-- Paper result 4.3. -/
theorem paper_lemma4_3 [Countable G] {R : Set G} (h : ¬ IsVdC R) :
    ∃ (X : Type) (mX : MeasurableSpace X) (_ : @StandardBorelSpace X mX)
      (S : @System G X _ mX) (f : X → ℝ),
      Measurable f ∧ (∀ x, f x = 1 ∨ f x = -1) ∧
      (∀ r ∈ R, ∫ x, f (S.act r x) * f x ∂S.measure = 0) ∧
      (∫ x, f x ∂S.measure) ≠ 0 :=
  SixProblems.lemma4_3 h

/-- Paper result 5.3. -/
theorem paper_theorem5_3 [Countable G] {H : Set G} (hne : H.Nonempty) :
    (IsVdC H ↔ IsOperatoriallyRecurrent H) ∧
      (IsVdC H ↔ NoConstantNegativePositiveDefinite H) :=
  SixProblems.theorem5_3 hne

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
  constructor
  · intro he d ρ hρ hI hN x y
    exact (SixProblems.proposition4_5_euclidean m ν).mp he d ρ hρ
      ⟨hI.1, fun _ _ _ ↦ Submodule.mem_top, fun W _ hW ↦ hI.2 W hW⟩ hN x y
  · intro h
    apply (SixProblems.proposition4_5_euclidean m ν).mpr
    intro d ρ hρ hI hN x y
    exact h d ρ hρ ⟨hI.1, fun W hW ↦ hI.2.2 W le_top hW⟩ hN x y

end

section
variable {G K : Type} [Group G] [Group K] [TopologicalSpace K] [T2Space K]
  [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

/-- Paper result 4.6. -/
theorem paper_theorem4_6 [Countable G] [StandardBorelSpace K] [Nontrivial K] (R : Set G)
    (m : Measure K) [IsProbabilityMeasure m] [m.IsHaarMeasure] :
    IsVdC R ↔ IsMeasureTheoreticVdC R m :=
  SixProblems.theorem4_6 R m

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
      ∀ a : G, MeasurePreserving (gaussianShift a) μ μ :=
  SixProblems.lemma5_1 φ hφ

end

section
open Real

/-- Paper result 5.2. -/
theorem paper_lemma5_2 (a b d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hS : (!![a,b; b,d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![a,b; b,d])
      {x | 0 < x 0 * x 1}).toReal = 1/2 + (1/π) * arcsin (b / √(a*d)) :=
  SixProblems.Gaussian.lemma5_2 a b d ha hd hS

end

section
variable {G K : Type} [Group G] [DecidableEq G] [Countable G] [Infinite G]
  [Group K] [MetricSpace K] [CompactSpace K] [IsTopologicalGroup K]
  [MeasurableSpace K] [BorelSpace K]

/-- Paper result 4.8. -/
theorem paper_theorem4_8 (F : LeftFolnerSequence G) (R : Set G) (m : Measure K)
    [IsProbabilityMeasure m] : IsFolnerVdC F R m ↔ IsMeasureTheoreticVdC R m :=
  SixProblems.theorem4_8 F R m

end
end SixProblems.Submission
