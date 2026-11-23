/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Combinatorics.Hindman
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Semigroup

/-!
# The Jacobs–de Leeuw–Glicksberg projection and return times

The proof entry points use the weak operator closure of a semigroup of
bounded linear operators. They isolate the decomposition, Proposition 3.4,
Theorems 1.2(v), 4.2(vi)–(ix), 5.2(i), and 5.3(ii), and Corollary 1.4
for groups in arXiv:2509.24003v3. The strict-convexity comparison proves the
revised contraction criterion and retains the counterexample to its v3 statement.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace JdLG.Submission

/-- An idempotent minimal in the order `f ≤ e` defined by `fe = ef = f`. -/
def IsMinimalIdempotent {S : Type*} [Semigroup S] (e : S) : Prop :=
  e * e = e ∧ ∀ f : S, f * f = f → f * e = f → e * f = f → f = e

section Largeness

variable {S : Type*} [Semigroup S]

/-- Every finite set has a right translate contained in `A`. -/
def IsThick (A : Set S) : Prop :=
  ∀ F : Finset S, ∃ x : S, ∀ a ∈ F, a * x ∈ A

/-- A nonempty finite union of left preimages of `A` is thick. -/
def IsPiecewiseSyndetic (A : Set S) : Prop :=
  ∃ H : Finset S, H.Nonempty ∧ IsThick {x | ∃ h ∈ H, h * x ∈ A}

/-- A thickly syndetic set meets every piecewise syndetic set. -/
def IsThicklySyndetic (A : Set S) : Prop :=
  ∀ B : Set S, IsPiecewiseSyndetic B → (A ∩ B).Nonempty

/-- A left ideal is stable under arbitrary multiplication on the left. -/
def LeftIdeal (L : Set S) : Prop :=
  ∀ a : S, ∀ ⦃b : S⦄, b ∈ L → a * b ∈ L

/-- A two-sided ideal is stable under arbitrary multiplication on both sides. -/
def IsTwoSidedIdeal (I : Set S) : Prop :=
  LeftIdeal I ∧ ∀ ⦃a⦄, a ∈ I → ∀ b, a * b ∈ I

/-- The intersection of the nonempty two-sided ideals. -/
def smallestIdeal (M : Type*) [Semigroup M] : Set M :=
  {a | ∀ I : Set M, I.Nonempty → IsTwoSidedIdeal I → a ∈ I}

end Largeness

/-- The Stone–Čech product on ultrafilters of a discrete semigroup. -/
scoped instance (priority := 1100) ultrafilterSemigroup {S : Type*} [Semigroup S] :
    Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

section WeakOperator

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every operator action on `x` can be reversed by a second operator. -/
def IsReversible (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  ∀ a : S, ∃ b : S, ρ b (ρ a x) = x

/-- Some operator acts on `x` as zero. -/
def IsAlmostWeaklyStable (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  ∃ a : S, ρ a x = 0

/-- The representation viewed in the weak operator topology. -/
def weakRepresentation (π : S →ₙ* (E →L[𝕜] E)) : S →ₙ* (E →WOT[𝕜] E) :=
  ContinuousLinearMapWOT.ringEquiv.symm.toMulHom.comp π

/-- The weak operator closure of the represented semigroup. -/
def weakOperatorClosure (π : S →ₙ* (E →L[𝕜] E)) : Subsemigroup (E →WOT[𝕜] E) :=
  (weakRepresentation π).srange.topologicalClosure

/-- The action of the closed operator semigroup. -/
def closureAction (π : S →ₙ* (E →L[𝕜] E)) : (weakOperatorClosure π) →ₙ* (E →L[𝕜] E) :=
  ContinuousLinearMapWOT.ringEquiv.toMulHom.comp (MulMemClass.subtype (weakOperatorClosure π))

/-- The weak operator closure is compact and has a unique minimal idempotent. -/
def IsJdLGAdmissible (π : S →ₙ* (E →L[𝕜] E)) : Prop :=
  IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E)) ∧
    ∃! e : weakOperatorClosure π, IsMinimalIdempotent e

end WeakOperator

section FixedPoints

open ContinuousLinearMapWOT Set

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every operator in `operators` fixes `x`. -/
def IsFixedBy (operators : Subsemigroup (E →WOT[𝕜] E)) (x : E) : Prop :=
  ∀ A ∈ operators, A x = x

end FixedPoints

section WeakOperator

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparatingDual 𝕜 E]

/-- Equation (1) and Section 2.2. The minimal idempotent is the projection. -/
theorem decomposition {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) :
    ∃ e : weakOperatorClosure π,
      IsMinimalIdempotent e ∧
      (∀ a : weakOperatorClosure π, e * a = a * e) ∧
      IsCompl (LinearMap.range (closureAction π e).toLinearMap)
        (LinearMap.ker (closureAction π e).toLinearMap) ∧
      (∀ x : E, IsReversible (closureAction π) x ↔
        x ∈ LinearMap.range (closureAction π e).toLinearMap) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        x ∈ LinearMap.ker (closureAction π e).toLinearMap :=
  JdLG.decomposition_of_admissible hπ

/-- Theorem 5.2(i). Idempotents in the closure of the smallest Stone–Čech ideal
converge to the JdLG projection. -/
theorem ultrafilter_projection {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) :
    ∃ e : weakOperatorClosure π, IsMinimalIdempotent e ∧
      (∀ p ∈ closure (smallestIdeal (Ultrafilter S)), p * p = p →
        Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (e : E →WOT[𝕜] E))) ∧
      (∀ x : E, IsReversible (closureAction π) x ↔
        x ∈ LinearMap.range (closureAction π e).toLinearMap) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        x ∈ LinearMap.ker (closureAction π e).toLinearMap :=
  JdLG.ultrafilter_limit_eq_jdlg_projection hπ

/-- Theorem 5.3(ii). Almost weak stability is equivalent to thickly syndetic
return to every weak neighborhood of zero. -/
theorem thicklySyndetic_returns [Nonempty S] {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ U : Set (WeakSpace 𝕜 E), IsOpen U → 0 ∈ U →
        IsThicklySyndetic {s | toWeakSpace 𝕜 E (π s x) ∈ U} :=
  JdLG.stable_iff_thicklySyndetic_weak_return hπ x

end WeakOperator

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Proposition 3.4. A unique common fixed vector in each orbit yields a
two-sided zero in the operator semigroup and identifies the reversible part. -/
theorem unique_fixed_points (operators : Subsemigroup (E →WOT[𝕜] E))
    (hcompact : IsCompact (operators : Set (E →WOT[𝕜] E)))
    (hfixed : ∀ x : E, ∃! y : E,
      (∃ A ∈ operators, A x = y) ∧ IsFixedBy operators y) :
    ∃ P ∈ operators, (∀ A ∈ operators, A * P = P ∧ P * A = P) ∧
      (∀ x : E, (∀ A ∈ operators, ∃ B ∈ operators, B (A x) = x) ↔
        IsFixedBy operators x) ∧
      ∀ x : E, (∃ A ∈ operators, A x = 0) ↔ P x = 0 :=
  JdLG.decomposition_of_unique_fixed_point operators hcompact hfixed


/-- Theorem 1.2(v). A semigroup of contractions on complex Lᵖ is admissible
for any measure space and 1 < p < ∞. -/
theorem lp_contractions {X M : Type*} [MeasurableSpace X] [Semigroup M] [Nonempty M]
    (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞)
    (π : M →ₙ* (Lp ℂ p μ →L[ℂ] Lp ℂ p μ)) (hπ : ∀ s, ‖π s‖ ≤ 1) :
    IsJdLGAdmissible π := by
  exact JdLG.admissible_of_complexLp_contractions μ hp hp_top π hπ

/-- Corollary 1.4. Every unital group representation with compact weak
operator closure is admissible. -/
theorem group_admissible {G : Type*} [Group G] (π : G →* (E →L[𝕜] E))
    (hπ : IsCompact (weakOperatorClosure π.toMulHom : Set (E →WOT[𝕜] E))) :
    IsJdLGAdmissible π.toMulHom := by
  exact JdLG.admissible_of_group π hπ

/-- Theorem 4.2(vi) and (ix). If the orbit lies in a weakly compact set,
density-one weak returns along compact Radon blocks of increasing mass
are equivalent to weak convergence on a single density-one set. -/
theorem radon_density_one_weak_decay {E' X : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop]
    (F : ℕ → Set X) (hF : ∀ n, IsCompact (F n)) (hFpos : ∀ n, μ (F n) ≠ 0)
    (hGrow : Tendsto (fun n ↦ μ (F n)) atTop (𝓝 ⊤))
    (φ : X → WeakSpace ℂ E') (hφ : Continuous φ) {K : Set (WeakSpace ℂ E')} (hK : IsCompact K)
    (hφK : range φ ⊆ K) (y : WeakSpace ℂ E') :
    let ν := fun n ↦ (μ (F n))⁻¹ • μ.restrict (F n)
    (∀ U : Set (WeakSpace ℂ E'), IsOpen U → y ∈ U →
      Tendsto (fun n ↦ (ν n).real (φ ⁻¹' U)) atTop (𝓝 1)) ↔
    ∃ A : Set X, MeasurableSet A ∧ Tendsto (fun n ↦ (ν n).real A) atTop (𝓝 1) ∧
      Tendsto φ (cocompact X ⊓ 𝓟 A) (𝓝 y) := by
  exact JdLG.density_one_weak_tendsto_iff_measuredBlocks μ F hF hFpos hGrow φ hφ hK hφK y

/-- Revised Theorem 1.2(iv). Contractions on a space with strictly convex
primal and dual norms are admissible when the weak operator closure is compact. -/
theorem strict_convexity_contractions {M F : Type*} [Semigroup M] [Nonempty M]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [StrictConvexSpace ℝ F]
    [StrictConvexSpace ℝ (StrongDual ℂ F)]
    (π : M →ₙ* (F →L[ℂ] F))
    (hcompact : IsCompact (weakOperatorClosure π : Set (F →WOT[ℂ] F)))
    (hcontractions : ∀ s, ‖π s‖ ≤ 1) : IsJdLGAdmissible π :=
  JdLG.admissible_of_strictConvex_contractions π hcompact hcontractions

/-- The two-dimensional counterexample to the v3 statement of Theorem 1.2(iv). -/
theorem strict_convexity_counterexample :
    let H := EuclideanSpace ℂ (Fin 2)
    StrictConvexSpace ℝ H ∧ StrictConvexSpace ℝ (StrongDual ℂ H) ∧
      ∃ T : Subsemigroup (H →L[ℂ] H),
        IsCompact (weakOperatorClosure (MulMemClass.subtype T) : Set (H →WOT[ℂ] H)) ∧
        ¬ IsJdLGAdmissible (MulMemClass.subtype T) := by
  let π := JdLG.PrintedClaimCounterexample.representation
  obtain ⟨h, h', hcompact, hadm⟩ :=
    JdLG.PrintedClaimCounterexample.printed_theorem_1_2_iv_counterexample
  let T := π.srange
  let H := EuclideanSpace ℂ (Fin 2)
  have hEq : (JdLG.weakOperatorClosure (MulMemClass.subtype T) : Set (H →WOT[ℂ] H)) =
      (JdLG.weakOperatorClosure π : Set (H →WOT[ℂ] H)) := by
    change closure (range (JdLG.weakRepresentation (MulMemClass.subtype T))) =
      closure (range (JdLG.weakRepresentation π))
    congr 1
    ext A
    constructor
    · rintro ⟨⟨B, ⟨s, rfl⟩⟩, rfl⟩
      exact mem_range_self s
    · rintro ⟨s, rfl⟩
      exact ⟨⟨π s, mem_range_self s⟩, rfl⟩
  exact ⟨h, h', T, hEq.symm ▸ hcompact,
    fun hT ↦ hadm ((JdLG.admissible_iff_of_equal_weakOperatorClosures _ _ hEq).mp hT)⟩

end JdLG.Submission
