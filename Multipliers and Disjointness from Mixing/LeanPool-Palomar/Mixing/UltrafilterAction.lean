module

public import Mixing.WeakOperatorCompactness
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Combinatorics.Hindman
public import Mathlib.Topology.Compactification.StoneCech

/-!
# The ultrafilter operator action

The paper uses additive notation for its group. Here the group law is written
multiplicatively, so that the paper's `p+q` appears as `p*q`.
-/

@[expose] public section

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
