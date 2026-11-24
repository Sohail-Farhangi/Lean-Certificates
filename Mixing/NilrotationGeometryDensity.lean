/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ErgodicBarycenters
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # Dense orbits for ergodic compact homogeneous systems -/

@[expose] public section

namespace Mixing

open Filter MeasureTheory Set TopologicalSpace
open scoped Pointwise

/-- On a second-countable space with positive measure on every nonempty open set,
almost every point of an ergodic countable-group action has dense orbit. -/
theorem System.ae_denseRange_act_of_ergodic {G X : Type*} [Group G] [Countable G]
    [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (S : System G X) (hS : S.IsErgodic)
    (hPos : ∀ U : Set X, IsOpen U → U.Nonempty → S.measure U ≠ 0) :
    ∀ᵐ x ∂S.measure, DenseRange (fun g : G ↦ S.act g x) := by
  let Basis := countableBasis X
  let E (U : Basis) := ⋃ n : G, S.act n ⁻¹' (U : Set X)
  have hE (U : Basis) : ∀ᵐ x ∂S.measure, x ∈ E U := by
    have hU : MeasurableSet (U : Set X) := (isOpen_of_mem_countableBasis U.2).measurableSet
    have hm : MeasurableSet (E U) := MeasurableSet.iUnion fun n ↦ (S.preserves n).measurable hU
    have hi (g : G) : S.act g ⁻¹' E U = E U := by
      ext x
      simp only [E, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n * g, by simpa only [S.act_mul, Function.comp_apply] using hn⟩
      · rintro ⟨n, hn⟩
        refine ⟨n * g⁻¹, ?_⟩
        change (S.act (n * g⁻¹) ∘ S.act g) x ∈ (U : Set X)
        rw [← S.act_mul, mul_assoc, inv_mul_cancel, mul_one]
        exact hn
    rcases eventuallyEmptyOrUniv_iff.mp
      (hS (E U) hm (fun g ↦ by rw [hi g])) with h | h
    · exact h
    · exfalso
      apply hPos U (isOpen_of_mem_countableBasis U.2) (nonempty_of_mem_countableBasis U.2)
      have hsub : (U : Set X) ⊆ E U := by
        intro x hx
        change x ∈ ⋃ n : G, S.act n ⁻¹' (U : Set X)
        exact mem_iUnion.mpr ⟨1, by simpa [S.act_one] using hx⟩
      have hnull : S.measure (E U) = 0 := by
        rw [show E U = {a | a ∈ E U} from Set.ext (fun _ ↦ Iff.rfl)]
        simpa only [not_not] using ae_iff.mp h
      exact measure_mono_null hsub hnull
  filter_upwards [ae_all_iff.mpr hE] with x hx
  apply (isBasis_countableBasis X).dense_iff.mpr
  intro U hU _
  obtain ⟨g, hg⟩ := mem_iUnion.mp (hx ⟨U, hU⟩)
  exact ⟨S.act g x, hg, mem_range_self g⟩

/-- A transitive invariant probability on a compact homogeneous space gives positive
measure to every nonempty open set. -/
theorem measure_ne_zero_of_compact_transitive_action
    {G X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X] [CompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [MulAction.IsPretransitive G X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (hInv : ∀ g : G, MeasurePreserving (fun x : X ↦ g • x) μ μ)
    (U : Set X) (hU : IsOpen U) (hNonempty : U.Nonempty) : μ U ≠ 0 := by
  rintro hzero
  obtain ⟨x, hx⟩ := hNonempty
  let t (g : G) := (fun y : X ↦ g • y) ⁻¹' U
  have ho (g : G) : IsOpen (t g) := hU.preimage (continuous_const_smul g)
  have hcover : (univ : Set X) ⊆ ⋃ g, t g := by
    intro y _
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G y x
    exact mem_iUnion.mpr ⟨g, by change g • y ∈ U; rw [hg]; exact hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover t ho hcover
  have hz (g : G) : μ (t g) = 0 :=
    ((hInv g).measure_preimage hU.measurableSet.nullMeasurableSet).trans hzero
  have hz' : μ (⋃ g ∈ s, t g) = 0 :=
    measure_biUnion_null_iff s.finite_toSet.countable |>.2 (fun g _ ↦ hz g)
  exact one_ne_zero ((measure_univ (μ := μ)).symm.trans (measure_mono_null hs hz'))

/-- An ergodic quotient rotation with invariant probability has a lifted dense coset
orbit in its acting group. The chosen orbit point need not be the identity coset. -/
theorem nilrotation_exists_dense_lifted_cosets {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G]
    (L : Subgroup G) [CompactSpace (G ⧸ L)] [MeasurableSpace (G ⧸ L)]
    [OpensMeasurableSpace (G ⧸ L)] (a : G)
    (S : System (Multiplicative ℤ) (G ⧸ L)) (hS : S.IsErgodic)
    (hAct : ∀ (n : ℤ) (x : G ⧸ L), S.act (Multiplicative.ofAdd n) x = a ^ n • x)
    (hInv : ∀ g : G, MeasurePreserving (fun x : G ⧸ L ↦ g • x) S.measure S.measure) :
    ∃ d : G, Dense {x : G | ∃ (n : ℤ) (γ : L), a ^ n * d * (γ : G) = x} := by
  let : Countable (Multiplicative ℤ) := by change Countable ℤ; infer_instance
  have hPos := measure_ne_zero_of_compact_transitive_action S.measure hInv
  obtain ⟨x, hx⟩ := (S.ae_denseRange_act_of_ergodic hS hPos).exists
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨d, ?_⟩
  have hR : (Set.range (fun g : Multiplicative ℤ ↦ S.act g (QuotientGroup.mk d))) =
      QuotientGroup.mk '' Set.range (fun n : ℤ ↦ a ^ n * d) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨a ^ g.toAdd * d, mem_range_self g.toAdd, ?_⟩
      change QuotientGroup.mk (a ^ g.toAdd * d) =
        S.act (Multiplicative.ofAdd g.toAdd) (QuotientGroup.mk d)
      rw [hAct]
      rfl
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd n, hAct n _⟩
  rw [DenseRange, hR] at hx
  have hDense := QuotientGroup.dense_image_mk.mp hx
  refine hDense.mono ?_
  rintro _ ⟨_, ⟨n, rfl⟩, γ, hγ, rfl⟩
  exact ⟨n, ⟨γ, hγ⟩, rfl⟩

/-- A dense lifted orbit stays dense when the stabilizer is enlarged. -/
theorem nilrotation_dense_lifted_cosets_mono {G : Type*} [Group G] [TopologicalSpace G]
    {L H : Subgroup G} (hLH : L ≤ H) {a d : G}
    (h : Dense {x : G | ∃ (n : ℤ) (γ : L), a ^ n * d * (γ : G) = x}) :
    Dense {x : G | ∃ (n : ℤ) (γ : H), a ^ n * d * (γ : G) = x} := by
  refine h.mono ?_
  rintro x ⟨n, γ, he⟩
  exact ⟨n, ⟨γ, hLH γ.2⟩, he⟩

end Mixing
