/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRigidityMultiplier
public import JdLG.PaperExamplesRigidDensity
public import JdLG.Stable
public import Mathlib.Topology.Instances.ZMod

/-!
# Explicit rigid unitary examples

Haar measure on the infinite binary group has null singletons. By coding its
points into a circle-valued rigidity phase, multiplication on its complex
`L²` space gives a nonzero strongly rigid unitary representation with no
nonzero eigenvectors.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter MeasureTheory
open scoped Topology ENNReal

/-- The compact binary group, written multiplicatively. -/
abbrev BinaryGroup := Multiplicative (ℕ → ZMod 2)

instance : MeasurableSpace (ZMod 2) := borel _

instance : BorelSpace (ZMod 2) := ⟨rfl⟩

instance : IsTopologicalAddGroup (ZMod 2) := isTopologicalAddGroup_of_discreteTopology

instance : T2Space BinaryGroup := inferInstanceAs (T2Space (ℕ → ZMod 2))

instance : MeasurableSingletonClass BinaryGroup where
  measurableSet_singleton _ := isClosed_singleton.measurableSet

instance : Infinite BinaryGroup := Infinite.of_injective
  (fun n : ℕ ↦ Multiplicative.ofAdd (Pi.single n (1 : ZMod 2))) (by
    classical
    intro n m h
    by_contra hne
    have hh := congrArg (fun v : BinaryGroup ↦ v.toAdd n) h
    change (Pi.single n (1 : ZMod 2) : ℕ → ZMod 2) n =
      (Pi.single m (1 : ZMod 2) : ℕ → ZMod 2) n at hh
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hh
    exact one_ne_zero hh)

/-- Haar probability on the compact binary group. -/
noncomputable def binaryMeasure : Measure BinaryGroup := normalizedHaar BinaryGroup

instance : IsProbabilityMeasure binaryMeasure := inferInstanceAs
  (IsProbabilityMeasure (normalizedHaar BinaryGroup))

instance : NullSingletonClass binaryMeasure where
  measure_singleton a := by
    change normalizedHaar BinaryGroup {a} = 0
    let μ := normalizedHaar BinaryGroup
    rw [Measure.haar_singleton μ a]
    by_contra hnon
    have ht := (Set.infinite_univ : (Set.univ : Set BinaryGroup).Infinite).meas_eq_top
      (μ := μ) ⟨μ {1}, hnon, fun x _ ↦ (Measure.haar_singleton μ x).ge⟩
    exact ENNReal.one_ne_top ((measure_univ (μ := μ)).symm.trans ht)

/-- The bit sequence corresponding to a point of the compact binary group. -/
def binaryBits (a : BinaryGroup) (n : ℕ) : Bool := decide (a.toAdd n = 1)

theorem continuous_binaryBits : Continuous binaryBits := by
  refine continuous_pi fun n ↦ ?_
  change Continuous (fun a : ℕ → ZMod 2 ↦ decide (a n = 1))
  exact (show Continuous (fun b : ZMod 2 ↦ decide (b = 1)) from
    continuous_of_discreteTopology).comp (continuous_apply n)

theorem binaryBits_injective : Function.Injective binaryBits := by
  have hcases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  intro a b h
  change a.toAdd = b.toAdd
  funext n
  have hh := congrFun h n
  change decide (a.toAdd n = 1) = decide (b.toAdd n = 1) at hh
  rcases hcases (a.toAdd n) with ha | ha <;>
    rcases hcases (b.toAdd n) with hb | hb <;>
    simp_all

/-- The Hilbert space carrying the explicit rigid representations. -/
noncomputable abbrev RigidityHilbert := Lp ℂ 2 binaryMeasure

/-- The constant-one vector, a nonzero vector in the probability space. -/
noncomputable def rigidityOne : RigidityHilbert :=
  (memLp_const (μ := binaryMeasure) (p := 2) (1 : ℂ)).toLp _

theorem rigidityOne_ne_zero : rigidityOne ≠ 0 := by
  intro h
  have hc : (rigidityOne : BinaryGroup → ℂ) =ᵐ[binaryMeasure] fun _ ↦ 1 :=
    (memLp_const (μ := binaryMeasure) (p := 2) (1 : ℂ)).coeFn_toLp
  rw [h] at hc
  have hzero : (fun _ : BinaryGroup ↦ (0 : ℂ)) =ᵐ[binaryMeasure] fun _ ↦ 1 :=
    (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := binaryMeasure)).symm.trans hc
  obtain ⟨_, hfalse⟩ := hzero.exists
  exact zero_ne_one hfalse

/-- A sufficiently late tail of a lacunary sequence has ratio at least eight
and starts above four. -/
theorem LacunarySequence.exists_fast_tail (r : LacunarySequence) :
    ∃ N : ℕ, (4 : ℝ) ≤ (r.value N : ℝ) ∧
      ∀ n, 8 * (r.value (n + N) : ℝ) ≤ (r.value (n + 1 + N) : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_atTop.1 r.ratiosDiverge) 8)
  have hp (n : ℕ) : (0 : ℝ) < (r.value n : ℝ) := Nat.cast_pos.2 (r.positive n)
  have hfirst := (le_div_iff₀ (hp N)).1 (hN N le_rfl)
  refine ⟨N + 1, ?_, fun n ↦ ?_⟩
  · have h₁ : (1 : ℝ) ≤ (r.value N : ℝ) := by exact_mod_cast r.positive N
    linarith
  · have ht := (le_div_iff₀ (hp (n + (N + 1)))).1 (hN (n + (N + 1)) (by omega))
    simpa only [Nat.add_right_comm n (N + 1) 1] using ht

/-- For each positive sequence whose successive ratios diverge, the explicit
unitary component is strongly rigid along that sequence and has no nonzero
eigenvectors. This supplies the cited existence input of Example 4.7. -/
theorem exists_rigid_unitary_component (r : LacunarySequence) :
    ∃ U : Multiplicative ℤ →* (RigidityHilbert ≃ₗᵢ[ℂ] RigidityHilbert),
      (∀ x : RigidityHilbert,
        Tendsto (fun n ↦ U (Multiplicative.ofAdd (r.value n : ℤ)) x) atTop (𝓝 x)) ∧
      ∀ c : ℂ, ∀ x : RigidityHilbert, U (Multiplicative.ofAdd 1) x = c • x → x = 0 := by
  obtain ⟨N, hN₀, hN⟩ := r.exists_fast_tail
  let q (n : ℕ) := r.value (n + N)
  have hq (n : ℕ) : (0 : ℝ) < (q n : ℝ) := Nat.cast_pos.2 (r.positive _)
  have hqRatio : Tendsto (fun n ↦ (q (n + 1) : ℝ) / (q n : ℝ)) atTop atTop := by
    have ht := r.ratiosDiverge.comp (tendsto_add_atTop_nat N)
    change Tendsto (fun n : ℕ ↦ (r.value (n + N + 1) : ℝ) / (r.value (n + N) : ℝ))
      atTop atTop at ht
    simpa only [q, Nat.add_right_comm] using ht
  let u : BinaryGroup → Circle :=
    circlePhase (fun n ↦ (q n : ℝ)) hN hq ∘ binaryBits
  have hcont : Continuous u :=
    (continuous_circlePhase (fun n ↦ (q n : ℝ)) hN hq).comp continuous_binaryBits
  have hinj : Function.Injective u :=
    (circlePhase_injective (fun n ↦ (q n : ℝ)) hN hq
      (by simpa only [q, zero_add] using hN₀)).comp binaryBits_injective
  refine ⟨circleMulRepresentation u hcont.measurable, ?_, ?_⟩
  · intro x
    apply (tendsto_add_atTop_iff_nat N).1
    have ht : TendstoUniformly (fun n a ↦ u a ^ q n) (fun _ ↦ (1 : Circle)) atTop :=
      (circlePhase_uniform_rigidity q hN hq hqRatio).comp binaryBits
    exact circleMulRepresentation_strongly_rigid u hcont.measurable q ht x
  · exact circleMulRepresentation_no_eigenvectors u hcont.measurable hinj

end JdLG.PaperExamplesRigid
