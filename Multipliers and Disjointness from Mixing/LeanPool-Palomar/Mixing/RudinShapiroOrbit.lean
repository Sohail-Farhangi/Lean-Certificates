/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.EmpiricalOrbitLaw
public import Mixing.RudinShapiroCorrelations
public import Mixing.System

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped Topology

/-- Two-sided sign words, written as Boolean sequences. -/
abbrev SignWords := ℤ → Bool

/-- The shift of a two-sided word by an integer. -/
def signWordShift (k : ℤ) (w : SignWords) : SignWords := fun j ↦ w (j + k)

theorem signWordShift_continuous (k : ℤ) : Continuous (signWordShift k) :=
  continuous_pi fun j ↦ continuous_apply (j + k)

theorem signWordShift_zero : signWordShift 0 = id := by
  funext w j
  simp [signWordShift]

theorem signWordShift_add (k l : ℤ) :
    signWordShift (k + l) = signWordShift k ∘ signWordShift l := by
  funext w j
  simp [signWordShift, add_assoc]

theorem signWordShift_iterate (n : ℕ) : (signWordShift 1)^[n] = signWordShift n := by
  induction n with
  | zero => simpa using signWordShift_zero.symm
  | succ n ih =>
    rw [Function.iterate_succ', ih, Nat.cast_succ, add_comm, signWordShift_add]

/-- A word with the Rudin–Shapiro signs at all nonnegative coordinates. -/
def rudinShapiroWord : SignWords := fun j ↦ decide (rudinShapiro j.toNat = 1)

/-- Convert a Boolean coordinate to its real sign. -/
def signValue (b : Bool) : ℝ := if b then 1 else -1

theorem signValue_rudinShapiroWord (j : ℤ) :
    signValue (rudinShapiroWord j) = rudinShapiro j.toNat := by
  have hS := rudinShapiro_sq j.toNat
  have h := mul_eq_zero.mp (show (rudinShapiro j.toNat - 1) * (rudinShapiro j.toNat + 1) = 0
    by nlinarith)
  rcases h with h | h
  · simp [signValue, rudinShapiroWord, sub_eq_zero.mp h]
  · have hr : rudinShapiro j.toNat = -1 := by linarith
    norm_num [signValue, rudinShapiroWord, hr]

private def pairSignObservable (k : ℤ) : C(SignWords, ℝ) where
  toFun w := signValue (w 0) * signValue (w k)
  continuous_toFun := by
    have hc : Continuous signValue := continuous_of_discreteTopology
    exact (hc.comp (continuous_apply 0)).mul (hc.comp (continuous_apply k))

/-- The invariant probability law obtained from dyadic samples of the
Rudin–Shapiro orbit. The selected limit law has the canonical one-coordinate
correlations. -/
def rudinShapiroOrbitLaw (p : Ultrafilter ℕ) : ProbabilityMeasure SignWords :=
  dyadicOrbitLaw (signWordShift 1) rudinShapiroWord p

theorem rudinShapiroOrbitLaw_preserving (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (k : ℤ) :
    MeasurePreserving (signWordShift k) (rudinShapiroOrbitLaw p : Measure SignWords)
      (rudinShapiroOrbitLaw p : Measure SignWords) := by
  let ν := (rudinShapiroOrbitLaw p : Measure SignWords)
  let H : AddSubgroup ℤ :=
    { carrier := {j | MeasurePreserving (signWordShift j) ν ν}
      zero_mem' := by
        change MeasurePreserving (signWordShift 0) ν ν
        rw [signWordShift_zero]
        exact MeasurePreserving.id ν
      add_mem' := by
        intro a b ha hb
        change MeasurePreserving (signWordShift a) ν ν at ha
        change MeasurePreserving (signWordShift b) ν ν at hb
        change MeasurePreserving (signWordShift (a + b)) ν ν
        rw [signWordShift_add]
        exact ha.comp hb
      neg_mem' := by
        intro a ha
        change MeasurePreserving (signWordShift a) ν ν at ha
        have hm := (signWordShift_continuous (-a)).measurable
        refine ⟨hm, ?_⟩
        calc
          ν.map (signWordShift (-a)) = (ν.map (signWordShift a)).map (signWordShift (-a)) := by
            rw [ha.map_eq]
          _ = ν := by
            rw [Measure.map_map hm ha.measurable, ← signWordShift_add, neg_add_cancel,
              signWordShift_zero, Measure.map_id] }
  have hOne : (1 : ℤ) ∈ H :=
    dyadicOrbitLaw_preserving (signWordShift 1) (signWordShift_continuous 1) rudinShapiroWord p hp
  change k ∈ H
  simpa using H.zsmul_mem hOne k

/-- The measured shift from the Rudin–Shapiro orbit law. -/
def rudinShapiroOrbitSystem (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    System (Multiplicative ℤ) SignWords where
  measure := rudinShapiroOrbitLaw p
  probability := inferInstance
  act g := signWordShift g.toAdd
  act_one := signWordShift_zero
  act_mul g h := signWordShift_add g.toAdd h.toAdd
  preserves g := rudinShapiroOrbitLaw_preserving p hp g.toAdd

/-- The actual invariant orbit law has vanishing nonzero correlations of
the coordinate sign in the Rudin–Shapiro sequence. -/
theorem integral_rudinShapiro_pairSign (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (k : ℕ) :
    (∫ w, signValue (w 0) * signValue (w k) ∂(rudinShapiroOrbitLaw p : Measure SignWords)) =
      if k = 0 then 1 else 0 := by
  have h := tendsto_integral_dyadicOrbitLaw (signWordShift 1) rudinShapiroWord p
    (pairSignObservable k)
  have he (n : ℕ) :
      (∑ i ∈ Finset.range (2 ^ n), pairSignObservable k ((signWordShift 1)^[i] rudinShapiroWord)) /
        (2 ^ n : ℝ) = rudinShapiroCorrelation n k := by
    unfold rudinShapiroCorrelation
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [signWordShift_iterate]
    change signValue (rudinShapiroWord (0 + i)) * signValue (rudinShapiroWord (k + i)) = _
    have hNat : ((k : ℤ) + (i : ℤ)).toNat = i + k := by omega
    rw [zero_add, signValue_rudinShapiroWord, signValue_rudinShapiroWord, hNat, Int.toNat_natCast]
  simp_rw [he] at h
  by_cases hk : k = 0
  · subst k
    simp only [rudinShapiroCorrelation_zero] at h
    change (∫ w, pairSignObservable 0 w ∂(rudinShapiroOrbitLaw p : Measure SignWords)) = 1
    exact tendsto_nhds_unique h tendsto_const_nhds
  · exact (tendsto_nhds_unique h ((rudinShapiro_dyadic_correlations k).1 hk |>.mono_left hp)).trans
      (ite_eq_right hk).symm

end Mixing
