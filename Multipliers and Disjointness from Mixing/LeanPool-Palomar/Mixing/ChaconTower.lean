/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.TwoLevelIntegralTower
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The classical Chacon tower over the ternary odometer

This is the height-one integral tower description in §2.2 of Janvresse, Prikhod’ko,
de la Rue and Ryzhikov, "Weak limits of powers of Chacon's automorphism"
(arXiv:1301.2904). The height is two over the spacer cylinders and one elsewhere.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Topology Classical

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The additive group of 3-adic integers, underlying the ternary odometer. -/
abbrev ChaconOdometer := ℤ_[3]

noncomputable instance : MeasurableSpace ChaconOdometer := borel ChaconOdometer
instance : BorelSpace ChaconOdometer := ⟨rfl⟩

/-- Haar probability of the ternary odometer, normalized on the whole compact group. -/
noncomputable def chaconOdometerMeasure : Measure ChaconOdometer :=
  addHaarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩

instance : IsProbabilityMeasure chaconOdometerMeasure :=
  ⟨addHaarMeasure_self (K₀ := ⟨⟨univ, isCompact_univ⟩, by simp⟩)⟩

instance : IsAddHaarMeasure chaconOdometerMeasure := by
  unfold chaconOdometerMeasure
  infer_instance

/-- In particular the exceptional odometer point with all digits equal to two has measure zero. -/
theorem chaconOdometerMeasure_singleton (x : ChaconOdometer) :
    chaconOdometerMeasure {x} = 0 := by
  let A (n : ℕ) : Set ChaconOdometer := {(n : ChaconOdometer)}
  have hm (n : ℕ) : MeasurableSet (A n) := measurableSet_singleton _
  have hDisj : Pairwise (fun i j ↦ _root_.Disjoint (A i) (A j)) := by
    intro i j hij
    exact Set.disjoint_singleton.mpr fun he ↦ hij (Nat.cast_injective he)
  have hMeasure (n : ℕ) : chaconOdometerMeasure (A n) = chaconOdometerMeasure {x} :=
    (addHaar_singleton chaconOdometerMeasure (n : ChaconOdometer)).trans
      (addHaar_singleton chaconOdometerMeasure x).symm
  by_contra hn
  have he : chaconOdometerMeasure (⋃ n, A n) = ⊤ := by
    rw [measure_iUnion hDisj hm]
    simp_rw [hMeasure]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hn
  exact (measure_ne_top _ _) he

instance : NullSingletonClass chaconOdometerMeasure := ⟨chaconOdometerMeasure_singleton⟩

/-- The ordinary integers in the odometer, including the exceptional orbit, form a null set. -/
theorem chaconOdometer_integerPoints_null :
    chaconOdometerMeasure (Set.range (fun n : ℤ ↦ (n : ChaconOdometer))) = 0 :=
  (Set.countable_range _).measure_zero _

/-- Adding one on the ternary odometer. -/
noncomputable def chaconOdometerStep : ChaconOdometer ≃ᵐ ChaconOdometer :=
  (Homeomorph.addRight (1 : ChaconOdometer)).toMeasurableEquiv

theorem chaconOdometerStep_preserving :
    MeasurePreserving chaconOdometerStep chaconOdometerMeasure chaconOdometerMeasure := by
  change MeasurePreserving (fun x : ChaconOdometer ↦ x + 1) chaconOdometerMeasure chaconOdometerMeasure
  simpa only [add_comm (_ : ChaconOdometer) 1] using
    measurePreserving_add_left chaconOdometerMeasure 1

/-- The additional level occurs when the first ternary digit, starting from the
least significant end, which is different from two is one. The congruence can
equivalently be imposed on `x + 1` at the first nonzero position. -/
noncomputable def chaconSpacer : Set ChaconOdometer :=
  ⋃ n : ℕ, {x | ‖x + 1 - (2 : ChaconOdometer) * (3 : ChaconOdometer) ^ n‖ ≤
    ((3 : ℕ) : ℝ) ^ (-(n + 1 : ℕ) : ℤ)}

theorem chaconSpacer_measurable : MeasurableSet chaconSpacer := by
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_le (by fun_prop) measurable_const

/-- The exact ternary-cylinder criterion for the spacer. For example, at
index `n = 0` it requires `x ≡ 1 (mod 3)`. -/
theorem mem_chaconSpacer_iff_modular (x : ChaconOdometer) :
    x ∈ chaconSpacer ↔ ∃ n : ℕ, PadicInt.toZModPow (n + 1) (x + 1) =
      (2 : ZMod (3 ^ (n + 1))) * (3 : ZMod (3 ^ (n + 1))) ^ n := by
  simp only [chaconSpacer, mem_iUnion, mem_ofPred_eq]
  refine exists_congr fun n ↦ ?_
  rw [PadicInt.norm_le_pow_iff_mem_span_pow (p := 3) _ (n + 1),
    ← PadicInt.ker_toZModPow (p := 3) (n + 1),
    RingHom.mem_ker, map_sub, sub_eq_zero, map_mul, map_pow, map_ofNat, map_ofNat]

/-- The probability-preserving Chacon tower system from the ternary odometer.
It uses counting measure on the allowed levels and Haar probability on the
odometer base, followed by a common normalization. -/
noncomputable def chaconTowerSystem : System (Multiplicative ℤ) (ChaconOdometer × Bool) :=
  twoLevelTowerSystem chaconOdometerStep chaconOdometerMeasure chaconOdometerStep_preserving
    chaconSpacer chaconSpacer_measurable

/-- The first step of the Chacon tower goes up precisely over a spacer cylinder. -/
theorem chaconTower_bottom_step (x : ChaconOdometer) :
    chaconTowerSystem.act (Multiplicative.ofAdd 1) (x, false) =
      if x ∈ chaconSpacer then (x, true) else (x + 1, false) := by
  classical
  change ((twoLevelTowerEquiv chaconOdometerStep chaconSpacer chaconSpacer_measurable).toEquiv ^
    (1 : ℤ)) (x, false) = _
  rw [zpow_one]
  change towerNext chaconOdometerStep chaconSpacer (x, false) = _
  simp [towerNext, towerTop, towerBottom, chaconOdometerStep]

/-- The step from an occupied upper level returns to the base at the odometer successor. -/
theorem chaconTower_top_step (x : ChaconOdometer) (hx : x ∈ chaconSpacer) :
    chaconTowerSystem.act (Multiplicative.ofAdd 1) (x, true) = (x + 1, false) := by
  change ((twoLevelTowerEquiv chaconOdometerStep chaconSpacer chaconSpacer_measurable).toEquiv ^
    (1 : ℤ)) (x, true) = _
  rw [zpow_one]
  change towerNext chaconOdometerStep chaconSpacer (x, true) = _
  simp [towerNext, towerBottom, chaconOdometerStep, hx]

end Mixing
