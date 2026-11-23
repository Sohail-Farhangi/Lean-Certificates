/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesPowersWap
public import JdLG.PaperExamplesIntegerWapMean
public import JdLG.ReversibleTopology
public import JdLG.WeaklyAlmostPeriodic

/-!
# The absolute-mean criterion for the WAP translation space

For integer translations, point evaluations separate the WAP vectors.
The invariant mean of the absolute function equals the Haar mean of the
absolute coefficient at zero on the compact group ideal.
-/

@[expose] public section

namespace JdLG.PaperExamplesPowers

open MeasureTheory
open scoped ENNReal

local notation "Times" => Multiplicative ℤ
local notation "T" => weakOperatorClosure wapTranslation

instance : CompactSpace T := isCompact_iff_compactSpace.1 wapTranslation_admissible.1

instance : Nonempty T := ⟨closureInclusion wapTranslation 1⟩

noncomputable instance : MeasurableSpace T := borel T

instance : BorelSpace T := ⟨rfl⟩

/-- Point evaluation on the WAP space of bounded integer functions. -/
noncomputable def wapEvaluation (t : ℤ) : StrongDual ℂ IntegerWap :=
  (lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) ∞ t).comp IntegerWap.subtypeL

@[simp] theorem wapEvaluation_apply (t : ℤ) (x : IntegerWap) : wapEvaluation t x = x.val t :=
  rfl

section Discrete

/-- The absolute value of a complex WAP function is a real WAP test. -/
noncomputable def wapAbsolute (x : IntegerWap) :
    weaklyAlmostPeriodicSubmodule (S := Times) :=
  wapPullback (closureInclusion wapTranslation) continuous_of_discreteTopology
    ⟨fun a ↦ ‖wapEvaluation 0 (closureAction wapTranslation a x)‖,
      (continuous_closureAction_coefficient wapTranslation x (wapEvaluation 0)).norm⟩

@[simp] theorem wapAbsolute_apply (x : IntegerWap) (a : Times) :
    (wapAbsolute x).val a = ‖x.val a.toAdd‖ := by
  change ‖x.val (a.toAdd + 0)‖ = ‖x.val a.toAdd‖
  rw [add_zero]

/-- The integer group admits a positive normalized bi-invariant mean on its
real WAP space. -/
theorem integer_wapBiInvariantMean_exists : Nonempty (WapBiInvariantMean (S := Times)) := by
  let : DiscreteMeasurableSpace Times := ⟨fun A ↦ (isOpen_discrete A).measurableSet⟩
  obtain ⟨m⟩ := integer_leftInvariantSetMean_exists
  exact ⟨m.toWapBiInvariantMean⟩

set_option maxHeartbeats 1500000 in
-- The Haar comparison elaborates the WAP pullback through the compact operator closure.
/-- The almost weakly stable part of the integer WAP translation space is
exactly the set of functions whose absolute value has mean zero. -/
theorem wapTranslation_aws_iff_absolute_mean_zero (m : WapBiInvariantMean (S := Times))
    (x : IntegerWap) :
    IsAlmostWeaklyStable (closureAction wapTranslation) x ↔
      m.functional (wapAbsolute x) = 0 := by
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible wapTranslation_admissible
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let π := closureAction wapTranslation
  let i : K.carrier →ₙ* T := ⟨Subtype.val, fun _ _ ↦ rfl⟩
  let M := m.toContinuousMean (closureInclusion wapTranslation) continuous_of_discreteTopology
    (denseRange_closureInclusion wapTranslation)
  let F := compactRealFunction (fun a ↦ ‖wapEvaluation 0 (π a x)‖)
    (continuous_closureAction_coefficient wapTranslation x (wapEvaluation 0)).norm
  have habsorb (s : T) : ∃ g : K.carrier, i g = i 1 * s :=
    ⟨⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩, rfl⟩
  have hmean : m.functional (wapAbsolute x) =
      ∫ g : K.carrier, ‖wapEvaluation 0 (π (i g) x)‖ ∂normalizedHaar K.carrier :=
    M.apply_eq_groupIdealHaar i continuous_subtype_val Subtype.val_injective habsorb F
  constructor
  · intro hx
    have hp := (K.stable_iff_projection_eq_zero π x).1 hx
    have hz (g : K.carrier) : π (i g) x = 0 := by
      calc
        π (i g) x = π (i g * K.identity) x := congrArg (fun a ↦ π a x) (K.mul_identity g.2).symm
        _ = π (i g) (π K.identity x) := by rw [map_mul]; rfl
        _ = 0 := by rw [show π K.identity x = 0 from hp, map_zero]
    calc
      m.functional (wapAbsolute x) = _ := hmean
      _ = 0 := by simp only [hz, map_zero, norm_zero, integral_zero]
  · intro h
    have h' : (∫ g : K.carrier, ‖wapEvaluation 0 (π (i g) x)‖
        ∂normalizedHaar K.carrier) = 0 := hmean.symm.trans h
    have hc : Continuous (fun g : K.carrier ↦ ‖wapEvaluation 0 (π (i g) x)‖) :=
      (continuous_closureAction_coefficient wapTranslation x (wapEvaluation 0)).norm.comp
        continuous_subtype_val
    have ha := (integral_eq_zero_iff_of_nonneg (fun _ ↦ norm_nonneg _)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 h'
    have hz := (hc.ae_eq_iff_eq (normalizedHaar K.carrier) continuous_zero).1 ha
    apply (K.stable_iff_projection_eq_zero π x).2
    apply Subtype.ext
    apply lp.ext
    funext t
    let s : Times := Multiplicative.ofAdd t
    let g : K.carrier := ⟨closureInclusion wapTranslation s * K.identity,
      K.mul_mem_left (closureInclusion wapTranslation s) K.identity_mem⟩
    have hcoeff := norm_eq_zero.1 (congrFun hz g)
    have heq : π (i g) x = wapTranslation s (π K.identity x) := by
      change π (closureInclusion wapTranslation s * K.identity) x = _
      rw [map_mul]
      rfl
    rw [heq] at hcoeff
    change (π K.identity x).val (t + 0) = 0 at hcoeff
    rw [add_zero] at hcoeff
    exact hcoeff

end Discrete

end JdLG.PaperExamplesPowers
