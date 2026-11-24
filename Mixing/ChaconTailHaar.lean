/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconTowerClock
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Haar disintegration by any finite prefix of the ternary odometer -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped Classical ENNReal Topology

namespace Mixing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Prepend the residue `r` to the odometer tail at scale `3^n`. -/
noncomputable def chaconScaleBranch (n r : ℕ) (x : ChaconOdometer) : ChaconOdometer :=
  (3 : ChaconOdometer)^n*x+r

theorem measurable_chaconScaleBranch (n r : ℕ) : Measurable (chaconScaleBranch n r) := by
  unfold chaconScaleBranch
  fun_prop

theorem exists_chaconScaleBranch (n : ℕ) (a : ChaconOdometer) :
    ∃ (r : ZMod (3^n)) (x : ChaconOdometer), chaconScaleBranch n r.val x = a := by
  let z := PadicInt.toZModPow (p := 3) n a
  have h : PadicInt.toZModPow (p := 3) n (a - (z.val : ChaconOdometer)) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, Nat.cast_ofNat] at h
  obtain ⟨x, hx⟩ := h
  exact ⟨z, x, eq_sub_iff_add_eq.mp hx.symm⟩

private theorem map_chaconScaleBranch_translate (n r s : ℕ) (x : ChaconOdometer) :
    ((chaconOdometerMeasure.map (chaconScaleBranch n r)).map
      (fun y ↦ chaconScaleBranch n s x + y)) =
        chaconOdometerMeasure.map (chaconScaleBranch n (r+s)) := by
  have hmeas : Measurable (fun y ↦ chaconScaleBranch n s x + y) := measurable_const.add measurable_id
  rw [Measure.map_map hmeas (measurable_chaconScaleBranch n r)]
  have hx := chaconOdometer_translate_preserving x
  nth_rw 2 [← hx.map_eq]
  rw [Measure.map_map (measurable_chaconScaleBranch n _) hx.measurable]
  congr 1
  funext y
  simp only [Function.comp_apply, chaconScaleBranch, Nat.cast_add]
  ring

private theorem map_chaconScaleBranch_mod (n r : ℕ) :
    chaconOdometerMeasure.map (chaconScaleBranch n r) =
      chaconOdometerMeasure.map (chaconScaleBranch n (r % 3^n)) := by
  have hx := chaconOdometer_translate_preserving ((r/3^n : ℕ) : ChaconOdometer)
  nth_rw 2 [← hx.map_eq]
  rw [Measure.map_map (measurable_chaconScaleBranch n _) hx.measurable]
  congr 1
  funext y
  have hr : (r : ChaconOdometer) =
      3^n * ((r/3^n : ℕ) : ChaconOdometer) + ((r%3^n : ℕ) : ChaconOdometer) := by
    exact_mod_cast (Nat.div_add_mod r (3^n)).symm
  simp only [Function.comp_apply, chaconScaleBranch]
  rw [hr]
  ring

/-- The residue prefix is uniform and independent of its Haar-distributed tail. -/
theorem chaconOdometerMeasure_scaleBranch_decomposition (n : ℕ) :
    chaconOdometerMeasure = ((↑(3^n : ℕ) : ℝ≥0∞)⁻¹) •
      ∑ r : ZMod (3^n), chaconOdometerMeasure.map (chaconScaleBranch n r.val) := by
  let D r := chaconOdometerMeasure.map (chaconScaleBranch n r)
  let ν : Measure ChaconOdometer := ((↑(3^n : ℕ) : ℝ≥0∞)⁻¹) • ∑ r : ZMod (3^n), D r.val
  change _ = ν
  have hu (r : ℕ) : D r univ = 1 := by
    simp [D, Measure.map_apply (measurable_chaconScaleBranch n r) MeasurableSet.univ]
  have hν : IsProbabilityMeasure ν := by
    constructor
    rw [show ν univ = ((↑(3^n : ℕ) : ℝ≥0∞)⁻¹) * (∑ r : ZMod (3^n), D r.val) univ by rfl]
    simp only [sum_apply, hu, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by positivity) (by simp)
  have hInv : IsAddLeftInvariant ν := by
    constructor
    intro a
    obtain ⟨s, x, rfl⟩ := exists_chaconScaleBranch n a
    let t (y : ChaconOdometer) := chaconScaleBranch n s.val x + y
    have hmeas : Measurable t := measurable_const.add measurable_id
    have hmaps (r : ℕ) : (D r).map t = D (r+s.val) :=
      map_chaconScaleBranch_translate n r s.val x
    have hmod (r : ℕ) : D r = D (r % 3^n) := map_chaconScaleBranch_mod n r
    have hs : (∑ r : ZMod (3^n), D r.val).map t = ∑ r : ZMod (3^n), (D r.val).map t := by
      ext A hA
      simp only [Measure.map_apply hmeas hA, sum_apply]
    change ν.map t = ν
    unfold ν
    rw [Measure.map_smul ((↑(3^n : ℕ) : ℝ≥0∞)⁻¹) hmeas.aemeasurable, hs]
    congr 1
    calc
      ∑ r : ZMod (3^n), (D r.val).map t = ∑ r : ZMod (3^n), D ((r+s).val) := by
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [hmaps, ZMod.val_add]
        exact hmod _
      _ = ∑ r : ZMod (3^n), D r.val := Equiv.sum_comp (Equiv.addRight s) (fun r ↦ D r.val)
  let : IsAddHaarMeasure ν := isAddHaarMeasure_of_isCompact_nonempty_interior ν univ
    isCompact_univ (by simp) (by simp) (by simp)
  exact isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

private theorem continuous_chaconScaleBranch (n r : ℕ) : Continuous (chaconScaleBranch n r) := by
  unfold chaconScaleBranch
  fun_prop

private theorem injective_chaconScaleBranch (n r : ℕ) :
    Function.Injective (chaconScaleBranch n r) := by
  intro x y h
  have he := add_right_cancel (show 3^n*x+(r : ChaconOdometer) = 3^n*y+r from h)
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num)) he

/-- The residue of an assembled odometer point is its prefixed digit block. -/
theorem chaconScaleBranch_residue (n : ℕ) (r : ZMod (3^n)) (x : ChaconOdometer) :
    PadicInt.toZModPow (p := 3) n (chaconScaleBranch n r.val x) = r := by
  have h₃ : PadicInt.toZModPow (p := 3) n ((3 : ChaconOdometer)^n) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, Nat.cast_ofNat]
  simp only [chaconScaleBranch, map_add, map_mul, map_natCast, h₃, zero_mul, zero_add,
    ZMod.natCast_zmod_val]

/-- Discard the `n` least significant ternary digits. -/
noncomputable def chaconTail (n : ℕ) (x : ChaconOdometer) : ChaconOdometer :=
  Classical.choose (Classical.choose_spec (exists_chaconScaleBranch n x))

/-- Reassemble a point from its discarded prefix and remaining tail. -/
theorem chaconScaleBranch_tail (n : ℕ) (x : ChaconOdometer) :
    chaconScaleBranch n (PadicInt.toZModPow (p := 3) n x).val (chaconTail n x) = x := by
  let r := Classical.choose (exists_chaconScaleBranch n x)
  have he : chaconScaleBranch n r.val (chaconTail n x) = x :=
    Classical.choose_spec (Classical.choose_spec (exists_chaconScaleBranch n x))
  have hr := chaconScaleBranch_residue n r (chaconTail n x)
  rw [he] at hr
  rwa [hr]

theorem chaconTail_scaleBranch (n : ℕ) (r : ZMod (3^n)) (x : ChaconOdometer) :
    chaconTail n (chaconScaleBranch n r.val x) = x := by
  apply injective_chaconScaleBranch n r.val
  have h := chaconScaleBranch_tail n (chaconScaleBranch n r.val x)
  rwa [chaconScaleBranch_residue] at h

theorem measurable_chaconTail (n : ℕ) : Measurable (chaconTail n) := by
  intro A hA
  have he : chaconTail n ⁻¹' A = ⋃ r : ZMod (3^n), chaconScaleBranch n r.val '' A := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_image]
    constructor
    · exact fun hx ↦ ⟨PadicInt.toZModPow (p := 3) n x, chaconTail n x, hx,
        chaconScaleBranch_tail n x⟩
    · rintro ⟨r, y, hy, rfl⟩
      rwa [chaconTail_scaleBranch]
  rw [he]
  exact MeasurableSet.iUnion fun r ↦ ((continuous_chaconScaleBranch n r.val).isClosedEmbedding
    (injective_chaconScaleBranch n r.val)).measurableEmbedding.measurableSet_image' hA

/-- Integration conditional on the first `n` digits. -/
theorem integral_chaconScaleBranch_decomposition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (n : ℕ) {f : ChaconOdometer → E}
    (hf : Integrable f chaconOdometerMeasure) :
    (∫ x, f x ∂chaconOdometerMeasure) = ((↑(3^n : ℕ) : ℝ)⁻¹) •
      ∑ r : ZMod (3^n), ∫ x, f (chaconScaleBranch n r.val x) ∂chaconOdometerMeasure := by
  let D (r : ZMod (3^n)) := chaconOdometerMeasure.map (chaconScaleBranch n r.val)
  have hμ : chaconOdometerMeasure = ((↑(3^n : ℕ) : ℝ≥0∞)⁻¹) • ∑ r, D r :=
    chaconOdometerMeasure_scaleBranch_decomposition n
  have hnn : ((↑(3^n : ℕ) : ℝ≥0∞)⁻¹) ≠ 0 := by simp
  have hfin : Integrable f (∑ r, D r) := by
    rwa [hμ, integrable_smul_measure hnn (ENNReal.inv_ne_top.mpr (by positivity))] at hf
  have hparts (r : ZMod (3^n)) : Integrable f (D r) := by
    refine hfin.mono_measure (Measure.le_iff.mpr fun A _ ↦ ?_)
    rw [sum_apply]
    exact Finset.single_le_sum (f := fun j ↦ D j A) (fun _ _ ↦ zero_le) (Finset.mem_univ r)
  conv_lhs => rw [hμ]
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    integral_finsetSum_measure (fun r _ ↦ hparts r)]
  congr 1
  exact Finset.sum_congr rfl fun r _ ↦ integral_map
    (measurable_chaconScaleBranch n r.val).aemeasurable (hparts r).aestronglyMeasurable

/-- The finite prefix, regarded as an ordinary natural number in the odometer. -/
noncomputable def chaconPrefix (n : ℕ) (x : ChaconOdometer) : ChaconOdometer :=
  ((PadicInt.toZModPow (p := 3) n x).val : ChaconOdometer)

theorem measurable_chaconPrefix (n : ℕ) : Measurable (chaconPrefix n) := by
  intro A _
  have he : chaconPrefix n ⁻¹' A =
      ⋃ r : {r : ZMod (3^n) // (r.val : ChaconOdometer) ∈ A},
        Set.range (chaconScaleBranch n r.val.val) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_range]
    constructor
    · exact fun hx ↦ ⟨⟨PadicInt.toZModPow (p := 3) n x, hx⟩, chaconTail n x,
        chaconScaleBranch_tail n x⟩
    · rintro ⟨r, y, rfl⟩
      simpa only [chaconPrefix, chaconScaleBranch_residue] using r.property
  rw [he]
  exact MeasurableSet.iUnion fun r ↦
    (isCompact_range (continuous_chaconScaleBranch n r.val.val)).isClosed.measurableSet

theorem dist_chaconPrefix_le (n : ℕ) (x : ChaconOdometer) :
    dist x (chaconPrefix n x) ≤ ((3 : ℝ)⁻¹)^n := by
  have h : x = (3 : ChaconOdometer)^n*chaconTail n x + chaconPrefix n x :=
    (chaconScaleBranch_tail n x).symm
  rw [dist_eq_norm, show x - chaconPrefix n x = (3 : ChaconOdometer)^n*chaconTail n x by
    exact (sub_eq_iff_eq_add).2 h]
  calc
    ‖(3 : ChaconOdometer)^n*chaconTail n x‖ ≤ ‖(3 : ChaconOdometer)^n‖ * ‖chaconTail n x‖ :=
      norm_mul_le _ _
    _ ≤ ‖(3 : ChaconOdometer)^n‖ * 1 :=
      mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ((3 : ℝ)⁻¹)^n := by
      rw [mul_one, norm_pow, show ‖(3 : ChaconOdometer)‖ = (3 : ℝ)⁻¹ by
        simpa only [Nat.cast_ofNat] using (PadicInt.norm_p (p := 3))]

/-- Every integrable function of the prefix is exactly independent of the remaining tail. -/
theorem integral_chaconPrefix_tail_preimage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (n : ℕ) (A : Set ChaconOdometer)
    (hA : MeasurableSet A) (f : ChaconOdometer → E)
    (hf : Integrable (f ∘ chaconPrefix n) chaconOdometerMeasure) :
    (∫ x in chaconTail n ⁻¹' A, f (chaconPrefix n x) ∂chaconOdometerMeasure) =
      chaconOdometerMeasure.real A •
        ∫ x, f (chaconPrefix n x) ∂chaconOdometerMeasure := by
  let S := chaconTail n ⁻¹' A
  have hS : MeasurableSet S := measurable_chaconTail n hA
  change (∫ x in S, (f ∘ chaconPrefix n) x ∂chaconOdometerMeasure) =
    chaconOdometerMeasure.real A • ∫ x, (f ∘ chaconPrefix n) x ∂chaconOdometerMeasure
  rw [← integral_indicator hS, integral_chaconScaleBranch_decomposition n (hf.indicator hS),
    integral_chaconScaleBranch_decomposition n hf]
  have he (r : ZMod (3^n)) (x : ChaconOdometer) :
      S.indicator (f ∘ chaconPrefix n) (chaconScaleBranch n r.val x) =
      A.indicator (fun _ ↦ f (r.val : ChaconOdometer)) x := by
    simp only [Set.indicator, S, mem_preimage, chaconTail_scaleBranch, Function.comp_apply,
      chaconPrefix, chaconScaleBranch_residue]
  simp only [he, integral_indicator_const _ hA, Function.comp_apply, chaconPrefix,
    chaconScaleBranch_residue, integral_const, probReal_univ, one_smul, ← Finset.smul_sum,
    smul_comm ((↑(3^n : ℕ) : ℝ)⁻¹) (chaconOdometerMeasure.real A)]

/-- A fixed measurable event of the distant tail becomes independent of every
integrable test on the odometer. -/
theorem tendsto_integral_chaconTail_preimage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (A : Set ChaconOdometer)
    (hA : MeasurableSet A) {f : ChaconOdometer → E}
    (hf : Integrable f chaconOdometerMeasure) :
    Tendsto (fun n : ℕ ↦ ∫ x in chaconTail n ⁻¹' A, f x ∂chaconOdometerMeasure) atTop
      (𝓝 (chaconOdometerMeasure.real A • ∫ x, f x ∂chaconOdometerMeasure)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hfg, hg⟩ := hf.exists_boundedContinuous_integral_sub_le (by linarith : 0 < ε/8)
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε/8) (by linarith)
  have hp : Tendsto (fun n : ℕ ↦ ((3 : ℝ)⁻¹)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [(tendsto_order.mp hp).2 δ hδ] with n hn
  let G := g ∘ chaconPrefix n
  have hG : Integrable G chaconOdometerMeasure :=
    Integrable.of_bound (g.continuous.measurable.comp (measurable_chaconPrefix n)).aestronglyMeasurable
      ‖g‖ (ae_of_all _ fun x ↦ g.norm_coe_le_norm (chaconPrefix n x))
  have hd (x : ChaconOdometer) : ‖g x - G x‖ ≤ ε/8 := by
    have hd' := hU (dist_chaconPrefix_le n x |>.trans_lt hn)
    simpa only [dist_eq_norm, G, Function.comp_apply] using hd'.le
  have hcost : (∫ x, ‖f x - G x‖ ∂chaconOdometerMeasure) ≤ ε/4 := by
    calc
      (∫ x, ‖f x - G x‖ ∂chaconOdometerMeasure) ≤
          ∫ x, ‖f x - g x‖ + ε/8 ∂chaconOdometerMeasure := by
        apply integral_mono (hf.sub hG).norm ((hf.sub hg).norm.add (integrable_const _))
        intro x
        have ht := dist_triangle (f x) (g x) (G x)
        simp only [dist_eq_norm] at ht
        exact ht.trans (add_le_add_right (hd x) _)
      _ ≤ ε/4 := by
        change (∫ x, ‖(f - ⇑g) x‖ + ε/8 ∂chaconOdometerMeasure) ≤ ε/4
        rw [integral_add (hf.sub hg).norm (integrable_const _), integral_const,
          probReal_univ, one_smul]
        have hfg' : (∫ x, ‖(f - ⇑g) x‖ ∂chaconOdometerMeasure) ≤ ε/8 := hfg
        linarith only [hfg']
  let S := chaconTail n ⁻¹' A
  have hind : (∫ x in S, G x ∂chaconOdometerMeasure) =
      chaconOdometerMeasure.real A • ∫ x, G x ∂chaconOdometerMeasure :=
    integral_chaconPrefix_tail_preimage n A hA _ hG
  have hsave : ‖∫ x in S, (f-G) x ∂chaconOdometerMeasure‖ ≤ ε/4 :=
    (norm_integral_le_integral_norm _).trans
      ((integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun _ ↦ norm_nonneg _)
        (hf.sub hG).norm).trans hcost)
  have hbase : ‖∫ x, (f-G) x ∂chaconOdometerMeasure‖ ≤ ε/4 :=
    (norm_integral_le_integral_norm _).trans hcost
  have hc0 : 0 ≤ chaconOdometerMeasure.real A := ENNReal.toReal_nonneg
  have hc1 : chaconOdometerMeasure.real A ≤ 1 := measureReal_le_one
  have hcostBase : ‖chaconOdometerMeasure.real A • ∫ x, (f-G) x ∂chaconOdometerMeasure‖ ≤ ε/4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans hbase
  rw [dist_eq_norm]
  change ‖(∫ x in S, f x ∂chaconOdometerMeasure) -
    chaconOdometerMeasure.real A • (∫ x, f x ∂chaconOdometerMeasure)‖ < ε
  have he : (∫ x in S, f x ∂chaconOdometerMeasure) -
      chaconOdometerMeasure.real A • (∫ x, f x ∂chaconOdometerMeasure) =
      (∫ x in S, (f-G) x ∂chaconOdometerMeasure) -
        chaconOdometerMeasure.real A • (∫ x, (f-G) x ∂chaconOdometerMeasure) := by
    change _ = (∫ x in S, f x - G x ∂chaconOdometerMeasure) -
      chaconOdometerMeasure.real A • (∫ x, f x - G x ∂chaconOdometerMeasure)
    rw [integral_sub hf hG, integral_sub hf.integrableOn hG.integrableOn, smul_sub, ← hind]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans_lt (by linarith)

end Mixing
