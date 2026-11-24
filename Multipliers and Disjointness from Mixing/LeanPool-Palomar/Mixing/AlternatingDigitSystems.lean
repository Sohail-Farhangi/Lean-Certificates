/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.BinaryDigitSpectra
public import Mixing.ProductMixingComplement
public import Mixing.WeakMixingBridge

/-! # A direct realization of the systems in Example 4 -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace Mixing.BinaryDigitSpectra

/-- Alternate binary digit blocks whose endpoints are consecutive squares. -/
def evenMask : Set ℕ := {k | ∃ i : ℕ, (2*i)^2 ≤ k ∧ k < (2*i + 1)^2}

private theorem notMem_evenMask_of_oddBlock {i k : ℕ}
    (hk : (2*i+1)^2 ≤ k) (hk' : k < (2*i+2)^2) : k ∉ evenMask := by
  rintro ⟨j, hJ, hJ'⟩
  by_cases hij : j ≤ i
  · have h : (2*j+1)^2 ≤ (2*i+1)^2 := by gcongr
    exact hJ'.not_ge (h.trans hk)
  · have h : (2*i+2)^2 ≤ (2*j)^2 := by gcongr; omega
    exact hk'.not_ge (h.trans hJ)

private theorem shifted_covariance_rigidity (A : Set ℕ) (s : ℕ → ℕ)
    (hGap : ∀ n, ∀ k ∈ A, k < s n + n → k + 2 ≤ s n) (j : ℤ) :
    Tendsto (fun n => StationaryGaussian.covariance (maskMeasure A) ((2 : ℤ)^s n + j))
      atTop (𝓝 (StationaryGaussian.covariance (maskMeasure A) j)) := by
  have hLim : Tendsto (fun n => transform A ((j : ℝ) + (2 : ℝ)^s n))
      atTop (𝓝 (transform A j)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hDecay : Tendsto (fun n : ℕ => Real.pi * (1 / 2 : ℝ)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).const_mul Real.pi
    filter_upwards [hDecay.eventually_lt_const hε] with n hn
    rw [dist_eq_norm]
    have h := norm_transform_shift_dyadic_sub_le A j (s n) (s n + n) (hGap n)
    refine h.trans_lt ?_
    have he : (2 : ℝ)^s n * (1 / 2 : ℝ)^s n = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      _ = Real.pi * ((2 : ℝ)^s n * (1 / 2 : ℝ)^s n) * (1 / 2 : ℝ)^n := by rw [pow_add]; ring
      _ < _ := by rwa [he, mul_one]
  have hr := (Complex.continuous_re.tendsto _).comp hLim
  change Tendsto (fun n => (transform A ((j : ℝ) + (2 : ℝ)^s n)).re)
    atTop (𝓝 (transform A j).re) at hr
  simpa only [covariance_maskMeasure, Int.cast_add, Int.cast_pow,
    Int.cast_ofNat, add_comm ((2 : ℝ)^_) (j : ℝ)] using hr

private theorem gaussian_rigid_of_long_gaps (A : Set ℕ) (s : ℕ → ℕ)
    (hs : StrictMono s) (hGap : ∀ n, ∀ k ∈ A, k < s n + n → k + 2 ≤ s n) :
    IsRigidRepresentation (StationaryGaussian.system (maskMeasure A)).koopmanRep := by
  let g (n : ℕ) := Multiplicative.ofAdd ((2 : ℤ)^s n)
  have hg : Function.Injective g := by
    have hg₀ : StrictMono (fun n : ℕ => (2 : ℤ)^n) := pow_right_strictMono₀ (by norm_num)
    exact (hg₀.comp hs).injective
  have ht : Tendsto g atTop cofinite := by
    simpa only [Nat.cofinite_eq_atTop] using hg.tendsto_cofinite
  exact StationaryGaussian.isRigidRepresentation_of_covariance_tendsto (maskMeasure A) g ht
    (shifted_covariance_rigidity A s hGap)

theorem gaussian_evenMask_rigid :
    IsRigidRepresentation (StationaryGaussian.system (maskMeasure evenMask)).koopmanRep := by
  let s (n : ℕ) := (2*n+1)^2+1
  apply gaussian_rigid_of_long_gaps evenMask s
  · intro m n hmn
    dsimp only [s]
    gcongr
  · intro n k hk hkn
    apply Nat.succ_le_of_lt
    dsimp only [s] at *
    have h : k < (2*n+1)^2 := by
      by_contra! h
      apply notMem_evenMask_of_oddBlock h _ hk
      have he : (2*n+2)^2 = (2*n+1)^2 + (4*n+3) := by ring
      omega
    omega

theorem gaussian_compl_evenMask_rigid :
    IsRigidRepresentation (StationaryGaussian.system (maskMeasure evenMaskᶜ)).koopmanRep := by
  let s (n : ℕ) := (2*n)^2+1
  apply gaussian_rigid_of_long_gaps evenMaskᶜ s
  · intro m n hmn
    dsimp only [s]
    gcongr
  · intro n k hk hkn
    apply Nat.succ_le_of_lt
    dsimp only [s] at *
    have h : k < (2*n)^2 := by
      by_contra! h
      apply hk
      refine ⟨n, h, ?_⟩
      have he : (2*n+1)^2 = (2*n)^2 + (4*n+1) := by ring
      omega
    omega

private theorem shifted_covariance_product_tendsto_zero (A : Set ℕ) (j k : ℤ) :
    Tendsto (fun g : Multiplicative ℤ => StationaryGaussian.covariance (maskMeasure A) (g.toAdd+j) *
      StationaryGaussian.covariance (maskMeasure Aᶜ) (g.toAdd+k)) cofinite (𝓝 0) := by
  have hz : Function.Injective (Multiplicative.toAdd : Multiplicative ℤ → ℤ) := fun _ _ h => h
  have hZ : Tendsto (Multiplicative.toAdd : Multiplicative ℤ → ℤ) cofinite cofinite := hz.tendsto_cofinite
  have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp
    ((transform_shifted_mul_compl_tendsto_zero A j k).comp hZ)
  rw [Complex.zero_re] at h
  apply h.congr
  intro g
  change (transform A ((g.toAdd : ℝ) + j) * transform Aᶜ ((g.toAdd : ℝ) + k)).re = _
  rw [transform_eq_ofReal_re A, transform_eq_ofReal_re Aᶜ, ← Complex.ofReal_mul, Complex.ofReal_re,
    covariance_maskMeasure, covariance_maskMeasure, Int.cast_add, Int.cast_add]

private theorem exists_covariance_limit (A : Set ℕ) (p : Ultrafilter (Multiplicative ℤ)) (j : ℤ) :
    ∃ l : ℝ, Tendsto (fun g : Multiplicative ℤ =>
      StationaryGaussian.covariance (maskMeasure A) (g.toAdd + j))
      (p : Filter (Multiplicative ℤ)) (𝓝 l) := by
  let f (g : Multiplicative ℤ) := StationaryGaussian.covariance (maskMeasure A) (g.toAdd + j)
  have h : Icc (-1 : ℝ) 1 ∈ p.map f := by
    change f ⁻¹' Icc (-1 : ℝ) 1 ∈ (p : Filter (Multiplicative ℤ))
    apply Filter.Eventually.of_forall
    intro g
    rw [Set.mem_Icc, ← abs_le]
    dsimp only [f]
    rw [covariance_maskMeasure]
    exact (Complex.abs_re_le_norm _).trans (norm_transform_le_one _ _)
  obtain ⟨l, _, hl⟩ := isCompact_Icc.ultrafilter_le_nhds' (p.map f) h
  exact ⟨l, hl⟩

/-- Every free ultrafilter mixes at least one of the two Gaussian
systems constructed from complementary binary digit masks. -/
theorem gaussian_complementary_mixing_masks (A : Set ℕ) :
    ∀ p ∈ freeUltrafilters (Multiplicative ℤ),
      (StationaryGaussian.system (maskMeasure A)).IsUMixing {p} ∨
      (StationaryGaussian.system (maskMeasure Aᶜ)).IsUMixing {p} := by
  classical
  intro p hp
  by_cases h : ∀ j : ℤ, Tendsto (fun g : Multiplicative ℤ =>
      StationaryGaussian.covariance (maskMeasure A) (g.toAdd + j))
      (p : Filter (Multiplicative ℤ)) (𝓝 0)
  · exact Or.inl (StationaryGaussian.isUMixing_singleton_of_covariance_tendsto _ p h)
  · push Not at h
    obtain ⟨j, hj⟩ := h
    obtain ⟨a, ha⟩ := exists_covariance_limit A p j
    have ha₀ : a ≠ 0 := by intro h0; subst a; exact hj ha
    right
    apply StationaryGaussian.isUMixing_singleton_of_covariance_tendsto
    intro k
    obtain ⟨b, hb⟩ := exists_covariance_limit Aᶜ p k
    have hprod : a * b = 0 := tendsto_nhds_unique (ha.mul hb)
      ((shifted_covariance_product_tendsto_zero A j k).mono_left hp)
    simpa only [(mul_eq_zero.mp hprod).resolve_left ha₀] using hb

private theorem gaussian_not_mixing_of_own_rigidity_ultrafilter (A : Set ℕ)
    (p : Ultrafilter (Multiplicative ℤ))
    (hId : ultrafilterOperator (StationaryGaussian.system (maskMeasure A)).koopmanRep p = 1) :
    ¬ (StationaryGaussian.system (maskMeasure A)).IsUMixing {p} := by
  intro hMix
  let S := StationaryGaussian.system (maskMeasure A)
  obtain ⟨B, hB, hB₀, hB₁⟩ := StationaryGaussian.exists_event_intermediate_probability (maskMeasure A)
  obtain ⟨a, ha, ha₀⟩ := exists_nonzero_centered_observable S.measure B hB hB₀ hB₁
  have h0 : (∫ x, a.l2 S.measure x ∂S.measure) = 0 := by
    exact (integral_congr_ae (a.coe_l2 S.measure)).trans ha
  let v : meanZero S.measure := ⟨a.l2 S.measure, (mem_meanZero_iff_integral _ _).mpr h0⟩
  have hSub : Intertwines S.koopmanZeroRep S.koopmanRep (meanZero S.measure).subtypeL := fun _ _ => rfl
  have he := hSub.ultrafilter p v
  have hMix₀ := hMix p (Set.mem_singleton p)
  change (↑(ultrafilterOperator S.koopmanZeroRep p v) : Lp ℂ 2 S.measure) =
    ultrafilterOperator S.koopmanRep p (v : Lp ℂ 2 S.measure) at he
  change ultrafilterOperator S.koopmanZeroRep p = 0 at hMix₀
  change ultrafilterOperator S.koopmanRep p = 1 at hId
  rw [hMix₀, hId, zero_apply, one_apply_eq_self] at he
  exact ha₀ he.symm

/-- The two rigid Gaussian systems used here are both weakly mixing. -/
theorem gaussian_alternating_weaklyMixing :
    IsWeaklyMixing (StationaryGaussian.system (maskMeasure evenMask)).koopmanZeroRep ∧
      IsWeaklyMixing (StationaryGaussian.system (maskMeasure evenMaskᶜ)).koopmanZeroRep := by
  obtain ⟨p, hp, hpId⟩ := exists_freeIdempotent_operator_eq_one_of_rigid _ gaussian_evenMask_rigid
  obtain ⟨q, hq, hqId⟩ := exists_freeIdempotent_operator_eq_one_of_rigid _ gaussian_compl_evenMask_rigid
  have hS := (gaussian_complementary_mixing_masks evenMask q hq.1).resolve_right
    (gaussian_not_mixing_of_own_rigidity_ultrafilter evenMaskᶜ q hqId)
  have hT := (gaussian_complementary_mixing_masks evenMask p hp.1).resolve_left
    (gaussian_not_mixing_of_own_rigidity_ultrafilter evenMask p hpId)
  exact ⟨isWeaklyMixing_of_isUMixing _ (Set.singleton_nonempty _) hS,
    isWeaklyMixing_of_isUMixing _ (Set.singleton_nonempty _) hT⟩

end Mixing.BinaryDigitSpectra

namespace Mixing

open BinaryDigitSpectra

/-- Example 4 realized by a pair of rigid Gaussian systems. Their product
is generated by two free idempotents, has a nonzero strongly mixing
component and is not generated by any singleton free ultrafilter. -/
theorem example4_alternating_binary_gaussian :
    let S := StationaryGaussian.system (maskMeasure evenMask)
    let T := StationaryGaussian.system (maskMeasure evenMaskᶜ)
    (∃ p ∈ freeIdempotentUltrafilters (Multiplicative ℤ),
      ∃ q ∈ freeIdempotentUltrafilters (Multiplicative ℤ),
        p ≠ q ∧ (S.prod T).IsUGenerated ({p} ∪ {q})) ∧
    (∀ r ∈ freeUltrafilters (Multiplicative ℤ), ¬ (S.prod T).IsUGenerated {r}) ∧
    ¬ IsRigidRepresentation (S.prod T).koopmanRep ∧
    (∃ w ∈ (S.productCoordinateSubmodule T).orthogonal, w ≠ 0) ∧
    IsStronglyMixing (unitarySubmoduleAction (S.prod T).koopmanRep
      (S.productCoordinateSubmodule T).orthogonal.toSubmodule
      (S.productCoordinateSubmodule_invariant T).orthogonal) := by
  let _ : Countable (Multiplicative ℤ) := by
    change Countable ℤ
    infer_instance
  let S := StationaryGaussian.system (maskMeasure evenMask)
  let T := StationaryGaussian.system (maskMeasure evenMaskᶜ)
  obtain ⟨A, hA, hA₀, hA₁⟩ := StationaryGaussian.exists_event_intermediate_probability (maskMeasure evenMask)
  obtain ⟨B, hB, hB₀, hB₁⟩ := StationaryGaussian.exists_event_intermediate_probability (maskMeasure evenMaskᶜ)
  have hCover := gaussian_complementary_mixing_masks evenMask
  obtain ⟨hGen, hNot, hRigid⟩ := example4_product_of_complementary_mixing S T
    gaussian_evenMask_rigid gaussian_compl_evenMask_rigid hCover hA hA₀ hA₁ hB hB₀ hB₁
  exact ⟨hGen, hNot, hRigid, example4_product_complement_nonzero S T hA hA₀ hA₁ hB hB₀ hB₁,
    example4_product_complement_stronglyMixing S T hCover⟩

end Mixing
