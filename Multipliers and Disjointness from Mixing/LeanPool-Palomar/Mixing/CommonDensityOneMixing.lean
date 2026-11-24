/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.WeakMixing
public import Mathlib.Order.Interval.Finset.Nat

/-! # A single density-one mixing set in separable Hilbert spaces -/

@[expose] public section

open Filter Set TopologicalSpace
open scoped BigOperators InnerProductSpace Topology

namespace Mixing

/-- Natural density on the initial segment from zero to n, inclusive. -/
noncomputable def prefixDensity (A : Set ℕ) (n : ℕ) : ℝ :=
  finsetDensity (Finset.range (n + 1)) A

theorem prefixDensity_add_compl (A : Set ℕ) (n : ℕ) :
    prefixDensity A n + prefixDensity Aᶜ n = 1 := by
  classical
  simp only [prefixDensity, finsetDensity, Set.mem_compl_iff, ← add_div, ← Nat.cast_add,
    Finset.card_filter_add_card_filter_not, Finset.card_range]
  exact div_self (by positivity)

private theorem prefixDensity_iUnion_lt_tendsto_zero (B : ℕ → Set ℕ)
    (h : ∀ i, Tendsto (prefixDensity (B i)) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (prefixDensity (⋃ i < k, B i)) atTop (𝓝 0) := by
  induction k with
  | zero =>
    classical
    have he : (⋃ i < 0, B i) = ∅ := by simp
    rw [he, show prefixDensity ∅ = fun _ => 0 from funext fun n => by simp [prefixDensity, finsetDensity]]
    exact tendsto_const_nhds
  | succ k ih =>
    have he : (⋃ i < k + 1, B i) = (⋃ i < k, B i) ∪ B k := by
      ext m
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hi, hm⟩
        by_cases hi' : i < k
        · exact Or.inl ⟨i, hi', hm⟩
        · have hEq : i = k := by omega
          exact Or.inr (hEq ▸ hm)
      · rintro (⟨i, hi, hm⟩ | hm)
        · exact ⟨i, by omega, hm⟩
        · exact ⟨k, by omega, hm⟩
    rw [he]
    apply squeeze_zero (fun n => finsetDensity_nonneg _ _)
      (fun n => finsetDensity_union_le (Finset.range (n + 1)) _ _)
    simpa only [zero_add, prefixDensity] using ih.add (h k)

/-- Countably many density-zero sets have a density-zero union after one
discarded initial segment in each set. -/
theorem exists_prefixDensity_zero_avoiding_each_tail (B : ℕ → Set ℕ)
    (h : ∀ i, Tendsto (prefixDensity (B i)) atTop (𝓝 0)) :
    ∃ E : Set ℕ, Tendsto (prefixDensity E) atTop (𝓝 0) ∧
      ∀ i, ∀ᶠ n in atTop, n ∈ B i → n ∈ E := by
  classical
  let C (k : ℕ) := ⋃ i < k + 1, B i
  have hc (k : ℕ) : Tendsto (prefixDensity (C k)) atTop (𝓝 0) :=
    prefixDensity_iUnion_lt_tendsto_zero B h (k + 1)
  have hN (k : ℕ) : ∃ N : ℕ, k ≤ N ∧
      ∀ n ≥ N, prefixDensity (C k) n ≤ 1 / ((k : ℝ) + 1) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((hc k).eventually_lt_const (by positivity :
      0 < 1 / ((k : ℝ) + 1)))
    exact ⟨max k N, le_max_left _ _, fun n hn => (hN n ((le_max_right _ _).trans hn)).le⟩
  choose N hNk hNc using hN
  let E : Set ℕ := {m | ∃ i, N i ≤ m ∧ m ∈ B i}
  let A (n : ℕ) := (Finset.range (n + 1)).filter (fun i => N i ≤ n)
  let j (n : ℕ) := (A n).sup id
  have hA {n i : ℕ} (hi : N i ≤ n) : i ∈ A n :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ((hNk i).trans hi)), hi⟩
  have hj : Tendsto j atTop atTop := by
    apply tendsto_atTop.mpr
    intro i
    filter_upwards [eventually_ge_atTop (N i)] with n hn
    exact Finset.le_sup (f := id) (hA hn)
  have hNA : ∀ᶠ n in atTop, N (j n) ≤ n := by
    filter_upwards [eventually_ge_atTop (N 0)] with n hn
    obtain ⟨i, hi, hij⟩ := (A n).sup_mem_of_nonempty (f := id) ⟨0, hA hn⟩
    change i = j n at hij
    exact hij ▸ (Finset.mem_filter.mp hi).2
  have hUpper : ∀ᶠ n in atTop, prefixDensity E n ≤ 1 / ((j n : ℝ) + 1) := by
    filter_upwards [hNA] with n hn
    apply le_trans ?_ (hNc (j n) n hn)
    unfold prefixDensity finsetDensity
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro m hm
    obtain ⟨hmRange, i, hNi, hBi⟩ := Finset.mem_filter.mp hm
    have hNm : N i ≤ n := hNi.trans (by simpa using hmRange)
    have hj' : i ≤ j n := Finset.le_sup (f := id) (hA hNm)
    exact Finset.mem_filter.mpr ⟨hmRange, Set.mem_iUnion₂.mpr ⟨i, by omega, hBi⟩⟩
  have hLim : Tendsto (fun n => 1 / ((j n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hj
  refine ⟨E, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLim ?_ hUpper, ?_⟩
  · exact .of_forall fun n => finsetDensity_nonneg _ _
  · intro i
    filter_upwards [eventually_ge_atTop (N i)] with n hn hB
    exact ⟨i, hn, hB⟩

private def positiveIntegerEmbedding : ℕ ↪ Multiplicative ℤ where
  toFun n := Multiplicative.ofAdd (n : ℤ)
  inj' := by
    intro a b hab
    have he := congrArg Multiplicative.toAdd hab
    change (a : ℤ) = (b : ℤ) at he
    exact_mod_cast he

private def positiveIntegerBlocks (n : ℕ) : Finset (Multiplicative ℤ) :=
  (Finset.range (n + 1)).map positiveIntegerEmbedding

private theorem finsetDensity_map {A G : Type*} (F : Finset A) (e : A ↪ G) (S : Set G) :
    finsetDensity (F.map e) S = finsetDensity F (e ⁻¹' S) := by
  classical
  simp only [finsetDensity, Finset.filter_map, Finset.card_map, Set.mem_preimage, Function.comp_apply]

private theorem positiveIntegerBlocks_isFolner : IsFolnerSequence positiveIntegerBlocks := by
  classical
  constructor
  · intro n
    exact ⟨positiveIntegerEmbedding 0, Finset.mem_map.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
  · intro a
    let d := a.toAdd.natAbs
    let defect : ℕ → Set ℕ := fun n =>
      positiveIntegerEmbedding ⁻¹' {g | ∀ y ∈ positiveIntegerBlocks n, g ≠ a * y}
    have hDefect (n j : ℕ) (hj : j < n + 1) (hd : d ≤ j) (hd' : j + d ≤ n) :
        j ∉ defect n := by
      intro hBad
      have ha : |a.toAdd| = (d : ℤ) := Int.abs_eq_natAbs _
      have haL := (abs_le.mp ha.le).1
      have haU := (abs_le.mp ha.le).2
      let k := ((j : ℤ) - a.toAdd).toNat
      have hk : (k : ℤ) = (j : ℤ) - a.toAdd := Int.toNat_of_nonneg (by omega)
      have hk' : k < n + 1 := by omega
      have hMem : positiveIntegerEmbedding k ∈ positiveIntegerBlocks n :=
        Finset.mem_map.mpr ⟨k, Finset.mem_range.mpr hk', rfl⟩
      apply hBad _ hMem
      change (j : ℤ) = a.toAdd + (k : ℤ)
      omega
    have hBound (n : ℕ) : prefixDensity (defect n) n ≤ (2 * (d : ℝ)) / ((n : ℝ) + 1) := by
      unfold prefixDensity finsetDensity
      simp only [Finset.card_range, Nat.cast_add, Nat.cast_one]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hSub : (Finset.range (n + 1)).filter (· ∈ defect n) ⊆
          Finset.range d ∪ Finset.Icc (n + 1 - d) n := by
        intro j hj
        obtain ⟨hj₁, hj₂⟩ := Finset.mem_filter.mp hj
        have hj' := Finset.mem_range.mp hj₁
        by_cases hjd : j < d
        · exact Finset.mem_union_left _ (Finset.mem_range.mpr hjd)
        · have hDiff : n < j + d := by
            by_contra! h
            exact hDefect n j hj' (by omega) h hj₂
          exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hCard : ((Finset.range (n + 1)).filter (· ∈ defect n)).card ≤ 2 * d := by
        refine (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans ?_)
        rw [Finset.card_range, Nat.card_Icc]
        omega
      exact_mod_cast hCard
    simp only [positiveIntegerBlocks, finsetDensity_map]
    change Tendsto (fun n => prefixDensity (defect n) n) atTop (𝓝 0)
    have hLim : Tendsto (fun n : ℕ => (2 * (d : ℝ)) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero, ← mul_div_assoc, mul_one] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (d : ℝ))
    exact squeeze_zero (fun n => finsetDensity_nonneg _ _) hBound hLim

private theorem prefixDensity_threshold_tendsto_zero (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun n => (∑ m ∈ Finset.range (n + 1), f m) / ((n : ℝ) + 1)) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (prefixDensity {m | δ ≤ f m}) atTop (𝓝 0) := by
  classical
  have hMajor (n : ℕ) : δ * prefixDensity {m | δ ≤ f m} n ≤
      (∑ m ∈ Finset.range (n + 1), f m) / ((n : ℝ) + 1) := by
    unfold prefixDensity finsetDensity
    simp only [Finset.card_range, Nat.cast_add, Nat.cast_one, ← mul_div_assoc, Set.mem_ofPred_eq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ = ∑ _ ∈ (Finset.range (n + 1)).filter (fun g => δ ≤ f g), δ := by simp [mul_comm]
      _ ≤ ∑ g ∈ (Finset.range (n + 1)).filter (fun g => δ ≤ f g), f g :=
        Finset.sum_le_sum fun g hg => (Finset.mem_filter.mp hg).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun g _ _ => hf g
  have hUpper (n : ℕ) : prefixDensity {m | δ ≤ f m} n ≤
      ((∑ m ∈ Finset.range (n + 1), f m) / ((n : ℝ) + 1)) / δ :=
    (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hMajor n)
  apply squeeze_zero (fun n => finsetDensity_nonneg _ _) hUpper
  simpa only [zero_div] using h.div_const δ

set_option maxHeartbeats 1200000 in
/-- Equation (10). A weakly mixing representation of the integers on a
separable Hilbert space has one density-one set along which all weak
matrix coefficients tend to zero. -/
theorem exists_common_densityOne_mixingSet {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) (hU : IsWeaklyMixing U) :
    ∃ D : Set ℕ, Tendsto (prefixDensity Dᶜ) atTop (𝓝 0) ∧
      ∀ x y : H, Tendsto (fun n : ℕ => ⟪x, U (Multiplicative.ofAdd (n : ℤ)) y⟫_ℂ)
        (atTop ⊓ 𝓟 D) (𝓝 0) := by
  let d := denseSeq H
  let f (i n : ℕ) : ℂ := ⟪d i, U (positiveIntegerEmbedding n) (d i)⟫_ℂ
  let δ (k : ℕ) := 1 / ((k : ℝ) + 1)
  let B (k : ℕ) := ⋃ i < k + 1, {n | δ k ≤ ‖f i n‖}
  have hAvg (i : ℕ) : Tendsto
      (fun n => (∑ m ∈ Finset.range (n + 1), ‖f i m‖) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := hU (d i) positiveIntegerBlocks positiveIntegerBlocks_isFolner
    simpa only [positiveIntegerBlocks, Finset.sum_map, Finset.card_map, Finset.card_range,
      Nat.cast_add, Nat.cast_one, f] using h
  have hB (k : ℕ) : Tendsto (prefixDensity (B k)) atTop (𝓝 0) := by
    apply prefixDensity_iUnion_lt_tendsto_zero
    intro i
    exact prefixDensity_threshold_tendsto_zero _ (fun _ => norm_nonneg _) (hAvg i) _ (by
      dsimp [δ]
      positivity)
  obtain ⟨E, hE, hAvoid⟩ := exists_prefixDensity_zero_avoiding_each_tail B hB
  let D := Eᶜ
  let L : Filter ℕ := atTop ⊓ 𝓟 D
  have hDiag (i : ℕ) : Tendsto (f i) L (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hε)
    let k := max i K
    have hδ : δ k < ε := hK k (le_max_right _ _)
    have hL : ∀ᶠ n in L, n ∈ D := Filter.le_principal_iff.mp
      (inf_le_right : L ≤ 𝓟 D)
    filter_upwards [(hAvoid k).filter_mono (inf_le_left : L ≤ atTop), hL] with n hn hnD
    rw [dist_zero_right]
    by_contra! hlarge
    have hN : n ∈ B k := Set.mem_iUnion₂.mpr ⟨i, Nat.lt_succ_of_le (le_max_left _ _),
      hδ.le.trans hlarge⟩
    exact hnD (hn hN)
  refine ⟨D, by simpa [D] using hE, fun x y => ?_⟩
  apply (Filter.tendsto_iff_ultrafilter _ _ _).mpr
  intro p hp
  let q := p.map positiveIntegerEmbedding
  let Q := ultrafilterOperator U q
  have hLim (x y : H) :
      Tendsto (fun n : ℕ => ⟪x, U (positiveIntegerEmbedding n) y⟫_ℂ) (p : Filter ℕ)
        (𝓝 ⟪x, Q y⟫_ℂ) := (tendsto_ultrafilterOperator_coeff U q x y).comp tendsto_map
  have hDenseDiag (i : ℕ) : ⟪d i, Q (d i)⟫_ℂ = 0 :=
    tendsto_nhds_unique (hLim (d i) (d i)) ((hDiag i).mono_left hp)
  have hAllDiag (x : H) : ⟪x, Q x⟫_ℂ = 0 := by
    have hCont : Continuous (fun z : H => ⟪z, Q z⟫_ℂ) := continuous_id.inner Q.continuous
    have hEq : (fun z : H => ⟪z, Q z⟫_ℂ) ∘ d = (fun _ : H => (0 : ℂ)) ∘ d :=
      funext hDenseDiag
    exact congrFun ((denseRange_denseSeq H).equalizer hCont continuous_const hEq) x
  have hQ : Q = 0 := by
    apply ContinuousLinearMap.coe_injective
    rw [ContinuousLinearMap.toLinearMap_zero, ← inner_map_self_eq_zero]
    intro z
    rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm, hAllDiag z, map_zero]
  change Tendsto (fun n : ℕ => ⟪x, U (positiveIntegerEmbedding n) y⟫_ℂ) (p : Filter ℕ) (𝓝 0)
  simpa only [hQ, zero_apply, inner_zero_right] using hLim x y

/-- Equation (10) with density expressed as convergence to one. -/
theorem exists_common_mixingSet_prefixDensity_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
    (U : Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H)) (hU : IsWeaklyMixing U) :
    ∃ D : Set ℕ, Tendsto (prefixDensity D) atTop (𝓝 1) ∧
      ∀ x y : H, Tendsto (fun n : ℕ => ⟪x, U (Multiplicative.ofAdd (n : ℤ)) y⟫_ℂ)
        (atTop ⊓ 𝓟 D) (𝓝 0) := by
  obtain ⟨D, hD, hMix⟩ := exists_common_densityOne_mixingSet U hU
  refine ⟨D, ?_, hMix⟩
  have he : (fun n => 1 - prefixDensity Dᶜ n) = prefixDensity D := by
    funext n
    linarith [prefixDensity_add_compl D n]
  simpa only [sub_zero, he] using (tendsto_const_nhds (x := (1 : ℝ))).sub hD

end Mixing
