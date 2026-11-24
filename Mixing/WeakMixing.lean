/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.SpectralDisjointness
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.LiminfLimsup

/-! # Weak mixing and essential ultrafilters -/

@[expose] public section

open Filter Set
open scoped BigOperators InnerProductSpace Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite-block density of a subset of the group. -/
noncomputable def finsetDensity (F : Finset G) (A : Set G) : ℝ := by
  classical
  exact ((F.filter fun g => g ∈ A).card : ℝ) / F.card

/-- A Følner sequence of nonempty finite subsets. Since the original block and
its translate have the same cardinality, the one-sided deficit used here is
half the symmetric-difference deficit. -/
def IsFolnerSequence (F : ℕ → Finset G) : Prop :=
  (∀ n, (F n).Nonempty) ∧ ∀ a : G,
    Tendsto (fun n => finsetDensity (F n) {g | ∀ y ∈ F n, g ≠ a * y}) atTop (𝓝 0)

/-- The upper density is positive along at least one Følner sequence. -/
def HasPositiveFolnerDensity (A : Set G) : Prop :=
  ∃ F : ℕ → Finset G, IsFolnerSequence F ∧
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n in atTop, ε ≤ finsetDensity (F n) A

/-- The family Λ(G) from §3.3. -/
def essentialUltrafilters (G : Type*) [Group G] : Set (Ultrafilter G) :=
  {p | ∀ A ∈ p, HasPositiveFolnerDensity A}

variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- Equation (8). Absolute diagonal matrix coefficients have zero Følner average. -/
def IsWeaklyMixing : Prop :=
  ∀ x : H, ∀ F : ℕ → Finset G, IsFolnerSequence F →
    Tendsto (fun n => (∑ g ∈ F n, ‖⟪x, U g x⟫_ℂ‖) / (F n).card) atTop (𝓝 0)

/-- A positive threshold on a set of positive Følner density gives a positive
lower bound for the averages on arbitrarily late blocks. -/
theorem not_tendsto_zero_of_hasPositiveFolnerDensity {f : G → ℝ} (hf : ∀ g, 0 ≤ f g)
    {δ : ℝ} (hδ : 0 < δ)
    (h : HasPositiveFolnerDensity {g | δ ≤ f g}) :
    ∃ F : ℕ → Finset G, IsFolnerSequence F ∧
      ¬ Tendsto (fun n => (∑ g ∈ F n, f g) / (F n).card) atTop (𝓝 0) := by
  classical
  obtain ⟨F, hF, ε, hε, hFreq⟩ := h
  refine ⟨F, hF, fun hlim => ?_⟩
  have hSmall := hlim.eventually_lt_const (mul_pos hδ hε)
  obtain ⟨n, hnLarge, hnSmall⟩ := (hFreq.and_eventually hSmall).exists
  have hBound : δ * finsetDensity (F n) {g | δ ≤ f g} ≤
      (∑ g ∈ F n, f g) / (F n).card := by
    rw [finsetDensity, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    calc
      δ * ((Finset.filter (fun g => δ ≤ f g) (F n)).card : ℝ) =
          ∑ _g ∈ (F n).filter (fun g => δ ≤ f g), δ := by simp [mul_comm]
      _ ≤ ∑ g ∈ (F n).filter (fun g => δ ≤ f g), f g :=
        Finset.sum_le_sum fun g hg => (Finset.mem_filter.mp hg).2
      _ ≤ ∑ g ∈ F n, f g :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun g _ _ => hf g
  exact hnSmall.not_ge ((mul_le_mul_of_nonneg_left hnLarge hδ.le).trans hBound)

/-- Proposition 4, weak mixing implies Λ(G)-mixing. -/
theorem isUMixing_essential_of_isWeaklyMixing (hU : IsWeaklyMixing U) :
    IsUMixing U (essentialUltrafilters G) := by
  intro p hp
  apply ContinuousLinearMap.coe_injective
  rw [ContinuousLinearMap.toLinearMap_zero, ← inner_map_self_eq_zero]
  intro x
  have hlim := tendsto_ultrafilterOperator_coeff U p x x
  have hz : ⟪x, ultrafilterOperator U p x⟫_ℂ = 0 := by
    by_contra hz
    let δ := ‖⟪x, ultrafilterOperator U p x⟫_ℂ‖ / 2
    have hδ : 0 < δ := half_pos (norm_pos_iff.mpr hz)
    have hNorm := hlim.norm
    have hLarge : {g | δ ≤ ‖⟪x, U g x⟫_ℂ‖} ∈ p := by
      have hThreshold : δ < ‖⟪x, ultrafilterOperator U p x⟫_ℂ‖ :=
        half_lt_self (norm_pos_iff.mpr hz)
      filter_upwards [hNorm.eventually_const_lt hThreshold] with g hg
      exact le_of_lt hg
    obtain ⟨F, hF, hfail⟩ := not_tendsto_zero_of_hasPositiveFolnerDensity
      (fun _ => norm_nonneg _) hδ (hp _ hLarge)
    exact hfail (hU x F hF)
  rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm, hz, map_zero]

section Densities

omit [Group G]

variable {A B : Set G} {F : ℕ → Finset G}

theorem finsetDensity_nonneg (E : Finset G) (A : Set G) : 0 ≤ finsetDensity E A := by
  unfold finsetDensity
  positivity

theorem finsetDensity_le_one (E : Finset G) (A : Set G) : finsetDensity E A ≤ 1 := by
  classical
  by_cases h : E.Nonempty
  · unfold finsetDensity
    rw [div_le_iff₀ (by exact_mod_cast h.card_pos), one_mul]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp [finsetDensity]

theorem finsetDensity_mono (E : Finset G) (h : A ⊆ B) :
    finsetDensity E A ≤ finsetDensity E B := by
  classical
  unfold finsetDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hx).1, h (Finset.mem_filter.mp hx).2⟩)

theorem finsetDensity_union_le (E : Finset G) (A B : Set G) :
    finsetDensity E (A ∪ B) ≤ finsetDensity E A + finsetDensity E B := by
  classical
  simp only [finsetDensity, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_cast
  apply le_trans (b := (E.filter (· ∈ A) ∪ E.filter (· ∈ B)).card)
  · apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hx ⊢
    tauto
  · exact Finset.card_union_le _ _

theorem finsetDensity_empty (E : Finset G) : finsetDensity E ∅ = 0 := by
  classical
  simp [finsetDensity]

/-- Sets whose complements have vanishing density along a fixed block sequence form a filter. -/
def densityOneFilter (F : ℕ → Finset G) : Filter G where
  sets := {A | Tendsto (fun n => finsetDensity (F n) Aᶜ) atTop (𝓝 0)}
  univ_sets := by
    simpa only [Set.mem_ofPred_eq, Set.compl_univ, finsetDensity_empty] using
      (tendsto_const_nhds (x := (0 : ℝ)) (f := (atTop : Filter ℕ)))
  sets_of_superset := fun {A B} hA hAB =>
    squeeze_zero (fun n => finsetDensity_nonneg (F n) Bᶜ)
      (fun n => finsetDensity_mono (F n) (Set.compl_subset_compl.mpr hAB)) hA
  inter_sets := fun {A B} hA hB => by
    change Tendsto (fun n => finsetDensity (F n) (A ∩ B)ᶜ) atTop (𝓝 0)
    rw [Set.compl_inter]
    have hlim := hA.add hB
    rw [add_zero] at hlim
    exact squeeze_zero (fun n => finsetDensity_nonneg (F n) _)
      (fun n => finsetDensity_union_le (F n) Aᶜ Bᶜ) hlim

theorem not_tendsto_finsetDensity_zero_iff :
    ¬ Tendsto (fun n => finsetDensity (F n) A) atTop (𝓝 0) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n in atTop, ε ≤ finsetDensity (F n) A := by
  rw [Metric.tendsto_nhds]
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (finsetDensity_nonneg _ _),
    not_forall, not_eventually, not_lt, exists_prop]

/-- A positive density set belongs to some essential ultrafilter. -/
theorem exists_essentialUltrafilter_mem_of_hasPositiveFolnerDensity
    [Group G] (hA : HasPositiveFolnerDensity A) :
    ∃ p ∈ essentialUltrafilters G, A ∈ p := by
  obtain ⟨F, hF, hPos⟩ := hA
  have hNot := not_tendsto_finsetDensity_zero_iff.mpr hPos
  have hNe : NeBot (densityOneFilter F ⊓ 𝓟 A) := by
    refine Filter.inf_principal_neBot_iff.mpr fun B hB => ?_
    by_contra hNone
    have hSub : A ⊆ Bᶜ := fun a ha hb => hNone ⟨a, hb, ha⟩
    exact hNot (squeeze_zero (fun n => finsetDensity_nonneg (F n) A)
      (fun n => finsetDensity_mono (F n) hSub) hB)
  obtain ⟨p, hp⟩ := Filter.exists_ultrafilter_le (densityOneFilter F ⊓ 𝓟 A)
  refine ⟨p, ?_, le_principal_iff.mp (hp.trans inf_le_right)⟩
  intro S hS
  refine ⟨F, hF, not_tendsto_finsetDensity_zero_iff.mp ?_⟩
  intro hZero
  apply Filter.compl_notMem hS
  apply hp.trans inf_le_left
  change Tendsto (fun n => finsetDensity (F n) Sᶜᶜ) atTop (𝓝 0)
  simpa only [compl_compl] using hZero

theorem finsetDensity_threshold_bound_average {f : G → ℝ} {M δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ g, f g ≤ M) (E : Finset G) (hE : E.Nonempty) :
    (∑ g ∈ E, f g) / E.card ≤ δ + M * finsetDensity E {g | δ ≤ f g} := by
  classical
  have hCard : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
  let A := E.filter fun g => δ ≤ f g
  have hSum : (∑ g ∈ E, f g) ≤ ∑ g ∈ E, (δ + if δ ≤ f g then M else 0) := by
    apply Finset.sum_le_sum
    intro g _
    by_cases hg : δ ≤ f g
    · rw [ite_eq_left hg]
      linarith [hf g]
    · rw [ite_eq_right hg, add_zero]
      exact le_of_lt (lt_of_not_ge hg)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hSum
  simp only [Finset.sum_const] at hSum
  have hSum' : (∑ g ∈ E, f g) ≤ (E.card : ℝ) * δ + (A.card : ℝ) * M := by
    simpa only [A, nsmul_eq_mul] using hSum
  apply (div_le_iff₀ hCard).mpr
  refine hSum'.trans_eq ?_
  change (E.card : ℝ) * δ + (A.card : ℝ) * M =
    (δ + M * ((A.card : ℝ) / E.card)) * E.card
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ hCard.ne']
  ring

/-- A bounded nonnegative function has zero averages if all its positive threshold
sets have asymptotic density zero. -/
theorem tendsto_zero_average_of_finsetDensity_threshold_zero {f : G → ℝ} {M : ℝ}
    (hf : ∀ g, 0 ≤ f g) (hfM : ∀ g, f g ≤ M) (hF : ∀ n, (F n).Nonempty)
    (h : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => finsetDensity (F n) {g | δ ≤ f g}) atTop (𝓝 0)) :
    Tendsto (fun n => (∑ g ∈ F n, f g) / (F n).card) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hLim := (tendsto_const_nhds (x := M)).mul (h (ε / 2) (half_pos hε))
  rw [mul_zero] at hLim
  filter_upwards [hLim.eventually_lt_const (half_pos hε)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Finset.sum_nonneg fun g _ => hf g)
    (Nat.cast_nonneg _))]
  linarith [finsetDensity_threshold_bound_average (f := f) (half_pos hε).le hfM
    (F n) (hF n)]

end Densities

/-- The frequent positive lower bound in the definition is equivalent to the
strictly positive limsup of the paper's finite-block densities. -/
theorem hasPositiveFolnerDensity_iff_limsup_pos (A : Set G) :
    HasPositiveFolnerDensity A ↔ ∃ F : ℕ → Finset G, IsFolnerSequence F ∧
      0 < Filter.limsup (fun n => finsetDensity (F n) A) atTop := by
  constructor
  · rintro ⟨F, hF, ε, hε, hfreq⟩
    have hbounded := isBoundedUnder_of_eventually_le
      (f := (atTop : Filter ℕ)) (.of_forall fun n => finsetDensity_le_one (F n) A)
    exact ⟨F, hF, hε.trans_le (le_limsup_of_frequently_le hfreq hbounded)⟩
  · rintro ⟨F, hF, hpos⟩
    obtain ⟨ε, hε, hlt⟩ := exists_between hpos
    have hc := isCoboundedUnder_le_of_eventually_le (atTop : Filter ℕ)
      (.of_forall fun n => finsetDensity_nonneg (F n) A)
    exact ⟨F, hF, ε, hε, (frequently_lt_of_lt_limsup hc hlt).mono fun _ => le_of_lt⟩

/-- Proposition 4(i), testing the family Λ(G) is equivalent to weak mixing. -/
theorem isWeaklyMixing_iff_isUMixing_essential :
    IsWeaklyMixing U ↔ IsUMixing U (essentialUltrafilters G) := by
  refine ⟨isUMixing_essential_of_isWeaklyMixing U, ?_⟩
  intro hU x F hF
  have hbound (g : G) : ‖⟪x, U g x⟫_ℂ‖ ≤ ‖x‖ * ‖x‖ := by
    simpa only [(U g).norm_map] using norm_inner_le_norm x (U g x)
  apply tendsto_zero_average_of_finsetDensity_threshold_zero (fun _ => norm_nonneg _) hbound hF.1
  intro δ hδ
  by_contra hz
  obtain ⟨p, hp, hA⟩ := exists_essentialUltrafilter_mem_of_hasPositiveFolnerDensity
    ⟨F, hF, not_tendsto_finsetDensity_zero_iff.mp hz⟩
  have hlim := (tendsto_ultrafilterOperator_coeff U p x x).norm
  rw [hU p hp, zero_apply, inner_zero_right, norm_zero] at hlim
  have hA' : ∀ᶠ g in (p : Filter G), δ ≤ ‖⟪x, U g x⟫_ℂ‖ := hA
  obtain ⟨g, hg, hsmall⟩ := (hA'.and (hlim.eventually_lt_const hδ)).exists
  exact hsmall.not_ge hg

end Mixing
