/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Bases
public import Mathlib.Tactic.Linarith

/-!
# Density-one diagonal selection

This is the countable diagonal argument in the proof of Theorem 4.2(ix) and
Corollary 4.3 of arXiv:2509.24003v3. The probability measures may have
overlapping compact supports.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace JdLG

variable {S : Type*} [MeasurableSpace S] [TopologicalSpace S]

/-- Given decreasing measurable sets of asymptotic mass one for probabilities
supported on compact blocks, one can meet all the sets outside compact
exceptions while keeping asymptotic mass one. -/
theorem density_one_diagonal (ν : ℕ → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    (F A : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFm : ∀ n, MeasurableSet (F n))
    (hsupp : ∀ n, ν n (F n)ᶜ = 0) (hA : ∀ k, MeasurableSet (A k)) (hAnti : Antitone A)
    (hdense : ∀ k, Tendsto (fun n ↦ (ν n).real (A k)) atTop (𝓝 1)) :
    ∃ B : Set S, MeasurableSet B ∧ Tendsto (fun n ↦ (ν n).real B) atTop (𝓝 1) ∧
      ∀ k, ∃ C : Set S, IsCompact C ∧ B \ A k ⊆ C := by
  classical
  let δ : ℕ → ℝ := fun k ↦ (1 / 2 : ℝ) ^ k
  have hδpos (k : ℕ) : 0 < δ k := pow_pos (by norm_num) _
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num) (by norm_num)
  have hthreshold (k : ℕ) : ∃ N, ∀ n ≥ N, 1 - δ k ≤ (ν n).real (A k) := by
    have hnear := (hdense k).eventually (lt_mem_nhds (sub_lt_self 1 (hδpos k)))
    exact eventually_atTop.1 (hnear.mono fun _ hn ↦ hn.le)
  let M : ℕ → ℕ := fun k ↦ (hthreshold k).choose
  let stage : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun k ↦ M k ≤ n) n
  have hstage : Tendsto stage atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (max k (M k))] with n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  let B := ⋃ n : ℕ, A (stage n) ∩ F n
  have hB : MeasurableSet B := MeasurableSet.iUnion fun n ↦ (hA (stage n)).inter (hFm n)
  refine ⟨B, hB, ?_, ?_⟩
  · have hv : Tendsto (fun n ↦ 1 - δ (stage n)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (hδ.comp hstage)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hv tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop (M 0)] with n hn
      have hMn : M (stage n) ≤ n := Nat.findGreatest_spec (P := fun k ↦ M k ≤ n)
        (Nat.zero_le n) hn
      have ha := (hthreshold (stage n)).choose_spec n hMn
      have hsame : (ν n).real (A (stage n) ∩ F n) = (ν n).real (A (stage n)) :=
        congrArg ENNReal.toReal (measure_inter_conull (hsupp n))
      let : IsProbabilityMeasure (ν n) := hprob n
      exact (ha.trans_eq hsame.symm).trans
        (measureReal_mono (subset_iUnion (fun k ↦ A (stage k) ∩ F k) n))
    · exact Eventually.of_forall fun n ↦ by
        let : IsProbabilityMeasure (ν n) := hprob n
        exact measureReal_le_one
  · intro k
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_atTop.1 hstage k)
    refine ⟨⋃ n ∈ Finset.range N, F n,
      (Finset.range N).isCompact_biUnion (fun n _ ↦ hF n), ?_⟩
    rintro s ⟨hs, hnot⟩
    obtain ⟨n, hAn, hFn⟩ := mem_iUnion.1 hs
    have hlt : n < N := by
      by_contra! hn
      exact hnot (hAnti (hN n hn) hAn)
    exact mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨Finset.mem_range.2 hlt, hFn⟩⟩

/-- A density-one set on which all bad returns lie in compact sets gives
full asymptotic return mass, provided those compact sets lose all mass. This
is the reverse implication in the diagonal step of Theorem 4.2(ix). -/
theorem density_one_return_of_compact_exception {ι : Type*} {l : Filter ι}
    (ν : ι → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    (hescape : ∀ C : Set S, IsCompact C → Tendsto (fun n ↦ (ν n).real C) l (𝓝 0))
    {A U : Set S} (hA : Tendsto (fun n ↦ (ν n).real A) l (𝓝 1))
    (hbad : ∃ C : Set S, IsCompact C ∧ A \ U ⊆ C) :
    Tendsto (fun n ↦ (ν n).real U) l (𝓝 1) := by
  obtain ⟨C, hC, hbad⟩ := hbad
  have hsubset : A ⊆ U ∪ C := fun x hx ↦ by
    by_cases hU : x ∈ U
    · exact Or.inl hU
    · exact Or.inr (hbad ⟨hx, hU⟩)
  have hv : Tendsto (fun n ↦ (ν n).real A - (ν n).real C) l (𝓝 1) := by
    simpa using hA.sub (hescape C hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hv tendsto_const_nhds ?_ ?_
  · exact Eventually.of_forall fun n ↦ by
      let : IsProbabilityMeasure (ν n) := hprob n
      exact sub_le_iff_le_add.2 ((measureReal_mono hsubset).trans (measureReal_union_le U C))
  · exact Eventually.of_forall fun n ↦ by
      let : IsProbabilityMeasure (ν n) := hprob n
      exact measureReal_le_one

/-- A countable neighborhood basis at the limit is sufficient for the
forward implication in Theorem 4.2(ix). The paper obtains such a basis
after restricting to a full-mass support in the weak orbit. -/
theorem exists_density_one_tendsto_cocompact_of_countableBasis
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (ν : ℕ → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFm : ∀ n, MeasurableSet (F n))
    (hsupp : ∀ n, ν n (F n)ᶜ = 0) (φ : S → X) (hφ : Measurable φ)
    (y : X) [Filter.IsCountablyGenerated (𝓝 y)]
    (hreturn : ∀ U : Set X, IsOpen U → y ∈ U →
      Tendsto (fun n ↦ (ν n).real (φ ⁻¹' U)) atTop (𝓝 1)) :
    ∃ A : Set S, MeasurableSet A ∧ Tendsto (fun n ↦ (ν n).real A) atTop (𝓝 1) ∧
      Tendsto φ (cocompact S ⊓ 𝓟 A) (𝓝 y) := by
  obtain ⟨U, hU, hb⟩ := (nhds_basis_opens y).exists_antitone_subbasis
  obtain ⟨A, hA, hd, ht⟩ := density_one_diagonal ν hprob F (fun n ↦ φ ⁻¹' U n) hF hFm hsupp
    (fun n ↦ (hU n).2.measurableSet.preimage hφ)
    (fun _ _ hn ↦ preimage_mono (hb.antitone hn))
    (fun n ↦ hreturn _ (hU n).2 (hU n).1)
  refine ⟨A, hA, hd, hb.toHasBasis.tendsto_right_iff.2 fun n _ ↦ ?_⟩
  obtain ⟨C, hC, hAC⟩ := ht n
  exact eventually_inf_principal.2
    ((Filter.hasBasis_cocompact.eventually_iff).2
      ⟨C, hC, fun {_} hc ha ↦ by
        by_contra hn
        exact hc (hAC ⟨ha, hn⟩)⟩)

/-- The reverse implication in Theorem 4.2(ix), with compact exceptions
expressed by convergence along a cocompact filter restricted to a set. -/
theorem density_one_returns_of_tendsto_cocompact
    {X I : Type*} [TopologicalSpace X] {l : Filter I}
    (ν : I → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    (hescape : ∀ C : Set S, IsCompact C → Tendsto (fun n ↦ (ν n).real C) l (𝓝 0))
    (φ : S → X) {y : X} {A : Set S} (hA : Tendsto (fun n ↦ (ν n).real A) l (𝓝 1))
    (hφ : Tendsto φ (cocompact S ⊓ 𝓟 A) (𝓝 y))
    (U : Set X) (hU : U ∈ 𝓝 y) :
    Tendsto (fun n ↦ (ν n).real (φ ⁻¹' U)) l (𝓝 1) := by
  apply density_one_return_of_compact_exception ν hprob hescape hA
  obtain ⟨C, hC, hCU⟩ := Filter.hasBasis_cocompact.eventually_iff.1
    (eventually_inf_principal.1 (hφ.eventually hU))
  exact ⟨C, hC, fun s hs ↦ by
    by_contra hn
    exact hs.2 (hCU hn hs.1)⟩

omit [TopologicalSpace S] in
theorem density_one_inter {I : Type*} {l : Filter I}
    (ν : I → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    {A B : Set S} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA : Tendsto (fun n ↦ (ν n).real A) l (𝓝 1))
    (hB : Tendsto (fun n ↦ (ν n).real B) l (𝓝 1)) :
    Tendsto (fun n ↦ (ν n).real (A ∩ B)) l (𝓝 1) := by
  have ht : Tendsto (fun n ↦ ((ν n).real A + (ν n).real B) - 1) l (𝓝 1) := by
    have h1 : Tendsto (fun _ : I ↦ (1 : ℝ)) l (𝓝 1) := tendsto_const_nhds
    convert (hA.add hB).sub h1 using 2
    norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ht tendsto_const_nhds ?_ ?_
  · exact Eventually.of_forall fun n ↦ by
      let : IsProbabilityMeasure (ν n) := hprob n
      have h := measureReal_union_le (μ := ν n) Aᶜ Bᶜ
      rw [← compl_inter, probReal_compl_eq_one_sub (hAm.inter hBm),
        probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hBm] at h
      linarith
  · exact Eventually.of_forall fun n ↦ by
      let : IsProbabilityMeasure (ν n) := hprob n
      exact measureReal_le_one

/-- One density-one set suffices for countably many convergence statements,
provided each statement holds on a density-one set. This is the common-set
step in Corollary 4.3. -/
theorem exists_common_density_one_tendsto_cocompact
    {X : Type*} [TopologicalSpace X]
    (ν : ℕ → Measure S) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    (F : ℕ → Set S) (hF : ∀ n, IsCompact (F n)) (hFm : ∀ n, MeasurableSet (F n))
    (hsupp : ∀ n, ν n (F n)ᶜ = 0) (φ : ℕ → S → X) (y : ℕ → X)
    (hφ : ∀ k, ∃ B : Set S, MeasurableSet B ∧
      Tendsto (fun n ↦ (ν n).real B) atTop (𝓝 1) ∧ Tendsto (φ k) (cocompact S ⊓ 𝓟 B) (𝓝 (y k))) :
    ∃ D : Set S, MeasurableSet D ∧ Tendsto (fun n ↦ (ν n).real D) atTop (𝓝 1) ∧
      ∀ k, Tendsto (φ k) (cocompact S ⊓ 𝓟 D) (𝓝 (y k)) := by
  choose B hBm hBd hBt using hφ
  let A : ℕ → Set S := fun n ↦ Nat.rec (B 0) (fun k prev ↦ prev ∩ B (k + 1)) n
  have hAstep (n : ℕ) : A (n + 1) = A n ∩ B (n + 1) := rfl
  have hAnti : Antitone A := antitone_nat_of_succ_le fun n ↦
    (hAstep n).symm ▸ inter_subset_left
  have hAB (n : ℕ) : A n ⊆ B n := by
    cases n with
    | zero => exact Subset.rfl
    | succ n => rw [hAstep]; exact inter_subset_right
  have hAm (n : ℕ) : MeasurableSet (A n) := by
    induction n with
    | zero => exact hBm 0
    | succ n ih => rw [hAstep]; exact ih.inter (hBm (n + 1))
  have hAd (k : ℕ) : Tendsto (fun n ↦ (ν n).real (A k)) atTop (𝓝 1) := by
    induction k with
    | zero => exact hBd 0
    | succ k ih =>
      simp only [hAstep]
      exact density_one_inter ν hprob (hAm k) (hBm (k + 1)) ih (hBd (k + 1))
  obtain ⟨D, hDm, hDd, hD⟩ := density_one_diagonal ν hprob F A hF hFm hsupp hAm hAnti hAd
  refine ⟨D, hDm, hDd, fun k ↦ (hBt k).mono_left ?_⟩
  apply le_inf inf_le_left
  apply le_principal_iff.2
  obtain ⟨C, hC, hDC⟩ := hD k
  exact eventually_inf_principal.2 (Filter.hasBasis_cocompact.eventually_iff.2
    ⟨C, hC, fun {_} hc hd ↦ by
      by_contra hn
      exact hc (hDC ⟨hd, fun ha ↦ hn (hAB k ha)⟩)⟩)

end JdLG
