/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroPhaseObservation
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped BigOperators Classical ENNReal Topology symmDiff

/-- Observation events decided by the central sign and a finite prefix of
the sequence of dyadic phases. -/
def rudinShapiroPrefixEvents : Set (Set RudinShapiroObservations) :=
  {s | ∃ k : ℕ, ∀ x y : RudinShapiroObservations,
    (∀ j ≤ k, x.1 j = y.1 j) → x.2 = y.2 → (x ∈ s ↔ y ∈ s)}

theorem rudinShapiroPrefixEvents_isSetAlgebra : IsSetAlgebra rudinShapiroPrefixEvents where
  empty_mem := ⟨0, fun _ _ _ _ ↦ Iff.rfl⟩
  compl_mem := by
    rintro s ⟨k, hs⟩
    exact ⟨k, fun x y hp hb ↦ not_congr (hs x y hp hb)⟩
  union_mem := by
    rintro s t ⟨k, hs⟩ ⟨l, ht⟩
    refine ⟨max k l, fun x y hp hb ↦ ?_⟩
    exact or_congr (hs x y (fun j hj ↦ hp j (hj.trans (le_max_left _ _))) hb)
      (ht x y (fun j hj ↦ hp j (hj.trans (le_max_right _ _))) hb)

theorem measurableSet_of_prefixEvent {s : Set RudinShapiroObservations}
    (hs : s ∈ rudinShapiroPrefixEvents) : MeasurableSet s := by
  obtain ⟨k, hs⟩ := hs
  let A := ((j : Fin (k + 1)) → Fin (2 ^ j.val)) × Bool
  let f (x : RudinShapiroObservations) : A := (fun j ↦ x.1 j.val, x.2)
  let g (v : A) : RudinShapiroObservations :=
    (fun j ↦ if h : j < k + 1 then v.1 ⟨j, h⟩ else ⟨0, by positivity⟩, v.2)
  have hf : Measurable f := (Measurable.of_eval fun j : Fin (k + 1) ↦
    (measurable_pi_apply j.val).comp measurable_fst).prodMk measurable_snd
  have hfg : s = f ⁻¹' (g ⁻¹' s) := by
    ext x
    apply hs x (g (f x)) _ rfl
    intro j hj
    change x.1 j = (if h : j < k + 1 then x.1 j else ⟨0, by positivity⟩)
    rw [dite_eq_left (Nat.lt_succ_of_le hj)]
  rw [hfg]
  exact hf MeasurableSet.of_discrete

theorem rudinShapiroPrefixEvents_generate :
    (inferInstance : MeasurableSpace RudinShapiroObservations) =
      MeasurableSpace.generateFrom rudinShapiroPrefixEvents := by
  apply le_antisymm _ (MeasurableSpace.generateFrom_le fun _ h ↦ measurableSet_of_prefixEvent h)
  let ambient := (inferInstance : MeasurableSpace RudinShapiroObservations)
  let m := MeasurableSpace.generateFrom rudinShapiroPrefixEvents
  have hp (k : ℕ) : @Measurable _ _ m _ (fun x : RudinShapiroObservations ↦ x.1 k) := by
    intro A _
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨k, fun x y h _ ↦ ?_⟩
    change x.1 k ∈ A ↔ y.1 k ∈ A
    rw [h k le_rfl]
  have hb : @Measurable _ _ m _ (Prod.snd : RudinShapiroObservations → Bool) := by
    intro A _
    apply MeasurableSpace.measurableSet_generateFrom
    exact ⟨0, fun x y _ h ↦ by change x.2 ∈ A ↔ y.2 ∈ A; rw [h]⟩
  have hid : @Measurable _ _ m ambient (id : RudinShapiroObservations → RudinShapiroObservations) :=
    (@Measurable.of_eval _ _ _ m _ _ hp).prodMk hb
  simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hid

private def rudinShapiroWordPrefixEvents : Set (Set SignWords) :=
  {s | ∃ t ∈ rudinShapiroPrefixEvents, s = rudinShapiroObservations ⁻¹' t}

private theorem measureDense_rudinShapiroWordPrefixEvents (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop) :
    (rudinShapiroOrbitLaw p : Measure SignWords).MeasureDense rudinShapiroWordPrefixEvents := by
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  let ν := μ.map rudinShapiroObservations
  let : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hν : ν.MeasureDense rudinShapiroPrefixEvents :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite ν
      rudinShapiroPrefixEvents_isSetAlgebra rudinShapiroPrefixEvents_generate
  refine ⟨?_, ?_⟩
  · rintro s ⟨t, ht, rfl⟩
    exact measurable_rudinShapiroObservations (measurableSet_of_prefixEvent ht)
  · intro s hs _ ε hε
    obtain ⟨t, ht, he⟩ := ae_eq_preimage_rudinShapiroObservations p hp hs
    obtain ⟨r, hr, hClose⟩ := hν.approx t ht (measure_ne_top _ _) ε hε
    refine ⟨rudinShapiroObservations ⁻¹' r, ⟨r, hr, rfl⟩, ?_⟩
    have hre : (rudinShapiroObservations ⁻¹' r : Set SignWords) =ᵐ[μ]
        (rudinShapiroObservations ⁻¹' r : Set SignWords) := Filter.Eventually.of_forall fun _ ↦ Iff.rfl
    rw [measure_congr (ae_eq_set_symmDiff he hre)]
    have h := measurableSet_of_prefixEvent hr
    rw [← Set.preimage_symmDiff, ← Measure.map_apply measurable_rudinShapiroObservations
      (ht.symmDiff h)]
    exact hClose

/-- The (L^2) indicator of a dyadic residue and a value of the central sign. -/
def rudinShapiroResidueSignLp (p : Ultrafilter ℕ) (k : ℕ) (a : Fin (2 ^ k)) (b : Bool) :
    Lp ℂ 2 (rudinShapiroOrbitLaw p : Measure SignWords) :=
  indicatorConstLp 2 ((measurableSet_rudinShapiroResidue k a).inter
    (measurable_pi_apply 0 (measurableSet_singleton b))) (measure_ne_top _ _) 1

private theorem indicatorConstLp_rudinShapiroPrefix_mem (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop)
    (W : Submodule ℂ (Lp ℂ 2 (rudinShapiroOrbitLaw p : Measure SignWords)))
    (hAtom : ∀ k a b, rudinShapiroResidueSignLp p k a b ∈ W)
    {s : Set SignWords} (hs : s ∈ rudinShapiroWordPrefixEvents) (hsm : MeasurableSet s) :
    indicatorConstLp 2 hsm (measure_ne_top _ _) (1 : ℂ) ∈ W := by
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  obtain ⟨t, ⟨k, hk⟩, rfl⟩ := hs
  let atom (ab : Fin (2 ^ k) × Bool) := {w : SignWords | rudinShapiroResidue k ab.1 w ∧ w 0 = ab.2}
  let I : Finset (Fin (2 ^ k) × Bool) := Finset.univ.filter fun ab ↦
    ∃ w ∈ rudinShapiroSubshift, w ∈ atom ab ∧ rudinShapiroObservations w ∈ t
  have ha (w : SignWords) (hw : w ∈ rudinShapiroSubshift) (ab : Fin (2 ^ k) × Bool) :
      w ∈ atom ab ↔ (rudinShapiroPhase k w, w 0) = ab := by
    change (rudinShapiroResidue k ab.1 w ∧ w 0 = ab.2) ↔ _
    rw [← rudinShapiroPhase_eq_iff hw, Prod.mk.injEq]
  have hI (w : SignWords) (hw : w ∈ rudinShapiroSubshift) :
      (rudinShapiroPhase k w, w 0) ∈ I ↔ rudinShapiroObservations w ∈ t := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, hab, ht⟩
      have hab' := (ha v hv _).mp hab
      have hpk : rudinShapiroPhase k v = rudinShapiroPhase k w := congrArg Prod.fst hab'
      have hsign : v 0 = w 0 := congrArg Prod.snd hab'
      exact (hk _ _ (fun j hj ↦ rudinShapiroPhase_eq_of_le hv hw hj hpk) hsign).mp ht
    · intro h
      exact ⟨w, hw, (ha w hw _).mpr rfl, h⟩
  have hcoe (ab : Fin (2 ^ k) × Bool) :
      (rudinShapiroResidueSignLp p k ab.1 ab.2 : SignWords → ℂ) =ᵐ[μ]
        (atom ab).indicator (fun _ ↦ 1) :=
    indicatorConstLp_coeFn
  have he : indicatorConstLp 2 hsm (measure_ne_top μ _) (1 : ℂ) =
      ∑ ab ∈ I, rudinShapiroResidueSignLp p k ab.1 ab.2 := by
    apply Lp.ext
    filter_upwards [ae_mem_rudinShapiroSubshift p hp, ae_all_iff.mpr hcoe,
      indicatorConstLp_coeFn (p := 2) (hs := hsm) (hμs := measure_ne_top μ _) (c := (1 : ℂ)),
      Lp.coeFn_fun_finsetSum I (fun ab ↦ rudinShapiroResidueSignLp p k ab.1 ab.2)]
      with w hw hAtoms hLeft hRight
    rw [hLeft, hRight]
    simp_rw [hAtoms]
    let ab := (rudinShapiroPhase k w, w 0)
    by_cases h : rudinShapiroObservations w ∈ t
    · rw [Set.indicator_of_mem (show w ∈ rudinShapiroObservations ⁻¹' t from h)]
      rw [Finset.sum_eq_single_of_mem ab ((hI w hw).mpr h)]
      · exact (Set.indicator_of_mem ((ha w hw ab).mpr rfl) (fun _ : SignWords ↦ (1 : ℂ))).symm
      · exact fun c _ hc ↦ Set.indicator_of_notMem
          (fun hc' ↦ hc ((ha w hw c).mp hc').symm) (fun _ : SignWords ↦ (1 : ℂ))
    · rw [Set.indicator_of_notMem (show w ∉ rudinShapiroObservations ⁻¹' t from h)]
      symm
      apply Finset.sum_eq_zero
      intro c hc
      exact Set.indicator_of_notMem
        (fun hc' ↦ h ((hI w hw).mp ((ha w hw c).mp hc' ▸ hc))) (fun _ : SignWords ↦ (1 : ℂ))
  rw [he]
  exact W.sum_mem fun ab _ ↦ hAtom k ab.1 ab.2

/-- The sign–residue atoms generate the entire Hilbert space. -/
theorem rudinShapiroResidueSign_closedSubmodule_eq_top (p : Ultrafilter ℕ)
    (hp : (p : Filter ℕ) ≤ atTop)
    (W : Submodule ℂ (Lp ℂ 2 (rudinShapiroOrbitLaw p : Measure SignWords)))
    (hW : IsClosed (W : Set (Lp ℂ 2 (rudinShapiroOrbitLaw p : Measure SignWords))))
    (hAtom : ∀ k a b, rudinShapiroResidueSignLp p k a b ∈ W) : W = ⊤ := by
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hDense := measureDense_rudinShapiroWordPrefixEvents p hp
  have hI {s : Set SignWords} (hs : MeasurableSet s) (c : ℂ) :
      indicatorConstLp 2 hs (measure_ne_top μ _) c ∈ W := by
    have hC := hDense.indicatorConstLp_subset_closure 2 c
    apply closure_minimal _ hW (hC ⟨s, hs, measure_ne_top μ _, rfl⟩)
    rintro - ⟨t, ht, hf, rfl⟩
    have h := indicatorConstLp_rudinShapiroPrefix_mem p hp W hAtom ht
      (hDense.measurable t ht)
    have he : indicatorConstLp 2 (hDense.measurable t ht) hf c =
        c • indicatorConstLp 2 (hDense.measurable t ht) hf (1 : ℂ) := by
      apply Lp.ext
      have he1 := indicatorConstLp_coeFn (p := 2) (hs := hDense.measurable t ht) (hμs := hf) (c := c)
      have he2 := indicatorConstLp_coeFn (p := 2) (hs := hDense.measurable t ht) (hμs := hf) (c := (1 : ℂ))
      filter_upwards [he1, he2, Lp.coeFn_smul c (indicatorConstLp 2 (hDense.measurable t ht) hf (1 : ℂ))]
        with x h1 h2 h3
      rw [h1, h3, Pi.smul_apply, h2]
      by_cases hx : x ∈ t <;> simp [hx]
    exact he.symm ▸ W.smul_mem c h
  apply top_unique
  intro f _
  have hDenseLp : DenseRange ((↑) : Lp.simpleFunc ℂ 2 μ → Lp ℂ 2 μ) :=
    Lp.simpleFunc.denseRange (by norm_num)
  refine hDenseLp.induction_on (p := fun g ↦ g ∈ W) f hW ?_
  intro f'
  refine Lp.simpleFunc.induction (P := fun g ↦ (g : Lp ℂ 2 μ) ∈ W)
    (by norm_num) (by norm_num) ?_ ?_ f'
  · intro c s hs hμs
    exact hI hs c
  · intro g h hg hh _ h₁ h₂
    exact W.add_mem h₁ h₂

end Mixing
