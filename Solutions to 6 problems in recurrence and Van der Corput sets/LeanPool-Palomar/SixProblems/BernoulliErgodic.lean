/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.BernoulliThreshold
public import Mixing.ErgodicBarycenters
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section
noncomputable section

namespace SixProblems

open Set MeasureTheory Filter Mixing ProbabilityTheory
open scoped ENNReal ProbabilityTheory symmDiff

variable {G X K : Type*} [MeasurableSpace X] [MeasurableSpace K]

/-- Keep the base point and restrict the Bernoulli configuration to a finite set. -/
private def windowView (I : Finset G) (x : X × (G → K)) : X × (I → K) :=
  (x.1, I.restrict x.2)

private theorem measurable_windowView (I : Finset G) :
    Measurable (windowView (X := X) (K := K) I) :=
  measurable_fst.prodMk ((Finset.measurable_restrict I).comp measurable_snd)

private def windowEvents (X K G : Type*) [MeasurableSpace X] [MeasurableSpace K] :
    Set (Set (X × (G → K))) :=
  {A | ∃ I : Finset G, ∃ C : Set (X × (I → K)), MeasurableSet C ∧ windowView I ⁻¹' C = A}

private theorem windowEvents_measurable {A : Set (X × (G → K))}
    (hA : A ∈ windowEvents X K G) : MeasurableSet A := by
  obtain ⟨I, C, hC, rfl⟩ := hA
  exact hC.preimage (measurable_windowView I)

private theorem windowEvents_univ : (univ : Set (X × (G → K))) ∈ windowEvents X K G :=
  ⟨∅, univ, MeasurableSet.univ, preimage_univ⟩

private def windowShrink {I J : Finset G} (h : I ⊆ J) (x : X × (J → K)) : X × (I → K) :=
  (x.1, Finset.restrict₂ (π := fun _ : G ↦ K) h x.2)

private theorem measurable_windowShrink {I J : Finset G} (h : I ⊆ J) :
    Measurable (windowShrink (X := X) (K := K) h) :=
  measurable_fst.prodMk ((Finset.measurable_restrict₂ (X := fun _ : G ↦ K) h).comp measurable_snd)

private theorem windowEvents_isSetRing : IsSetRing (windowEvents X K G) where
  empty_mem := ⟨∅, ∅, MeasurableSet.empty, preimage_empty⟩
  union_mem := by
    classical
    rintro A B ⟨I, C, hC, rfl⟩ ⟨J, D, hD, rfl⟩
    refine ⟨I ∪ J, windowShrink Finset.subset_union_left ⁻¹' C ∪
      windowShrink Finset.subset_union_right ⁻¹' D,
      (hC.preimage (measurable_windowShrink _)).union (hD.preimage (measurable_windowShrink _)), ?_⟩
    rfl
  sdiff_mem := by
    classical
    rintro A B ⟨I, C, hC, rfl⟩ ⟨J, D, hD, rfl⟩
    refine ⟨I ∪ J, (windowShrink Finset.subset_union_left ⁻¹' C) \
      (windowShrink Finset.subset_union_right ⁻¹' D),
      (hC.preimage (measurable_windowShrink _)).diff (hD.preimage (measurable_windowShrink _)), ?_⟩
    rfl

private theorem windowEvents_generate :
    (inferInstance : MeasurableSpace (X × (G → K))) =
      MeasurableSpace.generateFrom (windowEvents X K G) := by
  let M := MeasurableSpace.generateFrom (windowEvents X K G)
  apply le_antisymm
  · classical
    have hfst : @Measurable (X × (G → K)) X M _ Prod.fst := by
      intro U hU
      exact MeasurableSpace.measurableSet_generateFrom ⟨∅, Prod.fst ⁻¹' U, measurable_fst hU, rfl⟩
    have hcoord (g : G) : @Measurable (X × (G → K)) K M _ (fun z ↦ z.2 g) := by
      intro U hU
      let i : ({g} : Finset G) := ⟨g, Finset.mem_singleton_self g⟩
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨{g}, (fun z : X × (({g} : Finset G) → K) ↦ z.2 i) ⁻¹' U,
          ((measurable_pi_apply i).comp measurable_snd) hU, rfl⟩
    have hsnd : @Measurable (X × (G → K)) (G → K) M _ Prod.snd :=
      measurable_pi_iff.mpr hcoord
    exact hfst.prodMk hsnd
  · exact MeasurableSpace.generateFrom_le fun _ hA ↦ windowEvents_measurable hA

variable (m : Measure K) [IsProbabilityMeasure m]

private abbrev configurationLaw : Measure (G → K) := Measure.infinitePi (fun _ : G ↦ m)

private theorem configurationLaw_iIndepFun :
    iIndepFun (fun g (t : G → K) ↦ t g) (configurationLaw m) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (fun g ↦ measurable_pi_apply g)).mpr
  simp_rw [(measurePreserving_eval_infinitePi (fun _ : G ↦ m) _).map_eq]
  exact Measure.map_id

private theorem window_measure_inter_cylinder (μ : Measure X) [IsProbabilityMeasure μ]
    (I J : Finset G) (hIJ : _root_.Disjoint I J)
    {C : Set (X × (I → K))} (hC : MeasurableSet C)
    {D : Set (J → K)} (hD : MeasurableSet D) :
    let law := configurationLaw (G := G) m
    (μ.prod law) (windowView I ⁻¹' C ∩ Prod.snd ⁻¹' (J.restrict ⁻¹' D)) =
      (μ.prod law) (windowView I ⁻¹' C) * law (J.restrict ⁻¹' D) := by
  intro law
  have hd' : MeasurableSet (Prod.snd ⁻¹' (J.restrict ⁻¹' D) : Set (X × (G → K))) :=
    measurable_snd (hD.preimage (Finset.measurable_restrict J))
  rw [Measure.prod_apply ((hC.preimage (measurable_windowView I)).inter hd'),
    Measure.prod_apply (hC.preimage (measurable_windowView I))]
  rw [← lintegral_mul_const' _ _ (measure_ne_top _ _)]
  apply lintegral_congr
  intro x
  change law (I.restrict ⁻¹' (Prod.mk x ⁻¹' C) ∩ J.restrict ⁻¹' D) =
    law (I.restrict ⁻¹' (Prod.mk x ⁻¹' C)) * law (J.restrict ⁻¹' D)
  exact ((configurationLaw_iIndepFun (G := G) m).indepFun_finset I J hIJ
    (fun g ↦ measurable_pi_apply g)).measure_inter_preimage_eq_mul _ _
    (hC.preimage (measurable_const.prodMk measurable_id)) hD

variable [Group G]

private theorem exists_shift_disjoint [Infinite G] [DecidableEq G] (I J : Finset G) :
    ∃ g : G, _root_.Disjoint I (J.image fun j ↦ j * g) := by
  classical
  let B := (J.product I).image fun p : G × G ↦ p.1⁻¹ * p.2
  obtain ⟨g, hg⟩ := Infinite.exists_notMem_finset B
  refine ⟨g, Finset.disjoint_left.mpr fun i hi hi' ↦ hg ?_⟩
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi'
  exact Finset.mem_image.mpr ⟨(j,j*g), Finset.mem_product.mpr ⟨hj,hi⟩,
    inv_mul_cancel_left j g⟩

set_option maxHeartbeats 800000 in
/-- An invariant event in the product has independent finite-coordinate
sections on the Bernoulli side, even after restriction to a base event. -/
private theorem invariant_measure_rect_cylinder [Infinite G] (S : System G X)
    (A : Set (X × (G → K))) (hA : MeasurableSet A)
    (hInv : ∀ g, (S.prod (bernoulliShift G m)).act g ⁻¹' A =ᵐ[(S.prod (bernoulliShift G m)).measure] A)
    {U : Set X} (hU : MeasurableSet U) (J : Finset G) {D : Set (J → K)} (hD : MeasurableSet D) :
    let law := configurationLaw (G := G) m
    let ν := S.measure.prod law
    let V : Set (G → K) := J.restrict ⁻¹' D
    ν (A ∩ (U ×ˢ V)) = ν (A ∩ (U ×ˢ univ)) * law V := by
  classical
  let T := S.prod (bernoulliShift G m)
  let law := configurationLaw (G := G) m
  let ν := T.measure
  let V : Set (G → K) := J.restrict ⁻¹' D
  let W := U ×ˢ V
  let W₀ := U ×ˢ (univ : Set (G → K))
  have hV : MeasurableSet V := hD.preimage (Finset.measurable_restrict J)
  have hW : MeasurableSet W := hU.prod hV
  have hW₀ : MeasurableSet W₀ := hU.prod MeasurableSet.univ
  change ν (A ∩ W) = ν (A ∩ W₀) * law V
  have ha : ν (A ∩ W) ≠ ∞ := measure_ne_top _ _
  have hb : ν (A ∩ W₀) * law V ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  suffices hre : (ν (A ∩ W)).toReal = (ν (A ∩ W₀) * law V).toReal from
    le_antisymm ((ENNReal.toReal_le_toReal ha hb).mp hre.le)
      ((ENNReal.toReal_le_toReal hb ha).mp hre.ge)
  rw [ENNReal.toReal_mul]
  suffices hc : ∀ ε : ℝ, 0 < ε → |ν.real (A ∩ W) - ν.real (A ∩ W₀) * law.real V| < ε by
    by_contra hne
    exact (lt_irrefl _) (hc _ (abs_pos.mpr (sub_ne_zero.mpr hne)))
  intro ε hε
  have hε₀ : 0 < ε / 3 := by positivity
  have hcover : ∃ D : Set (Set (X × (G → K))), D.Countable ∧ D ⊆ windowEvents X K G ∧
      ν (⋃₀ D)ᶜ = 0 := by
    exact ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr windowEvents_univ, by simp⟩
  obtain ⟨Cset, ⟨I,C,hC,rfl⟩, hclose⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ν)
      windowEvents_isSetRing hcover windowEvents_generate hA (ENNReal.ofReal_pos.mpr hε₀)
  let B := windowView I ⁻¹' C
  have hB := hC.preimage (measurable_windowView I)
  have hClose : ν.real (B ∆ A) < ε / 3 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hclose
    rwa [ENNReal.toReal_ofReal hε₀.le] at h
  obtain ⟨g,hg⟩ := exists_shift_disjoint I J
  let L := J.image fun j ↦ j*g
  let Wg := T.act g ⁻¹' W
  let W₀g := T.act g ⁻¹' W₀
  let r (t : L → K) (j : J) : K := t ⟨(j : G) * g, Finset.mem_image_of_mem _ j.property⟩
  let E := r ⁻¹' D
  have hr : Measurable r := Measurable.of_eval fun _ ↦ measurable_pi_apply _
  have hE : MeasurableSet E := hD.preimage hr
  let U' := S.act g ⁻¹' U
  let C' := C ∩ Prod.fst ⁻¹' U'
  have hC' : MeasurableSet C' := hC.inter (measurable_fst ((S.preserves g).measurable hU))
  have hVg : L.restrict ⁻¹' E = rightShift g ⁻¹' V := by rfl
  have hBg : B ∩ Wg = windowView I ⁻¹' C' ∩ Prod.snd ⁻¹' (L.restrict ⁻¹' E) := by
    ext x
    change x ∈ B ∧ ((S.act g x.1) ∈ U ∧ rightShift g x.2 ∈ V) ↔
      (x ∈ B ∧ S.act g x.1 ∈ U) ∧ rightShift g x.2 ∈ V
    exact and_assoc.symm
  have hB₀g : B ∩ W₀g = windowView I ⁻¹' C' := by
    ext x
    change x ∈ B ∧ (S.act g x.1 ∈ U ∧ rightShift g x.2 ∈ univ) ↔ x ∈ B ∧ S.act g x.1 ∈ U
    simp only [mem_univ, and_true]
  have hShiftV : law (L.restrict ⁻¹' E) = law V := by
    rw [hVg]
    exact (measurePreserving_rightShift m g).measure_preimage hV.nullMeasurableSet
  have hfactor : ν.real (B ∩ Wg) = ν.real (B ∩ W₀g) * law.real V := by
    have h := window_measure_inter_cylinder m S.measure I L hg hC' hE
    change ν _ = ν _ * law _ at h
    rw [← hBg, ← hB₀g, hShiftV] at h
    exact (congrArg ENNReal.toReal h).trans ENNReal.toReal_mul
  have hInvariant {F : Set (X × (G → K))} (hF : MeasurableSet F) :
      ν.real (A ∩ F) = ν.real (A ∩ T.act g ⁻¹' F) := by
    have hpres := (T.preserves g).measure_preimage (hA.inter hF).nullMeasurableSet
    have hd : T.act g ⁻¹' (A ∩ F) =ᵐ[ν] A ∩ T.act g ⁻¹' F := by
      filter_upwards [hInv g] with x hx
      change (T.act g x ∈ A ∧ T.act g x ∈ F) ↔ (x ∈ A ∧ T.act g x ∈ F)
      exact and_congr_left' hx
    exact congrArg ENNReal.toReal (hpres.symm.trans (measure_congr hd))
  have hdiff {F : Set (X × (G → K))} (hF : MeasurableSet F) :
      |ν.real (A ∩ F) - ν.real (B ∩ F)| ≤ ν.real (B ∆ A) := by
    have hsub : (A ∩ F) ∆ (B ∩ F) ⊆ B ∆ A := by
      intro x
      simp only [symmDiff_def, mem_union, Set.mem_sdiff, mem_inter_iff]
      tauto
    exact (abs_measureReal_sub_le_measureReal_symmDiff (μ := ν)
      (hA.inter hF).nullMeasurableSet (hB.inter hF).nullMeasurableSet).trans
      (measureReal_mono hsub (measure_ne_top ν _))
  have hν₁ := hdiff ((T.preserves g).measurable hW)
  have hν₂ := hdiff ((T.preserves g).measurable hW₀)
  have hlaw0 : 0 ≤ law.real V := ENNReal.toReal_nonneg
  have hlaw1 : law.real V ≤ 1 := (measureReal_mono (subset_univ _) (measure_ne_top _ _)).trans_eq (by simp)
  rw [hInvariant hW, hInvariant hW₀]
  change |ν.real (A ∩ Wg) - ν.real (A ∩ W₀g) * law.real V| < ε
  calc
    _ ≤ |ν.real (A ∩ Wg) - ν.real (B ∩ Wg)| +
        |ν.real (B ∩ Wg) - ν.real (A ∩ W₀g) * law.real V| := abs_sub_le _ _ _
    _ ≤ ν.real (B ∆ A) + ν.real (B ∆ A) := by
      refine add_le_add hν₁ ?_
      rw [hfactor, ← sub_mul, abs_mul, abs_of_nonneg hlaw0, abs_sub_comm]
      exact (mul_le_mul_of_nonneg_right hν₂ hlaw0).trans
        (mul_le_of_le_one_right ENNReal.toReal_nonneg hlaw1)
    _ < ε := by linarith

set_option maxHeartbeats 800000 in
/-- The product of an ergodic action with an infinite-group Bernoulli shift
is ergodic. This is the ergodicity clause of Proposition 2.1. -/
theorem bernoulli_prod_isErgodic [Infinite G] (S : System G X) (hS : S.IsErgodic) :
    (S.prod (bernoulliShift G m)).IsErgodic := by
  intro A hA hInv
  let T := S.prod (bernoulliShift G m)
  let law := configurationLaw (G := G) m
  let ν := T.measure
  let ρ := ν.restrict A
  let η := ρ.map Prod.fst
  have hρ₁ (g : G) : MeasurePreserving (T.act g) ρ ρ := by
    have h := (T.preserves g).restrict_preimage hA
    have hr : T.measure.restrict (T.act g ⁻¹' A) = ρ := Measure.restrict_congr_set (hInv g)
    rwa [hr] at h
  have hη₁ (g : G) : MeasurePreserving (S.act g) η η := by
    refine ⟨(S.preserves g).measurable, ?_⟩
    have hcomp : S.act g ∘ Prod.fst = Prod.fst ∘ T.act g := rfl
    change (ρ.map Prod.fst).map (S.act g) = η
    rw [Measure.map_map (S.preserves g).measurable measurable_fst, hcomp,
      ← Measure.map_map measurable_fst (hρ₁ g).measurable, (hρ₁ g).map_eq]
  have hη_le : η ≤ S.measure := by
    calc
      η ≤ ν.map Prod.fst := Measure.map_mono Measure.restrict_le_self measurable_fst
      _ = S.measure := by
        change (S.measure.prod law).map Prod.fst = S.measure
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hη_eq := S.eq_smul_of_invariant_absolutelyContinuous hS η hη₁ hη_le.absolutelyContinuous
  have hη_univ : η univ = ν A := by
    change ρ.map Prod.fst univ = _
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
  have hProd : ρ = η.prod law := by
    apply Measure.ext_prod
    intro U V hU hV
    let ξ := (ρ.restrict (Prod.fst ⁻¹' U)).map Prod.snd
    have hξ_apply {W : Set (G → K)} (hW : MeasurableSet W) : ξ W = ρ (U ×ˢ W) := by
      rw [Measure.map_apply measurable_snd hW, Measure.restrict_apply (measurable_snd hW)]
      congr 1
      exact inter_comm _ _
    have hρ_apply {W : Set (G → K)} (hW : MeasurableSet W) :
        ρ (U ×ˢ W) = ν (A ∩ (U ×ˢ W)) := by
      rw [Measure.restrict_apply (hU.prod hW), inter_comm]
    have hη_apply : η U = ν (A ∩ (U ×ˢ univ)) := by
      rw [Measure.map_apply measurable_fst hU, Measure.restrict_apply (measurable_fst hU), inter_comm]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
    have heq : ξ = η U • law := by
      let C := measurableCylinders (fun _ : G ↦ K)
      apply Measure.ext_of_generateFrom_of_iUnion C (fun _ ↦ univ)
        generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
        (by rw [iUnion_const]) (fun _ ↦ univ_mem_measurableCylinders _) (fun _ ↦ measure_ne_top _ _)
      intro W hW
      obtain ⟨J, D, hD, rfl⟩ := (mem_measurableCylinders W).mp hW
      have h := invariant_measure_rect_cylinder m S A hA hInv hU J hD
      change ξ (J.restrict ⁻¹' D) = (η U • law) (J.restrict ⁻¹' D)
      rw [hξ_apply (hD.preimage (Finset.measurable_restrict J)),
        hρ_apply (hD.preimage (Finset.measurable_restrict J)), smul_apply,
        smul_eq_mul, hη_apply]
      exact h
    rw [← hξ_apply hV, heq, Measure.prod_prod, smul_apply, smul_eq_mul]
  have hρ_eq : ρ = ν A • ν := by
    rw [hProd, hη_eq, hη_univ, Measure.prod_smul_left]
    rfl
  have hzero := congrArg (fun q : Measure (X × (G → K)) ↦ q Aᶜ) hρ_eq
  change (ν.restrict A) Aᶜ = (ν A • ν) Aᶜ at hzero
  rw [Measure.restrict_apply hA.compl, compl_inter_self, measure_empty, smul_apply,
    smul_eq_mul] at hzero
  change Filter.EventuallyEmptyOrUniv A (ae ν)
  apply eventuallyEmptyOrUniv_iff.mpr
  rcases mul_eq_zero.mp hzero.symm with h | h
  · exact Or.inr (by simpa [ae_iff] using h)
  · exact Or.inl (ae_iff.mpr h)

end SixProblems
