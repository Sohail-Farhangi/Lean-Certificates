/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreDelta

/-! # Injective sequence witnesses for products of free ultrafilters -/

public section

open Filter Set

namespace JdLG

section Fusion

variable {S I : Type*}

/-- Iterated eventual membership, in the order specified by the list of ultrafilters. -/
def EventuallyAlong (p : I → Ultrafilter S) : List I → (List S → Prop) → Prop
  | [], P => P []
  | i :: is, P => ∀ᶠ x in (p i : Filter S), EventuallyAlong p is (fun xs ↦ P (x :: xs))

private structure FusionStage (S I : Type*) where
  states : List (List I × List S)
  prior : List (I → S)

private def FusionGood (p : I → Ultrafilter S) (P : List S → Prop) (s : FusionStage S I) :=
  ∀ q ∈ s.states, EventuallyAlong p q.1 (fun xs ↦ P (q.2 ++ xs))

private def FusionCondition (p : I → Ultrafilter S) (P : List S → Prop)
    (i : I) (x : S) (q : List I × List S) : Prop :=
  match q.1 with
  | [] => True
  | j :: js => i = j → EventuallyAlong p js (fun xs ↦ P ((q.2 ++ [x]) ++ xs))

private theorem fusion_exists_next (p : I → Ultrafilter S) (hp : ∀ i, IsFreeUltrafilter (p i))
    (P : List S → Prop) (s : FusionStage S I) (hs : FusionGood p P s) :
    ∃ f : I → S, (∀ i, f i ∉ s.prior.map (· i)) ∧
      ∀ i, ∀ q ∈ s.states, FusionCondition p P i (f i) q := by
  classical
  have hex (i : I) : ∃ x : S, x ∉ s.prior.map (· i) ∧
      ∀ q ∈ s.states, FusionCondition p P i x q := by
    have hFree : ∀ᶠ x in (p i : Filter S), x ∉ s.prior.map (· i) := by
      apply hp i
      rw [mem_cofinite]
      convert (s.prior.map (· i)).toFinset.finite_toSet using 1
      ext x
      simp
    have hState : ∀ᶠ x in (p i : Filter S), ∀ q ∈ s.states, FusionCondition p P i x q := by
      simpa only [List.mem_toFinset] using (s.states.toFinset.eventually_all.mpr <| by
        intro q hq
        obtain ⟨left, pre⟩ := q
        cases left with
        | nil => exact Eventually.of_forall fun _ ↦ trivial
        | cons j js =>
          by_cases h : i = j
          · subst j
            have hGood := hs (i :: js, pre) (List.mem_toFinset.mp hq)
            change ∀ᶠ x in (p i : Filter S), EventuallyAlong p js (fun xs ↦ P (pre ++ x :: xs))
              at hGood
            exact hGood.mono fun x hx ↦ by simpa [FusionCondition, List.append_assoc] using hx
          · exact Eventually.of_forall fun _ h' ↦ False.elim (h h'))
    exact (hFree.and hState).exists
  choose f h using hex
  exact ⟨f, fun i ↦ (h i).1, fun i ↦ (h i).2⟩

private noncomputable def fusionNext (p : I → Ultrafilter S) (hp : ∀ i, IsFreeUltrafilter (p i))
    (P : List S → Prop) (s : FusionStage S I) (hs : FusionGood p P s) : I → S :=
  (fusion_exists_next p hp P s hs).choose

private def fusionAdvance (f : I → S) : List I × List S → Option (List I × List S)
  | ([], _) => none
  | (i :: is, pre) => some (is, pre ++ [f i])

private noncomputable def fusionStep (p : I → Ultrafilter S) (hp : ∀ i, IsFreeUltrafilter (p i))
    (P : List S → Prop) (s : {s : FusionStage S I // FusionGood p P s}) :
    {s : FusionStage S I // FusionGood p P s} := by
  let f := fusionNext p hp P s s.property
  refine ⟨⟨s.val.states ++ s.val.states.filterMap (fusionAdvance f), f :: s.val.prior⟩, ?_⟩
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact s.property q hq
  · obtain ⟨⟨left, pre⟩, hmem, hadvance⟩ := List.mem_filterMap.mp hq
    cases left with
    | nil => simp [fusionAdvance] at hadvance
    | cons i is =>
      have hq' : (is, pre ++ [f i]) = q := Option.some.inj hadvance
      subst q
      exact (fusion_exists_next p hp P s s.property).choose_spec.2 i (i :: is, pre) hmem rfl

/-- A finite string of iterated free-ultrafilter quantifiers yields injective sequence
witnesses whose selected indices are strictly increasing in the specified order. -/
theorem exists_injective_sequences_of_eventuallyAlong (p : I → Ultrafilter S)
    (hp : ∀ i, IsFreeUltrafilter (p i)) (P : List S → Prop) (labels : List I)
    (h : EventuallyAlong p labels P) :
    ∃ f : ℕ → I → S, (∀ i, Function.Injective (f · i)) ∧
      ∀ ns : List ℕ, ns.length = labels.length → ns.Pairwise (· < ·) →
        P (List.zipWith (fun i n ↦ f n i) labels ns) := by
  let start : {s : FusionStage S I // FusionGood p P s} := ⟨⟨[(labels, [])], []⟩, by
    intro q hq
    have hq' : q = (labels, []) := List.mem_singleton.mp hq
    subst q
    simpa only [List.nil_append] using h⟩
  let stage : ℕ → {s : FusionStage S I // FusionGood p P s} :=
    Nat.rec start fun _ s ↦ fusionStep p hp P s
  let f (n : ℕ) := fusionNext p hp P (stage n).val (stage n).property
  have hFresh (n : ℕ) (i : I) : f n i ∉ (stage n).val.prior.map (· i) :=
    (fusion_exists_next p hp P _ (stage n).property).choose_spec.1 i
  have hPrior (m n : ℕ) (hmn : m < n) : f m ∈ (stage n).val.prior := by
    induction n with
    | zero => omega
    | succ n ih =>
      change f m ∈ f n :: (stage n).val.prior
      by_cases hm : m = n
      · exact List.mem_cons.mpr (Or.inl (congrArg f hm))
      · exact List.mem_cons_of_mem _ (ih (by omega))
  have hMono {a b : ℕ} (h : a ≤ b) :
      ∀ q ∈ (stage a).val.states, q ∈ (stage b).val.states := by
    induction h with
    | refl => exact fun _ hq ↦ hq
    | @step b _ ih =>
      intro q hq
      exact List.mem_append_left _ (ih q hq)
  have hAdvance {n : ℕ} {i : I} {is : List I} {pre : List S}
      (hq : (i :: is, pre) ∈ (stage n).val.states) :
      (is, pre ++ [f n i]) ∈ (stage (n + 1)).val.states :=
    List.mem_append_right _ <| List.mem_filterMap.mpr ⟨(i :: is, pre), hq, rfl⟩
  refine ⟨f, fun i a b hab ↦ ?_, ?_⟩
  · rcases lt_trichotomy a b with hlt | heq | hgt
    · exfalso
      apply hFresh b i
      change f a i = f b i at hab
      rw [← hab]
      exact List.mem_map_of_mem (hPrior a b hlt)
    · exact heq
    · exfalso
      apply hFresh a i
      change f a i = f b i at hab
      rw [hab]
      exact List.mem_map_of_mem (hPrior b a hgt)
  · have hRun (is : List I) (ns : List ℕ) (n : ℕ) (pre : List S)
        (hq : (is, pre) ∈ (stage n).val.states) (hlen : ns.length = is.length)
        (hsorted : ns.Pairwise (· < ·)) (hmin : ∀ a ∈ ns, n ≤ a) :
        P (pre ++ List.zipWith (fun i n ↦ f n i) is ns) := by
      induction is generalizing ns n pre with
      | nil =>
        have hnil : ns = [] := List.length_eq_zero_iff.mp hlen
        subst ns
        exact (stage n).property ([], pre) hq
      | cons i is ih =>
        cases ns with
        | nil => simp at hlen
        | cons a as =>
          have hqa := hMono (hmin a (List.mem_cons_self ..)) _ hq
          have hnext := hAdvance hqa
          have hsort := List.pairwise_cons.mp hsorted
          have hres := ih as (a + 1) (pre ++ [f a i]) hnext (by simpa using hlen)
            hsort.2 (fun b hb ↦ Nat.succ_le_of_lt (hsort.1 b hb))
          simpa [List.append_assoc] using hres
    intro ns hlen hsorted
    simpa only [List.nil_append] using hRun labels ns 0 [] (by simp [stage, start])
      hlen hsorted (fun _ _ ↦ Nat.zero_le _)

end Fusion

section Delta

variable {S G : Type*} [Semigroup S] [Group G]

/-- Use each entry of a list twice consecutively, once for each member of a difference pair. -/
def pairLabels {I : Type*} : List I → List I
  | [] => []
  | i :: is => i :: i :: pairLabels is

@[simp] private theorem pairLabels_map {I J : Type*} (f : I → J) (is : List I) :
    pairLabels (is.map f) = (pairLabels is).map f := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [pairLabels, ih]

/-- The group product of adjacent differences in a list of source elements. -/
def differenceValues (ι : S →ₙ* G) : List S → G
  | a :: b :: cs => (ι a)⁻¹ * ι b * differenceValues ι cs
  | _ => 1

/-- The injective-sequence definition of a delta set, with the increasing index
constraints expressed by a pairwise strictly increasing list. -/
def IsDeltaSet (ι : S →ₙ* G) (ℓ : ℕ) (A : Set G) : Prop :=
  ∃ fs : List (ℕ → S), fs.length = ℓ ∧ (∀ f ∈ fs, Function.Injective f) ∧
    ∀ ns : List ℕ, ns.length = (pairLabels fs).length → ns.Pairwise (· < ·) →
      differenceValues ι (List.zipWith (fun f n ↦ f n) (pairLabels fs) ns) ∈ A

omit [Semigroup S] in
private theorem eventuallyAlong_mapped_hyperfilter_of_ordered_sequences {I : Type*}
    (f : I → ℕ → S) (P : List S → Prop) (labels : List I)
    (h : ∀ ns : List ℕ, ns.length = labels.length → ns.Pairwise (· < ·) →
      P (List.zipWith (fun i n ↦ f i n) labels ns)) :
    EventuallyAlong (fun i ↦ (hyperfilter ℕ).map (f i)) labels P := by
  have hMain (n : ℕ) (h' : ∀ ns : List ℕ, ns.length = labels.length → ns.Pairwise (· < ·) →
      (∀ j ∈ ns, n ≤ j) → P (List.zipWith (fun i k ↦ f i k) labels ns)) :
      EventuallyAlong (fun i ↦ (hyperfilter ℕ).map (f i)) labels P := by
    clear h
    induction labels generalizing n P with
    | nil => exact h' [] rfl List.Pairwise.nil (by simp)
    | cons i is ih =>
      change ∀ᶠ x in (((hyperfilter ℕ).map (f i) : Ultrafilter S) : Filter S),
        EventuallyAlong _ is (fun xs ↦ P (x :: xs))
      rw [Ultrafilter.coe_map, Filter.eventually_map]
      filter_upwards [Nat.hyperfilter_le_atTop (eventually_ge_atTop n)] with a ha
      apply ih (fun xs ↦ P (f i a :: xs)) (a + 1)
      intro ns hlen hsort hmin
      apply h' (a :: ns)
      · simp [hlen]
      · exact List.pairwise_cons.mpr ⟨fun b hb ↦ Nat.lt_of_succ_le (hmin b hb), hsort⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact ha.trans ((Nat.le_succ a).trans (hmin b hb))
  exact hMain 0 fun ns hn hs _ ↦ h ns hn hs

omit [Semigroup S] in
private theorem free_hyperfilter_map_of_injective {f : ℕ → S} (hf : Function.Injective f) :
    IsFreeUltrafilter ((hyperfilter ℕ).map f) := by
  intro A hA
  apply hyperfilter_le_cofinite
  rw [mem_cofinite] at hA ⊢
  exact hA.preimage hf.injOn

private theorem ultrafilterDifferenceProduct_mem_iff_eventuallyAlong {I : Type*}
    (ι : S →ₙ* G) (p : I → Ultrafilter S) (labels : List I) (A : Set G) :
    A ∈ ultrafilterDifferenceProduct ι (labels.map p) ↔
      EventuallyAlong p (pairLabels labels) (fun xs ↦ differenceValues ι xs ∈ A) := by
  induction labels generalizing A with
  | nil =>
    change A ∈ (pure (1 : G) : Ultrafilter G) ↔ (1 : G) ∈ A
    exact Ultrafilter.mem_pure
  | cons i is ih =>
    change (∀ᶠ g in (((ultrafilterInverse ((p i).map ι) * (p i).map ι) *
      ultrafilterDifferenceProduct ι (is.map p) : Ultrafilter G) : Filter G), g ∈ A) ↔ _
    rw [Ultrafilter.eventually_mul, Ultrafilter.eventually_mul]
    simp only [ultrafilterInverse, Ultrafilter.coe_map, Filter.eventually_map,
      pairLabels, EventuallyAlong, differenceValues]
    refine eventually_congr (Eventually.of_forall fun a ↦ ?_)
    refine eventually_congr (Eventually.of_forall fun b ↦ ?_)
    exact ih {c | (ι a)⁻¹ * ι b * c ∈ A}

/-- The sequence and ultrafilter characterizations of delta sets agree. The set
itself lives in the ambient group, and every sequence takes values in the source. -/
theorem isDeltaSet_iff_exists_ultrafilterDifferenceProduct (ι : S →ₙ* G)
    (ℓ : ℕ) (A : Set G) :
    IsDeltaSet ι ℓ A ↔
      ∃ ps : List (Ultrafilter S), ps.length = ℓ ∧ (∀ p ∈ ps, IsFreeUltrafilter p) ∧
        A ∈ ultrafilterDifferenceProduct ι ps := by
  constructor
  · rintro ⟨fs, hfs, hInj, hseq⟩
    let p (f : ℕ → S) := (hyperfilter ℕ).map f
    refine ⟨fs.map p, by simpa, ?_, ?_⟩
    · intro q hq
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
      exact free_hyperfilter_map_of_injective (hInj f hf)
    · exact (ultrafilterDifferenceProduct_mem_iff_eventuallyAlong ι p fs A).mpr
        (eventuallyAlong_mapped_hyperfilter_of_ordered_sequences id _ (pairLabels fs) hseq)
  · rintro ⟨ps, hps, hfree, hmem⟩
    let is := List.finRange ps.length
    let p (i : Fin ps.length) := ps[i]
    have hp : is.map p = ps := List.map_get_finRange ps
    have hNested : EventuallyAlong p (pairLabels is) (fun xs ↦ differenceValues ι xs ∈ A) :=
      (ultrafilterDifferenceProduct_mem_iff_eventuallyAlong ι p is A).mp (hp.symm ▸ hmem)
    obtain ⟨f, hinj, hf⟩ := exists_injective_sequences_of_eventuallyAlong p
      (fun i ↦ hfree _ (List.getElem_mem i.isLt)) (fun xs ↦ differenceValues ι xs ∈ A)
      (pairLabels is) hNested
    let fs := is.map (fun i n ↦ f n i)
    refine ⟨fs, ?_, ?_, ?_⟩
    · simpa [fs, is] using hps
    · intro g hg
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      exact hinj i
    · intro ns hlen hsort
      simp only [fs, pairLabels_map, List.length_map] at hlen
      simpa only [fs, pairLabels_map, List.zipWith_map_left, Function.comp_apply] using
        hf ns hlen hsort

/-- The ultrafilter difference-star test is equivalent to meeting every
injective-sequence difference set contained in the embedded semigroup. -/
theorem isDeltaStar_iff_inter_nonempty_of_isDeltaSet {ι : S →ₙ* G}
    (hι : Function.Injective ι) (ℓ : ℕ) (A : Set S) :
    IsDeltaStar ι ℓ A ↔
      ∀ B : Set S, IsDeltaSet ι ℓ (ι '' B) → (A ∩ B).Nonempty := by
  constructor
  · intro h B hB
    obtain ⟨ps, hlen, hfree, hmem⟩ :=
      (isDeltaSet_iff_exists_ultrafilterDifferenceProduct ι ℓ (ι '' B)).mp hB
    let p := ultrafilterDifferenceProduct ι ps
    have hRange : range ι ∈ p := mem_of_superset hmem (image_subset_range _ _)
    let r := p.comap hι hRange
    have hr : r.map ι = p := Ultrafilter.coe_injective (Filter.map_comap_of_mem hRange)
    have hAr : A ∈ r := h ps hlen hfree r hr
    have hBr : B ∈ r := by
      change ι '' B ∈ p at hmem
      rw [← hr] at hmem
      change ι ⁻¹' (ι '' B) ∈ r at hmem
      rwa [preimage_image_eq _ hι] at hmem
    exact Ultrafilter.nonempty_of_mem (inter_mem hAr hBr)
  · intro h ps hlen hfree r hr
    by_contra hNot
    have hC : Aᶜ ∈ r := Ultrafilter.compl_mem_iff_notMem.mpr hNot
    have hCr : ι '' Aᶜ ∈ r.map ι := by
      change ι ⁻¹' (ι '' Aᶜ) ∈ r
      rwa [preimage_image_eq _ hι]
    rw [hr] at hCr
    have hS := (isDeltaSet_iff_exists_ultrafilterDifferenceProduct ι ℓ (ι '' Aᶜ)).mpr
      ⟨ps, hlen, hfree, hCr⟩
    obtain ⟨x, hx, hxc⟩ := h Aᶜ hS
    exact hxc hx

open scoped Topology

/-- Theorem 5.3(iii) in the sequence formulation. Each norm return set of a
reversible vector meets every delta set given by a positive number of sequences. -/
theorem reversible_iff_norm_return_meets_all_isDeltaSet [Nonempty S]
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (hUnit : PreservesIdentityWhenPresent π)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) (n : ℕ) (x : E) :
    IsReversible (closureAction π) x ↔
      ∀ ε > (0 : ℝ), ∀ B : Set S, IsDeltaSet ι (n + 1) (ι '' B) →
        ({s | ‖x - π s x‖ < ε} ∩ B).Nonempty := by
  rw [reversible_iff_norm_return_isDeltaStar hπ hUnit hι n x]
  simp only [isDeltaStar_iff_inter_nonempty_of_isDeltaSet hι.1]

end Delta

end JdLG
