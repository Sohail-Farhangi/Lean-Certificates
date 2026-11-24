/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mixing.SupportingJdLG.Core
public import Mixing.SupportingJdLG.Largeness
public import Mathlib.Combinatorics.Hindman

/-!
# Ultrafilter limits of semigroup homomorphisms

The compact semigroup extension used in Section 5 of Barthmann, Farhangi and
Kuznetsova, arXiv:2509.24003v3.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Mixing.JdLGBridge

/-- The Stone–Čech product of ultrafilters on a discrete semigroup. -/
scoped instance ultrafilterSemigroup {S : Type*} [Semigroup S] : Semigroup (Ultrafilter S) :=
  Ultrafilter.semigroup

/-- Evaluation of the Stone–Čech extension gives the ultrafilter limit. -/
theorem tendsto_ultrafilterExtend {S T : Type*} [TopologicalSpace T] [T2Space T]
    [CompactSpace T] (f : S → T) (p : Ultrafilter S) :
    Tendsto f (p : Filter S) (𝓝 (Ultrafilter.extend f p)) :=
  ultrafilter_extend_eq_iff.mp rfl

/-- The extension to ultrafilters of a homomorphism into a compact Hausdorff semitopological
semigroup is multiplicative. -/
theorem ultrafilterExtend_mul {S T : Type*} [Semigroup S] [Semigroup T] [TopologicalSpace T]
    [T2Space T] [CompactSpace T] (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T) (p q : Ultrafilter S) :
    Ultrafilter.extend f (p * q) = Ultrafilter.extend f p * Ultrafilter.extend f q := by
  apply ultrafilter_extend_eq_iff.mpr
  change Tendsto f ((p * q : Ultrafilter S) : Filter S) _
  rw [Filter.tendsto_def]
  intro neighborhood hNeighborhood
  obtain ⟨U, hSubset, hOpen, hProduct⟩ := mem_nhds_iff.mp hNeighborhood
  change ∀ᶠ s in ((p * q : Ultrafilter S) : Filter S), f s ∈ neighborhood
  rw [Ultrafilter.eventually_mul]
  have hOuter : ∀ᶠ x in (p : Filter S), f x * Ultrafilter.extend f q ∈ U :=
    (((continuousRight _).tendsto _).comp (tendsto_ultrafilterExtend f p)).eventually
      (hOpen.mem_nhds hProduct)
  filter_upwards [hOuter] with x hx
  have hInner : ∀ᶠ y in (q : Filter S), f x * f y ∈ U :=
    (((continuousLeft _).tendsto _).comp (tendsto_ultrafilterExtend f q)).eventually
      (hOpen.mem_nhds hx)
  filter_upwards [hInner] with y hy
  rw [map_mul]
  exact hSubset hy

/-- The Stone–Čech extension is onto a compact Hausdorff target if the original map has
dense range. -/
theorem surjective_ultrafilterExtend {S T : Type*} [TopologicalSpace T] [T2Space T]
    [CompactSpace T] (f : S → T) (hDense : DenseRange f) :
    Function.Surjective (Ultrafilter.extend f) := by
  have hClosed : IsClosed (range (Ultrafilter.extend f)) :=
    (isCompact_range (continuous_ultrafilter_extend f)).isClosed
  have hSubset : range f ⊆ range (Ultrafilter.extend f) := by
    rintro _ ⟨s, rfl⟩
    exact ⟨pure s, ultrafilter_extend_pure f s⟩
  exact fun x ↦ closure_minimal hSubset hClosed (hDense x)

/-- The compact semigroup limit map as a multiplicative homomorphism. -/
noncomputable def ultrafilterExtension {S T : Type*} [Semigroup S] [Semigroup T]
    [TopologicalSpace T] [T2Space T] [CompactSpace T]
    (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T) : Ultrafilter S →ₙ* T where
  toFun := Ultrafilter.extend f
  map_mul' := ultrafilterExtend_mul continuousLeft continuousRight f

section SmallestIdeal

variable {M : Type*} [Semigroup M]

/-- Stability of a set under arbitrary multiplication from either side. -/
def IsTwoSidedIdeal (I : Set M) : Prop :=
  LeftIdeal I ∧ ∀ ⦃a⦄, a ∈ I → ∀ b, a * b ∈ I

/-- The intersection of all nonempty two-sided ideals. In the compact Hausdorff setting of
Section 5 this is a nonempty two-sided ideal, as proved below. -/
def smallestIdeal (M : Type*) [Semigroup M] : Set M :=
  {a | ∀ I : Set M, I.Nonempty → IsTwoSidedIdeal I → a ∈ I}

/-- A point of the smallest ideal belongs to every nonempty two-sided ideal. -/
theorem smallestIdeal_subset {I : Set M} (hNonempty : I.Nonempty) (hIdeal : IsTwoSidedIdeal I) :
    smallestIdeal M ⊆ I := fun _ hx ↦ hx I hNonempty hIdeal

/-- The intersection defining the smallest ideal is stable under both multiplications. -/
theorem smallestIdeal_isTwoSidedIdeal : IsTwoSidedIdeal (smallestIdeal M) := by
  constructor
  · intro a b hb I hNonempty hIdeal
    exact hIdeal.1 a (hb I hNonempty hIdeal)
  · intro a ha b I hNonempty hIdeal
    exact hIdeal.2 (ha I hNonempty hIdeal) b

/-- Every minimal left ideal lies in the smallest two-sided ideal. -/
theorem minimalLeftIdeal_subset_smallestIdeal {L : Set M} (hL : MinimalLeftIdeal L) :
    L ⊆ smallestIdeal M := by
  intro x hx I hNonempty hIdeal
  obtain ⟨a, ha⟩ := hNonempty
  have hRange : range (· * (a * x)) = L :=
    principal_eq_of_minimalLeftIdeal hL (hL.2.1 a hx)
  have hxRange : x ∈ range (· * (a * x)) := hRange.symm ▸ hx
  obtain ⟨b, hb⟩ := hxRange
  exact hb ▸ hIdeal.1 b (hIdeal.2 ha x)

/-- The smallest two-sided ideal of a compact Hausdorff right topological semigroup
contains an idempotent. -/
theorem exists_idempotent_in_smallestIdeal [Nonempty M] [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (continuousRight : ∀ b : M, Continuous (· * b)) :
    ∃ p ∈ smallestIdeal M, p * p = p := by
  obtain ⟨L, hCompact, hL⟩ := exists_compact_minimalLeftIdeal continuousRight
  obtain ⟨p, hp, hIdempotent⟩ := exists_idempotent_in_compact_subsemigroup continuousRight
    L hL.1 hCompact fun a _ _ hb ↦ hL.2.1 a hb
  exact ⟨p, minimalLeftIdeal_subset_smallestIdeal hL hp, hIdempotent⟩

/-- Each point of the smallest two-sided ideal belongs to a compact minimal left ideal. -/
theorem exists_compact_minimalLeftIdeal_of_mem_smallestIdeal [Nonempty M] [TopologicalSpace M]
    [T2Space M] [CompactSpace M] (continuousRight : ∀ b : M, Continuous (· * b))
    {p : M} (hp : p ∈ smallestIdeal M) :
    ∃ L : Set M, IsCompact L ∧ MinimalLeftIdeal L ∧ p ∈ L := by
  obtain ⟨L, hCompact, hL⟩ := exists_compact_minimalLeftIdeal continuousRight
  let I : Set M := ⋃ t : M, (· * t) '' L
  obtain ⟨a, ha⟩ := hL.1
  have hNonempty : I.Nonempty := ⟨a * a, mem_iUnion.mpr ⟨a, ⟨a, ha, rfl⟩⟩⟩
  have hIdeal : IsTwoSidedIdeal I := by
    constructor
    · intro x y hy
      obtain ⟨t, a, ha, rfl⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨t, x * a, hL.2.1 x ha, mul_assoc x a t⟩
    · intro y hy x
      obtain ⟨t, a, ha, rfl⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨t * x, a, ha, (mul_assoc a t x).symm⟩
  obtain ⟨t, ht⟩ := mem_iUnion.mp (smallestIdeal_subset hNonempty hIdeal hp)
  exact ⟨(· * t) '' L, hCompact.image (continuousRight t), minimalLeftIdeal_image hL t, ht⟩

end SmallestIdeal

/-- There is a minimal idempotent ultrafilter on every nonempty discrete semigroup. -/
theorem exists_idempotent_ultrafilter_in_smallestIdeal {S : Type*} [Semigroup S] [Nonempty S] :
    ∃ p ∈ smallestIdeal (Ultrafilter S), p * p = p := by
  let : Nonempty (Ultrafilter S) := ⟨pure (Classical.choice ‹Nonempty S›)⟩
  exact exists_idempotent_in_smallestIdeal Ultrafilter.continuous_mul_left

section GroupIdeal

variable {S T : Type*} [Semigroup S] [Semigroup T] [TopologicalSpace T]
  [CompactSpace T] [T2Space T]

/-- A group ideal of a compact Hausdorff semigroup with continuous right translations
is closed, as it is the image of the entire semigroup under multiplication by the identity. -/
theorem GroupIdeal.isClosed_carrier (K : GroupIdeal T)
    (continuousRight : ∀ b : T, Continuous (· * b)) : IsClosed K.carrier := by
  have hRange : range (· * K.identity) = K.carrier := by
    ext x
    exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ K.mul_mem_left y K.identity_mem,
      fun hx ↦ ⟨x, K.mul_identity hx⟩⟩
  rw [← hRange]
  exact (isCompact_range (continuousRight K.identity)).isClosed

/-- The image of the closure of the smallest ideal of the Stone–Čech semigroup
is the group ideal of the target. -/
theorem GroupIdeal.ultrafilterExtend_mem_of_mem_closure_smallestIdeal
    (K : GroupIdeal T) (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T) (hDense : DenseRange f)
    {p : Ultrafilter S} (hp : p ∈ closure (smallestIdeal (Ultrafilter S))) :
    Ultrafilter.extend f p ∈ K.carrier := by
  let φ := ultrafilterExtension continuousLeft continuousRight f
  have hNonempty : (φ ⁻¹' K.carrier).Nonempty := by
    obtain ⟨q, hq⟩ := surjective_ultrafilterExtend f hDense K.identity
    refine ⟨q, ?_⟩
    change Ultrafilter.extend f q ∈ K.carrier
    rw [hq]
    exact K.identity_mem
  have hIdeal : IsTwoSidedIdeal (φ ⁻¹' K.carrier) := by
    constructor
    · intro a b hb
      change φ (a * b) ∈ K.carrier
      rw [map_mul]
      exact K.mul_mem_left _ hb
    · intro a ha b
      change φ (a * b) ∈ K.carrier
      rw [map_mul]
      exact K.mul_mem_right ha _
  exact closure_minimal (smallestIdeal_subset hNonempty hIdeal)
    ((K.isClosed_carrier continuousRight).preimage (continuous_ultrafilter_extend f)) hp

/-- Theorem 5.2(i) in the compact operator-semigroup formulation: an idempotent in
the closure of the smallest ideal converges to the identity of the group ideal. -/
theorem GroupIdeal.ultrafilterExtend_eq_identity_of_idempotent
    (K : GroupIdeal T) (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T) (hDense : DenseRange f)
    {p : Ultrafilter S} (hp : p ∈ closure (smallestIdeal (Ultrafilter S))) (hpp : p * p = p) :
    Ultrafilter.extend f p = K.identity := by
  apply K.eq_identity_of_idempotent
    (K.ultrafilterExtend_mem_of_mem_closure_smallestIdeal continuousLeft continuousRight f
      hDense hp)
  rw [← ultrafilterExtend_mul continuousLeft continuousRight f, hpp]

/-- The ultrafilter convergence statement in Theorem 5.2(i). -/
theorem GroupIdeal.tendsto_identity_of_idempotent
    (K : GroupIdeal T) (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T) (hDense : DenseRange f)
    {p : Ultrafilter S} (hp : p ∈ closure (smallestIdeal (Ultrafilter S))) (hpp : p * p = p) :
    Tendsto f (p : Filter S) (𝓝 K.identity) := by
  rw [← K.ultrafilterExtend_eq_identity_of_idempotent continuousLeft continuousRight f
    hDense hp hpp]
  exact tendsto_ultrafilterExtend f p

/-- The image of every idempotent ultrafilter under the compact group retraction is its
identity. This is the semigroup step in Lemma 5.1(i). -/
theorem GroupIdeal.groupRetraction_ultrafilterExtend_eq_one_of_idempotent
    (K : GroupIdeal T) (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T)
    {p : Ultrafilter S} (hp : p * p = p) :
    K.groupRetraction (Ultrafilter.extend f p) = 1 := by
  have h := congrArg K.groupRetraction
    ((ultrafilterExtend_mul continuousLeft continuousRight f p p).symm.trans
      (congrArg (Ultrafilter.extend f) hp))
  rw [map_mul] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

end GroupIdeal

section IP

variable {S : Type*} [Semigroup S]

/-- An IP set contains all nonempty ordered finite products of an infinite sequence. -/
def IsIP (A : Set S) : Prop := ∃ a : Stream' S, ∀ s, Hindman.FP a s → s ∈ A

/-- An IP-star set meets every IP set. -/
def IsIPStar (A : Set S) : Prop := ∀ B : Set S, IsIP B → (A ∩ B).Nonempty

/-- The idempotent-ultrafilter characterization of IP sets from Section 2.5.1. -/
theorem isIP_iff_exists_idempotent_mem {A : Set S} :
    IsIP A ↔ ∃ p : Ultrafilter S, p * p = p ∧ A ∈ p := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨p, hp, hProducts⟩ := Hindman.exists_idempotent_ultrafilter_le_FP a
    exact ⟨p, hp, hProducts.mono fun s hs ↦ ha s hs⟩
  · rintro ⟨p, hp, hA⟩
    exact Hindman.exists_FP_of_large p hp A hA

/-- The idempotent-ultrafilter characterization of IP-star sets from Section 2.5.1. -/
theorem isIPStar_iff_forall_idempotent_mem {A : Set S} :
    IsIPStar A ↔ ∀ p : Ultrafilter S, p * p = p → A ∈ p := by
  constructor
  · intro h p hp
    by_contra hA
    have hAc : Aᶜ ∈ p := Ultrafilter.compl_mem_iff_notMem.mpr hA
    obtain ⟨x, hx, hxc⟩ := h Aᶜ (isIP_iff_exists_idempotent_mem.mpr ⟨p, hp, hAc⟩)
    exact hxc hx
  · intro h B hB
    obtain ⟨p, hp, hBp⟩ := isIP_iff_exists_idempotent_mem.mp hB
    exact Ultrafilter.nonempty_of_mem (inter_mem (h p hp) hBp)

end IP

section Syndetic

variable {S : Type*} [Semigroup S]

private theorem mem_pure_mul_iff (s : S) (q : Ultrafilter S) (A : Set S) :
    A ∈ ((pure s : Ultrafilter S) * q) ↔ {t | s * t ∈ A} ∈ q := by
  change (∀ᶠ t in (((pure s : Ultrafilter S) * q) : Filter S), t ∈ A) ↔ _
  rw [Ultrafilter.eventually_mul]
  exact Ultrafilter.mem_pure

private theorem thick_iff_exists_ultrafilter {A : Set S} :
    IsThick A ↔ ∃ q : Ultrafilter S, ∀ a : S, {t | a * t ∈ A} ∈ q := by
  constructor
  · intro hThick
    classical
    let translate (a : S) : Set S := {t | a * t ∈ A}
    have hFinite (F : Finset (Set S)) (hF : (F : Set (Set S)) ⊆ range translate) :
        (⋂₀ (F : Set (Set S))).Nonempty := by
      have hPreimage (B : F) : ∃ a, translate a = B := hF B.2
      let select (B : F) : S := (hPreimage B).choose
      obtain ⟨x, hx⟩ := hThick (F.attach.image select)
      refine ⟨x, mem_sInter.mpr fun B hB ↦ ?_⟩
      have hSelect : select ⟨B, hB⟩ ∈ F.attach.image select :=
        Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
      have hMem : x ∈ translate (select ⟨B, hB⟩) := hx _ hSelect
      have hEq : translate (select ⟨B, hB⟩) = B := (hPreimage ⟨B, hB⟩).choose_spec
      rwa [hEq] at hMem
    obtain ⟨q, hq⟩ :=
      Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty (range translate) hFinite
    exact ⟨q, fun a ↦ hq (mem_range_self a)⟩
  · rintro ⟨q, hq⟩ F
    have h : ∀ᶠ x in (q : Filter S), ∀ a ∈ F, a * x ∈ A :=
      (eventually_all_finset F).mpr fun a _ ↦ hq a
    exact h.exists

/-- The finite-translate definition of piecewise syndeticity agrees with membership in
an ultrafilter in the smallest two-sided ideal. -/
theorem isPiecewiseSyndetic_iff_exists_mem_smallestIdeal [Nonempty S] {A : Set S} :
    IsPiecewiseSyndetic A ↔ ∃ p ∈ smallestIdeal (Ultrafilter S), A ∈ p := by
  constructor
  · rintro ⟨H, _, hThick⟩
    let B : Set S := {x | ∃ s ∈ H, s * x ∈ A}
    obtain ⟨q, hq⟩ := thick_iff_exists_ultrafilter.mp hThick
    obtain ⟨p, hp, _⟩ := exists_idempotent_ultrafilter_in_smallestIdeal (S := S)
    have hpq : p * q ∈ smallestIdeal (Ultrafilter S) := smallestIdeal_isTwoSidedIdeal.2 hp q
    have hB : ∀ᶠ t in ((p * q : Ultrafilter S) : Filter S), ∃ s ∈ H, s * t ∈ A := by
      change ∀ᶠ t in ((p * q : Ultrafilter S) : Filter S), t ∈ B
      rw [Ultrafilter.eventually_mul]
      exact Eventually.of_forall fun s ↦ hq s
    obtain ⟨s, _, hs⟩ := (Ultrafilter.eventually_exists_mem_iff H.finite_toSet).mp hB
    exact ⟨(pure s : Ultrafilter S) * (p * q), smallestIdeal_isTwoSidedIdeal.1 _ hpq,
      (mem_pure_mul_iff _ _ _).mpr hs⟩
  · rintro ⟨p, hp, hA⟩
    let : Nonempty (Ultrafilter S) := ⟨p⟩
    obtain ⟨L, hCompact, hL, hpL⟩ :=
      exists_compact_minimalLeftIdeal_of_mem_smallestIdeal Ultrafilter.continuous_mul_left hp
    let U (s : S) : Set (Ultrafilter S) := {q | {t | s * t ∈ A} ∈ q}
    have hCover : L ⊆ ⋃ s : S, U s := by
      intro q hq
      have hrange : range (· * q) = L := principal_eq_of_minimalLeftIdeal hL hq
      have hpRange : p ∈ range (· * q) := hrange.symm ▸ hpL
      obtain ⟨u, rfl⟩ := hpRange
      have hEventually : ∀ᶠ t in ((u * q : Ultrafilter S) : Filter S), t ∈ A := hA
      rw [Ultrafilter.eventually_mul] at hEventually
      obtain ⟨s, hs⟩ := hEventually.exists
      exact mem_iUnion.mpr ⟨s, hs⟩
    obtain ⟨H, hH⟩ := hCompact.elim_finite_subcover U
      (fun s ↦ ultrafilter_isOpen_basic {t | s * t ∈ A}) hCover
    have hWitness {q : Ultrafilter S} (hq : q ∈ L) :
        ∃ s ∈ H, {t | s * t ∈ A} ∈ q := by
      simpa only [mem_iUnion, U, mem_ofPred_eq, exists_prop] using hH hq
    obtain ⟨s, hs, _⟩ := hWitness hpL
    refine ⟨H, ⟨s, hs⟩, thick_iff_exists_ultrafilter.mpr ⟨p, fun a ↦ ?_⟩⟩
    obtain ⟨b, hb, hba⟩ := hWitness (hL.2.1 (pure a) hpL)
    have hBa : {t | b * (a * t) ∈ A} ∈ p := (mem_pure_mul_iff a p {t | b * t ∈ A}).mp hba
    exact mem_of_superset hBa fun _ h ↦ ⟨b, hb, h⟩

/-- A piecewise syndetic set belongs to an ultrafilter in the closure of the smallest
two-sided ideal, and conversely. -/
theorem isPiecewiseSyndetic_iff_exists_mem_closure_smallestIdeal [Nonempty S] {A : Set S} :
    IsPiecewiseSyndetic A ↔ ∃ p ∈ closure (smallestIdeal (Ultrafilter S)), A ∈ p := by
  rw [isPiecewiseSyndetic_iff_exists_mem_smallestIdeal]
  constructor
  · rintro ⟨p, hp, hA⟩
    exact ⟨p, subset_closure hp, hA⟩
  · rintro ⟨p, hp, hA⟩
    have hNeighborhood : {q : Ultrafilter S | A ∈ q} ∈ 𝓝 p :=
      (ultrafilter_isOpen_basic A).mem_nhds hA
    obtain ⟨q, hAq, hq⟩ := mem_closure_iff_nhds.mp hp _ hNeighborhood
    exact ⟨q, hq, hAq⟩

/-- The ultrafilter characterization of thickly syndetic sets from Section 2.5.1. -/
theorem isThicklySyndetic_iff_forall_mem_closure_smallestIdeal [Nonempty S] {A : Set S} :
    IsThicklySyndetic A ↔ ∀ p ∈ closure (smallestIdeal (Ultrafilter S)), A ∈ p := by
  constructor
  · intro h p hp
    by_contra hA
    have hAc : Aᶜ ∈ p := Ultrafilter.compl_mem_iff_notMem.mpr hA
    obtain ⟨x, hx, hxc⟩ := h Aᶜ
      (isPiecewiseSyndetic_iff_exists_mem_closure_smallestIdeal.mpr ⟨p, hp, hAc⟩)
    exact hxc hx
  · intro h B hB
    obtain ⟨p, hp, hBp⟩ := isPiecewiseSyndetic_iff_exists_mem_closure_smallestIdeal.mp hB
    exact Ultrafilter.nonempty_of_mem (inter_mem (h p hp) hBp)

end Syndetic

section ReturnTimes

variable {S T X : Type*} [Semigroup S] [Nonempty S] [Semigroup T] [TopologicalSpace T]
  [CompactSpace T] [T2Space T] [TopologicalSpace X] [T2Space X]

/-- The compact semigroup return-time argument from Theorem 5.3(ii). The point `z`
absorbs the entire group ideal if evaluation at its identity gives `z`. -/
theorem GroupIdeal.eval_identity_eq_iff_thicklySyndetic (K : GroupIdeal T)
    (continuousLeft : ∀ a : T, Continuous (a * ·))
    (continuousRight : ∀ b : T, Continuous (· * b)) (f : S →ₙ* T) (hDense : DenseRange f)
    (g : T → X) (hg : Continuous g) (z : X)
    (hAbsorb : g K.identity = z → ∀ a ∈ K.carrier, g a = z) :
    g K.identity = z ↔ ∀ U : Set X, IsOpen U → z ∈ U → IsThicklySyndetic {s | g (f s) ∈ U} := by
  constructor
  · intro hZero U hOpen hU
    apply isThicklySyndetic_iff_forall_mem_closure_smallestIdeal.mpr
    intro p hp
    have hLimit := (hg.tendsto _).comp (tendsto_ultrafilterExtend f p)
    have hValue : g (Ultrafilter.extend f p) = z := hAbsorb hZero _
      (K.ultrafilterExtend_mem_of_mem_closure_smallestIdeal continuousLeft continuousRight f
        hDense hp)
    rw [hValue] at hLimit
    exact hLimit.eventually (hOpen.mem_nhds hU)
  · intro hReturn
    obtain ⟨p, hp, hpp⟩ := exists_idempotent_ultrafilter_in_smallestIdeal (S := S)
    have hLimit := (hg.tendsto _).comp
      (K.tendsto_identity_of_idempotent continuousLeft continuousRight f
        hDense (subset_closure hp) hpp)
    have hLimit' : Tendsto (g ∘ f) (p : Filter S) (𝓝 z) := by
      rw [Filter.tendsto_def]
      intro U hU
      obtain ⟨V, hVU, hOpen, hz⟩ := mem_nhds_iff.mp hU
      have hVp := isThicklySyndetic_iff_forall_mem_closure_smallestIdeal.mp
        (hReturn V hOpen hz) p (subset_closure hp)
      exact mem_of_superset hVp fun _ h ↦ hVU h
    exact tendsto_nhds_unique hLimit hLimit'

end ReturnTimes

section WeakOperator

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparatingDual 𝕜 E]

/-- Theorem 5.2(i). For a JdLG-admissible representation of a discrete semigroup, an
idempotent in the closure of the smallest ideal converges in the weak operator topology to
the JdLG projection. Its range is the reversible part and its kernel is the almost weakly
stable part. -/
theorem ultrafilter_limit_eq_jdlg_projection {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) :
    ∃ e : weakOperatorClosure π, IsMinimalIdempotent e ∧
      (∀ p ∈ closure (smallestIdeal (Ultrafilter S)), p * p = p →
        Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (e : E →WOT[𝕜] E))) ∧
      (∀ x : E, IsReversible (closureAction π) x ↔
        x ∈ LinearMap.range (closureAction π e).toLinearMap) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        x ∈ LinearMap.ker (closureAction π e).toLinearMap := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  refine ⟨K.identity, K.isMinimalIdempotent_identity, ?_, K.reversible_iff_mem_range _,
    K.stable_iff_mem_ker _⟩
  intro p hp hpp
  exact (continuous_subtype_val.tendsto K.identity).comp
    (K.tendsto_identity_of_idempotent continuous_const_mul continuous_mul_const
      (closureInclusion π) (denseRange_closureInclusion π) hp hpp)

/-- Theorem 5.3(ii). An orbit returns to every weak neighborhood of zero on a thickly
syndetic set of times exactly when the vector is almost weakly stable. -/
theorem stable_iff_thicklySyndetic_weak_return [Nonempty S] {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      ∀ U : Set (WeakSpace 𝕜 E), IsOpen U → 0 ∈ U →
        IsThicklySyndetic {s | toWeakSpace 𝕜 E (π s x) ∈ U} := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  let g (A : weakOperatorClosure π) : WeakSpace 𝕜 E := toWeakSpace 𝕜 E (closureAction π A x)
  have hg : Continuous g := by
    refine WeakBilin.continuous_of_continuous_eval _ fun l ↦ ?_
    exact (ContinuousLinearMapWOT.continuous_dual_apply x l).comp continuous_subtype_val
  have hAbsorb (h : g K.identity = 0) (a : weakOperatorClosure π) (ha : a ∈ K.carrier) :
      g a = 0 := by
    have hx : closureAction π K.identity x = 0 :=
      (toWeakSpace 𝕜 E).injective <| by simpa [g] using h
    rw [← K.mul_identity ha]
    simp [g, map_mul, hx]
  have hReturn := K.eval_identity_eq_iff_thicklySyndetic continuous_const_mul continuous_mul_const
    (closureInclusion π) (denseRange_closureInclusion π)
    g hg 0 hAbsorb
  rw [K.stable_iff_projection_eq_zero (closureAction π) x]
  have hZero : K.projection (closureAction π) x = 0 ↔ g K.identity = 0 := by
    change closureAction π K.identity x = 0 ↔ toWeakSpace 𝕜 E (closureAction π K.identity x) = 0
    rw [← (toWeakSpace 𝕜 E).map_zero, (toWeakSpace 𝕜 E).injective.eq_iff]
  rw [hZero, hReturn]
  rfl

end WeakOperator

end Mixing.JdLGBridge
