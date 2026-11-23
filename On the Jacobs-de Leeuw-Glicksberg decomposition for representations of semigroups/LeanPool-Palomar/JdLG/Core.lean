/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Semigroup

/-!
# The group ideal and the JdLG projection

The identity of the smallest group ideal determines the reversible and almost
weakly stable parts of every continuous linear action of the semigroup. We
also construct the group ideal from uniqueness of the minimal idempotent in
a compact Hausdorff semigroup with continuous right translations.
-/

@[expose] public section

namespace JdLG

/-- A two-sided ideal of a semigroup that is a group for the inherited multiplication. -/
structure GroupIdeal (S : Type*) [Semigroup S] where
  carrier : Set S
  identity : S
  identity_mem : identity ∈ carrier
  mul_mem_left : ∀ a : S, ∀ {b : S}, b ∈ carrier → a * b ∈ carrier
  mul_mem_right : ∀ {a : S}, a ∈ carrier → ∀ b : S, a * b ∈ carrier
  identity_mul : ∀ {a : S}, a ∈ carrier → identity * a = a
  mul_identity : ∀ {a : S}, a ∈ carrier → a * identity = a
  inverse_exists : ∀ {a : S}, a ∈ carrier →
    ∃ b ∈ carrier, b * a = identity ∧ a * b = identity

namespace GroupIdeal

variable {S : Type*} [Semigroup S] (K : GroupIdeal S)

instance : Nonempty K.carrier := ⟨⟨K.identity, K.identity_mem⟩⟩

noncomputable instance : Group K.carrier where
  mul a b := ⟨a.1 * b.1, K.mul_mem_right a.2 b.1⟩
  one := ⟨K.identity, K.identity_mem⟩
  inv a := ⟨(K.inverse_exists a.2).choose, (K.inverse_exists a.2).choose_spec.1⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (K.identity_mul a.2)
  mul_one a := Subtype.ext (K.mul_identity a.2)
  inv_mul_cancel a := Subtype.ext (K.inverse_exists a.2).choose_spec.2.1

@[simp] theorem coe_one : ((1 : K.carrier) : S) = K.identity := rfl

@[simp] theorem coe_mul (a b : K.carrier) : ((a * b : K.carrier) : S) = a.1 * b.1 := rfl

/-- The identity of the group ideal is an idempotent of the ambient semigroup. -/
theorem identity_idempotent : K.identity * K.identity = K.identity :=
  K.identity_mul K.identity_mem

/-- The identity of the group ideal commutes with every ambient element. -/
theorem identity_mul_eq_mul_identity (s : S) : K.identity * s = s * K.identity := by
  calc
    K.identity * s = (K.identity * s) * K.identity :=
      (K.mul_identity (K.mul_mem_right K.identity_mem s)).symm
    _ = K.identity * (s * K.identity) := mul_assoc _ _ _
    _ = s * K.identity := K.identity_mul (K.mul_mem_left s K.identity_mem)

/-- A group has just one idempotent. -/
theorem eq_identity_of_idempotent {a : S} (ha : a ∈ K.carrier) (haa : a * a = a) :
    a = K.identity := by
  obtain ⟨b, hb, hba, _⟩ := K.inverse_exists ha
  calc
    a = K.identity * a := (K.identity_mul ha).symm
    _ = (b * a) * a := by rw [hba]
    _ = b * a := by rw [mul_assoc, haa]
    _ = K.identity := hba

/-- A group ideal is contained in every nonempty two-sided ideal. -/
theorem subset_of_ideal {I : Set S} (hI : I.Nonempty)
    (hleft : ∀ s : S, ∀ {a : S}, a ∈ I → s * a ∈ I)
    (hright : ∀ {a : S}, a ∈ I → ∀ s : S, a * s ∈ I) : K.carrier ⊆ I := by
  obtain ⟨a, ha⟩ := hI
  obtain ⟨b, hb, hba, _⟩ := K.inverse_exists (K.mul_mem_left a K.identity_mem)
  have hidentity : K.identity ∈ I := hba ▸ hleft b (hright ha K.identity)
  intro x hx
  exact K.identity_mul hx ▸ hright hidentity x

/-- Projection onto the group ideal by multiplication by its identity. -/
noncomputable def groupRetraction : S →ₙ* K.carrier where
  toFun s := ⟨K.identity * s, K.mul_mem_right K.identity_mem s⟩
  map_mul' a b := Subtype.ext <| by
    change K.identity * (a * b) = (K.identity * a) * (K.identity * b)
    rw [← mul_assoc, ← mul_assoc (K.identity * a),
      K.mul_identity (K.mul_mem_right K.identity_mem a)]

theorem groupRetraction_surjective : Function.Surjective K.groupRetraction := fun a =>
  ⟨a.1, Subtype.ext (K.identity_mul a.2)⟩

/-- A surjective semigroup homomorphism sends a group ideal to a group ideal. -/
def map {T : Type*} [Semigroup T] (φ : S →ₙ* T) (hφ : Function.Surjective φ) : GroupIdeal T where
  carrier := φ '' K.carrier
  identity := φ K.identity
  identity_mem := ⟨K.identity, K.identity_mem, rfl⟩
  mul_mem_left := by
    rintro t _ ⟨b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := hφ t
    exact ⟨a * b, K.mul_mem_left a hb, φ.map_mul a b⟩
  mul_mem_right := by
    rintro _ ⟨a, ha, rfl⟩ t
    obtain ⟨b, rfl⟩ := hφ t
    exact ⟨a * b, K.mul_mem_right ha b, φ.map_mul a b⟩
  identity_mul := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, K.identity_mul ha]
  mul_identity := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, K.mul_identity ha]
  inverse_exists := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba, hab⟩ := K.inverse_exists ha
    exact ⟨φ b, ⟨b, hb, rfl⟩,
      by rw [← map_mul, hba], by rw [← map_mul, hab]⟩

end GroupIdeal

/-- Minimality in the usual order on idempotents, `f ≤ e` when `fe = ef = f`. -/
def IsMinimalIdempotent {S : Type*} [Semigroup S] (e : S) : Prop :=
  e * e = e ∧ ∀ f : S, f * f = f → f * e = f → e * f = f → f = e

theorem GroupIdeal.isMinimalIdempotent_identity {S : Type*} [Semigroup S] (K : GroupIdeal S) :
    IsMinimalIdempotent K.identity := by
  refine ⟨K.identity_idempotent, fun f hff hfe _ => ?_⟩
  apply K.eq_identity_of_idempotent _ hff
  exact hfe ▸ K.mul_mem_left f K.identity_mem

theorem GroupIdeal.eq_identity_of_isMinimalIdempotent {S : Type*} [Semigroup S]
    (K : GroupIdeal S) {f : S} (hf : IsMinimalIdempotent f) : f = K.identity := by
  have hff : (K.identity * f) * (K.identity * f) = K.identity * f := by
    have h := congrArg (fun a : K.carrier => (a : S)) (K.groupRetraction.map_mul f f)
    exact h.symm.trans (congrArg (K.identity * ·) hf.1)
  have hid : K.identity * f = K.identity :=
    K.eq_identity_of_idempotent (K.mul_mem_right K.identity_mem f) hff
  exact (hf.2 K.identity K.identity_idempotent hid
    ((K.identity_mul_eq_mul_identity f).symm.trans hid)).symm

section CompactSemigroup

variable {S : Type*} [Semigroup S]

/-- A subset stable under multiplication on the left by every ambient element. -/
def LeftIdeal (L : Set S) : Prop :=
  ∀ a : S, ∀ ⦃b : S⦄, b ∈ L → a * b ∈ L

/-- A nonempty left ideal that is minimal among nonempty left ideals. -/
def MinimalLeftIdeal (L : Set S) : Prop :=
  L.Nonempty ∧ LeftIdeal L ∧
    ∀ V : Set S, V.Nonempty → LeftIdeal V → V ⊆ L → V = L

theorem principal_leftIdeal (x : S) : LeftIdeal (Set.range (· * x)) := by
  intro a b hb
  obtain ⟨c, rfl⟩ := hb
  exact ⟨a * c, mul_assoc a c x⟩

theorem principal_eq_of_minimalLeftIdeal {L : Set S} (hL : MinimalLeftIdeal L)
    {x : S} (hx : x ∈ L) : Set.range (· * x) = L := by
  let : Nonempty S := ⟨x⟩
  apply hL.2.2 _ (Set.range_nonempty _) (principal_leftIdeal x)
  rintro _ ⟨y, rfl⟩
  exact hL.2.1 y hx

theorem minimalLeftIdeal_image {L : Set S} (hL : MinimalLeftIdeal L) (s : S) :
    MinimalLeftIdeal ((· * s) '' L) := by
  refine ⟨hL.1.image _, ?_, ?_⟩
  · intro a b hb
    obtain ⟨c, hc, rfl⟩ := hb
    exact ⟨a * c, hL.2.1 a hc, mul_assoc a c s⟩
  · intro V hV hVleft hVL
    let U : Set S := {x ∈ L | x * s ∈ V}
    have hU : U.Nonempty := by
      obtain ⟨v, hv⟩ := hV
      obtain ⟨x, hx, rfl⟩ := hVL hv
      exact ⟨x, hx, hv⟩
    have hUleft : LeftIdeal U := by
      intro a y hy
      exact ⟨hL.2.1 a hy.1, (mul_assoc a y s).symm ▸ hVleft a hy.2⟩
    have hUL : U = L := hL.2.2 U hU hUleft fun _ h => h.1
    refine le_antisymm hVL ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxU : x ∈ U := hUL.symm ▸ hx
    exact hxU.2

theorem exists_compact_minimalLeftIdeal [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [Nonempty S]
    (hcont : ∀ s : S, Continuous (· * s)) :
    ∃ L : Set S, IsCompact L ∧ MinimalLeftIdeal L := by
  let P : Set (Set S) := {L | IsClosed L ∧ L.Nonempty ∧ LeftIdeal L}
  have hmin : ∃ L, Minimal (· ∈ P) L := by
    refine zorn_superset _ fun C hCP hC => ?_
    refine ⟨⋂₀ C, ⟨isClosed_sInter fun L hL => (hCP hL).1, ?_, ?_⟩,
      fun L hL => Set.sInter_subset_of_mem hL⟩
    · obtain rfl | hCnonempty := C.eq_empty_or_nonempty
      · rw [Set.sInter_empty]
        exact Set.univ_nonempty
      convert
        @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ _ _ hCnonempty.coe_sort
          ((↑) : C → Set S) ?_ ?_ ?_ ?_
      · exact Set.sInter_eq_iInter
      · exact DirectedOn.directed_val (IsChain.directedOn hC.symm)
      · exact fun L => (hCP L.2).2.1
      · exact fun L => (hCP L.2).1.isCompact
      · exact fun L => (hCP L.2).1
    · exact fun a _ hb => Set.mem_sInter.mpr fun L hL =>
        (hCP hL).2.2 a (Set.mem_sInter.mp hb L hL)
  obtain ⟨L, hL⟩ := hmin
  refine ⟨L, hL.prop.1.isCompact, hL.prop.2.1, hL.prop.2.2, ?_⟩
  intro V hV hVleft hVL
  obtain ⟨v, hv⟩ := hV
  have hsubset : Set.range (· * v) ⊆ V := by
    rintro _ ⟨w, rfl⟩
    exact hVleft w hv
  have hEq : Set.range (· * v) = L := hL.eq_of_subset
    ⟨(isCompact_range (hcont v)).isClosed, Set.range_nonempty _, principal_leftIdeal v⟩
    (hsubset.trans hVL)
  exact le_antisymm hVL (hEq ▸ hsubset)

theorem isMinimalIdempotent_of_mem_minimalLeftIdeal {L : Set S}
    (hL : MinimalLeftIdeal L) {e : S} (he : e ∈ L) (heid : e * e = e) :
    IsMinimalIdempotent e := by
  refine ⟨heid, fun f hff hfe hef => ?_⟩
  have hf : f ∈ L := hfe ▸ hL.2.1 f he
  have he' : e ∈ Set.range (· * f) := (principal_eq_of_minimalLeftIdeal hL hf).symm ▸ he
  obtain ⟨a, ha⟩ := he'
  change a * f = e at ha
  calc
    f = e * f := hef.symm
    _ = (a * f) * f := by rw [ha]
    _ = a * f := by rw [mul_assoc, hff]
    _ = e := ha

variable [TopologicalSpace S] [T2Space S]

private theorem unique_idempotent_mem_minimalLeftIdeal {e : S}
    (hcont : ∀ s : S, Continuous (· * s))
    (heUnique : ∀ f : S, IsMinimalIdempotent f → f = e)
    {L : Set S} (hcompact : IsCompact L) (hL : MinimalLeftIdeal L) : e ∈ L := by
  obtain ⟨f, hf, hff⟩ := exists_idempotent_in_compact_subsemigroup hcont L hL.1 hcompact
    (fun a _ _ hb => hL.2.1 a hb)
  exact heUnique f (isMinimalIdempotent_of_mem_minimalLeftIdeal hL hf hff) ▸ hf

variable [CompactSpace S]

/-- In a compact Hausdorff semigroup with continuous right translations,
uniqueness of the minimal idempotent gives a compact group ideal. -/
theorem exists_compact_groupIdeal_of_existsUnique_minimalIdempotent
    (hcont : ∀ s : S, Continuous (· * s)) (h : ∃! e : S, IsMinimalIdempotent e) :
    ∃ K : GroupIdeal S, IsCompact K.carrier := by
  obtain ⟨e, he, heUnique⟩ := h
  let : Nonempty S := ⟨e⟩
  obtain ⟨L, hcompact, hL⟩ := exists_compact_minimalLeftIdeal hcont
  have heL := unique_idempotent_mem_minimalLeftIdeal hcont heUnique hcompact hL
  have hprincipal := principal_eq_of_minimalLeftIdeal hL heL
  have image_eq (s : S) : (· * s) '' L = L := by
    have hmin := minimalLeftIdeal_image hL s
    have he' := unique_idempotent_mem_minimalLeftIdeal hcont heUnique
      (hcompact.image (hcont s)) hmin
    exact (principal_eq_of_minimalLeftIdeal hmin he').symm.trans hprincipal
  have hrightId {a : S} (ha : a ∈ L) : a * e = a := by
    have ha' : a ∈ Set.range (· * e) := hprincipal.symm ▸ ha
    obtain ⟨x, rfl⟩ := ha'
    rw [mul_assoc, he.1]
  have inv_pair {a : S} (ha : a ∈ L) : ∃ b ∈ L, b * a = e ∧ a * b = e := by
    have he' : e ∈ (· * a) '' L := (image_eq a).symm ▸ heL
    obtain ⟨b, hb, hba⟩ := he'
    change b * a = e at hba
    refine ⟨b, hb, hba, heUnique _ (isMinimalIdempotent_of_mem_minimalLeftIdeal hL
      (hL.2.1 a hb) ?_)⟩
    rw [mul_assoc, ← mul_assoc b a b, hba, ← mul_assoc, hrightId ha]
  refine ⟨⟨L, e, heL, hL.2.1, ?_, ?_, @hrightId, @inv_pair⟩, hcompact⟩
  · intro a ha s
    exact image_eq s ▸ (show a * s ∈ (· * s) '' L from ⟨a, ha, rfl⟩)
  · intro a ha
    obtain ⟨b, _, hba, hab⟩ := inv_pair ha
    rw [← hab, mul_assoc, hba, hrightId ha]

/-- The minimal-idempotent criterion for a compact group ideal. -/
theorem exists_compact_groupIdeal_iff_existsUnique_minimalIdempotent
    (hcont : ∀ s : S, Continuous (· * s)) :
    (∃ K : GroupIdeal S, IsCompact K.carrier) ↔ ∃! e : S, IsMinimalIdempotent e := by
  refine ⟨?_, exists_compact_groupIdeal_of_existsUnique_minimalIdempotent hcont⟩
  rintro ⟨K, _⟩
  exact ⟨K.identity, K.isMinimalIdempotent_identity,
    fun _ h => K.eq_identity_of_isMinimalIdempotent h⟩

/-- A nonempty compact commutative semigroup has a unique minimal idempotent. -/
theorem existsUnique_minimalIdempotent_of_commutative [Nonempty S]
    (hcont : ∀ s : S, Continuous (· * s)) (hcomm : ∀ a b : S, a * b = b * a) :
    ∃! e : S, IsMinimalIdempotent e := by
  obtain ⟨L, hcompact, hL⟩ := exists_compact_minimalLeftIdeal hcont
  obtain ⟨e, he, hee⟩ := exists_idempotent_in_compact_subsemigroup hcont L hL.1 hcompact
    (fun a _ _ hb => hL.2.1 a hb)
  have hmin := isMinimalIdempotent_of_mem_minimalLeftIdeal hL he hee
  refine ⟨e, hmin, fun f hf => ?_⟩
  have hfe : (f * e) * e = f * e := by rw [mul_assoc, hee]
  have hef : (f * e) * f = f * e := by
    rw [mul_assoc, hcomm e f, ← mul_assoc, hf.1]
  have hff : (f * e) * (f * e) = f * e := by rw [← mul_assoc, hef, hfe]
  have hEqE := hmin.2 (f * e) hff hfe ((hcomm e (f * e)).trans hfe)
  have hEqF := hf.2 (f * e) hff hef ((hcomm f (f * e)).trans hef)
  exact hEqF.symm.trans hEqE

end CompactSemigroup

section Operators

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Equation (1), expressed for the semigroup acting by bounded operators. -/
def IsReversible (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  ∀ a : S, ∃ b : S, ρ b (ρ a x) = x

/-- Equation (1)'s almost weakly stable part, expressed using the operator closure. -/
def IsAlmostWeaklyStable (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  ∃ a : S, ρ a x = 0

variable (K : GroupIdeal S) (ρ : S →ₙ* (E →L[𝕜] E))

/-- The JdLG projection is the action of the group-ideal identity. -/
def GroupIdeal.projection : E →L[𝕜] E := ρ K.identity

theorem GroupIdeal.projection_apply_apply (x : E) : K.projection ρ (K.projection ρ x) =
    K.projection ρ x := by
  change (ρ K.identity * ρ K.identity) x = ρ K.identity x
  rw [← map_mul, K.identity_idempotent]

theorem GroupIdeal.projection_commutes (s : S) (x : E) :
    K.projection ρ (ρ s x) = ρ s (K.projection ρ x) := by
  change (ρ K.identity * ρ s) x = (ρ s * ρ K.identity) x
  rw [← map_mul, ← map_mul, K.identity_mul_eq_mul_identity]

theorem GroupIdeal.reversible_iff_fixed (x : E) :
    IsReversible ρ x ↔ K.projection ρ x = x := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h K.identity
    calc
      K.projection ρ x = K.projection ρ (ρ b (K.projection ρ x)) :=
        congrArg (K.projection ρ) hb.symm
      _ = ρ b (K.projection ρ (K.projection ρ x)) := K.projection_commutes ρ b _
      _ = x := by rw [K.projection_apply_apply]; exact hb
  · intro hx a
    obtain ⟨b, hb, hba, _⟩ := K.inverse_exists (K.mul_mem_right K.identity_mem a)
    refine ⟨b, ?_⟩
    change (ρ b * ρ a) x = x
    have hb' : b * a = K.identity := by rwa [← mul_assoc, K.mul_identity hb] at hba
    rw [← map_mul, hb']
    exact hx

theorem GroupIdeal.stable_iff_projection_eq_zero (x : E) :
    IsAlmostWeaklyStable ρ x ↔ K.projection ρ x = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, _, hba, _⟩ := K.inverse_exists (K.mul_mem_right K.identity_mem a)
    change ρ K.identity x = 0
    rw [← hba, map_mul, map_mul]
    change ρ b (ρ K.identity (ρ a x)) = 0
    simp [ha]
  · exact fun h => ⟨K.identity, h⟩

theorem GroupIdeal.projection_isIdempotentElem :
    IsIdempotentElem (K.projection ρ).toLinearMap := by
  change (K.projection ρ).toLinearMap * (K.projection ρ).toLinearMap =
    (K.projection ρ).toLinearMap
  ext x
  exact K.projection_apply_apply ρ x

/-- The reversible part is the image of the projection. -/
theorem GroupIdeal.reversible_iff_mem_range (x : E) :
    IsReversible ρ x ↔ x ∈ LinearMap.range (K.projection ρ).toLinearMap := by
  exact (K.reversible_iff_fixed ρ x).trans
    (LinearMap.IsIdempotentElem.mem_range_iff (K.projection_isIdempotentElem ρ)).symm

/-- The almost weakly stable part is the kernel of the projection. -/
theorem GroupIdeal.stable_iff_mem_ker (x : E) :
    IsAlmostWeaklyStable ρ x ↔ x ∈ LinearMap.ker (K.projection ρ).toLinearMap :=
  (K.stable_iff_projection_eq_zero ρ x).trans LinearMap.mem_ker.symm

/-- The reversible range and the almost weakly stable kernel are complementary. -/
theorem GroupIdeal.range_isCompl_ker :
    IsCompl (LinearMap.range (K.projection ρ).toLinearMap)
      (LinearMap.ker (K.projection ρ).toLinearMap) :=
  LinearMap.IsIdempotentElem.isCompl (K.projection_isIdempotentElem ρ)

/-- The reversible range is a closed subspace of the Banach space. -/
theorem GroupIdeal.isClosed_range_projection :
    IsClosed (LinearMap.range (K.projection ρ).toLinearMap : Set E) := by
  have hEq : (LinearMap.range (K.projection ρ).toLinearMap : Set E) =
      {x | K.projection ρ x = x} := by
    ext x
    exact LinearMap.IsIdempotentElem.mem_range_iff (K.projection_isIdempotentElem ρ)
  rw [hEq]
  exact isClosed_eq (K.projection ρ).continuous continuous_id

/-- The stable kernel is a closed subspace of the Banach space. -/
theorem GroupIdeal.isClosed_ker_projection :
    IsClosed (LinearMap.ker (K.projection ρ).toLinearMap : Set E) := by
  change IsClosed {x | K.projection ρ x = 0}
  exact isClosed_eq (K.projection ρ).continuous continuous_const

/-- The projection and its complementary projection give the two components of a vector. -/
theorem GroupIdeal.projection_splitting (x : E) :
    IsReversible ρ (K.projection ρ x) ∧
    IsAlmostWeaklyStable ρ (x - K.projection ρ x) ∧
    x = K.projection ρ x + (x - K.projection ρ x) := by
  refine ⟨(K.reversible_iff_fixed ρ _).mpr (K.projection_apply_apply ρ x), ?_, ?_⟩
  · apply (K.stable_iff_projection_eq_zero ρ _).mpr
    rw [map_sub, K.projection_apply_apply, sub_self]
  · rw [add_comm, sub_add_cancel]

/-- The projection intertwines under a quotient homomorphism on the acting semigroups. -/
theorem GroupIdeal.projection_intertwines {T F : Type*} [Semigroup T] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (φ : S →ₙ* T) (hφ : Function.Surjective φ)
    (τ : T →ₙ* (F →L[𝕜] F)) (f : E →L[𝕜] F)
    (hf : ∀ s x, τ (φ s) (f x) = f (ρ s x)) (x : E) :
    (K.map φ hφ).projection τ (f x) = f (K.projection ρ x) := hf K.identity x

/-- The range and kernel identities of Theorem 2.3(ii), given the induced surjective homomorphism
on the acting semigroups. -/
theorem GroupIdeal.projection_range_kernel_map {T F : Type*} [Semigroup T]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (φ : S →ₙ* T) (hφ : Function.Surjective φ)
    (τ : T →ₙ* (F →L[𝕜] F)) (f : E →L[𝕜] F) (hfSurj : Function.Surjective f)
    (hf : ∀ s x, τ (φ s) (f x) = f (ρ s x)) :
    (LinearMap.range (K.projection ρ).toLinearMap).map f.toLinearMap =
        LinearMap.range ((K.map φ hφ).projection τ).toLinearMap ∧
      (LinearMap.ker (K.projection ρ).toLinearMap).map f.toLinearMap =
        LinearMap.ker ((K.map φ hφ).projection τ).toLinearMap := by
  have hP := K.projection_intertwines ρ φ hφ τ f hf
  constructor
  · ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨f y, hP y⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hfSurj y
      exact ⟨K.projection ρ x, ⟨x, rfl⟩, (hP x).symm⟩
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (K.map φ hφ).projection τ (f x) = 0
      rw [hP, show K.projection ρ x = 0 from hx, map_zero]
    · intro hz
      obtain ⟨x, rfl⟩ := hfSurj z
      refine ⟨x - K.projection ρ x, ?_, ?_⟩
      · change K.projection ρ (x - K.projection ρ x) = 0
        rw [map_sub, K.projection_apply_apply, sub_self]
      · change f (x - K.projection ρ x) = f x
        rw [map_sub, ← hP, show (K.map φ hφ).projection τ (f x) = 0 from hz, sub_zero]

end Operators

section WeakOperator

variable {S 𝕜 E : Type*} [Semigroup S] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The given representation viewed in the weak operator topology. -/
def weakRepresentation (π : S →ₙ* (E →L[𝕜] E)) : S →ₙ* (E →WOT[𝕜] E) :=
  ContinuousLinearMapWOT.ringEquiv.symm.toMulHom.comp π

/-- The weak operator closure of the represented semigroup. -/
def weakOperatorClosure (π : S →ₙ* (E →L[𝕜] E)) : Subsemigroup (E →WOT[𝕜] E) :=
  (weakRepresentation π).srange.topologicalClosure

/-- The action of the operator closure, returning ordinary continuous linear maps. -/
def closureAction (π : S →ₙ* (E →L[𝕜] E)) : (weakOperatorClosure π) →ₙ* (E →L[𝕜] E) :=
  ContinuousLinearMapWOT.ringEquiv.toMulHom.comp (MulMemClass.subtype (weakOperatorClosure π))

/-- The original semigroup maps into its weak operator closure with dense image. -/
def closureInclusion (π : S →ₙ* (E →L[𝕜] E)) : S →ₙ* weakOperatorClosure π :=
  (weakRepresentation π).codRestrict (weakOperatorClosure π) fun s => subset_closure ⟨s, rfl⟩

@[simp] theorem closureAction_inclusion (π : S →ₙ* (E →L[𝕜] E)) (s : S) :
    closureAction π (closureInclusion π s) = π s := rfl

theorem denseRange_closureInclusion (π : S →ₙ* (E →L[𝕜] E)) :
    DenseRange (closureInclusion π) := by
  intro a
  rw [closure_subtype, ← Set.range_comp]
  exact a.2

/-- The paper's JdLG-admissibility condition on the weak operator closure. -/
def IsJdLGAdmissible (π : S →ₙ* (E →L[𝕜] E)) : Prop :=
  IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E)) ∧
    ∃! e : weakOperatorClosure π, IsMinimalIdempotent e

variable [SeparatingDual 𝕜 E]

/-- The weak operator closure of an admissible representation has a compact group ideal. -/
theorem exists_groupIdeal_of_admissible {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) :
    ∃ K : GroupIdeal (weakOperatorClosure π), IsCompact K.carrier := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  exact exists_compact_groupIdeal_of_existsUnique_minimalIdempotent
    continuous_mul_const hπ.2

/-- Almost weak stability means that zero belongs to the weak closure of the original orbit. -/
theorem stable_iff_zero_mem_weakOrbitClosure {π : S →ₙ* (E →L[𝕜] E)}
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E))) (x : E) :
    IsAlmostWeaklyStable (closureAction π) x ↔
      (0 : WeakSpace 𝕜 E) ∈ closure (Set.range fun s : S => toWeakSpace 𝕜 E (π s x)) := by
  let evaluation : (E →WOT[𝕜] E) → WeakSpace 𝕜 E := fun a => toWeakSpace 𝕜 E (a x)
  have hEval : Continuous evaluation := WeakBilin.continuous_of_continuous_eval _
    fun y => ContinuousLinearMapWOT.continuous_dual_apply x y
  have hImage : evaluation '' (weakOperatorClosure π : Set (E →WOT[𝕜] E)) =
      closure (Set.range fun s : S => toWeakSpace 𝕜 E (π s x)) := by
    apply le_antisymm
    · have hEvalRange : evaluation '' Set.range (weakRepresentation π) =
          Set.range (fun s : S => toWeakSpace 𝕜 E (π s x)) := by
        rw [← Set.range_comp]
        rfl
      change evaluation '' closure (Set.range (weakRepresentation π)) ⊆ _
      rw [← hEvalRange]
      exact image_closure_subset_closure_image hEval
    · apply closure_minimal _ (hcompact.image hEval).isClosed
      rintro _ ⟨s, rfl⟩
      exact ⟨weakRepresentation π s, (closureInclusion π s).2, rfl⟩
  rw [← hImage]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.1, a.2, (congrArg (toWeakSpace 𝕜 E) ha).trans (map_zero _)⟩
  · rintro ⟨a, ha, hz⟩
    exact ⟨⟨a, ha⟩, (toWeakSpace 𝕜 E).injective (hz.trans (map_zero _).symm)⟩

/-- The commutative case of Theorem 1.2(i). Weak compactness of the operator closure suffices. -/
theorem admissible_of_commutative [Nonempty S] {π : S →ₙ* (E →L[𝕜] E)}
    (hcompact : IsCompact (weakOperatorClosure π : Set (E →WOT[𝕜] E)))
    (hcomm : ∀ a b : S, π a * π b = π b * π a) : IsJdLGAdmissible π := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hcompact
  let : Nonempty (weakOperatorClosure π) := ⟨⟨weakRepresentation π (Classical.arbitrary S),
    subset_closure ⟨Classical.arbitrary S, rfl⟩⟩⟩
  have : IsMulCommutative (weakRepresentation π).srange := by
    apply IsMulCommutative.of_setLike_mul_comm
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    apply ContinuousLinearMapWOT.ringEquiv.injective
    rw [map_mul, map_mul]
    exact hcomm a b
  let : IsMulCommutative (weakOperatorClosure π) := inferInstanceAs
    (IsMulCommutative (weakRepresentation π).srange.topologicalClosure)
  exact ⟨hcompact, existsUnique_minimalIdempotent_of_commutative continuous_mul_const
    (fun a b => mul_comm' a b)⟩

/-- The JdLG decomposition for a relatively weakly compact, admissible representation.
The projection belongs to the weak operator closure, commutes with that closure,
and identifies the two spaces of equation (1) as its range and kernel. -/
theorem decomposition_of_admissible {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π) :
    ∃ e : weakOperatorClosure π,
      IsMinimalIdempotent e ∧
      (∀ a : weakOperatorClosure π, e * a = a * e) ∧
      IsCompl (LinearMap.range (closureAction π e).toLinearMap)
        (LinearMap.ker (closureAction π e).toLinearMap) ∧
      (∀ x : E, IsReversible (closureAction π) x ↔
        x ∈ LinearMap.range (closureAction π e).toLinearMap) ∧
      ∀ x : E, IsAlmostWeaklyStable (closureAction π) x ↔
        x ∈ LinearMap.ker (closureAction π e).toLinearMap := by
  obtain ⟨K, _⟩ := exists_groupIdeal_of_admissible hπ
  exact ⟨K.identity, K.isMinimalIdempotent_identity, K.identity_mul_eq_mul_identity,
    K.range_isCompl_ker _, K.reversible_iff_mem_range _, K.stable_iff_mem_ker _⟩


end WeakOperator

end JdLG
