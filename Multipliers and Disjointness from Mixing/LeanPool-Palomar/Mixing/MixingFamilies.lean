/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.UltrafilterAction
public import Mixing.NormalOperator

/-!
# Equivalent families for mixing

Proposition 3 of arXiv:2604.12915v2.
-/

@[expose] public section

open Filter Set
open scoped Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (P : Set (Ultrafilter G))

/-- A string of `n+1` factors taken from the family. The recursion starts at one
because an ultrafilter semigroup has no need of an identity for this construction. -/
def ultrafilterProductsSucc (P : Set (Ultrafilter G)) : ℕ → Set (Ultrafilter G)
  | 0 => P
  | n + 1 => {r | ∃ p ∈ ultrafilterProductsSucc P n, ∃ q ∈ P, r = p * q}

/-- The family of all inverse–original pairs, written Δ in the paper. -/
def ultrafilterDelta : Set (Ultrafilter G) :=
  (fun p => inverseUltrafilter p * p) '' P

/-- The unsigned and inverse ultrafilters generate this semigroup. -/
def signedUltrafilterSemigroup : Subsemigroup (Ultrafilter G) :=
  Subsemigroup.closure (P ∪ inverseUltrafilter '' P)

/-- The closure of the set obtained by multiplying the signed semigroup on
both sides by arbitrary ultrafilters. -/
def closedSignedUltrafilterIdeal : Set (Ultrafilter G) :=
  closure {r | ∃ x y z : Ultrafilter G, y ∈ signedUltrafilterSemigroup P ∧ r = x * y * z}

theorem continuous_ultrafilterOperator_wot :
    Continuous (fun p : Ultrafilter G => ContinuousLinearMapWOT.ofCLM (ultrafilterOperator U p)) :=
  continuous_subtype_val.comp (continuous_ultrafilter_extend (weakClosureInclusion U))

theorem isClosed_ultrafilterOperator_eq_zero :
    IsClosed {p | ultrafilterOperator U p = 0} := by
  have h := isClosed_eq (continuous_ultrafilterOperator_wot U) continuous_const
    (g := fun _ => (0 : H →WOT[ℂ] H))
  simpa only [← ContinuousLinearMapWOT.ofCLM_zero,
    ContinuousLinearMapWOT.ofCLM_injective.eq_iff] using h

omit [CompleteSpace H] in
/-- Equation (6), the common kernel of a mixing family is all of the Hilbert space. -/
theorem isUMixing_iff_iInf_ker_eq_top :
    IsUMixing U P ↔ (⨅ p : P, (ultrafilterOperator U p).ker) = ⊤ := by
  rw [iInf_eq_top]
  constructor
  · intro h p
    rw [h p p.property]
    exact LinearMap.ker_zero
  · intro h p hp
    apply ContinuousLinearMap.ext
    intro x
    change x ∈ (ultrafilterOperator U p).ker
    rw [h ⟨p, hp⟩]
    exact Submodule.mem_top

theorem isUMixing_iff_signedUltrafilterSemigroup :
    IsUMixing U P ↔ IsUMixing U (signedUltrafilterSemigroup P) := by
  constructor
  · intro h p hp
    refine Subsemigroup.closure_induction (s := P ∪ inverseUltrafilter '' P)
      (p := fun q _ => ultrafilterOperator U q = 0) ?_ ?_ hp
    · rintro q (hq | ⟨r, hr, rfl⟩)
      · exact h q hq
      · rw [ultrafilterOperator_inverse, h r hr]
        simp
    · intro q r _ _ hq _
      rw [ultrafilterOperator_mul, hq, zero_mul]
  · intro h p hp
    exact h p (Subsemigroup.subset_closure (Or.inl hp))

theorem isUMixing_iff_closedSignedUltrafilterIdeal :
    IsUMixing U P ↔ IsUMixing U (closedSignedUltrafilterIdeal P) := by
  rw [isUMixing_iff_signedUltrafilterSemigroup U P]
  constructor
  · intro h
    apply closure_minimal _ (isClosed_ultrafilterOperator_eq_zero U)
    rintro r ⟨x, y, z, hy, rfl⟩
    change ultrafilterOperator U (x * y * z) = 0
    rw [ultrafilterOperator_mul, ultrafilterOperator_mul, h y hy, mul_zero, zero_mul]
  · intro h p hp
    have hp' : p ∈ closedSignedUltrafilterIdeal P := by
      apply subset_closure
      refine ⟨pure 1, p, pure 1, hp, ?_⟩
      apply Ultrafilter.coe_inj.mp
      ext s
      change (∀ᶠ g in (p : Filter G), g ∈ s) ↔
        ∀ᶠ g in ((pure 1 * p * pure 1 : Ultrafilter G) : Filter G), g ∈ s
      simp [Ultrafilter.eventually_mul]
    exact h p hp'

theorem isUMixing_iff_ultrafilterSemigroup :
    IsUMixing U P ↔ IsUMixing U (Subsemigroup.closure P : Set (Ultrafilter G)) := by
  constructor
  · intro h p hp
    exact (isUMixing_iff_signedUltrafilterSemigroup U P).mp h p
      (Subsemigroup.closure_mono (subset_union_left : P ⊆ P ∪ _) hp)
  · intro h p hp
    exact h p (Subsemigroup.subset_closure hp)

theorem IsUMixing.ultrafilterProductsSucc {U : G →* (H ≃ₗᵢ[ℂ] H)} {P : Set (Ultrafilter G)}
    (h : IsUMixing U P) (n : ℕ) : IsUMixing U (ultrafilterProductsSucc P n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rintro _ ⟨p, hp, q, _, rfl⟩
    rw [ultrafilterOperator_mul, ih p hp, zero_mul]

/-- Repeating the same factor in a nonempty product gives the corresponding positive
power of its ultrafilter operator. -/
theorem exists_ultrafilterProductsSucc_eq_pow {p : Ultrafilter G} (hp : p ∈ P) (n : ℕ) :
    ∃ q ∈ ultrafilterProductsSucc P n, ultrafilterOperator U q = (ultrafilterOperator U p) ^ (n + 1) := by
  induction n with
  | zero => exact ⟨p, hp, (pow_one _).symm⟩
  | succ n ih =>
    obtain ⟨q, hq, hEq⟩ := ih
    refine ⟨q * p, ⟨q, hq, p, hp, rfl⟩, ?_⟩
    rw [ultrafilterOperator_mul, hEq, ← pow_succ]

section Abelian

variable [IsMulCommutative G]

theorem isUMixing_iff_ultrafilterProductsSucc (n : ℕ) :
    IsUMixing U P ↔ IsUMixing U (ultrafilterProductsSucc P n) := by
  constructor
  · intro h
    exact h.ultrafilterProductsSucc n
  · intro h p hp
    obtain ⟨q, hq, hEq⟩ := exists_ultrafilterProductsSucc_eq_pow U P hp n
    have hpow := normal_ker_pow (ultrafilterOperator U p) (ultrafilterOperator_normal U p)
      (Nat.zero_lt_succ n)
    rw [← hEq, h q hq] at hpow
    apply ContinuousLinearMap.ext
    intro x
    change x ∈ (ultrafilterOperator U p).ker
    rw [← hpow]
    rfl

theorem isUMixing_iff_all_ultrafilterProducts :
    IsUMixing U P ↔ ∀ n : ℕ, 0 < n → IsUMixing U (ultrafilterProductsSucc P n) :=
  ⟨fun h n _ => h.ultrafilterProductsSucc n,
    fun h => (isUMixing_iff_ultrafilterProductsSucc U P 1).mpr (h 1 Nat.one_pos)⟩

theorem isUMixing_iff_some_ultrafilterProducts :
    IsUMixing U P ↔ ∃ n : ℕ, 0 < n ∧ IsUMixing U (ultrafilterProductsSucc P n) := by
  constructor
  · intro h
    exact ⟨1, Nat.one_pos, h.ultrafilterProductsSucc 1⟩
  · rintro ⟨n, _, hn⟩
    exact (isUMixing_iff_ultrafilterProductsSucc U P n).mpr hn

end Abelian

theorem isUMixing_iff_ultrafilterDelta :
    IsUMixing U P ↔ IsUMixing U (ultrafilterDelta P) := by
  constructor
  · rintro h _ ⟨p, hp, rfl⟩
    rw [ultrafilterOperator_mul, h p hp, mul_zero]
  · intro h p hp
    have h' := h _ ⟨p, hp, rfl⟩
    rw [ultrafilterOperator_mul, ultrafilterOperator_inverse] at h'
    have hker := ContinuousLinearMap.ker_adjoint_comp_self (ultrafilterOperator U p)
    change ((ultrafilterOperator U p).adjoint * ultrafilterOperator U p).ker = _ at hker
    rw [h'] at hker
    apply ContinuousLinearMap.ext
    intro x
    change x ∈ (ultrafilterOperator U p).ker
    rw [← hker]
    rfl

/-- Proposition 3. Each alternate family gives exactly the original mixing
condition. In the fourth and fifth equivalences, `n+1` is the actual length, so
`0 < n` means that the length is greater than one. -/
theorem proposition3 [IsMulCommutative G] :
    (IsUMixing U P ↔ IsUMixing U (closedSignedUltrafilterIdeal P)) ∧
    (IsUMixing U P ↔ IsUMixing U (signedUltrafilterSemigroup P)) ∧
    (IsUMixing U P ↔ IsUMixing U (Subsemigroup.closure P : Set (Ultrafilter G))) ∧
    (IsUMixing U P ↔ ∀ n : ℕ, 0 < n → IsUMixing U (ultrafilterProductsSucc P n)) ∧
    (IsUMixing U P ↔ ∃ n : ℕ, 0 < n ∧ IsUMixing U (ultrafilterProductsSucc P n)) ∧
    (IsUMixing U P ↔ IsUMixing U (ultrafilterDelta P)) :=
  ⟨isUMixing_iff_closedSignedUltrafilterIdeal U P, isUMixing_iff_signedUltrafilterSemigroup U P,
    isUMixing_iff_ultrafilterSemigroup U P, isUMixing_iff_all_ultrafilterProducts U P,
    isUMixing_iff_some_ultrafilterProducts U P, isUMixing_iff_ultrafilterDelta U P⟩

end Mixing
