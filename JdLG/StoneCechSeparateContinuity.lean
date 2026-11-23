/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreCanonical
public import Mathlib.Algebra.FreeMonoid.Basic

/-! # Separate continuity can fail for Stone–Čech multiplication -/

@[expose] public section

open Filter Set
open scoped Topology

namespace JdLG

/-- The free monoid on countably many letters has no separately continuous
extension of its product to the space of ultrafilters. -/
theorem no_separatelyContinuous_ultrafilter_extension_freeMonoid :
    ¬ ∃ f : Ultrafilter (FreeMonoid ℕ) → Ultrafilter (FreeMonoid ℕ) →
        Ultrafilter (FreeMonoid ℕ),
      (∀ q, Continuous (f · q)) ∧ (∀ p, Continuous (f p)) ∧
      ∀ s t : FreeMonoid ℕ, f (pure s) (pure t) = pure (s * t) := by
  rintro ⟨f, hfR, hfL, hAgree⟩
  let u := hyperfilter ℕ
  let q := u.map FreeMonoid.of
  let A : Set (FreeMonoid ℕ) := {w | ∃ m n : ℕ, m < n ∧ w.toList = [m, n]}
  have hword (m n : ℕ) : FreeMonoid.of m * FreeMonoid.of n ∈ A ↔ m < n := by
    change (∃ a b : ℕ, a < b ∧ [m, n] = [a, b]) ↔ _
    simp
  have htail (m : ℕ) : ∀ᶠ n in (u : Filter ℕ), m < n :=
    (eventually_gt_atTop m).filter_mono Nat.hyperfilter_le_atTop
  have hmem : A ∈ q * q := by
    change ∀ᶠ w in ((q * q : Ultrafilter (FreeMonoid ℕ)) : Filter (FreeMonoid ℕ)), w ∈ A
    rw [Ultrafilter.eventually_mul]
    change ∀ᶠ m in (u : Filter ℕ), ∀ᶠ n in (u : Filter ℕ),
      FreeMonoid.of m * FreeMonoid.of n ∈ A
    exact Eventually.of_forall fun m ↦ (htail m).mono fun n hn ↦ (hword m n).2 hn
  have hnomem (n : ℕ) : A ∉ q * pure (FreeMonoid.of n) := by
    intro h
    change ∀ᶠ w in ((q * pure (FreeMonoid.of n) : Ultrafilter (FreeMonoid ℕ)) :
      Filter (FreeMonoid ℕ)), w ∈ A at h
    rw [Ultrafilter.eventually_mul] at h
    simp only [Ultrafilter.coe_pure, Filter.eventually_pure] at h
    change ∀ᶠ m in (u : Filter ℕ), FreeMonoid.of m * FreeMonoid.of n ∈ A at h
    obtain ⟨m, hmn, hnm⟩ := (h.and (htail n)).exists
    exact (hword m n).1 hmn |>.not_gt hnm
  have heq : f = (· * ·) := ultrafilter_mul_unique_of_principal_left_continuous f (· * ·)
    hfR Ultrafilter.continuous_mul_left (fun s ↦ hfL (pure s)) (fun s ↦ by
      simpa only [pure_mul_as_map] using continuous_ultrafilter_map (s * ·))
    (fun s t ↦ by rw [hAgree, pure_mul_as_map, Ultrafilter.map_pure])
  have hcont := hfL q
  rw [heq] at hcont
  have ht : Tendsto (fun n : ℕ ↦ pure (FreeMonoid.of n)) (u : Filter ℕ) (𝓝 q) :=
    q.tendsto_pure_self
  have hAt : ∀ᶠ n in (u : Filter ℕ), A ∈ q * pure (FreeMonoid.of n) :=
    ((hcont.tendsto q).comp ht).eventually
      ((ultrafilter_isOpen_basic A).mem_nhds hmem)
  obtain ⟨n, hn⟩ := hAt.exists
  exact hnomem n hn

section LeftTopological

variable {S : Type*} [Semigroup S]

/-- The left-topological Stone–Čech product, obtained by passing to the
opposite semigroup and reversing the order of multiplication. -/
noncomputable def leftTopologicalUltrafilterMul (p q : Ultrafilter S) : Ultrafilter S :=
  (q.map MulOpposite.op * p.map MulOpposite.op).map MulOpposite.unop

theorem leftTopologicalUltrafilterMul_assoc (p q r : Ultrafilter S) :
    leftTopologicalUltrafilterMul (leftTopologicalUltrafilterMul p q) r =
      leftTopologicalUltrafilterMul p (leftTopologicalUltrafilterMul q r) := by
  simp only [leftTopologicalUltrafilterMul, Ultrafilter.map_map, Function.comp_def,
    MulOpposite.op_unop, Ultrafilter.map_id', mul_assoc]

theorem leftTopologicalUltrafilterMul_continuous (p : Ultrafilter S) :
    Continuous (leftTopologicalUltrafilterMul p) :=
  (continuous_ultrafilter_map MulOpposite.unop).comp
    ((Ultrafilter.continuous_mul_left (p.map MulOpposite.op)).comp
      (continuous_ultrafilter_map MulOpposite.op))

@[simp]
theorem leftTopologicalUltrafilterMul_pure (s t : S) :
    leftTopologicalUltrafilterMul (pure s) (pure t) = pure (s * t) := by
  simp only [leftTopologicalUltrafilterMul, Ultrafilter.map_pure, pure_mul_as_map,
    MulOpposite.unop_mul, MulOpposite.unop_op]

end LeftTopological

end JdLG

