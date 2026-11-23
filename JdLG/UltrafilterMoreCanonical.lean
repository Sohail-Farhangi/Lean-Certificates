/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreDelta
public import Mathlib.Algebra.Group.TypeTags.Basic

/-! # Uniqueness of the Stone–Čech multiplication

Continuity of right translations and of left translations by principal ultrafilters
implies uniqueness. On the nonnegative integers, dropping the latter condition
allows another right-topological extension.
-/

public section

open Filter Set

namespace JdLG

/-- Two extensions of an operation on principal ultrafilters coincide if both
are continuous in the left argument and continuous in the right argument
whenever the left argument is principal. -/
theorem ultrafilter_mul_unique_of_principal_left_continuous {S : Type*}
    (f g : Ultrafilter S → Ultrafilter S → Ultrafilter S)
    (hfRight : ∀ q, Continuous (f · q)) (hgRight : ∀ q, Continuous (g · q))
    (hfLeft : ∀ s : S, Continuous (f (pure s))) (hgLeft : ∀ s : S, Continuous (g (pure s)))
    (hAgree : ∀ s t : S, f (pure s) (pure t) = g (pure s) (pure t)) : f = g := by
  have hLeft (s : S) : f (pure s) = g (pure s) :=
    (hfLeft s).ext_on denseRange_pure (hgLeft s) (by rintro _ ⟨t, rfl⟩; exact hAgree s t)
  funext p q
  have hRight : (f · q) = (g · q) :=
    (hfRight q).ext_on denseRange_pure (hgRight q) (by
      rintro _ ⟨s, rfl⟩
      exact congrFun (hLeft s) q)
  exact congrFun hRight p

/-- A multiplicative map with dense range into a compact Hausdorff
semitopological semigroup extends to a unique continuous surjective homomorphism. -/
theorem existsUnique_continuous_surjective_ultrafilterLift {S T : Type*} [Semigroup S] [Semigroup T]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [SeparatelyContinuousMul T]
    (i : S →ₙ* T) (hi : DenseRange i) :
    ∃! h : Ultrafilter S →ₙ* T, Continuous h ∧ Function.Surjective h ∧
      ∀ s : S, h (pure s) = i s := by
  let h := ultrafilterExtension continuous_const_mul continuous_mul_const i
  have hh : Continuous h := continuous_ultrafilter_extend i
  have hp (s : S) : h (pure s) = i s := ultrafilter_extend_pure _ _
  have hs : Function.Surjective h := surjective_ultrafilterExtend i hi
  refine ⟨h, ⟨hh, hs, hp⟩, ?_⟩
  rintro F ⟨hF, _, hFp⟩
  apply DFunLike.ext'
  exact hF.ext_on denseRange_pure hh (by rintro _ ⟨s, rfl⟩; exact (hFp s).trans (hp s).symm)

section Counterexample

local notation "B" => Ultrafilter (Multiplicative ℕ)

private theorem nat_free_mul_principal {p : B} (hp : IsFreeUltrafilter p) (s : Multiplicative ℕ) :
    IsFreeUltrafilter (p * pure s) := by
  intro A hA
  change ∀ᶠ x in ((p * pure s : B) : Filter (Multiplicative ℕ)), x ∈ A
  rw [Ultrafilter.eventually_mul]
  simp only [Ultrafilter.coe_pure, Filter.eventually_pure]
  apply hp
  rw [mem_cofinite] at hA ⊢
  exact hA.preimage (mul_left_injective s).injOn

private theorem nat_not_principal_of_free {p : B} (hp : IsFreeUltrafilter p) :
    ¬ ∃ s : Multiplicative ℕ, p = pure s := by
  rintro ⟨s, rfl⟩
  have h := hp (finite_singleton s).compl_mem_cofinite
  change {s}ᶜ ∈ (pure s : B) at h
  exact (Ultrafilter.mem_pure.mp h) (mem_singleton s)

/-- A different multiplication on the Stone–Čech space of the nonnegative integers. -/
noncomputable def rightTopologicalAlternativeNat (p q : B) : B := by
  classical
  exact if ∃ s : Multiplicative ℕ, q = pure s then p * q else q

private theorem alt_of_principal (p : B) {q : B} (h : ∃ s : Multiplicative ℕ, q = pure s) :
    rightTopologicalAlternativeNat p q = p * q := by
  simp [rightTopologicalAlternativeNat, h]

private theorem alt_of_nonprincipal (p : B) {q : B} (h : ¬ ∃ s : Multiplicative ℕ, q = pure s) :
    rightTopologicalAlternativeNat p q = q := by
  simp [rightTopologicalAlternativeNat, h]

theorem rightTopologicalAlternativeNat_assoc (p q r : B) :
    rightTopologicalAlternativeNat (rightTopologicalAlternativeNat p q) r =
      rightTopologicalAlternativeNat p (rightTopologicalAlternativeNat q r) := by
  classical
  by_cases hr : ∃ s : Multiplicative ℕ, r = pure s
  · obtain ⟨s, rfl⟩ := hr
    have hr' : ∃ t : Multiplicative ℕ, (pure s : B) = pure t := ⟨s, rfl⟩
    simp only [alt_of_principal _ hr']
    by_cases hq : ∃ t : Multiplicative ℕ, q = pure t
    · obtain ⟨t, rfl⟩ := hq
      have hmul : (pure t : B) * pure s = pure (t * s) := by
        rw [pure_mul_as_map, Ultrafilter.map_pure]
      have hq' : ∃ u : Multiplicative ℕ, (pure t : B) = pure u := ⟨t, rfl⟩
      have hqr : ∃ u : Multiplicative ℕ, (pure t : B) * pure s = pure u := ⟨t * s, hmul⟩
      rw [alt_of_principal _ hq', alt_of_principal _ hqr, mul_assoc]
    · have hqFree : IsFreeUltrafilter q := by
        rcases q.le_cofinite_or_eq_pure with h | h
        · exact h
        · exact False.elim (hq h)
      rw [alt_of_nonprincipal _ hq,
        alt_of_nonprincipal _ (nat_not_principal_of_free (nat_free_mul_principal hqFree s))]
  · simp only [alt_of_nonprincipal _ hr]

theorem rightTopologicalAlternativeNat_continuous_right (q : B) :
    Continuous (rightTopologicalAlternativeNat · q) := by
  classical
  by_cases hq : ∃ s : Multiplicative ℕ, q = pure s
  · simpa only [alt_of_principal _ hq] using Ultrafilter.continuous_mul_left q
  · simpa only [alt_of_nonprincipal _ hq] using
      (continuous_const : Continuous (fun _ : B ↦ q))

theorem rightTopologicalAlternativeNat_agree (s t : Multiplicative ℕ) :
    rightTopologicalAlternativeNat (pure s) (pure t) = pure (s * t) := by
  rw [alt_of_principal _ (show ∃ u : Multiplicative ℕ, (pure t : B) = pure u from ⟨t, rfl⟩),
    pure_mul_as_map, Ultrafilter.map_pure]

/-- The alternate operation differs from the canonical one. A shift by one
interchanges the parity classes, so its pushforward fixes no ultrafilter. -/
theorem rightTopologicalAlternativeNat_ne_mul :
    rightTopologicalAlternativeNat ≠ (· * · : B → B → B) := by
  intro h
  let s := Multiplicative.ofAdd (1 : ℕ)
  let q := hyperfilter (Multiplicative ℕ)
  have hFree : IsFreeUltrafilter q := hyperfilter_le_cofinite
  have hfix : (pure s : B) * q = q := by
    have heq := congrFun (congrFun h (pure s)) q
    rw [alt_of_nonprincipal _ (nat_not_principal_of_free hFree)] at heq
    exact heq.symm
  let A : Set (Multiplicative ℕ) := {n | n.toAdd % 2 = 0}
  have hpre : (s * ·) ⁻¹' A = Aᶜ := by
    ext n
    change (1 + n.toAdd) % 2 = 0 ↔ ¬ n.toAdd % 2 = 0
    omega
  have hIff : A ∈ q ↔ Aᶜ ∈ q := by
    conv_lhs => rw [← hfix, pure_mul_as_map]
    change (s * ·) ⁻¹' A ∈ q ↔ Aᶜ ∈ q
    rw [hpre]
  exact iff_not_self (hIff.trans Ultrafilter.compl_mem_iff_notMem)

/-- There are two distinct right-topological semigroup operations extending
addition on the principal ultrafilters of the nonnegative integers. -/
theorem exists_distinct_rightTopological_extension_nat :
    ∃ f : B → B → B,
      (∀ p q r, f (f p q) r = f p (f q r)) ∧
      (∀ q, Continuous (f · q)) ∧
      (∀ s t : Multiplicative ℕ, f (pure s) (pure t) = pure (s * t)) ∧
      f ≠ (· * ·) :=
  ⟨rightTopologicalAlternativeNat, rightTopologicalAlternativeNat_assoc,
    rightTopologicalAlternativeNat_continuous_right, rightTopologicalAlternativeNat_agree,
    rightTopologicalAlternativeNat_ne_mul⟩

end Counterexample

section Largeness

variable {S : Type*} [Semigroup S]

/-- Finitely many left preimages of a syndetic set cover the semigroup. -/
def IsSyndetic (A : Set S) : Prop :=
  ∃ H : Finset S, H.Nonempty ∧ ∀ x : S, ∃ h ∈ H, h * x ∈ A

/-- A piecewise syndetic set is exactly an intersection of a syndetic set
with a thick set. -/
theorem isPiecewiseSyndetic_iff_inter_syndetic_thick [Nonempty S] (A : Set S) :
    IsPiecewiseSyndetic A ↔
      ∃ B T : Set S, IsSyndetic B ∧ IsThick T ∧ A = B ∩ T := by
  classical
  constructor
  · rintro ⟨H, _, hH⟩
    let V : Set S := {x | ∃ h ∈ H, h * x ∈ A}
    let T := A ∪ V
    let B := A ∪ Tᶜ
    have hT : IsThick T := by
      intro F
      obtain ⟨x, hx⟩ := hH F
      exact ⟨x, fun s hs ↦ Or.inr (hx s hs)⟩
    have hEq : A = B ∩ T := by
      ext x
      constructor
      · exact fun hx ↦ ⟨Or.inl hx, Or.inl hx⟩
      · intro hx
        exact hx.1.resolve_right (fun h ↦ h hx.2)
    obtain ⟨s⟩ := ‹Nonempty S›
    have hB : IsSyndetic B := by
      refine ⟨insert s (H.image (· * s)), ⟨s, Finset.mem_insert_self _ _⟩, fun x ↦ ?_⟩
      by_cases hT : s * x ∈ T
      · rcases hT with hs | ⟨t, ht, htx⟩
        · exact ⟨s, Finset.mem_insert_self _ _, Or.inl hs⟩
        · exact ⟨t * s, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ht),
            Or.inl (by rwa [mul_assoc])⟩
      · exact ⟨s, Finset.mem_insert_self _ _, Or.inr hT⟩
    exact ⟨B, T, hB, hT, hEq⟩
  · rintro ⟨B, T, ⟨H, hH, hB⟩, hT, rfl⟩
    refine ⟨H, hH, fun F ↦ ?_⟩
    let K : Finset S := H.biUnion (fun h ↦ F.image (h * ·))
    obtain ⟨x, hx⟩ := hT K
    refine ⟨x, fun f hf ↦ ?_⟩
    obtain ⟨h, hh, hhB⟩ := hB (f * x)
    have hK : h * f ∈ K :=
      Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_image_of_mem (h * ·) hf⟩
    exact ⟨h, hh, hhB, by rw [← mul_assoc]; exact hx _ hK⟩

end Largeness

end JdLG
