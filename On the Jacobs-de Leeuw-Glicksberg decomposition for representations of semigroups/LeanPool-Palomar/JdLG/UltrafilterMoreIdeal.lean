/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMoreDensity

/-! # Stone–Čech ideals in the group of right quotients -/

@[expose] public section

open Filter Set

namespace JdLG

variable {S G : Type*} [Semigroup S] [Group G] {ι : S →ₙ* G}

private theorem pure_mul_pure_eq {M : Type*} [Semigroup M] (a b : M) :
    (pure a : Ultrafilter M) * pure b = pure (a * b) := by
  rw [pure_mul_as_map, Ultrafilter.map_pure]

private theorem ultrafilter_image_isLeftIdeal_of_surj_principal (hι : IsGroupOfRightQuotients ι)
    {D : Set (Ultrafilter S)} (hD : IsClosed D)
    (hLeft : ∀ a : Ultrafilter S, ∀ {p : Ultrafilter S}, p ∈ D → a * p ∈ D)
    (hSurj : ∀ b : S, ∀ p ∈ D, ∃ r ∈ D, (pure b : Ultrafilter S) * r = p) :
    ∀ a : Ultrafilter G, ∀ {p : Ultrafilter G},
      p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' D →
      a * p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' D := by
  rintro a _ ⟨p, hp, rfl⟩
  let C := (fun u : Ultrafilter S ↦ u.map ι) '' D
  have hC : IsClosed C := (hD.isCompact.image (continuous_ultrafilter_map ι)).isClosed
  let f : Ultrafilter G → Ultrafilter G := (· * p.map ι)
  have hf : Continuous f := Ultrafilter.continuous_mul_left (p.map ι)
  have hRange : range (pure : G → Ultrafilter G) ⊆ f ⁻¹' C := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨u, v, rfl⟩ := hι.2 g
    obtain ⟨r, hr, hvr⟩ := hSurj v p hp
    refine ⟨pure u * r, hLeft (pure u) hr, ?_⟩
    change (pure u * r).map ι = pure (ι u * (ι v)⁻¹) * p.map ι
    rw [ultrafilter_map_mul, Ultrafilter.map_pure]
    nth_rewrite 1 [← hvr]
    rw [ultrafilter_map_mul, Ultrafilter.map_pure, ← mul_assoc, pure_mul_pure_eq,
      inv_mul_cancel_right]
  exact closure_minimal hRange (hC.preimage hf) (denseRange_pure a)

/-- The embedded closure of the smallest ideal in βS is a left ideal in βG. -/
theorem ultrafilter_image_closure_smallestIdeal_isLeftIdeal [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) (a : Ultrafilter G) {p : Ultrafilter G}
    (hp : p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' closure (smallestIdeal (Ultrafilter S))) :
    a * p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' closure (smallestIdeal (Ultrafilter S)) := by
  apply ultrafilter_image_isLeftIdeal_of_surj_principal hι isClosed_closure _ _ a hp
  · intro b q hq
    have hmem : ∀ s : S, (pure s : Ultrafilter S) * q ∈
        closure (smallestIdeal (Ultrafilter S)) := by
      intro s
      let f : Ultrafilter S → Ultrafilter S := ((pure s : Ultrafilter S) * ·)
      have hf : Continuous f := by
        simpa only [f, pure_mul_as_map] using continuous_ultrafilter_map (s * ·)
      exact closure_minimal (s := smallestIdeal (Ultrafilter S))
        (t := f ⁻¹' closure (smallestIdeal (Ultrafilter S)))
        (fun _ ht ↦ subset_closure ((smallestIdeal_isTwoSidedIdeal (M := Ultrafilter S)).1 _ ht))
        (isClosed_closure.preimage hf) hq
    apply closure_minimal (s := range (pure : S → Ultrafilter S))
      (t := (· * q) ⁻¹' closure (smallestIdeal (Ultrafilter S))) _
      (isClosed_closure.preimage (Ultrafilter.continuous_mul_left q)) (denseRange_pure b)
    rintro _ ⟨s, rfl⟩
    exact hmem s
  · exact fun s _ hs ↦ principal_mul_surj_closure_smallestIdeal hι s hs

/-- The embedded smallest ideal in βS is a left ideal in βG. -/
theorem ultrafilter_image_smallestIdeal_isLeftIdeal [Nonempty S]
    (hι : IsGroupOfRightQuotients ι) (a : Ultrafilter G) {p : Ultrafilter G}
    (hp : p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' smallestIdeal (Ultrafilter S)) :
    a * p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' smallestIdeal (Ultrafilter S) := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨r, _, hr⟩ := ultrafilter_image_closure_smallestIdeal_isLeftIdeal hι a
    ⟨q, subset_closure hq, rfl⟩
  obtain ⟨e, he, _, hqe⟩ := exists_idempotent_right_identity_of_mem_smallestIdeal
    Ultrafilter.continuous_mul_left hq
  have hre : r * e = r := by
    apply ultrafilter_map_injective hι.1
    change (r * e).map ι = r.map ι
    change r.map ι = a * q.map ι at hr
    rw [ultrafilter_map_mul, hr, mul_assoc, ← ultrafilter_map_mul, hqe]
  exact ⟨r, hre ▸ (smallestIdeal_isTwoSidedIdeal (M := Ultrafilter S)).1 r he, hr⟩

/-- The embedded essential ultrafilters of βS form a left ideal in βG. -/
theorem ultrafilter_image_essentialUltrafilters_isLeftIdeal
    (hι : IsGroupOfRightQuotients ι) (a : Ultrafilter G) {p : Ultrafilter G}
    (hp : p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' essentialUltrafilters S) :
    a * p ∈ (fun u : Ultrafilter S ↦ u.map ι) '' essentialUltrafilters S :=
  ultrafilter_image_isLeftIdeal_of_surj_principal hι isClosed_essentialUltrafilters
    essentialUltrafilters_isTwoSidedIdeal.1
    (fun s _ hs ↦ principal_mul_surj_essentialUltrafilters hι.1 s hs) a hp

end JdLG
