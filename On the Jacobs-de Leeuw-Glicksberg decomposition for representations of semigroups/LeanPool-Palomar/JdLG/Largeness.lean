/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finset.Image

/-!
# Thickly syndetic principal right ideals

Lemma 2.5 of arXiv:2509.24003v3 is proved here using finite intersections of
principal right ideals. The definitions are the finite-set formulations from
Section 2.5.1 of the paper.
-/

@[expose] public section

namespace JdLG

variable {S : Type*} [Semigroup S]

/-- Principal right ideals have nonempty pairwise intersection. -/
def IsLeftReversible (S : Type*) [Semigroup S] : Prop :=
  ∀ a b : S, ∃ x y : S, a * x = b * y

/-- Every finite set has a right translate contained in `A`. -/
def IsThick (A : Set S) : Prop :=
  ∀ F : Finset S, ∃ x : S, ∀ a ∈ F, a * x ∈ A

/-- A nonempty finite union of left preimages of `A` is thick. -/
def IsPiecewiseSyndetic (A : Set S) : Prop :=
  ∃ H : Finset S, H.Nonempty ∧ IsThick {x | ∃ h ∈ H, h * x ∈ A}

/-- A set is thickly syndetic when it meets every piecewise syndetic set. -/
def IsThicklySyndetic (A : Set S) : Prop :=
  ∀ B : Set S, IsPiecewiseSyndetic B → (A ∩ B).Nonempty

theorem IsPiecewiseSyndetic.mono {A B : Set S} (hA : IsPiecewiseSyndetic A) (hAB : A ⊆ B) :
    IsPiecewiseSyndetic B := by
  obtain ⟨H, hH, hthick⟩ := hA
  refine ⟨H, hH, fun F ↦ ?_⟩
  obtain ⟨x, hx⟩ := hthick F
  refine ⟨x, fun a ha ↦ ?_⟩
  obtain ⟨h, hh, hm⟩ := hx a ha
  exact ⟨h, hh, hAB hm⟩

private theorem exists_common_right_multiple [Nonempty S] (hreversible : IsLeftReversible S)
    (F : Finset S) : ∃ x : S, ∀ a ∈ F, ∃ y : S, x = a * y := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary S, by simp⟩
  | @insert a F _ ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨u, v, huv⟩ := hreversible x a
    refine ⟨x * u, fun b hb ↦ ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨v, huv⟩
    · obtain ⟨w, hw⟩ := hx b hb
      exact ⟨w * u, by rw [hw, mul_assoc]⟩

/-- Lemma 2.5, first conclusion. The complement of a principal right ideal of
a left reversible semigroup is never piecewise syndetic. -/
theorem not_piecewiseSyndetic_compl_principal_right_ideal
    (hreversible : IsLeftReversible S) (a : S) :
    ¬ IsPiecewiseSyndetic (Set.range (fun x : S ↦ a * x))ᶜ := by
  classical
  let : Nonempty S := ⟨a⟩
  intro hpiecewise
  obtain ⟨H, _, hthick⟩ := hpiecewise
  have hright (h : S) : ∃ t : S, h * t ∈ Set.range (fun x : S ↦ a * x) := by
    obtain ⟨u, v, huv⟩ := hreversible h a
    exact ⟨u, v, huv.symm⟩
  let t := fun h ↦ (hright h).choose
  have ht (h : S) := (hright h).choose_spec
  obtain ⟨r, hr⟩ := exists_common_right_multiple hreversible (H.image t)
  obtain ⟨x, hx⟩ := hthick {r}
  obtain ⟨h, hh, hbad⟩ := hx r (Finset.mem_singleton_self r)
  obtain ⟨u, hu⟩ := hr (t h) (Finset.mem_image_of_mem t hh)
  obtain ⟨v, hv⟩ := ht h
  change a * v = h * t h at hv
  apply hbad
  refine ⟨v * (u * x), ?_⟩
  calc
    a * (v * (u * x)) = (a * v) * (u * x) := (mul_assoc _ _ _).symm
    _ = (h * t h) * (u * x) := by rw [hv]
    _ = h * ((t h * u) * x) := by simp only [mul_assoc]
    _ = h * (r * x) := by rw [← hu]

/-- Lemma 2.5, second conclusion. A principal right ideal is thickly syndetic
in a left reversible semigroup. -/
theorem thicklySyndetic_principal_right_ideal (hreversible : IsLeftReversible S) (a : S) :
    IsThicklySyndetic (Set.range (fun x : S ↦ a * x)) := by
  intro B hB
  by_contra hnone
  have hsub : B ⊆ (Set.range (fun x : S ↦ a * x))ᶜ :=
    fun b hb ha ↦ hnone ⟨b, ha, hb⟩
  exact not_piecewiseSyndetic_compl_principal_right_ideal hreversible a (hB.mono hsub)

end JdLG
