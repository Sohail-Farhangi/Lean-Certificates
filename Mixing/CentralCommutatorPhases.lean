/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RotationSpectralDecay
public import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Connected central commutator phase images -/

@[expose] public section
noncomputable section

open Set TopologicalSpace
open scoped ComplexConjugate Topology

namespace Mixing

private theorem circle_re_lt_one_of_ne_one {z : Circle} (hz : z ≠ 1) : (z : ℂ).re < 1 := by
  have hLe := Complex.re_le_norm (z : ℂ)
  rw [Circle.norm_coe] at hLe
  apply lt_of_le_of_ne hLe
  intro he
  apply hz
  have hs := Circle.normSq_coe z
  rw [Complex.normSq_apply, he] at hs
  have hi : (z : ℂ).im = 0 := by nlinarith
  apply Subtype.ext
  exact Complex.ext he hi

private theorem circle_eq_or_eq_inv_of_re_eq {z w : Circle} (h : (z : ℂ).re = (w : ℂ).re) :
    z = w ∨ z = w⁻¹ := by
  have hz := Circle.normSq_coe z
  have hw := Circle.normSq_coe w
  rw [Complex.normSq_apply, h] at hz
  rw [Complex.normSq_apply] at hw
  have hSq : ((z : ℂ).im-(w : ℂ).im)*((z : ℂ).im+(w : ℂ).im) = 0 := by nlinarith
  rcases mul_eq_zero.mp hSq with he | he
  · left
    exact Subtype.ext (Complex.ext h (sub_eq_zero.mp he))
  · right
    apply Subtype.ext
    rw [Circle.coe_inv_eq_conj]
    apply Complex.ext
    · exact h
    · rw [Complex.conj_im]
      linarith

/-- A connected subgroup of the circle containing a point besides the
identity is the whole circle. No closedness of the subgroup is assumed. -/
theorem circle_subgroup_eq_top_of_connected_of_ne_one (K : Subgroup Circle)
    (hK : IsConnected (K : Set Circle)) {z : Circle} (hz : z ∈ K) (hz1 : z ≠ 1) : K = ⊤ := by
  let re : Circle → ℝ := fun z => (z : ℂ).re
  have hRe : Continuous re := Complex.continuous_re.comp continuous_subtype_val
  have hImage := hK.isPreconnected.image re hRe.continuousOn
  have hLow : re z ∈ re '' (K : Set Circle) := mem_image_of_mem _ hz
  have hHigh : 1 ∈ re '' (K : Set Circle) := ⟨1, K.one_mem, rfl⟩
  have hNear : (K : Set Circle) ∈ 𝓝 (1 : Circle) := by
    have hOpen : IsOpen {w : Circle | re z < re w} := isOpen_lt continuous_const hRe
    refine Filter.mem_of_superset (hOpen.mem_nhds (circle_re_lt_one_of_ne_one hz1)) ?_
    intro w hw
    have hLe := Complex.re_le_norm (w : ℂ)
    rw [Circle.norm_coe] at hLe
    change re z < re w at hw
    obtain ⟨y, hy, he⟩ := hImage.ordConnected.out hLow hHigh (show re w ∈ Icc (re z) 1 from ⟨hw.le, hLe⟩)
    rcases circle_eq_or_eq_inv_of_re_eq he.symm with he' | he'
    · exact he' ▸ hy
    · exact he' ▸ K.inv_mem hy
  have hO := K.isOpen_of_mem_nhds hNear
  have hC := K.isClosed_of_isOpen hO
  have he := (isClopen_iff.mp ⟨hC, hO⟩).resolve_left (nonempty_iff_ne_empty.mp ⟨1, K.one_mem⟩)
  exact SetLike.coe_injective he

/-- In particular any nontrivial continuous circle character on a connected
group is surjective. -/
theorem continuous_circle_hom_surjective_of_nontrivial {A : Type*} [Group A]
    [TopologicalSpace A] [ConnectedSpace A] (f : A →* Circle) (hf : Continuous f)
    (h : ∃ a, f a ≠ 1) : Function.Surjective f := by
  obtain ⟨a, ha⟩ := h
  have hK : IsConnected (f.range : Set Circle) := by
    rw [MonoidHom.coe_range]
    exact isConnected_range hf
  have hTop := circle_subgroup_eq_top_of_connected_of_ne_one f.range hK ⟨a,rfl⟩ ha
  exact MonoidHom.range_eq_top.mp hTop

section Commutators

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable {A C : Subgroup Γ} (hC : C ≤ Subgroup.center Γ) (a : Γ)
variable (hm : ∀ b : A, a⁻¹*(b : Γ)⁻¹*a*(b : Γ) ∈ C)

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
private theorem time_commutator_relation (b : Γ) :
    a*b = b*a*(a⁻¹*b⁻¹*a*b) := by group

/-- The commutator is a homomorphism on a subgroup where its values are central. -/
def centralTimeCommutator : A →* C where
  toFun b := ⟨a⁻¹*(b : Γ)⁻¹*a*(b : Γ), hm b⟩
  map_one' := Subtype.ext (by change a⁻¹*1⁻¹*a*1 = 1; group)
  map_mul' b d := by
    let u := a⁻¹*(b : Γ)⁻¹*a*(b : Γ)
    let v := a⁻¹*(d : Γ)⁻¹*a*(d : Γ)
    apply Subtype.ext
    change a⁻¹*((b : Γ)*(d : Γ))⁻¹*a*((b : Γ)*(d : Γ)) = u*v
    apply mul_left_cancel (a := (b : Γ)*(d : Γ)*a)
    have hu : a*(b : Γ) = (b : Γ)*a*u := time_commutator_relation a b
    have hv : a*(d : Γ) = (d : Γ)*a*v := time_commutator_relation a d
    have hComm : u*(d : Γ) = (d : Γ)*u := ((Subgroup.mem_center_iff.mp (hC (hm b))) d).symm
    have hComm' : u*v = v*u := ((Subgroup.mem_center_iff.mp (hC (hm b))) v).symm
    rw [← time_commutator_relation]
    calc
      a*((b : Γ)*(d : Γ)) = (b : Γ)*a*u*(d : Γ) := by rw [← mul_assoc, hu]
      _ = (b : Γ)*a*(u*(d : Γ)) := by group
      _ = (b : Γ)*a*((d : Γ)*u) := by rw [hComm]
      _ = (b : Γ)*(a*(d : Γ))*u := by group
      _ = (b : Γ)*((d : Γ)*a*v)*u := by rw [hv]
      _ = (b : Γ)*(d : Γ)*a*(v*u) := by group
      _ = _ := by rw [← hComm', mul_assoc]

theorem centralTimeCommutator_continuous : Continuous (centralTimeCommutator hC a hm) := by
  exact (((continuous_const.mul continuous_subtype_val.inv).mul continuous_const).mul continuous_subtype_val).subtype_mk _

/-- A connected subgroup with one nontrivial commutator phase already
supplies every phase required by Parry's criterion. -/
theorem centralTimeCommutator_full_phases [ConnectedSpace A] (χ : C →* Circle) (hχ : Continuous χ)
    (h : ∃ b : A, χ (centralTimeCommutator hC a hm b) ≠ 1) :
    ∀ s : UnitAddCircle, ∃ (b : Γ) (u : C), a*b = b*a*(u : Γ) ∧ χ u = AddCircle.toCircle s := by
  have hSurj := continuous_circle_hom_surjective_of_nontrivial (χ.comp (centralTimeCommutator hC a hm))
    (hχ.comp (centralTimeCommutator_continuous hC a hm)) h
  intro s
  obtain ⟨b, hb⟩ := hSurj (AddCircle.toCircle s)
  exact ⟨b, centralTimeCommutator hC a hm b, time_commutator_relation a b, hb⟩

end Commutators

end Mixing
