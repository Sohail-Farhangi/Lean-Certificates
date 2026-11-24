/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ToralNilrotation

/-! # Topological group and lattice structures for the toral nilrotation -/

@[expose] public section

open Filter MeasureTheory Set Topology

namespace Mixing.ToralNilrotation

theorem continuous_shear : Continuous (fun t : ℤ × Torus => shear t.1 t.2) := by
  apply continuous_prod_of_discrete_left.mpr
  intro n
  exact continuous_fst.prodMk (continuous_snd.add ((continuous_zsmul n).comp continuous_fst))

instance : IsTopologicalGroup ShearGroup where
  continuous_mul := by
    have h₁ : Continuous (fun a : ShearGroup × ShearGroup => groupEquiv a.1) :=
      continuous_groupEquiv.comp continuous_fst
    have h₂ : Continuous (fun a : ShearGroup × ShearGroup => groupEquiv a.2) :=
      continuous_groupEquiv.comp continuous_snd
    rw [continuous_induced_rng]
    exact (h₁.fst.add (continuous_shear.comp (h₁.snd.prodMk h₂.fst))).prodMk (h₁.snd.add h₂.snd)
  continuous_inv := by
    rw [continuous_induced_rng]
    exact (continuous_shear.comp (continuous_groupEquiv.snd.neg.prodMk continuous_groupEquiv.fst.neg)).prodMk
      continuous_groupEquiv.snd.neg

instance : CompactSpace (ShearGroup ⧸ lattice) := quotientHomeomorph.symm.compactSpace

theorem lattice_isClosed : IsClosed (lattice : Set ShearGroup) := by
  have he : (lattice : Set ShearGroup) = (fun a => (groupEquiv a).1) ⁻¹' {0} := by
    ext a
    exact mem_lattice a
  rw [he]
  exact isClosed_singleton.preimage continuous_groupEquiv.fst

/-- The coset homeomorphism intertwines each actual left translation with its affine formula. -/
theorem quotientHomeomorph_smul (a : ShearGroup) (q : ShearGroup ⧸ lattice) :
    quotientHomeomorph (a • q) = affineAct a (quotientHomeomorph q) := by
  induction q using QuotientGroup.induction_on with
  | _ b => exact quotientEquiv_left_translation a b

/-- No distinct pair can have a common orbit limit along the same filter. -/
theorem eq_of_common_orbit_limit (α : UnitAddCircle) {x y z : Torus}
    {l : Filter (Multiplicative ℤ)} [l.NeBot]
    (hx : Tendsto (fun g => (system α).act g x) l (𝓝 z))
    (hy : Tendsto (fun g => (system α).act g y) l (𝓝 z)) : x = y := by
  have h₁ := ((continuous_fst.tendsto z).comp hx).sub ((continuous_fst.tendsto z).comp hy)
  have hFirst (g : Multiplicative ℤ) : ((system α).act g x).1 - ((system α).act g y).1 = x.1 - y.1 := by
    let t := translatingElement α ^ g.toAdd
    change (t.left.toAdd.1 + x.1) - (t.left.toAdd.1 + y.1) = x.1 - y.1
    abel
  have hxy₁ : x.1 = y.1 := by
    apply sub_eq_zero.mp
    exact (tendsto_nhds_unique (tendsto_const_nhds.congr (fun g => (hFirst g).symm)) h₁).trans (sub_self _)
  have h₂ := ((continuous_snd.tendsto z).comp hx).sub ((continuous_snd.tendsto z).comp hy)
  have hSecond (g : Multiplicative ℤ) : ((system α).act g x).2 - ((system α).act g y).2 = x.2 - y.2 := by
    let t := translatingElement α ^ g.toAdd
    change (t.left.toAdd.2 + (x.2 + t.right.toAdd • x.1)) -
      (t.left.toAdd.2 + (y.2 + t.right.toAdd • y.1)) = x.2 - y.2
    rw [hxy₁]
    abel
  have hxy₂ : x.2 = y.2 := by
    apply sub_eq_zero.mp
    exact (tendsto_nhds_unique (tendsto_const_nhds.congr (fun g => (hSecond g).symm)) h₂).trans (sub_self _)
  exact Prod.ext hxy₁ hxy₂

end Mixing.ToralNilrotation
