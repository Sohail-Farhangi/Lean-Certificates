/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroLebesguePair
public import Mixing.RudinShapiroAtomDensity
public import Mixing.RudinShapiroResidueSpectrum

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped Classical InnerProductSpace

variable (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)

private theorem rudinShapiroResidueCutoffObservable_mem_span_all (k : ℕ) (a : Fin (2 ^ k)) :
    (rudinShapiroResidueCutoffObservable k a).l2 (rudinShapiroOrbitSystem p hp).measure ∈
      rudinShapiroPairSpan p hp := by
  cases k with
  | zero =>
    have he : (rudinShapiroResidueCutoffObservable 0 a).l2 (rudinShapiroOrbitSystem p hp).measure =
        (rudinShapiroZeroCutoffObservable 0 false).l2 (rudinShapiroOrbitSystem p hp).measure := by
      apply BoundedObservable.l2_eq_of_ae_eq
      exact Eventually.of_forall fun w ↦ by
        simp [rudinShapiroResidueCutoffObservable, rudinShapiroResidueCutoff, rudinShapiroResidue,
          rudinShapiroZeroCutoffObservable, rudinShapiroZeroCutoff, rudinShapiroZeroPhase]
    rw [he]
    exact rudinShapiroZeroCutoffObservable_mem_span p hp 0 false
  | succ k => exact rudinShapiroResidueCutoffObservable_mem_span p hp k a a.isLt

private theorem rudinShapiroResidueSignLp_eq_even_add_odd (k : ℕ) (a : Fin (2 ^ k)) (b : Bool) :
    rudinShapiroResidueSignLp p k a b =
      (2 : ℂ)⁻¹ • (rudinShapiroResidueIndicator p hp k a +
        (signValue b : ℂ) • (rudinShapiroResidueCutoffObservable k a).l2
          (rudinShapiroOrbitSystem p hp).measure) := by
  let S := rudinShapiroOrbitSystem p hp
  let I := rudinShapiroResidueIndicator p hp k a
  let s := (rudinShapiroResidueCutoffObservable k a).l2 S.measure
  have hA : rudinShapiroResidueSignLp p k a b =ᵐ[S.measure]
      ({w : SignWords | rudinShapiroResidue k a w ∧ w 0 = b}).indicator (fun _ ↦ (1 : ℂ)) :=
    indicatorConstLp_coeFn
  apply Lp.ext
  filter_upwards [hA, ae_rudinShapiroResidueIndicator p hp k a,
    (rudinShapiroResidueCutoffObservable k a).coe_l2 S.measure,
    Lp.coeFn_smul (2 : ℂ)⁻¹ (I + (signValue b : ℂ) • s), Lp.coeFn_add I ((signValue b : ℂ) • s),
    Lp.coeFn_smul (signValue b : ℂ) s] with w h hI hs hS hAdd hSmul
  change I w = _ at hI
  change s w = _ at hs
  change rudinShapiroResidueSignLp p k a b w = ((2 : ℂ)⁻¹ • (I + (signValue b : ℂ) • s)) w
  rw [h, hS, Pi.smul_apply, hAdd, Pi.add_apply, hSmul, Pi.smul_apply, hI, hs]
  by_cases ha : rudinShapiroResidue k a w <;> cases hb : w 0 <;> cases b <;>
    norm_num [Set.indicator, rudinShapiroResidueCutoffObservable, rudinShapiroResidueCutoff,
      signValue, ha, hb, smul_eq_mul]

/-- The closed span of the actual dyadic phase indicators. -/
def rudinShapiroResidueSpan : Submodule ℂ (Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure) :=
  (Submodule.span ℂ (range fun i : Σ k : ℕ, Fin (2 ^ k) ↦
    rudinShapiroResidueIndicator p hp i.1 i.2)).topologicalClosure

theorem rudinShapiroResidueSpan_le_purePointPart :
    rudinShapiroResidueSpan p hp ≤ purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, a⟩, rfl⟩
    exact rudinShapiroResidueIndicator_mem_purePointPart p hp k a
  · exact isClosed_purePointPart _

theorem rudinShapiro_residueSpan_sup_pairSpan :
    (rudinShapiroResidueSpan p hp ⊔ rudinShapiroPairSpan p hp).topologicalClosure = ⊤ := by
  let R := rudinShapiroResidueSpan p hp
  let Q := rudinShapiroPairSpan p hp
  let W := (R ⊔ Q).topologicalClosure
  change W = ⊤
  have hW : IsClosed (W : Set (Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure)) :=
    (R ⊔ Q).isClosed_topologicalClosure
  refine rudinShapiroResidueSign_closedSubmodule_eq_top p hp W hW ?_
  intro k a b
  have hLeR : R ≤ R ⊔ Q := le_sup_left
  have hLeQ : Q ≤ R ⊔ Q := le_sup_right
  have hI : rudinShapiroResidueIndicator p hp k a ∈ R ⊔ Q :=
    hLeR (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨k, a⟩, rfl⟩))
  have hS : (rudinShapiroResidueCutoffObservable k a).l2
      (rudinShapiroOrbitSystem p hp).measure ∈ R ⊔ Q :=
    hLeQ (rudinShapiroResidueCutoffObservable_mem_span_all p hp k a)
  rw [rudinShapiroResidueSignLp_eq_even_add_odd p hp k a b]
  exact (Submodule.le_topologicalClosure (R ⊔ Q)) ((R ⊔ Q).smul_mem _
    ((R ⊔ Q).add_mem hI ((R ⊔ Q).smul_mem _ hS)))

/-- The dyadic phase indicators generate the entire Kronecker subspace. -/
theorem rudinShapiroResidueSpan_eq_purePointPart :
    rudinShapiroResidueSpan p hp = purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep := by
  let S := rudinShapiroOrbitSystem p hp
  let R := rudinShapiroResidueSpan p hp
  let P := purePointPart S.koopmanRep
  let Q := rudinShapiroPairSpan p hp
  let : CompleteSpace R := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hRle := rudinShapiroResidueSpan_le_purePointPart p hp
  have hQle : Q ≤ Pᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact rudinShapiroPairOrbit_mem_purePoint_orthogonal p hp i
  refine le_antisymm hRle ?_
  intro x hx
  let z := x - R.starProjection x
  let K := (innerSL ℂ z).ker
  have hzR : z ∈ Rᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hzP : z ∈ P := P.sub_mem hx (hRle (R.starProjection_apply_mem x))
  have hK : R ⊔ Q ≤ K := sup_le
    (fun y hy ↦ inner_eq_zero_symm.mp (hzR y hy))
    (fun y hy ↦ (hQle hy) z hzP)
  have hTop : (⊤ : Submodule ℂ (Lp ℂ 2 S.measure)) ≤ K := by
    rw [← rudinShapiro_residueSpan_sup_pairSpan p hp]
    exact Submodule.topologicalClosure_minimal _ hK (innerSL ℂ z).isClosed_ker
  have hz : z = 0 := inner_self_eq_zero.mp (hTop Submodule.mem_top)
  change x - R.starProjection x = 0 at hz
  rw [sub_eq_zero.mp hz]
  exact R.starProjection_apply_mem x

/-- The Rudin–Shapiro orbit has a Lebesgue complement of precisely
multiplicity two to the Kronecker subspace. -/
theorem rudinShapiro_hasLebesgueComplement :
    HasLebesgueComplement (rudinShapiroOrbitSystem p hp).koopmanRep Bool := by
  apply rudinShapiro_hasLebesgueComplement_of_parent_span p hp
  rw [← rudinShapiroResidueSpan_eq_purePointPart p hp]
  exact rudinShapiro_residueSpan_sup_pairSpan p hp

/-- The generated factor conclusion of Example 3 for the measured
Rudin–Shapiro subshift and every nonempty family of free ultrafilters. -/
theorem example3_rudinShapiro_generatedSigma (A : Set (Ultrafilter (Multiplicative ℤ)))
    (hNonempty : A.Nonempty) (hFree : A ⊆ freeUltrafilters (Multiplicative ℤ)) :
    (rudinShapiroOrbitSystem p hp).generatedSigma A = (rudinShapiroOrbitSystem p hp).kroneckerSigma :=
  example1_generatedSigma_of_purePoint_lebesgue _ Bool
    (rudinShapiro_hasLebesgueComplement p hp) A hNonempty hFree

end Mixing
