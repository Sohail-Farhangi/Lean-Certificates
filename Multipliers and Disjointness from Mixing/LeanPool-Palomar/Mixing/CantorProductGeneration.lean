/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CantorGenerated
public import Mixing.CantorSumFactor
public import Mixing.GeneratedDensity
public import Mixing.GenerationAgreement

/-! # Generation of the Cantor product systems in Examples 6 and 7 -/

@[expose] public section

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Mixing

/-- The product case of Lemma 9, expressed in terms of the ordinary binary product. -/
theorem System.isUGenerated_prod_union {G X Y : Type*} [CommGroup G]
    [MeasurableSpace X] [MeasurableSpace Y] (S : System G X) (T : System G Y)
    (P Q : Set (Ultrafilter G)) (hS : S.IsUGenerated P) (hT : T.IsUGenerated Q) :
    (S.prod T).IsUGenerated (P ∪ Q) := by
  apply (S.prod T).isUGenerated_of_generatedSigma_eq
  apply le_antisymm ((S.prod T).generatedSigma_le _)
  let J := product_isJoining S T
  have hfst := J.fstFactor.measurable_generatedSigma (P := P) (Set.subset_union_left (t := Q))
  have hsnd := J.sndFactor.measurable_generatedSigma (P := Q) (Set.subset_union_right (s := P))
  rw [S.generatedSigma_eq_of_isUGenerated hS] at hfst
  rw [T.generatedSigma_eq_of_isUGenerated hT] at hsnd
  have hi : @Measurable (X × Y) (X × Y) ((S.prod T).generatedSigma (P ∪ Q)) _ id :=
    hfst.prodMk hsnd
  simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hi

/-- Doubling an integer, written in the multiplicative presentation of the acting group. -/
def cantorDilation (g : Multiplicative ℤ) : Multiplicative ℤ :=
  Multiplicative.ofAdd (g.toAdd * 2)

private theorem cantorDilation_injective : Function.Injective cantorDilation := by
  intro g h he
  change g.toAdd * 2 = h.toAdd * 2 at he
  have hh : g.toAdd = h.toAdd := mul_right_cancel₀ (by decide : (2 : ℤ) ≠ 0) he
  exact hh

private theorem cantorDilation_map_free (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite) :
    ((p.map cantorDilation : Ultrafilter (Multiplicative ℤ)) : Filter (Multiplicative ℤ)) ≤
      cofinite := by
  exact (Filter.map_mono hp).trans cantorDilation_injective.tendsto_cofinite

private theorem cantorDilation_map_map_support (p : Ultrafilter (Multiplicative ℤ))
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈
      (p.map cantorDilation).map cantorDilation := by
  change cantorDilation ⁻¹' (cantorDilation ⁻¹' _) ∈ p
  refine Filter.mem_of_superset hsupp ?_
  rintro _ ⟨j, rfl⟩
  refine ⟨j + 1, ?_⟩
  change (4 : ℤ)^(j + 1) = ((4 : ℤ)^j * 2) * 2
  rw [pow_succ]
  ring

private theorem cantorDouble_koopman (g : Multiplicative ℤ)
    (x : Lp ℂ 2 example5CantorSystem.measure) :
    (circleSkew cantorCircleMeasure 2).koopmanRep g x =
      example5CantorSystem.koopmanRep (cantorDilation g) x := by
  have hact : (circleSkew cantorCircleMeasure 2).act g =
      example5CantorSystem.act (cantorDilation g) := by
    funext w
    change (w.1, w.2 + (g.toAdd * 2) • w.1) =
      (w.1, w.2 + ((g.toAdd * 2) * 1) • w.1)
    rw [mul_one]
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving x ((circleSkew cantorCircleMeasure 2).preserves g)).trans
    ((EventuallyEq.of_eq (congrArg (fun a ↦ (x : _ → ℂ) ∘ a) hact)).trans
      (Lp.coeFn_compMeasurePreserving x (example5CantorSystem.preserves (cantorDilation g))).symm)

private theorem cantorDouble_ultrafilterOperator (q : Ultrafilter (Multiplicative ℤ)) :
    ultrafilterOperator (circleSkew cantorCircleMeasure 2).koopmanRep q =
      ultrafilterOperator example5CantorSystem.koopmanRep (q.map cantorDilation) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₂ := tendsto_ultrafilterOperator_coeff (circleSkew cantorCircleMeasure 2).koopmanRep q y x
  have h₂' := h₂.congr (fun g ↦ congrArg (inner ℂ y) (cantorDouble_koopman g x))
  have h₁ := tendsto_ultrafilterOperator_coeff example5CantorSystem.koopmanRep
    (q.map cantorDilation) y x
  have h₁' := h₁.comp (tendsto_map (f := cantorDilation) (x := (q : Filter (Multiplicative ℤ))))
  exact tendsto_nhds_unique h₂' h₁'

private theorem cantorDouble_isUGenerated_from (q : Ultrafilter (Multiplicative ℤ))
    (hgen : example5CantorSystem.IsUGenerated {q.map cantorDilation}) :
    (circleSkew cantorCircleMeasure 2).IsUGenerated {q} := by
  let T := circleSkew cantorCircleMeasure 2
  have htranslate (f : BoundedObservable (UnitAddCircle × UnitAddCircle)) :
      T.ultrafilterTranslate q f =
        example5CantorSystem.ultrafilterTranslate (q.map cantorDilation) f := by
    unfold System.ultrafilterTranslate
    change BoundedObservable.ofLp
        (ultrafilterOperator T.koopmanRep q (f.l2 T.measure)) f.bound f.bound_nonneg = _
    rw [cantorDouble_ultrafilterOperator q]
    rfl
  have hsub : example5CantorSystem.generatedProducts {q.map cantorDilation} ⊆
      T.generatedProducts {q} := by
    rintro _ ⟨n, p, f, hp, rfl⟩
    have he : p = fun _ ↦ q.map cantorDilation :=
      funext fun i ↦ Set.mem_singleton_iff.mp (hp i)
    subst p
    refine ⟨n, fun _ ↦ q, f, fun _ ↦ rfl, ?_⟩
    unfold System.ultrafilterProduct
    simp_rw [htranslate]
    rfl
  exact hgen.mono (Submodule.span_mono hsub)

/-- Doubling the ultrafilter generates the speed-two skew rotation, as in (12). -/
theorem example6_doubleSpeed_isUGenerated (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    (circleSkew cantorCircleMeasure 2).IsUGenerated {p.map cantorDilation} :=
  cantorDouble_isUGenerated_from (p.map cantorDilation)
    (example5_cantor_isUGenerated _ (cantorDilation_map_free _ (cantorDilation_map_free p hp))
      (cantorDilation_map_map_support p hsupp))

/-- Example 6's product is generated by the original ultrafilter and its double. -/
theorem example6_cantor_product_isUGenerated (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    example6CantorSystem.IsUGenerated {p, p.map cantorDilation} := by
  have h := System.isUGenerated_prod_union example5CantorSystem (circleSkew cantorCircleMeasure 2)
    {p} {p.map cantorDilation} (example5_cantor_isUGenerated p hp hsupp)
      (example6_doubleSpeed_isUGenerated p hp hsupp)
  change (example5CantorSystem.prod (circleSkew cantorCircleMeasure 2)).IsUGenerated _
  simpa only [Set.singleton_union] using h

/-- The source system in Example 7 is generated by the same single free ultrafilter. -/
theorem example7_cantor_product_isUGenerated (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    (example5CantorSystem.prod example5CantorSystem).IsUGenerated {p} := by
  have h := example5_cantor_isUGenerated p hp hsupp
  simpa only [Set.union_self] using
    System.isUGenerated_prod_union example5CantorSystem example5CantorSystem {p} {p} h h


/-- Projection onto the second skew rotation of the Example 6 product. -/
noncomputable def example6SecondProjection :
    FactorMap example6CantorSystem (circleSkew cantorCircleMeasure 2) :=
  (product_isJoining example5CantorSystem (circleSkew cantorCircleMeasure 2)).sndFactor

/-- Equation (12), for the fibre character of the second skew rotation in the product. -/
theorem example6_second_fibre_eigenvector (p : Ultrafilter (Multiplicative ℤ))
    (hp : (p : Filter (Multiplicative ℤ)) ≤ cofinite)
    (hsupp : Set.range (fun j : ℕ ↦ Multiplicative.ofAdd ((4 : ℤ)^j)) ∈ p) :
    let f := circlePairFourierLp (circleSkew cantorCircleMeasure 2).measure ![0, 1]
    ultrafilterOperator example6CantorSystem.koopmanRep (p.map cantorDilation)
      (example6SecondProjection.pullback f) =
      cantorFourier (-1) • example6SecondProjection.pullback f := by
  let q := p.map cantorDilation
  let n : Fin 2 → ℤ := ![0, 1]
  let f := circlePairFourierLp example5CantorSystem.measure n
  let J : Lp ℂ 2 example5CantorSystem.measure →ₗᵢ[ℂ] Lp ℂ 2 example6CantorSystem.measure :=
    example6SecondProjection.pullback
  change ultrafilterOperator example6CantorSystem.koopmanRep q
      (J f) = cantorFourier (-1) • J f
  have hcomm := example6SecondProjection.intertwines_pullback.ultrafilter q f
  have h := example5_cantor_ultrafilter_eigenvector n (q.map cantorDilation)
    (cantorDilation_map_free q (cantorDilation_map_free p hp)) (cantorDilation_map_map_support p hsupp)
  have hn : n 1 = 1 := rfl
  have hf : ultrafilterOperator example5CantorSystem.koopmanRep (q.map cantorDilation) f =
      cantorFourier (-1) • f := by
    simpa only [hn, Int.cast_neg, Int.cast_one] using h
  calc
    _ = J (ultrafilterOperator (circleSkew cantorCircleMeasure 2).koopmanRep q f) := hcomm.symm
    _ = J (ultrafilterOperator example5CantorSystem.koopmanRep (q.map cantorDilation) f) :=
      congrArg J (DFunLike.congr_fun (cantorDouble_ultrafilterOperator q) f)
    _ = J (cantorFourier (-1) • f) := congrArg J hf
    _ = _ := map_smul J _ _

end Mixing
