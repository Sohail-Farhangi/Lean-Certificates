/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.UltrafilterMore
public import JdLG.UltrafilterMoreStoneCech

/-!
# Ultrafilter difference products and reversible vectors

The right-fraction argument of Lemma 5.1(ii) and Theorem 5.2(iii).
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace JdLG

theorem ultrafilterExtend_map_comp {S T X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (f : T → X) (g : S → T) (p : Ultrafilter S) :
    Ultrafilter.extend f (p.map g) = Ultrafilter.extend (f ∘ g) p := by
  symm
  exact ultrafilter_extend_eq_iff.mpr
    ((tendsto_ultrafilterExtend f (p.map g)).comp tendsto_map)

/-- A group map with compact target respects inverses on ultrafilter limits if inversion
is continuous in the target. -/
theorem ultrafilterExtend_map_inv {G K : Type*} [Group G] [Group K] [TopologicalSpace K]
    [T2Space K] [CompactSpace K] (f : G →* K) (hInv : Continuous (Inv.inv : K → K))
    (p : Ultrafilter G) : Ultrafilter.extend f (ultrafilterInverse p) =
      (Ultrafilter.extend f p)⁻¹ := by
  rw [ultrafilterInverse, ultrafilterExtend_map_comp]
  apply ultrafilter_extend_eq_iff.mpr
  change Tendsto (f ∘ Inv.inv) (p : Filter G) _
  have h := (hInv.tendsto (Ultrafilter.extend f p)).comp (tendsto_ultrafilterExtend f p)
  simpa only [Function.comp_def, map_inv] using h

section OperatorLimits

variable {S G 𝕜 E : Type*} [Semigroup S] [Group G] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparatingDual 𝕜 E]

/-- The retraction to the reversible group agrees with the extension of the
group homomorphism from the group of right quotients. -/
theorem GroupIdeal.exists_ultrafilterExtend_rightFractionLift
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) (hK : IsCompact K.carrier)
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) :
    ∃ F : G →* K.carrier, ∀ p : Ultrafilter S,
      K.groupRetraction (Ultrafilter.extend (closureInclusion π) p) =
        Ultrafilter.extend F (p.map ι) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let f : S →ₙ* K.carrier := K.groupRetraction.comp (closureInclusion π)
  obtain ⟨F, hF, _⟩ := existsUnique_rightFractionLift hι f
  have hRet : Continuous K.groupRetraction :=
    (continuous_const_mul K.identity).subtype_mk _
  refine ⟨F, fun p ↦ ?_⟩
  have hExtend : Ultrafilter.extend f p = K.groupRetraction
      (Ultrafilter.extend (closureInclusion π) p) :=
    ultrafilter_extend_eq_iff.mpr
      ((hRet.tendsto _).comp (tendsto_ultrafilterExtend (closureInclusion π) p))
  have hFun : (F : G → K.carrier) ∘ ι = f := funext hF
  rw [← hExtend, ← hFun, ← ultrafilterExtend_map_comp]

/-- The retraction to the reversible group sends all source inverse-product ultrafilters
to the identity. The quotient group embedding and continuity of inversion on the group
ideal are the two structural inputs. -/
theorem GroupIdeal.ultrafilterExtend_retraction_of_inverse_product
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) (hK : IsCompact K.carrier)
    (hInv : Continuous (Inv.inv : K.carrier → K.carrier))
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) {p q : Ultrafilter S}
    (hp : p.map ι = ultrafilterInverse (q.map ι) * q.map ι) :
    K.groupRetraction (Ultrafilter.extend (closureInclusion π) p) = 1 := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  obtain ⟨F, hF⟩ := K.exists_ultrafilterExtend_rightFractionLift hπ hK hι
  have hLeft (a : K.carrier) : Continuous (a * ·) :=
    ((continuous_const_mul a.1).comp continuous_subtype_val).subtype_mk _
  have hRight (b : K.carrier) : Continuous (· * b) :=
    ((continuous_mul_const b.1).comp continuous_subtype_val).subtype_mk _
  rw [hF, hp]
  change Ultrafilter.extend F.toMulHom _ = 1
  rw [ultrafilterExtend_mul hLeft hRight F.toMulHom]
  change Ultrafilter.extend F (ultrafilterInverse (q.map ι)) *
    Ultrafilter.extend F (q.map ι) = 1
  rw [ultrafilterExtend_map_inv F hInv, inv_mul_cancel]

/-- If the group retraction evaluates to its identity, every reversible vector is fixed. -/
theorem GroupIdeal.reversible_tendsto_of_retraction_eq_one
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) {p : Ultrafilter S}
    (hp : K.groupRetraction (Ultrafilter.extend (closureInclusion π) p) = 1)
    {x : E} (hx : IsReversible (closureAction π) x) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 (toWeakSpace 𝕜 E x)) := by
  let A := Ultrafilter.extend (closureInclusion π) p
  have hRet := congrArg Subtype.val hp
  change K.identity * A = K.identity at hRet
  have hFix := (K.reversible_iff_fixed (closureAction π) x).mp hx
  have hPoint : closureAction π A x = x := by
    calc
      closureAction π A x = closureAction π A (closureAction π K.identity x) :=
        congrArg (closureAction π A) hFix.symm
      _ = closureAction π (A * K.identity) x := by rw [map_mul]; rfl
      _ = x := by rw [← K.identity_mul_eq_mul_identity, hRet]; exact hFix
  have hLimit := tendsto_weakOrbit_ultrafilterExtend hπ p x
  change Tendsto _ _ (𝓝 (toWeakSpace 𝕜 E (closureAction π A x))) at hLimit
  rwa [hPoint] at hLimit

/-- The vector limit in Lemma 5.1(ii), with the compact group ideal and its continuous
inversion displayed explicitly. -/
theorem GroupIdeal.reversible_tendsto_of_inverse_product
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) (hK : IsCompact K.carrier)
    (hInv : Continuous (Inv.inv : K.carrier → K.carrier))
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) {p q : Ultrafilter S}
    (hp : p.map ι = ultrafilterInverse (q.map ι) * q.map ι)
    {x : E} (hx : IsReversible (closureAction π) x) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 (toWeakSpace 𝕜 E x)) :=
  K.reversible_tendsto_of_retraction_eq_one hπ
    (K.ultrafilterExtend_retraction_of_inverse_product hπ hK hInv hι hp) hx

/-- The projection formula in Theorem 5.2(iii), with the group ideal's continuity
of inversion displayed explicitly. -/
theorem GroupIdeal.tendsto_projection_of_inverse_product_smallestIdeal [Nonempty S]
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) (hK : IsCompact K.carrier)
    (hInv : Continuous (Inv.inv : K.carrier → K.carrier))
    {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι) {p q : Ultrafilter S}
    (hq : q ∈ closure (smallestIdeal (Ultrafilter S)))
    (hp : p.map ι = ultrafilterInverse (q.map ι) * q.map ι) :
    Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (K.identity : E →WOT[𝕜] E)) := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  have hSmall := inverse_product_mem_ultrafilterMap_closure_smallestIdeal hι hq q
  obtain ⟨r, hr, heq⟩ := hSmall
  have hrp : r = p := ultrafilter_map_injective hι.1 (heq.trans hp.symm)
  have hMem := K.ultrafilterExtend_mem_of_mem_closure_smallestIdeal continuous_const_mul
    continuous_mul_const (closureInclusion π) (denseRange_closureInclusion π) (hrp ▸ hr)
  have hRet := congrArg Subtype.val (K.ultrafilterExtend_retraction_of_inverse_product
    hπ hK hInv hι hp)
  change K.identity * Ultrafilter.extend (closureInclusion π) p = K.identity at hRet
  rw [K.identity_mul hMem] at hRet
  have hLimit := tendsto_ultrafilterExtend (closureInclusion π) p
  rw [hRet] at hLimit
  exact (continuous_subtype_val.tendsto K.identity).comp hLimit

end OperatorLimits

end JdLG
