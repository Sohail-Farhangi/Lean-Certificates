module

public import Mixing.JoiningSpectrum
public import Mixing.JoiningExtreme
public import Mixing.StrongMixing
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

noncomputable section

namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology

variable {G X K : Type*} [CommGroup G] [MeasurableSpace X]
variable [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
variable [MeasurableSpace K] [BorelSpace K]

/-- A compact abelian rotation with its translation-invariant probability measure. -/
def compactRotation (a : G →* K) (ν : Measure K)
    [IsProbabilityMeasure ν] [IsMulLeftInvariant ν] : System G K where
  measure := ν
  probability := inferInstance
  act g x := a g * x
  act_one := by funext x; simp
  act_mul := by intro g k; funext x; simp [mul_assoc]
  preserves g := measurePreserving_mul_left ν (a g)

variable [CompactSpace K]

private def compactRotationMap (t : K) : C(K, K) :=
  ⟨fun x ↦ t * x, continuous_const.mul continuous_id⟩

omit [T2Space K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] in
private theorem continuous_compactRotationMap : Continuous (compactRotationMap (K := K)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (by
    change Continuous (fun z : K × K ↦ z.1 * z.2)
    exact continuous_fst.mul continuous_snd)

/-- On a compact rotation every weak Koopman ultrafilter limit is itself
pullback by a rotation. -/
theorem compactRotation_ultrafilterOperator_apply (a : G →* K) (ν : Measure K)
    [IsProbabilityMeasure ν] [IsMulLeftInvariant ν] [ν.InnerRegularCompactLTTop]
    (p : Ultrafilter G) (f : Lp ℂ 2 ν) :
    ultrafilterOperator (compactRotation a ν).koopmanRep p f =
      Lp.compMeasurePreserving (fun x ↦ Ultrafilter.extend a p * x)
        (measurePreserving_mul_left ν (Ultrafilter.extend a p)) f := by
  let t := Ultrafilter.extend a p
  have hlim : Tendsto (fun g ↦ (compactRotation a ν).koopmanRep g f) (p : Filter G)
      (𝓝 (Lp.compMeasurePreserving (fun x ↦ t * x) (measurePreserving_mul_left ν t) f)) := by
    have hrot := (continuous_compactRotationMap.tendsto t).comp (tendsto_ultrafilterExtend a p)
    exact tendsto_const_nhds.compMeasurePreservingLp hrot
      (fun g ↦ measurePreserving_mul_left ν (a g)) (measurePreserving_mul_left ν t) (by norm_num)
  apply ext_inner_left ℂ
  intro h
  exact tendsto_nhds_unique
    (tendsto_ultrafilterOperator_coeff (compactRotation a ν).koopmanRep p h f)
    (((InnerProductSpace.toDual ℂ _ h).continuous.tendsto _).comp hlim)

theorem injective_compactRotation_ultrafilterOperator_zero (a : G →* K) (ν : Measure K)
    [IsProbabilityMeasure ν] [IsMulLeftInvariant ν] [ν.InnerRegularCompactLTTop] (p : Ultrafilter G) :
    Function.Injective (ultrafilterOperator (compactRotation a ν).koopmanZeroRep p) := by
  let T := compactRotation a ν
  have hi : Intertwines T.koopmanZeroRep T.koopmanRep (meanZero ν).subtypeL :=
    fun _ _ ↦ rfl
  have hinj : Function.Injective (ultrafilterOperator T.koopmanRep p) := by
    intro f h he
    change ultrafilterOperator (compactRotation a ν).koopmanRep p f =
      ultrafilterOperator (compactRotation a ν).koopmanRep p h at he
    rw [compactRotation_ultrafilterOperator_apply a ν p f,
      compactRotation_ultrafilterOperator_apply a ν p h] at he
    exact (Lp.isometry_compMeasurePreserving (p := 2) (E := ℂ)
      (measurePreserving_mul_left ν (Ultrafilter.extend a p))).injective he
  intro f h he
  apply Subtype.ext
  apply hinj
  have he' := congrArg (meanZero ν).subtypeL he
  exact (hi.ultrafilter p f).symm.trans (he'.trans (hi.ultrafilter p h))

/-- The forward implication of Theorem 1.1(ii), for compact abelian rotations
with their regular Haar probability measure. -/
theorem disjoint_compactRotation_of_weaklyMixing [Countable G] (S : System G X)
    (hS : IsWeaklyMixing S.koopmanZeroRep)
    (a : G →* K) (ν : Measure K)
    [IsProbabilityMeasure ν] [IsMulLeftInvariant ν] [ν.InnerRegularCompactLTTop] :
    Disjoint S (compactRotation a ν) := by
  obtain ⟨p, hp⟩ := S.exists_isUMixing_singleton hS
  exact disjoint_of_spectrallyDisjoint <| SpectrallyDisjoint.symm <|
    spectrallyDisjoint_of_ultrafilterOperator_injective (compactRotation a ν).koopmanZeroRep
      S.koopmanZeroRep p (injective_compactRotation_ultrafilterOperator_zero a ν p)
      (hp p (mem_singleton p))

end Mixing
