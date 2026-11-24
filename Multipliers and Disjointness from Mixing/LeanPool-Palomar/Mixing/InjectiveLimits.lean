module

public import Mixing.MainTheorems
public import Mixing.PartialRigidity

@[expose] public section

namespace Mixing

open MeasureTheory Set Filter
open scoped Topology

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

theorem System.ultrafilterOperator_constantOne (S : System G X) (p : Ultrafilter G) :
    ultrafilterOperator S.koopmanRep p (constantOne S.measure) = constantOne S.measure := by
  apply ext_inner_left ℂ
  intro f
  have hlim := tendsto_ultrafilterOperator_coeff S.koopmanRep p f (constantOne S.measure)
  have hEq : (fun g ↦ inner ℂ f (S.koopmanRep g (constantOne S.measure))) =
      fun _ ↦ inner ℂ f (constantOne S.measure) := by
    funext g
    exact congrArg (inner ℂ f) (S.koopman_constantOne g)
  rw [hEq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem System.injective_full_limit_of_injective_meanZero (S : System G X) (p : Ultrafilter G)
    (h : Function.Injective (ultrafilterOperator S.koopmanZeroRep p)) :
    Function.Injective (ultrafilterOperator S.koopmanRep p) := by
  let A := ultrafilterOperator S.koopmanRep p
  let A₀ := ultrafilterOperator S.koopmanZeroRep p
  have hsub : Intertwines S.koopmanZeroRep S.koopmanRep (meanZero S.measure).subtypeL :=
    fun _ _ ↦ rfl
  intro f k he
  let v := f - k
  have hv : A v = 0 := by simp [A, v, he]
  rw [← sub_eq_zero]
  change v = 0
  let v₀ := center S.measure v
  let c := inner ℂ (constantOne S.measure) v
  have hdecomp : v = (v₀ : Lp ℂ 2 S.measure) + c • constantOne S.measure :=
    eq_center_add S.measure v
  have hv₀ : A (v₀ : Lp ℂ 2 S.measure) = (A₀ v₀ : meanZero S.measure) :=
    (hsub.ultrafilter p v₀).symm
  rw [hdecomp, map_add, map_smul, S.ultrafilterOperator_constantOne p, hv₀] at hv
  have hzero : inner ℂ (constantOne S.measure) (A₀ v₀ : Lp ℂ 2 S.measure) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A₀ v₀).property
  have hc := congrArg (inner ℂ (constantOne S.measure)) hv
  rw [inner_add_right, hzero, zero_add, inner_smul_right, inner_constantOne_self,
    mul_one, inner_zero_right] at hc
  rw [hc, zero_smul, add_zero] at hv hdecomp
  have hv' : A₀ v₀ = 0 := Subtype.ext hv
  have hv₀' : v₀ = 0 := h (hv'.trans (map_zero A₀).symm)
  rw [hdecomp, hv₀']
  rfl

/-- The two final conclusions of Proposition 7 follow from injectivity on the
mean-zero space. This statement also applies to the polynomial case of Example 2. -/
theorem System.generated_and_spectrallyDisjoint_of_injective_limit
    (S : System G X) (p : Ultrafilter G)
    (h : Function.Injective (ultrafilterOperator S.koopmanZeroRep p)) :
    S.generatedSigma {p} = (inferInstance : MeasurableSpace X) ∧
      ∀ {Y : Type*} [MeasurableSpace Y] (T : System G Y), T.IsUMixing {p} →
        SpectrallyDisjoint S.koopmanZeroRep T.koopmanZeroRep := by
  constructor
  · apply System.generatedSigma_eq_of_isUGenerated
    apply System.isUGenerated_of_koopmanIsUGenerated
    apply (isUGenerated_iff _ _).2
    rw [Submodule.eq_bot_iff]
    intro f hf
    simp only [mixingSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] at hf
    have hf0 : ultrafilterOperator S.koopmanRep p f = 0 :=
      hf ⟨p, mem_singleton p⟩
    exact S.injective_full_limit_of_injective_meanZero p h (hf0.trans (map_zero _).symm)
  · intro Y _ T hT
    exact spectrallyDisjoint_of_ultrafilterOperator_injective S.koopmanZeroRep T.koopmanZeroRep
      p h (hT p (mem_singleton p))

end Mixing
