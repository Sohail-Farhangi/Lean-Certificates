module

public import Mixing.Koopman

@[expose] public section

noncomputable section

namespace Mixing

open MeasureTheory Set

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable {S : System G X} {T : System G Y} {joining : Measure (X × Y)}

theorem Intertwines.comp {H K L : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [InnerProductSpace ℂ L] {U : G →* (H ≃ₗᵢ[ℂ] H)} {V : G →* (K ≃ₗᵢ[ℂ] K)}
    {W : G →* (L ≃ₗᵢ[ℂ] L)} {J : H →L[ℂ] K} {K' : K →L[ℂ] L}
    (hK : Intertwines V W K') (hJ : Intertwines U V J) :
    Intertwines U W (K'.comp J) := by
  intro g x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hJ g x, hK g (J x)]

/-- The centered correlation operator of a joining, realized by the two factor embeddings. -/
def IsJoining.crossOperator (h : IsJoining S T joining) :
    meanZero T.measure →L[ℂ] meanZero S.measure :=
  h.fstFactor.pullbackZero.adjoint.comp h.sndFactor.pullbackZero

theorem IsJoining.crossOperator_intertwines (h : IsJoining S T joining) :
    Intertwines T.koopmanZeroRep S.koopmanZeroRep h.crossOperator :=
  h.fstFactor.intertwines_pullbackZero.adjoint.comp h.sndFactor.intertwines_pullbackZero

theorem IsJoining.inner_pullbacks (h : IsJoining S T joining)
    (hz : h.crossOperator = 0) (f : Lp ℂ 2 S.measure) (k : Lp ℂ 2 T.measure) :
    inner ℂ (h.fstFactor.pullback f) (h.sndFactor.pullback k) =
      star (∫ x, f x ∂S.measure) * (∫ y, k y ∂T.measure) := by
  let f₀ := center S.measure f
  let k₀ := center T.measure k
  have hleft := h.fstFactor.pullback_mem_meanZero f₀
  have hright := h.sndFactor.pullback_mem_meanZero k₀
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_left] at hleft
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right] at hright
  have hcross : inner ℂ (h.fstFactor.pullback f₀) (h.sndFactor.pullback k₀) = 0 := by
    change inner ℂ (h.fstFactor.pullbackZero f₀) (h.sndFactor.pullbackZero k₀) = 0
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ f₀ (h.crossOperator k₀) = 0
    rw [hz, zero_apply, inner_zero_right]
  have hone : inner ℂ (h.fstFactor.pullback (constantOne S.measure))
      (h.sndFactor.pullback (constantOne T.measure)) = 1 := by
    rw [h.fstFactor.pullback_one, h.sndFactor.pullback_one]
    exact inner_constantOne_self h.system.measure
  have hleft' : inner ℂ (h.fstFactor.pullback f₀)
      (h.sndFactor.pullback (constantOne T.measure)) = 0 := by
    rw [h.sndFactor.pullback_one]
    exact hleft
  have hright' : inner ℂ (h.fstFactor.pullback (constantOne S.measure))
      (h.sndFactor.pullback k₀) = 0 := by
    rw [h.fstFactor.pullback_one]
    exact hright
  change inner ℂ (h.fstFactor.pullback f) (h.sndFactor.pullback k) = _
  have hf := eq_center_add S.measure f
  have hk := eq_center_add T.measure k
  change f = (f₀ : Lp ℂ 2 S.measure) + _ at hf
  change k = (k₀ : Lp ℂ 2 T.measure) + _ at hk
  conv_lhs => rw [hf, hk]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hcross, hleft', hright', hone,
    mul_zero, mul_one, zero_add, add_zero, inner_constantOne_left]
  exact mul_comm _ _

/-- A joining with zero centered correlation operator is the product joining. -/
theorem IsJoining.eq_prod_of_crossOperator_zero (h : IsJoining S T joining)
    (hz : h.crossOperator = 0) : joining = S.measure.prod T.measure := by
  have : IsProbabilityMeasure joining := h.probability
  symm
  apply Measure.prod_eq
  intro A B hA hB
  let f : Lp ℂ 2 S.measure := indicatorConstLp 2 hA (measure_ne_top _ _) 1
  let k : Lp ℂ 2 T.measure := indicatorConstLp 2 hB (measure_ne_top _ _) 1
  have hf : ∫ x, f x ∂S.measure = (S.measure.real A : ℂ) := by
    rw [integral_congr_ae indicatorConstLp_coeFn, integral_indicator hA, setIntegral_const]
    simp
  have hk : ∫ y, k y ∂T.measure = (T.measure.real B : ℂ) := by
    rw [integral_congr_ae indicatorConstLp_coeFn, integral_indicator hB, setIntegral_const]
    simp
  have hinner := h.inner_pullbacks hz f k
  rw [hf, hk, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul] at hinner
  change inner ℂ (Lp.compMeasurePreserving Prod.fst h.fst f)
    (Lp.compMeasurePreserving Prod.snd h.snd k) = _ at hinner
  unfold f k at hinner
  rw [Lp.indicatorConstLp_compMeasurePreserving, Lp.indicatorConstLp_compMeasurePreserving,
    L2.inner_indicatorConstLp_one_indicatorConstLp_one] at hinner
  have hset : Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B = A ×ˢ B := rfl
  rw [hset] at hinner
  have hreal : (joining (A ×ˢ B)).toReal = (S.measure A * T.measure B).toReal := by
    rw [ENNReal.toReal_mul]
    exact Complex.ofReal_injective hinner
  have heq := congrArg ENNReal.ofReal hreal
  rwa [ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))] at heq

/-- The implication from spectral disjointness to Furstenberg disjointness in Section 2.3. -/
theorem disjoint_of_spectrallyDisjoint (hd : SpectrallyDisjoint S.koopmanZeroRep T.koopmanZeroRep) :
    Disjoint S T :=
  fun _ h ↦ h.eq_prod_of_crossOperator_zero (hd _ h.crossOperator_intertwines)

end Mixing
