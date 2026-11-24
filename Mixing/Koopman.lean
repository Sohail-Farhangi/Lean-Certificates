module

public import Mixing.System
public import Mixing.SpectralDisjointness
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section

namespace Mixing

open MeasureTheory Filter
open scoped Topology

universe u

variable {G Y : Type*} {X : Type u} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]

private theorem pullback_congr {μ : Measure X} {ν : Measure Y} {a b : X → Y}
    (ha : MeasurePreserving a μ ν) (hb : MeasurePreserving b μ ν) (hab : a = b)
    (f : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving a ha f = Lp.compMeasurePreserving b hb f := by
  subst b
  rfl

/-- Koopman pullback is composition by the action in the paper's convention. -/
def System.koopman (S : System G X) (g : G) : Lp ℂ 2 S.measure ≃ₗᵢ[ℂ] Lp ℂ 2 S.measure where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (S.act g) (S.preserves g)
  invFun := Lp.compMeasurePreserving (E := ℂ) (p := 2) (S.act g⁻¹) (S.preserves g⁻¹)
  left_inv x := by
    change Lp.compMeasurePreserving _ (S.preserves g⁻¹)
      (Lp.compMeasurePreserving _ (S.preserves g) x) = x
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (pullback_congr _ (MeasurePreserving.id S.measure)
      (by rw [← S.act_mul, mul_inv_cancel, S.act_one]) x).trans
      (Lp.compMeasurePreserving_id_apply x)
  right_inv x := by
    change Lp.compMeasurePreserving _ (S.preserves g)
      (Lp.compMeasurePreserving _ (S.preserves g⁻¹) x) = x
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact (pullback_congr _ (MeasurePreserving.id S.measure)
      (by rw [← S.act_mul, inv_mul_cancel, S.act_one]) x).trans
      (Lp.compMeasurePreserving_id_apply x)

/-- The unitary Koopman representation on the full complex L² space. -/
def System.koopmanRep (S : System G X) : G →* (Lp ℂ 2 S.measure ≃ₗᵢ[ℂ] Lp ℂ 2 S.measure) where
  toFun := S.koopman
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    change Lp.compMeasurePreserving _ (S.preserves 1) x = x
    calc
      _ = Lp.compMeasurePreserving id (MeasurePreserving.id S.measure) x :=
        pullback_congr _ _ S.act_one x
      _ = x := Lp.compMeasurePreserving_id_apply x
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro x
    change Lp.compMeasurePreserving _ (S.preserves (g * h)) x =
      Lp.compMeasurePreserving _ (S.preserves g) (Lp.compMeasurePreserving _ (S.preserves h) x)
    rw [← Lp.compMeasurePreserving_comp_apply]
    exact pullback_congr _ _ (by rw [mul_comm g h, S.act_mul]) x

/-- The vector represented by the constant function one. -/
def constantOne (μ : Measure X) [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  Lp.const 2 μ 1

/-- Orthogonal complement of the constants on the complex L² space. -/
def meanZero (μ : Measure X) [IsFiniteMeasure μ] : Submodule ℂ (Lp ℂ 2 μ) :=
  (ℂ ∙ constantOne μ)ᗮ

instance meanZero_completeSpace (μ : Measure X) [IsFiniteMeasure μ] :
    CompleteSpace (meanZero μ) :=
  (Submodule.isClosed_orthogonal _).completeSpace_coe

theorem inner_constantOne_left (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    inner ℂ (constantOne μ) f = ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ)] with x hx
  change constantOne μ x = _ at hx
  rw [hx]
  simp [RCLike.inner_apply]

/-- The orthogonal complement of constants is exactly the space of mean-zero functions. -/
theorem mem_meanZero_iff_integral (μ : Measure X) [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    f ∈ meanZero μ ↔ ∫ x, f x ∂μ = 0 := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_constantOne_left]

@[simp]
theorem inner_constantOne_self (μ : Measure X) [IsProbabilityMeasure μ] :
    inner ℂ (constantOne μ) (constantOne μ) = 1 := by
  rw [inner_constantOne_left, constantOne,
    integral_congr_ae (Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ))]
  simp

/-- Subtract the mean of an L² function on a probability space. -/
def center (μ : Measure X) [IsProbabilityMeasure μ] (f : Lp ℂ 2 μ) : meanZero μ :=
  ⟨f - inner ℂ (constantOne μ) f • constantOne μ, by
    rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      inner_smul_right, inner_constantOne_self, mul_one, sub_self]⟩

theorem eq_center_add (μ : Measure X) [IsProbabilityMeasure μ] (f : Lp ℂ 2 μ) :
    f = (center μ f : Lp ℂ 2 μ) + inner ℂ (constantOne μ) f • constantOne μ := by
  change f = f - _ + _
  exact (sub_add_cancel _ _).symm

theorem System.koopman_constantOne (S : System G X) (g : G) :
    S.koopman g (constantOne S.measure) = constantOne S.measure := by
  change Lp.compMeasurePreserving _ (S.preserves g) _ = _
  apply Lp.ext
  have hone := Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)
  exact (Lp.coeFn_compMeasurePreserving _ _).trans
    (((S.preserves g).quasiMeasurePreserving.ae_eq_comp hone).trans hone.symm)

theorem System.koopman_mem_meanZero (S : System G X) (g : G) {f : Lp ℂ 2 S.measure}
    (hf : f ∈ meanZero S.measure) : S.koopman g f ∈ meanZero S.measure := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right] at hf ⊢
  rw [← S.koopman_constantOne g, (S.koopman g).inner_map_map]
  exact hf

/-- The Koopman equivalence restricted to the mean-zero subspace. -/
def System.koopmanZero (S : System G X) (g : G) :
    meanZero S.measure ≃ₗᵢ[ℂ] meanZero S.measure where
  toFun f := ⟨S.koopman g f, S.koopman_mem_meanZero g f.property⟩
  invFun f := ⟨S.koopman g⁻¹ f, S.koopman_mem_meanZero g⁻¹ f.property⟩
  left_inv f := by
    apply Subtype.ext
    change (S.koopmanRep g⁻¹ * S.koopmanRep g) (f : Lp ℂ 2 S.measure) = ↑f
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv f := by
    apply Subtype.ext
    change (S.koopmanRep g * S.koopmanRep g⁻¹) (f : Lp ℂ 2 S.measure) = ↑f
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  map_add' f h := Subtype.ext (map_add (S.koopman g) (f : Lp ℂ 2 S.measure) h)
  map_smul' c f := Subtype.ext (map_smul (S.koopman g) c (f : Lp ℂ 2 S.measure))
  norm_map' f := (S.koopman g).norm_map (f : Lp ℂ 2 S.measure)

/-- The Koopman representation on the complex mean-zero L² space. -/
def System.koopmanZeroRep (S : System G X) : G →* (meanZero S.measure ≃ₗᵢ[ℂ] meanZero S.measure) where
  toFun := S.koopmanZero
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Subtype.ext
    change S.koopmanRep 1 _ = _
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearIsometryEquiv.ext
    intro f
    apply Subtype.ext
    change S.koopmanRep (g * h) _ = S.koopmanRep g (S.koopmanRep h _)
    rw [map_mul]
    rfl

/-- The U-mixing condition on the mean-zero Koopman representation. -/
def System.IsUMixing (S : System G X) (P : Set (Ultrafilter G)) : Prop :=
  Mixing.IsUMixing S.koopmanZeroRep P

theorem System.koopman_coeff_eq (S : System G X) (g : G) (f h : Lp ℂ 2 S.measure) :
    inner ℂ f (S.koopmanRep g h) =
      inner ℂ (center S.measure f) (S.koopmanZeroRep g (center S.measure h)) +
        star (inner ℂ (constantOne S.measure) f) * inner ℂ (constantOne S.measure) h := by
  let f₀ := center S.measure f
  let h₀ := center S.measure h
  let c := constantOne S.measure
  have hf : inner ℂ (f₀ : Lp ℂ 2 S.measure) c = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp f₀.property
  have hh : inner ℂ c (S.koopman g h₀) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (S.koopman_mem_meanZero g h₀.property)
  have hfc := eq_center_add S.measure f
  have hhc := eq_center_add S.measure h
  change inner ℂ (center S.measure f : Lp ℂ 2 S.measure) (constantOne S.measure) = 0 at hf
  change inner ℂ (constantOne S.measure)
    (S.koopman g (center S.measure h : Lp ℂ 2 S.measure)) = 0 at hh
  change inner ℂ f (S.koopman g h) =
    inner ℂ (f₀ : Lp ℂ 2 S.measure) (S.koopman g h₀) + star (inner ℂ c f) * inner ℂ c h
  conv_lhs =>
    rw [hfc, hhc]
  simp only [map_add, map_smul, S.koopman_constantOne, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, hf, hh, inner_constantOne_self,
    mul_zero, mul_one, zero_add, add_zero]
  rw [mul_comm (inner ℂ (constantOne S.measure) h)]
  rfl

/-- U-mixing is convergence of all Koopman correlations to their independent values. -/
theorem System.isUMixing_iff_lp_correlations (S : System G X) (P : Set (Ultrafilter G)) :
    S.IsUMixing P ↔ ∀ p ∈ P, ∀ f h : Lp ℂ 2 S.measure,
      Tendsto (fun g ↦ inner ℂ f (S.koopmanRep g h)) (p : Filter G)
        (𝓝 (star (∫ x, f x ∂S.measure) * (∫ x, h x ∂S.measure))) := by
  constructor
  · intro hmix p hp f h
    have hlim := tendsto_ultrafilterOperator_coeff S.koopmanZeroRep p
      (center S.measure f) (center S.measure h)
    rw [hmix p hp, zero_apply, inner_zero_right] at hlim
    simpa only [S.koopman_coeff_eq, inner_constantOne_left, zero_add] using
      hlim.add_const (star (∫ x, f x ∂S.measure) * (∫ x, h x ∂S.measure))
  · intro hmix p hp
    apply ContinuousLinearMap.ext
    intro h
    apply ext_inner_left ℂ
    intro f
    have hlim := hmix p hp (f : Lp ℂ 2 S.measure) (h : Lp ℂ 2 S.measure)
    rw [(mem_meanZero_iff_integral _ _).mp f.property,
      (mem_meanZero_iff_integral _ _).mp h.property, star_zero, zero_mul] at hlim
    rw [zero_apply, inner_zero_right]
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff S.koopmanZeroRep p f h) hlim

variable {S : System G X} {T : System G Y}

/-- Isometric pullback on L² induced by a factor map. -/
def FactorMap.pullback (f : FactorMap S T) : Lp ℂ 2 T.measure →ₗᵢ[ℂ] Lp ℂ 2 S.measure :=
  Lp.compMeasurePreservingₗᵢ ℂ f.toFun f.preserves

theorem FactorMap.pullback_one (f : FactorMap S T) :
    f.pullback (constantOne T.measure) = constantOne S.measure := by
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ f.preserves).trans
    ((f.preserves.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_const (p := 2) (μ := T.measure) (1 : ℂ))).trans
      (Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)).symm)

theorem FactorMap.pullback_mem_meanZero (f : FactorMap S T) (x : meanZero T.measure) :
    f.pullback x ∈ meanZero S.measure := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, ← f.pullback_one,
    f.pullback.inner_map_map]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property

theorem FactorMap.pullback_koopman (f : FactorMap S T) (g : G) (x : Lp ℂ 2 T.measure) :
    f.pullback (T.koopmanRep g x) = S.koopmanRep g (f.pullback x) := by
  change Lp.compMeasurePreserving f.toFun f.preserves
      (Lp.compMeasurePreserving _ (T.preserves g) x) =
    Lp.compMeasurePreserving _ (S.preserves g) (Lp.compMeasurePreserving f.toFun f.preserves x)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  exact pullback_congr _ _ (f.equivariant g).symm x

theorem FactorMap.intertwines_pullback (f : FactorMap S T) :
    Intertwines T.koopmanRep S.koopmanRep f.pullback.toContinuousLinearMap :=
  f.pullback_koopman

/-- Pullback on the mean-zero L² spaces of a factor map. -/
def FactorMap.pullbackZero (f : FactorMap S T) : meanZero T.measure →L[ℂ] meanZero S.measure :=
  (f.pullback.toContinuousLinearMap.comp (meanZero T.measure).subtypeL).codRestrict
    (meanZero S.measure) f.pullback_mem_meanZero

theorem FactorMap.intertwines_pullbackZero (f : FactorMap S T) :
    Intertwines T.koopmanZeroRep S.koopmanZeroRep f.pullbackZero :=
  fun g x ↦ Subtype.ext (f.pullback_koopman g x)

/-- The equivalence of Theorem 1.3(i) and its mean-zero Koopman form of (iii). -/
theorem theorem1_3_i_iii (S : System G X) (P : Set (Ultrafilter G)) :
    S.IsUMixing P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUGenerated V P →
        SpectrallyDisjoint S.koopmanZeroRep V :=
  corollary3 S.koopmanZeroRep P

end Mixing
