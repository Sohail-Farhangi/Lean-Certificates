/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ToralNilrotation
public import Mixing.CantorEigenvectors
public import Mixing.CantorLebesgueSpectrum
public import Mixing.PurePointLebesgue

/-! # Fourier modes for the toral skew shift -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace Mixing.ToralNilrotation

local notation "m" => (AddCircle.haarAddCircle : Measure UnitAddCircle)

variable (α : UnitAddCircle)

/-- Translate a pair of frequencies to the finite-coordinate Fourier index. -/
def modeIndex (u : ℤ × ℤ) : Fin 2 → ℤ := fun i => if i = 0 then u.1 else u.2

@[simp] theorem modeIndex_zero (u : ℤ × ℤ) : modeIndex u 0 = u.1 := rfl
@[simp] theorem modeIndex_one (u : ℤ × ℤ) : modeIndex u 1 = u.2 := rfl

/-- The complex torus character with horizontal and vertical frequencies. -/
noncomputable def mode (u : ℤ × ℤ) : Lp ℂ 2 (system α).measure :=
  circlePairFourierLp (system α).measure (modeIndex u)

theorem mode_ae (u : ℤ × ℤ) :
    mode α u =ᵐ[(system α).measure] fun x => fourier u.1 x.1 * fourier u.2 x.2 := by
  change (circlePairFourierLp (system α).measure (modeIndex u)) =ᵐ[(system α).measure]
    example5CantorCharacter u.1 u.2
  simpa only [modeIndex_zero, modeIndex_one] using
    circlePairFourierLp_ae_eq (system α).measure (modeIndex u)

theorem mode_dense : (Submodule.span ℂ (range (mode α))).topologicalClosure = ⊤ := by
  have he : range (mode α) = range (circlePairFourierLp (system α).measure) := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨modeIndex u, rfl⟩
    · rintro _ ⟨n, rfl⟩
      refine ⟨(n 0, n 1), ?_⟩
      have h : modeIndex (n 0, n 1) = n := by funext i; fin_cases i <;> simp
      rw [mode, h]
  rw [he]
  exact circlePairFourierLp_closure_span _

theorem inner_mode (u v : ℤ × ℤ) :
    ⟪mode α u, mode α v⟫_ℂ = if u = v then 1 else 0 := by
  classical
  rw [L2.inner_def]
  have he : (∫ x, inner ℂ (mode α u x) (mode α v x) ∂(system α).measure) =
      ∫ x : Torus, fourier (v.1-u.1) x.1 * fourier (v.2-u.2) x.2 ∂(m).prod m := by
    apply integral_congr_ae
    filter_upwards [mode_ae α u, mode_ae α v] with x hu hv
    rw [hu, hv, RCLike.inner_apply', map_mul, ← fourier_neg, ← fourier_neg]
    simp only [sub_eq_add_neg, fourier_add]
    ring
  rw [he, integral_prod_mul (fun x => fourier (v.1-u.1) x) (fun y => fourier (v.2-u.2) y)]
  by_cases h₁ : u.1 = v.1
  · by_cases h₂ : u.2 = v.2
    · have h : u = v := Prod.ext h₁ h₂
      subst v
      simp
    · rw [integral_haar_fourier_zero _ (sub_ne_zero.mpr (Ne.symm h₂)), mul_zero,
        ite_eq_right (fun h => h₂ (congrArg Prod.snd h))]
  · rw [integral_haar_fourier_zero _ (sub_ne_zero.mpr (Ne.symm h₁)), zero_mul,
      ite_eq_right (fun h => h₁ (congrArg Prod.fst h))]

theorem mode_orthonormal : Orthonormal ℂ (mode α) := by
  constructor
  · intro u
    have hr : ‖mode α u‖ ^ 2 = 1 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_mode, ite_eq_left rfl, RCLike.one_re]
    nlinarith [norm_nonneg (mode α u)]
  · intro u v huv
    rw [inner_mode, ite_eq_right huv]

theorem eq_zero_of_mode_inner (x : Lp ℂ 2 (system α).measure)
    (hx : ∀ u, ⟪mode α u, x⟫_ℂ = 0) : x = 0 := by
  let L := innerSL ℂ x
  have hB : range (mode α) ⊆ L.ker := by
    rintro _ ⟨u, rfl⟩
    change ⟪x, mode α u⟫_ℂ = 0
    rw [← inner_conj_symm, hx, map_zero]
  have hK := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hB) L.isClosed_ker
  rw [mode_dense] at hK
  exact inner_self_eq_zero.mp (hK (Submodule.mem_top (x := x)))

private theorem right_translatingElement_zpow (g : Multiplicative ℤ) :
    (translatingElement α ^ g.toAdd).right.toAdd = g.toAdd := by
  have h := congrArg Multiplicative.toAdd
    ((SemidirectProduct.rightHom (φ := shearAction)).map_zpow (translatingElement α) g.toAdd)
  change (translatingElement α ^ g.toAdd).right.toAdd = g.toAdd • (1 : ℤ) at h
  simpa using h

private theorem base_translatingElement_zpow (g : Multiplicative ℤ) :
    (translatingElement α ^ g.toAdd).left.toAdd.1 = g.toAdd • α := by
  have h := congrArg (fun x : Multiplicative (UnitAddCircle × ℤ) => x.toAdd.1)
    (abelianProjection.map_zpow (translatingElement α) g.toAdd)
  exact h

/-- The scalar phase from the translating element's toral coordinates. -/
noncomputable def phase (g : Multiplicative ℤ) (u : ℤ × ℤ) : ℂ :=
  let x := (translatingElement α ^ g.toAdd).left.toAdd
  fourier u.1 x.1 * fourier u.2 x.2

theorem norm_phase (g : Multiplicative ℤ) (u : ℤ × ℤ) : ‖phase α g u‖ = 1 := by
  simp only [phase, norm_mul, fourier_apply, Circle.norm_coe, mul_one]

/-- The skew shift advances each nonzero vertical Fourier mode in its
horizontal direction, with an explicit unit-norm phase. -/
theorem koopman_mode (g : Multiplicative ℤ) (u : ℤ × ℤ) :
    (system α).koopmanRep g (mode α u) =
      phase α g u • mode α (u.1+u.2*g.toAdd, u.2) := by
  let b := (u.1+u.2*g.toAdd, u.2)
  let a := translatingElement α ^ g.toAdd
  have hp : (system α).koopmanRep g (mode α u) =ᵐ[(system α).measure]
      fun x => fourier u.1 ((system α).act g x).1 * fourier u.2 ((system α).act g x).2 :=
    (Lp.coeFn_compMeasurePreserving _ ((system α).preserves g)).trans
      (((system α).preserves g).quasiMeasurePreserving.ae_eq_comp (mode_ae α u))
  apply Lp.ext
  filter_upwards [hp, Lp.coeFn_smul (phase α g u) (mode α b), mode_ae α b] with x hx hS hB
  rw [hx, hS, Pi.smul_apply, hB]
  change fourier u.1 (a.left.toAdd.1 + x.1) *
      fourier u.2 (a.left.toAdd.2 + (x.2 + a.right.toAdd • x.1)) =
    (fourier u.1 a.left.toAdd.1 * fourier u.2 a.left.toAdd.2) *
      (fourier (u.1+u.2*g.toAdd) x.1 * fourier u.2 x.2)
  have h : a.right.toAdd = g.toAdd := right_translatingElement_zpow α g
  rw [h]
  simp_rw [fourier_circle_add, fourier_circle_zsmul, fourier_add]
  ring

private noncomputable def horizontalCharacter (k : ℤ) : Multiplicative ℤ →* Circle where
  toFun g := AddCircle.toCircle (k • (g.toAdd • α))
  map_one' := by change AddCircle.toCircle (k • ((0 : ℤ) • α)) = 1; simp
  map_mul' g h := by
    change AddCircle.toCircle (k • ((g.toAdd + h.toAdd) • α)) =
      AddCircle.toCircle (k • (g.toAdd • α)) * AddCircle.toCircle (k • (h.toAdd • α))
    rw [add_zsmul, zsmul_add, AddCircle.toCircle_add]

theorem horizontal_mode_eigen (k : ℤ) :
    mode α (k, 0) ∈ unitaryEigenvectors (system α).koopmanRep := by
  refine ⟨horizontalCharacter α k, fun g => ?_⟩
  rw [koopman_mode]
  simp only [zero_mul, add_zero, phase, base_translatingElement_zpow, fourier_apply,
    zero_zsmul, AddCircle.toCircle_zero, Circle.coe_one, mul_one]
  rfl

theorem vertical_mode_killed (u : ℤ × ℤ) (hu : u.2 ≠ 0) (p : Ultrafilter (Multiplicative ℤ))
    (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    ultrafilterOperator (system α).koopmanRep p (mode α u) = 0 := by
  apply eq_zero_of_mode_inner
  intro v
  have hLim := tendsto_ultrafilterOperator_coeff (system α).koopmanRep p (mode α v) (mode α u)
  have hZero : ∀ᶠ g in (p : Filter (Multiplicative ℤ)),
      ⟪mode α v, (system α).koopmanRep g (mode α u)⟫_ℂ = 0 := by
    have hInjective : Function.Injective (fun g : Multiplicative ℤ => u.1 + u.2 * g.toAdd) := by
      intro g h he
      have he' : g.toAdd = h.toAdd := mul_left_cancel₀ hu (add_left_cancel he)
      exact Multiplicative.ext he'
    have hFinite : {g : Multiplicative ℤ | u.1 + u.2 * g.toAdd = v.1}.Finite :=
      (Set.finite_singleton v.1).preimage hInjective.injOn
    filter_upwards [hp hFinite.compl_mem_cofinite] with g hg
    have hNe : v ≠ (u.1 + u.2 * g.toAdd, u.2) := fun he => hg (congrArg Prod.fst he).symm
    rw [koopman_mode, inner_smul_right, inner_mode, ite_eq_right hNe, mul_zero]
  exact tendsto_nhds_unique hLim (tendsto_const_nhds.congr' (hZero.mono fun _ h => h.symm))

/-- All the free-ultrafilter images are precisely the Kronecker subspace. -/
theorem ultrafilter_range_eq_purePointPart (p : Ultrafilter (Multiplicative ℤ))
    (hp : p ∈ freeUltrafilters (Multiplicative ℤ)) :
    (ultrafilterOperator (system α).koopmanRep p).range = purePointPart (system α).koopmanRep := by
  let U := (system α).koopmanRep
  let A := ultrafilterOperator U p
  let W := purePointPart U
  have hA : (range (mode α)) ⊆ W.comap A.toLinearMap := by
    rintro _ ⟨u, rfl⟩
    change A (mode α u) ∈ W
    by_cases hu : u.2 = 0
    · have he : u = (u.1, 0) := Prod.ext rfl hu
      rw [he]
      apply ultrafilterOperator_mem_purePointPart U p
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (horizontal_mode_eigen α u.1))
    · rw [show A (mode α u) = 0 from vertical_mode_killed α u hu p hp]
      exact W.zero_mem
  have hall := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hA)
    ((isClosed_purePointPart U).preimage A.continuous)
  rw [mode_dense α] at hall
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact hall (Submodule.mem_top (x := x))
  · intro x hx
    exact ⟨A.adjoint x, (ultrafilterOperator_purePoint_inverse U p hx).1⟩

/-- The toral nilrotation explicitly satisfies the generated-factor conclusion of Example 1. -/
theorem generatedSigma_eq_kronecker (P : Set (Ultrafilter (Multiplicative ℤ)))
    (hP : P.Nonempty) (hFree : P ⊆ freeUltrafilters (Multiplicative ℤ)) :
    (system α).generatedSigma P = (system α).kroneckerSigma := by
  apply (system α).generatedSigma_eq_sigmaOfSubmodule P hP
  exact fun p hp => ultrafilter_range_eq_purePointPart α p (hFree hp)

/-- Every character with a nonzero vertical frequency has Lebesgue spectral measure. -/
theorem vertical_mode_Lebesgue (u : ℤ × ℤ) (hu : u.2 ≠ 0) :
    integerVectorSpectralMeasure (system α).koopmanRep (mode α u) = m := by
  apply circleMeasure_eq_of_fourier_eq
  intro n
  rw [integral_fourier_integerVectorSpectralMeasure]
  by_cases hn : n = 0
  · subst n
    change ⟪mode α u, (system α).koopmanRep 1 (mode α u)⟫_ℂ = _
    rw [map_one]
    change ⟪mode α u, mode α u⟫_ℂ = _
    rw [inner_mode, ite_eq_left rfl]
    simp
  · rw [integral_haar_fourier_zero n hn, koopman_mode, inner_smul_right, inner_mode]
    have hne : u ≠ (u.1 + u.2*n, u.2) := by
      intro h
      have hh := congrArg Prod.fst h
      dsimp only at hh
      exact (mul_ne_zero hu hn) (by omega)
    simp only [toAdd_ofAdd, ite_eq_right hne, mul_zero]

end Mixing.ToralNilrotation
