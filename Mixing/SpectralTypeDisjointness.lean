/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CyclicIntertwiner
public import Mixing.FourierUniqueness
public import Mixing.SpectralTypeTheorem
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.MeasureTheory.Function.Holder

/-! # Spectral disjointness and the maximal spectral measures -/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ComplexConjugate ENNReal InnerProductSpace Mixing Topology

namespace Mixing

variable {G H K : Type*} [CommGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (V : G →* (K ≃ₗᵢ[ℂ] K))

/-- The image of a vector under an intertwiner has the same spectral measure
as the image under the positive factor of that intertwiner. -/
theorem dualVectorSpectralMeasure_intertwiner_eq (J : H →L[ℂ] K)
    (hJ : Intertwines U V J) (x : H) :
    dualVectorSpectralMeasure V (J x) =
      dualVectorSpectralMeasure U (CFC.sqrt (J.adjoint.comp J) x) := by
  let A := J.adjoint.comp J
  let B := CFC.sqrt A
  have hA : 0 ≤ A := ContinuousLinearMap.nonneg_iff_isPositive.mpr J.isPositive_adjoint_comp_self
  have hBsa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hBsq : B * B = A := CFC.sqrt_mul_sqrt_self A hA
  have hComm (g : G) : Commute A (linearRepresentation U g) := by
    show A * linearRepresentation U g = linearRepresentation U g * A
    ext z
    change J.adjoint (J (U g z)) = U g (J.adjoint (J z))
    rw [hJ g z, hJ.adjoint g (J z)]
  have hBComm (g : G) : Commute B (linearRepresentation U g) := by
    dsimp only [B]
    rw [CFC.sqrt_eq_real_sqrt A hA]
    exact (hComm g).cfcₙ_real Real.sqrt
  apply eq_of_spectralFourier_eq
  intro g
  rw [spectralFourier_dualVectorSpectralMeasure, spectralFourier_dualVectorSpectralMeasure]
  change ⟪J x, V g (J x)⟫_ℂ = ⟪B x, U g (B x)⟫_ℂ
  have hCommx : B (U g x) = U g (B x) :=
    DFunLike.congr_fun (hBComm g).eq x
  calc
    _ = ⟪J x, J (U g x)⟫_ℂ := by rw [hJ]
    _ = ⟪x, A (U g x)⟫_ℂ := (J.adjoint_inner_right _ _).symm
    _ = ⟪x, B (B (U g x))⟫_ℂ := by rw [← hBsq]; rfl
    _ = ⟪x, B (U g (B x))⟫_ℂ := by rw [hCommx]
    _ = _ := by
      have h := B.adjoint_inner_right x (U g (B x))
      rw [show B.adjoint = B from hBsa.star_eq] at h
      exact h

set_option maxHeartbeats 1200000 in
omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
/-- Matrix coefficients in the cyclic spectral representation are weighted
integrals with weight equal to the squared modulus of the input vector. -/
theorem inner_cyclicSpectralIsometry_diag (x : H) (g : G)
    (w : Lp ℂ 2 (vectorSpectralMeasure U x)) :
    ⟪cyclicSpectralIsometry U x w, U g (cyclicSpectralIsometry U x w)⟫_ℂ =
      ∫ z, conj (w z) * (spectralCoefficient U g z * w z) ∂vectorSpectralMeasure U x := by
  let μ := vectorSpectralMeasure U x
  let f := spectralCoefficient U g
  have hf : MemLp f ∞ μ := MemLp.of_bound f.continuous.aestronglyMeasurable 1
    (.of_forall fun z => by simp [f, spectralCoefficient_apply, Circle.norm_coe])
  let a := hf.toLp f
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun b => a • b
      map_add' := Lp.add_smul a
      map_smul' := fun c b => (Lp.smul_comm c a b).symm }
  let M := L.mkContinuous ‖a‖ (fun b => Lp.norm_smul_le (r := 2) a b)
  let C := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let E := cyclicSpectralIsometry U x
  have hD := ContinuousMap.toLp_denseRange (p := 2) ℂ μ ℂ ENNReal.ofNat_ne_top
  have hM (b : C(RepresentationSpectrum U, ℂ)) : M (C b) = C (f * b) := by
    apply Lp.ext
    change (a • C b : Lp ℂ 2 μ) =ᵐ[μ] C (f * b)
    filter_upwards [Lp.coeFn_lpSMul (r := 2) a (C b), hf.coeFn_toLp,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ b,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (f * b)] with z hz ha hb hc
    rw [hz, hc]
    change a z * (C b) z = f z * b z
    exact congrArg₂ (· * ·) ha hb
  have hE : (fun b => E (M b)) ∘ C = (fun b => U g (E b)) ∘ C := by
    funext b
    change cyclicSpectralIsometry U x (M (C b)) = U g (cyclicSpectralIsometry U x (C b))
    rw [hM, cyclicSpectralIsometry_toLp, cyclicSpectralIsometry_toLp, map_mul]
    change spectralCalculus U f (spectralCalculus U b x) = U g (spectralCalculus U b x)
    rw [show spectralCalculus U f = linearRepresentation U g from spectralCalculus_spectralCoefficient U g]
    rfl
  have hEw : E (M w) = U g (E w) := congrFun
    (hD.equalizer (E.continuous.comp M.continuous) ((U g).continuous.comp E.continuous) hE) w
  change ⟪E w, U g (E w)⟫_ℂ = _
  rw [← hEw, E.inner_map_map, L2.inner_def]
  apply integral_congr_ae
  have hMw := Lp.coeFn_lpSMul (r := 2) a w
  filter_upwards [hMw, hf.coeFn_toLp] with z hz ha
  change inner ℂ (w z) ((a • w : Lp ℂ 2 μ) z) = _
  rw [hz, RCLike.inner_apply']
  change conj (w z) * (a z * w z) = conj (w z) * (f z * w z)
  rw [ha]

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
/-- Every finite positive measure dominated by a vector spectral measure is
itself a vector spectral measure in the same representation. -/
theorem exists_dualVectorSpectralMeasure_eq_of_ac [Countable G] (x : H) (ν : Measure (DiscreteDual G))
    [IsFiniteMeasure ν] (hν : ν ≪ dualVectorSpectralMeasure U x) :
    ∃ y : H, dualVectorSpectralMeasure U y = ν := by
  let μ := vectorSpectralMeasure U x
  let σ := dualVectorSpectralMeasure U x
  let e := spectralPointDual U
  let ρ (χ : DiscreteDual G) := (ν.rnDeriv σ χ).toReal
  let w (z : RepresentationSpectrum U) : ℂ := Real.sqrt (ρ (e z))
  have he : Measurable e := (spectralPointDual_continuous U).measurable
  have hρ : Measurable ρ := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hwm : Measurable w := Complex.continuous_ofReal.measurable.comp
    (Real.continuous_sqrt.measurable.comp (hρ.comp he))
  have hw_sq (z : RepresentationSpectrum U) : ‖w z‖ ^ 2 = ρ (e z) := by
    rw [show ‖w z‖ = |Real.sqrt (ρ (e z))| from Complex.norm_real _,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]
  have hw : MemLp w 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).mpr
    simp only [hw_sq]
    change Integrable ((fun χ => (ν.rnDeriv σ χ).toReal) ∘ e) μ
    exact (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := σ)).comp_measurable he
  let v := hw.toLp w
  refine ⟨cyclicSpectralIsometry U x v, eq_of_spectralFourier_eq _ _ ?_⟩
  intro g
  rw [spectralFourier_dualVectorSpectralMeasure, inner_cyclicSpectralIsometry_diag]
  have hIntegrand : (fun z => conj (v z) * (spectralCoefficient U g z * v z)) =ᵐ[μ]
      fun z => (ρ (e z) : ℂ) * (dualEvaluation g (e z) : ℂ) := by
    filter_upwards [hw.coeFn_toLp] with z hz
    change v z = w z at hz
    rw [hz]
    have hStar : conj (w z) = w z := Complex.conj_ofReal _
    rw [hStar]
    change w z * ((dualEvaluation g (e z) : ℂ) * w z) = _
    have hSquare : w z * w z = (ρ (e z) : ℂ) := by
      rw [show w z = (Real.sqrt (ρ (e z)) : ℂ) from rfl, ← Complex.ofReal_mul,
        Real.mul_self_sqrt ENNReal.toReal_nonneg]
    calc
      _ = (w z * w z) * (dualEvaluation g (e z) : ℂ) := by ring
      _ = _ := by rw [hSquare]
  have hMeas : Measurable fun χ => (ρ χ : ℂ) * (dualEvaluation g χ : ℂ) :=
    (Complex.continuous_ofReal.measurable.comp hρ).mul
      (continuous_subtype_val.comp (dualEvaluation g).continuous).measurable
  calc
    _ = ∫ z, (ρ (e z) : ℂ) * (dualEvaluation g (e z) : ℂ) ∂μ := integral_congr_ae hIntegrand
    _ = ∫ χ, (ρ χ : ℂ) * (dualEvaluation g χ : ℂ) ∂σ :=
      (integral_map he.aemeasurable hMeas.aestronglyMeasurable).symm
    _ = _ := integral_rnDeriv_smul hν

/-- Mutually singular maximal spectral measures exclude all nonzero intertwiners. -/
theorem spectrallyDisjoint_of_maximalSpectralVectors_mutuallySingular
    (x : H) (y : K) (hx : IsMaximalSpectralVector U x) (hy : IsMaximalSpectralVector V y)
    (hSing : dualVectorSpectralMeasure U x ⟂ₘ dualVectorSpectralMeasure V y) :
    SpectrallyDisjoint U V := by
  intro J hJ
  ext z
  have hEq := dualVectorSpectralMeasure_intertwiner_eq V U J hJ z
  have hAc : dualVectorSpectralMeasure U (J z) ≪ dualVectorSpectralMeasure V y := by
    rw [hEq]
    exact hy _
  have hSing' := hSing.mono_ac (hx (J z)) Measure.AbsolutelyContinuous.rfl
  have hZero := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hAc hSing'
  have hMass : dualVectorSpectralMeasure U (J z) univ = 0 := by simp [hZero]
  simp only [dualVectorSpectralMeasure_univ, ENNReal.ofReal_eq_zero] at hMass
  have hz : J z = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (J z)])
  simpa only [zero_apply] using hz

/-- The characterization from Section 2.3, expressed using representatives
of the maximal spectral types of the two unitary representations. -/
theorem spectrallyDisjoint_iff_maximalSpectralVectors_mutuallySingular [Countable G]
    (x : H) (y : K) (hx : IsMaximalSpectralVector U x) (hy : IsMaximalSpectralVector V y) :
    SpectrallyDisjoint U V ↔ dualVectorSpectralMeasure U x ⟂ₘ dualVectorSpectralMeasure V y := by
  refine ⟨?_, spectrallyDisjoint_of_maximalSpectralVectors_mutuallySingular U V x y hx hy⟩
  intro hd
  by_contra hn
  let μ := dualVectorSpectralMeasure U x
  let ν := dualVectorSpectralMeasure V y
  let γ := ν.withDensity (μ.rnDeriv ν)
  have hγU : γ ≤ μ := Measure.withDensity_rnDeriv_le μ ν
  let _ : IsFiniteMeasure γ := isFiniteMeasure_of_le μ hγU
  have hγV : γ ≪ ν := withDensity_absolutelyContinuous _ _
  have hγ : γ ≠ 0 := by
    intro h0
    have h := Measure.singularPart_add_rnDeriv μ ν
    change μ.singularPart ν + γ = μ at h
    rw [h0, add_zero] at h
    exact hn ((Measure.singularPart_eq_self).mp h)
  obtain ⟨u, hu⟩ := exists_dualVectorSpectralMeasure_eq_of_ac U x γ (Measure.absolutelyContinuous_of_le hγU)
  obtain ⟨v, hv⟩ := exists_dualVectorSpectralMeasure_eq_of_ac V y γ hγV
  have hu' : u ≠ 0 := by
    intro h0
    apply hγ
    rw [← hu, h0, ← Measure.measure_univ_eq_zero, dualVectorSpectralMeasure_univ]
    simp
  have hCoeff (g : G) : ⟪u, U g u⟫_ℂ = ⟪v, V g v⟫_ℂ := by
    rw [← spectralFourier_dualVectorSpectralMeasure, ← spectralFourier_dualVectorSpectralMeasure, hu, hv]
  exact (not_spectrallyDisjoint_of_equal_diagonal_coefficients U V u v hu' hCoeff) hd

/-- In separable Hilbert spaces spectral disjointness is mutual singularity
of the maximal spectral types. -/
theorem spectrallyDisjoint_iff_maximalSpectralTypes_mutuallySingular [Countable G]
    [SeparableSpace H] [SeparableSpace K] :
    SpectrallyDisjoint U V ↔
      ∀ μ ∈ maximalSpectralType U, ∀ ν ∈ maximalSpectralType V, μ ⟂ₘ ν := by
  constructor
  · rintro h μ ⟨_, x, hx, hμ, _⟩ ν ⟨_, y, hy, hν, _⟩
    exact ((spectrallyDisjoint_iff_maximalSpectralVectors_mutuallySingular U V x y hx hy).mp h).mono_ac hμ hν
  · intro h
    obtain ⟨x, hx⟩ := exists_isMaximalSpectralVector U
    obtain ⟨y, hy⟩ := exists_isMaximalSpectralVector V
    apply (spectrallyDisjoint_iff_maximalSpectralVectors_mutuallySingular U V x y hx hy).mpr
    exact h _ ⟨inferInstance, x, hx, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
      _ ⟨inferInstance, y, hy, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩

end Mixing
