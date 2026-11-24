/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroCylinderRigidity
public import Mixing.RigidEventBounds
public import Mathlib.MeasureTheory.Measure.MeasuredSets

/-! # Half-rigidity of the measured Rudin–Shapiro shift -/

@[expose] public section
noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology symmDiff

namespace Mixing

/-- A finite-window event is determined by the coordinates in a symmetric finite interval. -/
def finiteWindowEvents : Set (Set SignWords) :=
  {A | ∃ n : ℕ, ∀ x y : SignWords, (∀ i : ℤ, -(n:ℤ) ≤ i → i ≤ n → x i = y i) → (x ∈ A ↔ y ∈ A)}

private theorem finiteWindowEvents_isSetRing : IsSetRing finiteWindowEvents where
  empty_mem := ⟨0, fun _ _ _ => Iff.rfl⟩
  union_mem := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨max a b, fun x y hxy => ?_⟩
    have hA := ha x y (fun i hl hr => hxy i (by omega) (by omega))
    have hB := hb x y (fun i hl hr => hxy i (by omega) (by omega))
    exact or_congr hA hB
  sdiff_mem := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨max a b, fun x y hxy => ?_⟩
    have hA := ha x y (fun i hl hr => hxy i (by omega) (by omega))
    have hB := hb x y (fun i hl hr => hxy i (by omega) (by omega))
    exact and_congr hA hB.not

private theorem finiteWindowEvents_univ : univ ∈ finiteWindowEvents := ⟨0, fun _ _ _ => Iff.rfl⟩

private theorem finiteWindow_indicator_continuous {A : Set SignWords} (hA : A ∈ finiteWindowEvents) :
    Continuous (A.indicator (fun _ => (1:ℝ))) := by
  classical
  obtain ⟨n, hn⟩ := hA
  let I := Finset.Icc (-(n:ℤ)) (n:ℤ)
  let P : SignWords → (I → Bool) := fun x i => x i.1
  have hP : Continuous P := continuous_pi (fun i => continuous_apply i.1)
  let F : (I → Bool) → ℝ := (P '' A).indicator (fun _ => 1)
  have hF : Continuous F := continuous_of_discreteTopology
  have he (x : SignWords) : P x ∈ P '' A ↔ x ∈ A := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine (hn y x (fun i hl hr => ?_)).mp hy
      exact congrFun hxy ⟨i, Finset.mem_Icc.mpr ⟨hl,hr⟩⟩
    · intro hx
      exact mem_image_of_mem _ hx
  have heq : A.indicator (fun _ => (1:ℝ)) = F ∘ P := by
    ext x
    by_cases hx : x ∈ A
    · simp only [Function.comp_apply, F, indicator_of_mem hx, indicator_of_mem ((he x).2 hx)]
    · simp only [Function.comp_apply, F, indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((he x).1 h))]
  rw [heq]
  exact hF.comp hP

private theorem finiteWindow_measurable {A : Set SignWords} (hA : A ∈ finiteWindowEvents) : MeasurableSet A := by
  classical
  have hf := (finiteWindow_indicator_continuous hA).measurable
  have he : A = A.indicator (fun _ => (1:ℝ)) ⁻¹' {1} := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [he]
  exact hf (measurableSet_singleton 1)

private theorem finiteWindow_generate : (inferInstance : MeasurableSpace SignWords) = MeasurableSpace.generateFrom finiteWindowEvents := by
  apply le_antisymm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨i, A, hA, rfl⟩
    refine ⟨i.natAbs, fun x y hxy => ?_⟩
    have he := hxy i (by omega) (by omega)
    change (x i ∈ A ↔ y i ∈ A)
    rw [he]
  · exact MeasurableSpace.generateFrom_le (fun _ hA => finiteWindow_measurable hA)

/-- The integer sequence of shifts along which the lower bound holds. -/
def rudinShapiroRigidTime (k : ℕ) : Multiplicative ℤ := Multiplicative.ofAdd (2^(k+1)*2 : ℕ)

private theorem finiteWindow_correlation_lower_bound (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    {A : Set SignWords} (hA : A ∈ finiteWindowEvents) :
    ∃ w : ℕ, ∀ k : ℕ, (1/2:ℝ) * (rudinShapiroOrbitLaw p : Measure SignWords).real A ≤
      (rudinShapiroOrbitLaw p : Measure SignWords).real (A ∩ signWordShift (rudinShapiroRigidTime k).toAdd ⁻¹' A) +
        ((w:ℝ)/(2:ℝ)^(k+1))/2 := by
  classical
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  let f : C(SignWords,ℝ) := ⟨A.indicator (fun _ => (1:ℝ)), finiteWindow_indicator_continuous hA⟩
  obtain ⟨n, hn⟩ := hA
  let j : C(SignWords,SignWords) := ⟨signWordShift n, signWordShift_continuous n⟩
  let g := f.comp j
  have hDep : DependsOnPrefix (2*n+1) g := by
    intro x y hxy
    have hEq := hn (signWordShift n x) (signWordShift n y) (fun i hl hr => by
      have hi : (i+(n:ℤ)).toNat < 2*n+1 := by omega
      have he : ((i+(n:ℤ)).toNat:ℤ) = i+n := by omega
      change x (i+n) = y (i+n)
      rw [← he]
      exact hxy _ hi)
    change A.indicator (fun _ => (1:ℝ)) (signWordShift n x) = A.indicator (fun _ => (1:ℝ)) (signWordShift n y)
    by_cases hx : signWordShift n x ∈ A
    · rw [indicator_of_mem hx, indicator_of_mem (hEq.mp hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hEq.mpr h))]
  have h₀ (x : SignWords) : 0 ≤ g x := indicator_nonneg (fun _ _ => zero_le_one) _
  have h₁ (x : SignWords) : g x ≤ 1 := by
    change A.indicator (fun _ => (1:ℝ)) (signWordShift n x) ≤ 1
    exact indicator_le_self' (fun _ _ => zero_le_one) _
  refine ⟨2*n+1, fun k => ?_⟩
  let t := (rudinShapiroRigidTime k).toAdd
  have hPres := rudinShapiroOrbitLaw_preserving p hp n
  have h := rudinShapiro_prefix_correlation_lower_bound p hp g (2*n+1) hDep h₀ h₁ k
  change (1/2:ℝ) * (∫ x, (f (signWordShift n x))^2 ∂μ) ≤
    (∫ x, f (signWordShift n x) * f (signWordShift n (signWordShift t x)) ∂μ) + _ at h
  have hc (x : SignWords) : signWordShift n (signWordShift t x) = signWordShift t (signWordShift n x) := by
    rw [← Function.comp_apply (f := signWordShift n) (g := signWordShift t), ← signWordShift_add,
      add_comm, signWordShift_add, Function.comp_apply]
  simp_rw [hc] at h
  have hComp (F : SignWords → ℝ) (hF : Continuous F) :
      (∫ x, F (signWordShift n x) ∂μ) = ∫ x, F x ∂μ := by
    rw [← integral_map hPres.measurable.aemeasurable hF.aestronglyMeasurable, hPres.map_eq]
  have hInt := hComp (fun x => (f x)^2) (f.continuous.pow 2)
  have hPair := hComp (fun x => f x * f (signWordShift t x))
    (f.continuous.mul (f.continuous.comp (signWordShift_continuous t)))
  rw [hInt, hPair] at h
  have hA' : MeasurableSet A := finiteWindow_measurable ⟨n,hn⟩
  have hE : (∫ x, (f x)^2 ∂μ) = μ.real A := by
    rw [show (fun x => (f x)^2) = A.indicator (fun _ => (1:ℝ)) by
      ext x
      by_cases hx : x ∈ A <;> simp [f, hx]]
    rw [integral_indicator hA', setIntegral_const, smul_eq_mul, mul_one]
  have hP : (∫ x, f x * f (signWordShift t x) ∂μ) = μ.real (A ∩ signWordShift t ⁻¹' A) := by
    have hm : MeasurableSet (A ∩ signWordShift t ⁻¹' A) := hA'.inter (hA'.preimage (signWordShift_continuous t).measurable)
    rw [show (fun x => f x * f (signWordShift t x)) = (A ∩ signWordShift t ⁻¹' A).indicator (fun _ => (1:ℝ)) by
      ext x
      by_cases hx : x ∈ A <;> by_cases hx' : signWordShift t x ∈ A <;> simp [f, hx, hx']]
    rw [integral_indicator hm, setIntegral_const, smul_eq_mul, mul_one]
  rwa [hE, hP] at h

private theorem signWordShift_symmDiff_bound (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    {A C : Set SignWords} (hA : MeasurableSet A) (hC : MeasurableSet C) (t : ℤ) :
    |(rudinShapiroOrbitLaw p : Measure SignWords).real (A ∩ signWordShift t ⁻¹' A) -
      (rudinShapiroOrbitLaw p : Measure SignWords).real (C ∩ signWordShift t ⁻¹' C)| ≤
      2 * (rudinShapiroOrbitLaw p : Measure SignWords).real (C ∆ A) := by
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  let U := signWordShift t
  have hPres := rudinShapiroOrbitLaw_preserving p hp t
  have hD : (A ∩ U ⁻¹' A) ∆ (C ∩ U ⁻¹' C) ⊆ (C ∆ A) ∪ U ⁻¹' (C ∆ A) := by
    intro x
    simp only [symmDiff_def, mem_union, Set.mem_sdiff, mem_inter_iff, mem_preimage]
    tauto
  have h := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ)
    (hA.inter (hA.preimage hPres.measurable)).nullMeasurableSet (hC.inter (hC.preimage hPres.measurable)).nullMeasurableSet
  have hm := (measureReal_mono (μ := μ) hD (measure_ne_top μ _)).trans (measureReal_union_le _ _)
  have he : μ.real (U ⁻¹' (C ∆ A)) = μ.real (C ∆ A) :=
    congrArg ENNReal.toReal (hPres.measure_preimage (hC.symmDiff hA).nullMeasurableSet)
  change _ ≤ _ at h hm ⊢
  rw [he] at hm
  linarith

/-- The all-measurable-sets lower bound in the definition of one-half rigidity,
with an arbitrary positive error on a tail of an explicit dyadic sequence. -/
theorem rudinShapiro_eventually_half_rigid (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    {A : Set SignWords} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (1/2:ℝ) * (rudinShapiroOrbitLaw p : Measure SignWords).real A ≤
      (rudinShapiroOrbitLaw p : Measure SignWords).real (A ∩ signWordShift (rudinShapiroRigidTime k).toAdd ⁻¹' A) + ε := by
  let μ := (rudinShapiroOrbitLaw p : Measure SignWords)
  obtain ⟨C, hC, hClose⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ) finiteWindowEvents_isSetRing
    ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr finiteWindowEvents_univ, by simp⟩
    finiteWindow_generate hA (ENNReal.ofReal_pos.mpr (show 0 < ε/6 by positivity))
  have hclose : μ.real (C ∆ A) < ε/6 := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hClose
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hObs := abs_measureReal_sub_le_measureReal_symmDiff (μ := μ) (finiteWindow_measurable hC).nullMeasurableSet hA.nullMeasurableSet
  obtain ⟨w, hw⟩ := finiteWindow_correlation_lower_bound p hp hC
  have hPow : Tendsto (fun k : ℕ => ((w:ℝ)/(2:ℝ)^(k+1))/2) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (2:ℝ)⁻¹) (by norm_num)
    have hh := (h.comp (tendsto_add_atTop_nat 1)).const_mul (w:ℝ)
    simpa only [Function.comp_def, div_eq_mul_inv, inv_pow, mul_zero, zero_mul] using hh.mul_const ((2:ℝ)⁻¹)
  filter_upwards [hPow.eventually_lt_const (show 0 < ε/2 by positivity)] with k hk
  have hCouple := signWordShift_symmDiff_bound p hp hA (finiteWindow_measurable hC) (rudinShapiroRigidTime k).toAdd
  have hM := hw k
  linarith [(abs_le.mp hObs).1, (abs_le.mp hCouple).1]

/-- The Rudin–Shapiro measured orbit model is one-half rigid along a free ultrafilter. -/
theorem rudinShapiro_half_rigid (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    ∃ q ∈ freeUltrafilters (Multiplicative ℤ), (rudinShapiroOrbitSystem p hp).IsPartiallyRigidAlong q (1/2) := by
  let q := (hyperfilter ℕ).map rudinShapiroRigidTime
  have hInj : Function.Injective rudinShapiroRigidTime := by
    intro a b he
    have hh := congrArg Multiplicative.toAdd he
    change (↑(2^(a+1)*2 : ℕ):ℤ) = ↑(2^(b+1)*2 : ℕ) at hh
    have hNat : 2^(a+1)*2 = 2^(b+1)*2 := by exact_mod_cast hh
    have hPow : 2^(a+1) = 2^(b+1) := Nat.eq_of_mul_eq_mul_right (by decide) hNat
    have hExp := (Nat.pow_right_injective (by decide : 1 < 2)) hPow
    omega
  have hFree : q ∈ freeUltrafilters (Multiplicative ℤ) := by
    change (q : Filter (Multiplicative ℤ)) ≤ cofinite
    rw [Ultrafilter.coe_map]
    exact hInj.tendsto_cofinite.mono_left hyperfilter_le_cofinite
  refine ⟨q, hFree, fun A hA => ?_⟩
  let S := rudinShapiroOrbitSystem p hp
  let L := (inner ℂ (eventVector S hA) (ultrafilterOperator S.koopmanRep q (eventVector S hA))).re
  have hLim := (Complex.continuous_re.tendsto _).comp
    (tendsto_ultrafilterOperator_coeff S.koopmanRep q (eventVector S hA) (eventVector S hA))
  simp only [Function.comp_def, koopman_event_coeff, Complex.ofReal_re] at hLim
  rw [show (q : Filter (Multiplicative ℤ)) = map rudinShapiroRigidTime (hyperfilter ℕ : Filter ℕ) from Ultrafilter.coe_map _ _] at hLim
  have hSeq : Tendsto (fun k => S.measure.real (A ∩ signWordShift (rudinShapiroRigidTime k).toAdd ⁻¹' A))
      (hyperfilter ℕ : Filter ℕ) (𝓝 L) := hLim
  change (1/2:ℝ) * S.measure.real A ≤ L
  by_contra! h
  let ε := ((1/2:ℝ) * S.measure.real A - L) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hev := Nat.hyperfilter_le_atTop (rudinShapiro_eventually_half_rigid p hp hA hε)
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds (hSeq.add_const ε) hev
  dsimp [ε] at hh
  change (1/2:ℝ) * S.measure.real A ≤ L + ((1/2:ℝ)*S.measure.real A-L)/2 at hh
  linarith

end Mixing
