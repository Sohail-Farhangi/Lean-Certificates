/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.FolnerCriteria
public import JdLG.ReversibleAction

/-!
# Admissibility for amenable measured groups

A left mean supplies a right mean on continuous operator-closure tests by
pulling back along inversion. The two means combine using iterated
integration on the compact host.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped CompactlySupported ENNReal Topology

namespace JdLG

section Combine

variable {T : Type*} [Semigroup T] [TopologicalSpace T] [SeparatelyContinuousMul T]
  [CompactSpace T] [T2Space T] [MeasurableSpace T] [BorelSpace T]

/-- Left and right invariant positive normalized functionals on the same
compact semitopological semigroup give a two-sided invariant mean. -/
theorem exists_biInvariantMean_of_left_and_right
    (m : LeftInvariantContinuousMean (fun a : T ↦ continuous_const_mul a))
    (Φ : C_c(T, ℝ) →ₚ[ℝ] ℝ)
    (hunit : Φ (compactRealFunction (fun _ ↦ 1) continuous_const) = 1)
    (hr : ∀ (a : T) (f : C_c(T, ℝ)),
      Φ (compactRealFunction (fun b ↦ f (b * a))
        (f.continuous.comp (continuous_mul_const a))) = Φ f) :
    ∃ b : LeftInvariantContinuousMean (fun a : T ↦ continuous_const_mul a),
      b.IsRightInvariant (fun a ↦ continuous_mul_const a) := by
  let μ := RealRMK.rieszMeasure Φ
  let sectionOf (a : T) (f : C_c(T, ℝ)) :=
    compactRealFunction (fun b ↦ f (a * b)) (f.continuous.comp (continuous_const_mul a))
  have hc (f : C_c(T, ℝ)) : Continuous fun a ↦ Φ (sectionOf a f) := by
    have h := continuous_integral_of_separatelyContinuous μ (fun a b ↦ f (a * b))
      (fun b ↦ f.continuous.comp (continuous_mul_const b))
      (fun a ↦ f.continuous.comp (continuous_const_mul a))
      ‖f.toContinuousMap‖ (fun a b ↦ f.toContinuousMap.norm_coe_le_norm (a * b))
    have he (a : T) : (∫ b, f (a * b) ∂μ) = Φ (sectionOf a f) :=
      RealRMK.integral_rieszMeasure Φ (sectionOf a f)
    simpa only [he] using h
  let H (f : C_c(T, ℝ)) : C_c(T, ℝ) :=
    compactRealFunction (fun a ↦ Φ (sectionOf a f)) (hc f)
  let M : C_c(T, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ m.functional (H f)
      map_add' := fun f g ↦ by
        have h : H (f + g) = H f + H g := CompactlySupportedContinuousMap.ext fun a ↦
          map_add Φ (sectionOf a f) (sectionOf a g)
        change m.functional (H (f + g)) = _
        rw [h, map_add]
      map_smul' := fun r f ↦ by
        have h : H (r • f) = r • H f := CompactlySupportedContinuousMap.ext fun a ↦
          map_smul Φ r (sectionOf a f)
        change m.functional (H (r • f)) = r • m.functional (H f)
        rw [h, map_smul]
      monotone' := fun f g hf ↦ m.functional.monotone' fun a ↦
        Φ.monotone' (fun b ↦ hf (a * b)) }
  have hMunit : M (compactRealFunction (fun _ ↦ 1) continuous_const) = 1 := by
    have h : H (compactRealFunction (fun _ ↦ 1) continuous_const) =
        compactRealFunction (fun _ ↦ 1) continuous_const :=
      CompactlySupportedContinuousMap.ext fun _ ↦ hunit
    change m.functional (H (compactRealFunction (fun _ ↦ 1) continuous_const)) = 1
    rw [h, m.normalized]
  have hMleft (a : T) (f : C_c(T, ℝ)) :
      M (compactRealFunction (fun b ↦ f (a * b))
        (f.continuous.comp (continuous_const_mul a))) = M f := by
    have h : H (sectionOf a f) =
        compactRealFunction (fun b ↦ H f (a * b))
          ((H f).continuous.comp (continuous_const_mul a)) := by
      apply CompactlySupportedContinuousMap.ext
      intro b
      change Φ (sectionOf b (sectionOf a f)) = Φ (sectionOf (a * b) f)
      congr 1
      exact CompactlySupportedContinuousMap.ext fun c ↦ congrArg f (mul_assoc a b c).symm
    change m.functional (H (sectionOf a f)) = m.functional (H f)
    rw [h, m.translate]
  refine ⟨⟨M, hMunit, hMleft⟩, fun a f ↦ ?_⟩
  let g := compactRealFunction (fun b ↦ f (b * a)) (f.continuous.comp (continuous_mul_const a))
  have h : H g = H f := by
    apply CompactlySupportedContinuousMap.ext
    intro b
    change Φ (sectionOf b g) = Φ (sectionOf b f)
    have he : sectionOf b g = compactRealFunction (fun t ↦ sectionOf b f (t * a))
        ((sectionOf b f).continuous.comp (continuous_mul_const a)) :=
      CompactlySupportedContinuousMap.ext fun t ↦ congrArg f (mul_assoc b t a)
    rw [he, hr]
  change m.functional (H g) = m.functional (H f)
  rw [h]

end Combine

section Operator

variable {G E : Type*} [Group G] [MeasurableSpace G] {μ : Measure G}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  (π : G →ₙ* (E →L[ℂ] E))
  [CompactSpace (weakOperatorClosure π)] [MeasurableSpace (weakOperatorClosure π)]
  [BorelSpace (weakOperatorClosure π)]

/-- Admissibility for a relatively weakly compact representation of an
amenable group, from its left measured mean and measurable inversion. -/
theorem admissible_of_groupLeftInvariantMean (hπ : Measurable (closureInclusion π))
    (hInv : Measurable (Inv.inv : G → G)) (m : MeasuredMean μ) (hm : m.IsLeftInvariant) :
    IsJdLGAdmissible π := by
  let i := closureInclusion π
  let j (s : G) := i s⁻¹
  have hj : Measurable j := hπ.comp hInv
  let T := weakOperatorClosure π
  let test (f : C_c(T, ℝ)) : G → ℝ := f ∘ j
  have hf (f : C_c(T, ℝ)) : MemLp (test f) ∞ μ :=
    memLp_top_of_bound (f.continuous.measurable.comp hj).aestronglyMeasurable
      ‖f.toContinuousMap‖ (ae_of_all _ fun s ↦ f.toContinuousMap.norm_coe_le_norm (j s))
  let Φ : C_c(T, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f ↦ m.value (test f) (hf f)
      map_add' := fun f g ↦ (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
        (m.value_add (hf f) (hf g))
      map_smul' := fun r f ↦ (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans
        (m.value_smul r (hf f))
      monotone' := fun _ _ h ↦ m.value_mono (ae_of_all _ fun s ↦ h (j s)) }
  have hunit : Φ (compactRealFunction (fun _ ↦ 1) continuous_const) = 1 :=
    (m.value_congr_ae (ae_of_all _ fun _ ↦ rfl)).trans m.value_one
  have hr (a : T) (f : C_c(T, ℝ)) :
      Φ (compactRealFunction (fun b ↦ f (b * a))
        (f.continuous.comp (continuous_mul_const a))) = Φ f := by
    have hjDense : DenseRange j := by
      have hRange : range j = range i := (inv_involutive.surjective.range_comp i)
      rw [DenseRange, hRange]
      exact denseRange_closureInclusion π
    refine MeasuredMean.continuousFunctional_translate_of_dense j Φ hunit (fun a b ↦ b * a)
      (fun s ↦ continuous_const_mul s) (fun s ↦ continuous_mul_const s)
      hjDense (fun s f ↦ ?_) a f
    let g := compactRealFunction (fun b ↦ f (b * j s))
      (f.continuous.comp (continuous_mul_const (j s)))
    have he (t : G) : test g t = test f (s * t) := by
      change f (i t⁻¹ * i s⁻¹) = f (i (s * t)⁻¹)
      rw [mul_inv_rev, map_mul i]
    have ht : MemLp (test f ∘ (s * ·)) ∞ μ := (hf g).ae_eq (ae_of_all _ he)
    exact (m.value_congr_ae (ae_of_all _ he)).trans (hm s _ (hf f) ht)
  let mL := m.toContinuousMean i hπ (fun s ↦ continuous_const_mul s)
    (fun s ↦ continuous_mul_const s) (denseRange_closureInclusion π) hm
  obtain ⟨b, hb⟩ := exists_biInvariantMean_of_left_and_right mL Φ hunit hr
  exact ⟨isCompact_iff_compactSpace.mpr inferInstance,
    b.existsUnique_minimalIdempotent_of_biInvariant hb⟩

end Operator

/-- Compact WOT closures determine admissibility independently of the
semigroups used to represent them, as in Corollary 1.4. -/
theorem isJdLGAdmissible_iff_of_eq_weakOperatorClosure {S T E : Type*} [Semigroup S] [Semigroup T]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (π : S →ₙ* (E →L[ℂ] E)) (ρ : T →ₙ* (E →L[ℂ] E))
    (h : (weakOperatorClosure π : Set (E →WOT[ℂ] E)) =
      (weakOperatorClosure ρ : Set (E →WOT[ℂ] E))) :
    IsJdLGAdmissible π ↔ IsJdLGAdmissible ρ := by
  have he : weakOperatorClosure π = weakOperatorClosure ρ :=
    SetLike.coe_injective h
  unfold IsJdLGAdmissible
  rw [he]

/-- The admissibility, reversible-orbit, and fixed-coefficient conclusions
of Theorem 1.6 for a left Følner family on an amenable measured group. -/
theorem amenable_group_decomposition_and_folner_coefficient {G E I : Type*}
    [Group G] [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (π : G →* (E →L[ℂ] E))
    [CompactSpace (weakOperatorClosure π.toMulHom)]
    [MeasurableSpace (weakOperatorClosure π.toMulHom)]
    [BorelSpace (weakOperatorClosure π.toMulHom)] (hπ : Measurable (closureInclusion π.toMulHom))
    (hInv : Measurable (Inv.inv : G → G)) (m : MeasuredMean μ) (hm : m.IsLeftInvariant)
    (ν : I → Measure G) (hprob : ∀ n, IsProbabilityMeasure (ν n))
    (l : Filter I) [l.NeBot] (hν : LeftFolnerProbabilities ν l) :
    IsJdLGAdmissible π.toMulHom ∧
    (∀ x, IsReversible (closureAction π.toMulHom) x ↔ HasPrecompactOrbit π.toMulHom x) ∧
    ∀ x, IsAlmostWeaklyStable (closureAction π.toMulHom) x ↔
      ∀ f : StrongDual ℂ E, Tendsto (fun n ↦ ∫ s, ‖f (π.toMulHom s x)‖ ∂ν n) l (𝓝 0) := by
  have h := admissible_of_groupLeftInvariantMean π.toMulHom hπ hInv m hm
  refine ⟨h, group_reversible_iff_precompactOrbit π h, fun x ↦ ?_⟩
  simpa only [Real.rpow_one] using
    stable_iff_folnerCoefficientMoments π.toMulHom hπ ν hprob hν h x 1 zero_lt_one

end JdLG
