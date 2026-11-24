/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconColumnCorrelations
public import Mixing.ChaconKoopmanHeightLimits

@[expose] public section
noncomputable section
namespace Mixing

open Filter MeasureTheory Set
open scoped Classical ENNReal Topology InnerProductSpace

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : IsProbabilityMeasure chaconTowerSystem.measure := chaconTowerSystem.probability

theorem chaconPrefix_prefix {N n : ℕ} (hN : N ≤ n) (x : ChaconOdometer) :
    chaconPrefix N (chaconPrefix n x) = chaconPrefix N x := by
  have hz := congrArg (ZMod.cast : ZMod (3^n) → ZMod (3^N))
    (ZMod.natCast_zmod_val (PadicInt.toZModPow (p := 3) n x))
  rw [ZMod.cast_natCast (pow_dvd_pow 3 hN), PadicInt.cast_toZModPow N n hN] at hz
  unfold chaconPrefix
  rw [map_natCast, hz]

theorem IsChaconPrefixTest.mono {N n : ℕ} (hN : N ≤ n)
    {f : ChaconOdometer × Bool → ℂ} (hf : IsChaconPrefixTest N f) :
    IsChaconPrefixTest n f := by
  intro x b
  rw [hf x b, hf (chaconPrefix n x) b, chaconPrefix_prefix hN]

/-- A bounded observable depending on finitely many digits and the layer. -/
abbrev ChaconPrefixObservable :=
  {f : BoundedObservable (ChaconOdometer × Bool) // ∃ N, IsChaconPrefixTest N f}

private def chaconApproxObs (F : C(ChaconOdometer × Bool, ℂ)) (n : ℕ) :
    ChaconPrefixObservable :=
  ⟨{ toFun := fun x ↦ F (chaconPrefix n x.1, x.2)
     measurable := F.continuous.measurable.comp
       (((measurable_chaconPrefix n).comp measurable_fst).prodMk measurable_snd)
     bound := ‖F‖
     bound_nonneg := norm_nonneg _
     norm_le := fun _ ↦ F.norm_coe_le_norm _ },
   n, fun x b ↦ by
     change F (chaconPrefix n x,b) = F (chaconPrefix n (chaconPrefix n x),b)
     rw [chaconPrefix_prefix le_rfl]⟩

private theorem tendsto_chaconApproxObs (F : C(ChaconOdometer × Bool, ℂ)) :
    Tendsto (fun n ↦ (chaconApproxObs F n).val.l2 chaconTowerSystem.measure) atTop
      (𝓝 (ContinuousMap.toLp 2 chaconTowerSystem.measure ℂ F)) := by
  let μ := chaconTowerSystem.measure
  let L := ContinuousMap.toLp 2 μ ℂ F
  have hL := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ F
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hSlice (b : Bool) : ∀ᶠ n in atTop, ∀ x : ChaconOdometer,
      ‖F (chaconPrefix n x,b) - F (x,b)‖ ≤ ε/2 := by
    have hcont : Continuous (fun x : ChaconOdometer ↦ F (x,b)) :=
      F.continuous.comp (continuous_id.prodMk continuous_const)
    have hu := CompactSpace.uniformContinuous_of_continuous hcont
    obtain ⟨δ, hδ, hUniform⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (by positivity)
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3 : ℝ)⁻¹)
      (by norm_num) (by norm_num)).eventually_lt_const hδ
    filter_upwards [hh] with n hn x
    exact (by simpa only [dist_eq_norm] using
      (hUniform (a := chaconPrefix n x) (b := x) ((dist_comm x (chaconPrefix n x)) ▸
        (dist_chaconPrefix_le n x).trans_lt hn)) :
          ‖F (chaconPrefix n x,b) - F (x,b)‖ < ε/2).le
  filter_upwards [hSlice false, hSlice true] with n hn₀ hn₁
  rw [dist_eq_norm]
  have he : ∀ᵐ x ∂μ, ‖((chaconApproxObs F n).val.l2 μ - L) x‖ ≤ ε/2 := by
    filter_upwards [Lp.coeFn_sub ((chaconApproxObs F n).val.l2 μ) L,
      (chaconApproxObs F n).val.coe_l2 μ, hL] with x hsub hf hval
    rw [hsub, Pi.sub_apply, hf, hval]
    rcases x with ⟨x,b⟩
    cases b
    · exact hn₀ x
    · exact hn₁ x
  have hnorm : ‖(chaconApproxObs F n).val.l2 μ - L‖ ≤ ε/2 := by
    simpa [measureUnivNNReal, measure_univ] using Lp.norm_le_of_ae_bound (by positivity : 0 ≤ ε/2) he
  exact hnorm.trans_lt (by linarith)

/-- Bounded finite-prefix observables are dense in the tower's full L². -/
theorem denseRange_chaconPrefixObservable :
    DenseRange (fun f : ChaconPrefixObservable ↦ f.val.l2 chaconTowerSystem.measure) := by
  intro v
  let A := range (fun f : ChaconPrefixObservable ↦ f.val.l2 chaconTowerSystem.measure)
  have hD := ContinuousMap.toLp_denseRange (p := 2) ℂ chaconTowerSystem.measure ℂ ENNReal.ofNat_ne_top
  apply closure_minimal _ isClosed_closure (hD v)
  rintro x ⟨F, rfl⟩
  exact mem_closure_of_tendsto (tendsto_chaconApproxObs F)
    (Eventually.of_forall fun n ↦ show _ ∈ A from ⟨chaconApproxObs F n, rfl⟩)

/-- A finite-prefix test centered by subtracting its integral. -/
def chaconCenteredObservable (F : ChaconPrefixObservable) : BoundedObservable (ChaconOdometer × Bool) :=
  F.val.sub (BoundedObservable.const (∫ x, F.val x ∂chaconTowerSystem.measure))

theorem chaconCenteredObservable_prefix (F : ChaconPrefixObservable) :
    ∃ N, IsChaconPrefixTest N (chaconCenteredObservable F) := by
  obtain ⟨N, hN⟩ := F.property
  exact ⟨N, fun x b ↦ by
    simp only [chaconCenteredObservable, BoundedObservable.sub_apply, BoundedObservable.const_apply, hN x b]⟩

theorem ae_center_chaconPrefixObservable (F : ChaconPrefixObservable) :
    (center chaconTowerSystem.measure (F.val.l2 chaconTowerSystem.measure) :
      Lp ℂ 2 chaconTowerSystem.measure) =ᵐ[chaconTowerSystem.measure] chaconCenteredObservable F := by
  let μ := chaconTowerSystem.measure
  let f := F.val.l2 μ
  have hC : inner ℂ (constantOne μ) f = ∫ x, F.val x ∂μ := by
    rw [inner_constantOne_left]
    exact integral_congr_ae (F.val.coe_l2 μ)
  rw [show (center μ f : Lp ℂ 2 μ) = f - inner ℂ (constantOne μ) f • constantOne μ from rfl, hC]
  let c := ∫ x, F.val x ∂μ
  filter_upwards [F.val.coe_l2 μ, Lp.coeFn_sub f (c • constantOne μ),
    Lp.coeFn_smul c (constantOne μ), Lp.coeFn_const (p := 2) (μ := μ) (1 : ℂ)] with x hx hsub hsmul hconst
  rw [hsub, Pi.sub_apply, hx, hsmul, Pi.smul_apply]
  change constantOne μ x = 1 at hconst
  rw [hconst, smul_eq_mul, mul_one]
  rfl

theorem denseRange_center_chaconPrefixObservable :
    DenseRange (fun f : ChaconPrefixObservable ↦
      center chaconTowerSystem.measure (f.val.l2 chaconTowerSystem.measure)) := by
  let μ := chaconTowerSystem.measure
  have hSurj : Function.Surjective (center μ) := by
    intro v
    refine ⟨v, Subtype.ext ?_⟩
    have hv : inner ℂ (constantOne μ) (v : Lp ℂ 2 μ) = 0 :=
      v.property (constantOne μ) (Submodule.mem_span_singleton_self _)
    change (v : Lp ℂ 2 μ) - inner ℂ (constantOne μ) (v : Lp ℂ 2 μ) • constantOne μ = v
    simp [hv]
  have hc : Continuous (center μ) := by
    apply Continuous.subtype_mk
    have hi : Continuous (fun x : Lp ℂ 2 μ ↦ ⟪constantOne μ, x⟫_ℂ) :=
      continuous_const.inner continuous_id
    exact continuous_id.sub (hi.smul (continuous_const : Continuous (fun _ : Lp ℂ 2 μ ↦ constantOne μ)))
  exact hSurj.denseRange.comp denseRange_chaconPrefixObservable hc

end Mixing
