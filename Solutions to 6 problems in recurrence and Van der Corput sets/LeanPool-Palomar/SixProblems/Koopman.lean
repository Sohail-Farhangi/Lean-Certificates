/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import SixProblems.Definitions
public import Mixing.NilrotationKoopmanAction

@[expose] public section
noncomputable section

namespace SixProblems

open MeasureTheory Mixing
open scoped InnerProductSpace

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-- The action underlying a system, used with inverse pullback for
noncommutative acting groups. -/
@[instance_reducible] def systemMulAction (S : System G X) : MulAction G X where
  smul := S.act
  one_smul x := congrFun S.act_one x
  mul_smul g h x := congrFun (S.act_mul g h) x

/-- The convention in the paper, `U_g f = f ∘ T_(g⁻¹)`. -/
def systemKoopman (S : System G X) : G →* (Lp ℂ 2 S.measure ≃ₗᵢ[ℂ] Lp ℂ 2 S.measure) :=
  letI := systemMulAction S
  inverseActionKoopmanRep S.measure S.preserves

theorem ae_systemKoopman (S : System G X) (g : G) (v : Lp ℂ 2 S.measure) :
    (systemKoopman S g v : X → ℂ) =ᵐ[S.measure] fun x ↦ v (S.act g⁻¹ x) :=
  letI := systemMulAction S
  ae_inverseActionKoopmanRep_apply S.measure S.preserves g v

theorem systemKoopman_constantOne (S : System G X) (g : G) :
    systemKoopman S g (constantOne S.measure) = constantOne S.measure := by
  apply Lp.ext
  have hc := Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)
  exact (ae_systemKoopman S g _).trans
    (((S.preserves g⁻¹).quasiMeasurePreserving.ae_eq_comp hc).trans hc.symm)

theorem inner_systemKoopman_of_memLp (S : System G X) {f : X → ℂ}
    (hf : MemLp f 2 S.measure) (g : G) :
    ⟪hf.toLp f, systemKoopman S g (hf.toLp f)⟫_ℂ = correlation S f g⁻¹ := by
  rw [L2.inner_def, correlation]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, (ae_systemKoopman S g _).trans
    ((S.preserves g⁻¹).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)] with x h₁ h₂
  rw [RCLike.inner_apply', h₁, h₂]
  exact mul_comm _ _

theorem bounded_measurable_memLp (S : System G X) {f : X → ℂ} (hf : Measurable f)
    (hbound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : MemLp f 2 S.measure := by
  obtain ⟨C,hC⟩ := hbound
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

end SixProblems
