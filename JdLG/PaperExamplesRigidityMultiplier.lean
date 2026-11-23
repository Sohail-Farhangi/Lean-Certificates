/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRigidityCircle
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Unitary multiplication by a circle-valued function

Uniform rigidity of the multiplier implies strong rigidity on the entire
Hilbert space. An injective multiplier on a space with null singletons
gives a generator with no nonzero eigenvectors.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable instance : MeasurableSpace Circle := borel _

instance : BorelSpace Circle := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

local notation "H" => Lp ℂ 2 μ

/-- An integer power of a measurable circle-valued function is measurable. -/
theorem measurable_circle_zpow {u : Ω → Circle} (hu : Measurable u) (n : ℤ) :
    Measurable (fun a ↦ u a ^ n) :=
  ((continuous_id (X := Circle)).zpow n).measurable.comp hu

theorem memLp_mul_circle (u : Ω → Circle) (hu : Measurable u) (x : H) :
    MemLp (fun a ↦ (u a : ℂ) * x a) 2 μ := by
  have hc : Continuous (fun z : Circle ↦ (z : ℂ)) := continuous_subtype_val
  have hmeas : Measurable (fun a ↦ (u a : ℂ)) := hc.measurable.comp hu
  refine (Lp.memLp x).norm.mono' (hmeas.aestronglyMeasurable.mul (Lp.aestronglyMeasurable x)) ?_
  exact Eventually.of_forall fun _ ↦ by rw [norm_mul, Circle.norm_coe, one_mul]

/-- The pointwise product of a unit-circle valued function with an `L²` vector. -/
noncomputable def circleMulVector (u : Ω → Circle) (hu : Measurable u) (x : H) : H :=
  (memLp_mul_circle u hu x).toLp _

theorem circleMulVector_ae (u : Ω → Circle) (hu : Measurable u) (x : H) :
    circleMulVector u hu x =ᵐ[μ] fun a ↦ (u a : ℂ) * x a :=
  (memLp_mul_circle u hu x).coeFn_toLp

/-- Multiplication by a measurable circle-valued function is unitary. -/
noncomputable def circleMulUnitary (u : Ω → Circle) (hu : Measurable u) : H ≃ₗᵢ[ℂ] H where
  toFun := circleMulVector u hu
  invFun := circleMulVector (fun a ↦ (u a)⁻¹) hu.inv
  left_inv x := Lp.ext (by
    filter_upwards [circleMulVector_ae u hu x,
      circleMulVector_ae (fun a ↦ (u a)⁻¹) hu.inv (circleMulVector u hu x)] with a ha hb
    rw [hb, ha, ← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul])
  right_inv x := Lp.ext (by
    filter_upwards [circleMulVector_ae (fun a ↦ (u a)⁻¹) hu.inv x,
      circleMulVector_ae u hu (circleMulVector (fun a ↦ (u a)⁻¹) hu.inv x)] with a ha hb
    rw [hb, ha, ← mul_assoc, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_mul])
  map_add' x y := Lp.ext (by
    filter_upwards [circleMulVector_ae u hu x, circleMulVector_ae u hu y,
      circleMulVector_ae u hu (x + y), Lp.coeFn_add x y,
      Lp.coeFn_add (circleMulVector u hu x) (circleMulVector u hu y)] with a hx hy hz hxy hsum
    rw [hz, hxy, hsum]
    simp only [Pi.add_apply, hx, hy, mul_add])
  map_smul' z x := Lp.ext (by
    filter_upwards [circleMulVector_ae u hu x, circleMulVector_ae u hu (z • x),
      Lp.coeFn_smul z x, Lp.coeFn_smul z (circleMulVector u hu x)] with a h₁ h₂ h₃ h₄
    change circleMulVector u hu (z • x) a = (z • circleMulVector u hu x) a
    rw [h₂, h₃, h₄]
    simp only [Pi.smul_apply, h₁, smul_eq_mul]
    ring)
  norm_map' x := by
    change ‖circleMulVector u hu x‖ = ‖x‖
    have hn : ∀ᵐ a ∂μ, ‖circleMulVector u hu x a‖ = ‖x a‖ :=
      (circleMulVector_ae u hu x).mono fun _ h ↦ by rw [h, norm_mul, Circle.norm_coe, one_mul]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h ↦ h.le))
      (Lp.norm_le_norm_of_ae_le (hn.mono fun _ h ↦ h.ge))

/-- The unitary integer action by the integer powers of a circle multiplier. -/
noncomputable def circleMulRepresentation (u : Ω → Circle) (hu : Measurable u) :
    Multiplicative ℤ →* (H ≃ₗᵢ[ℂ] H) where
  toFun n := circleMulUnitary (fun a ↦ u a ^ n.toAdd) (measurable_circle_zpow hu _)
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    apply Lp.ext
    change circleMulVector (fun _ : Ω ↦ (1 : Circle)) measurable_const x =ᵐ[μ] x
    simpa only [Circle.coe_one, one_mul] using
      circleMulVector_ae (fun _ : Ω ↦ (1 : Circle)) measurable_const x
  map_mul' n m := by
    apply LinearIsometryEquiv.ext
    intro x
    apply Lp.ext
    let y := circleMulVector (fun a ↦ u a ^ m.toAdd) (measurable_circle_zpow hu _) x
    change circleMulVector (fun a ↦ u a ^ (n.toAdd + m.toAdd)) (measurable_circle_zpow hu _) x
      =ᵐ[μ] circleMulVector (fun a ↦ u a ^ n.toAdd) (measurable_circle_zpow hu _) y
    filter_upwards [circleMulVector_ae (fun a ↦ u a ^ (n.toAdd + m.toAdd))
      (measurable_circle_zpow hu _) x, circleMulVector_ae (fun a ↦ u a ^ n.toAdd)
      (measurable_circle_zpow hu _) y, circleMulVector_ae (fun a ↦ u a ^ m.toAdd)
      (measurable_circle_zpow hu _) x] with a h₁ h₂ h₃
    rw [h₁, h₂]
    change _ = _ * circleMulVector (fun a ↦ u a ^ m.toAdd) (measurable_circle_zpow hu _) x a
    rw [h₃, zpow_add, Circle.coe_mul, mul_assoc]

theorem circleMulRepresentation_ae (u : Ω → Circle) (hu : Measurable u) (n : ℤ) (x : H) :
    circleMulRepresentation u hu (Multiplicative.ofAdd n) x =ᵐ[μ]
      fun a ↦ ((u a ^ n : Circle) : ℂ) * x a :=
  circleMulVector_ae (fun a ↦ u a ^ n) (measurable_circle_zpow hu n) x

/-- A uniformly rigid circle multiplier acts strongly rigidly on all vectors. -/
theorem circleMulRepresentation_strongly_rigid (u : Ω → Circle) (hu : Measurable u)
    (q : ℕ → ℕ) (hq : TendstoUniformly (fun n a ↦ u a ^ q n) (fun _ ↦ (1 : Circle)) atTop)
    (x : H) : Tendsto (fun n ↦ circleMulRepresentation u hu (Multiplicative.ofAdd (q n : ℤ)) x)
      atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := ε / (‖x‖ + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [Metric.tendstoUniformly_iff.1 hq δ hδ] with n hn
  let y := circleMulRepresentation u hu (Multiplicative.ofAdd (q n : ℤ)) x
  change dist y x < ε
  rw [dist_eq_norm]
  have hbound : ‖y - x‖ ≤ δ * ‖x‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub y x, circleMulRepresentation_ae u hu (q n : ℤ) x] with a ha hb
    rw [ha]
    simp only [Pi.sub_apply]
    rw [hb, show ((u a ^ (q n : ℤ) : Circle) : ℂ) * x a - x a =
      (((u a ^ (q n : ℤ) : Circle) : ℂ) - 1) * x a by ring, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hd := hn a
    change dist (1 : ℂ) (((u a ^ q n : Circle) : ℂ)) < δ at hd
    rw [dist_comm, dist_eq_norm] at hd
    simpa only [zpow_natCast] using hd.le
  have heq : δ * (‖x‖ + 1) = ε := div_mul_cancel₀ _ (by positivity)
  linarith

/-- An injective circle multiplier with null singleton fibers has no nonzero
eigenvectors in its Hilbert space. -/
theorem circleMulRepresentation_no_eigenvectors [NullSingletonClass μ]
    (u : Ω → Circle) (hu : Measurable u) (hi : Function.Injective u)
    (c : ℂ) (x : H)
    (h : circleMulRepresentation u hu (Multiplicative.ofAdd 1) x = c • x) :
    x = 0 := by
  have hS : {a | (u a : ℂ) = c}.Subsingleton :=
    fun a ha b hb ↦ hi (Subtype.ext (ha.trans hb.symm))
  have hne : ∀ᵐ a ∂μ, (u a : ℂ) ≠ c := ae_iff.2 (by simpa using hS.measure_zero μ)
  apply Lp.ext
  filter_upwards [circleMulRepresentation_ae u hu 1 x, Lp.coeFn_smul c x, hne,
    (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ))] with a ha hb hd hzero
  rw [h] at ha
  change (c • x : H) a = _ at ha
  rw [hb, Pi.smul_apply, smul_eq_mul, zpow_one] at ha
  have hmul : ((u a : ℂ) - c) * x a = 0 := by rw [sub_mul, ← ha, sub_self]
  rw [hzero]
  exact (mul_eq_zero.1 hmul).resolve_left (sub_ne_zero.2 hd)

end JdLG.PaperExamplesRigid
