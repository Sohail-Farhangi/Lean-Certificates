/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRows
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Bilateral shift on the row Følner net

Example 4.5 uses the literal bilateral unitary shift on `ℓ²(ℤ)`. Its powers
converge weakly to zero along the cofinite filter on integers, while weak
decay on a set of times in the row semigroup forces finite vertical fibers.
-/

@[expose] public section

namespace JdLG.PaperExamplesBilateral

open Filter
open scoped Topology ENNReal

local notation "H" => lp (fun _ : ℤ ↦ ℂ) 2
local notation "Point" => PaperExamplesRows.Point

private theorem positive_exponent : 0 < (2 : ℝ≥0∞).toReal := by norm_num

/-- A vector translated by `a`, with the coordinate at `k` read from `k - a`. -/
noncomputable def shiftedVector (a : ℤ) (x : H) : H :=
  ⟨fun k ↦ x (k - a), memℓp_gen (by
    change Summable ((fun k ↦ ‖x k‖ ^ (2 : ℝ≥0∞).toReal) ∘ (Equiv.subRight a))
    exact (Equiv.subRight a).summable_iff.2 ((lp.memℓp x).summable positive_exponent))⟩

@[simp] theorem shiftedVector_apply (a : ℤ) (x : H) (k : ℤ) :
    shiftedVector a x k = x (k - a) := rfl

/-- The unitary bilateral shift by `a`. -/
noncomputable def shift (a : ℤ) : H ≃ₗᵢ[ℂ] H where
  toFun := shiftedVector a
  invFun := shiftedVector (-a)
  left_inv x := lp.ext (funext fun k ↦ by
    change x ((k - (-a)) - a) = x k
    rw [show k - (-a) - a = k by omega])
  right_inv x := lp.ext (funext fun k ↦ by
    change x ((k - a) - (-a)) = x k
    rw [show k - a - (-a) = k by omega])
  map_add' x y := lp.ext (funext fun k ↦ rfl)
  map_smul' c x := lp.ext (funext fun k ↦ rfl)
  norm_map' x := by
    change ‖shiftedVector a x‖ = ‖x‖
    rw [lp.norm_eq_tsum_rpow positive_exponent, lp.norm_eq_tsum_rpow positive_exponent]
    congr 1
    exact (Equiv.subRight a).tsum_eq (fun k ↦ ‖x k‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] theorem shift_apply (a : ℤ) (x : H) (k : ℤ) :
    shift a x k = x (k - a) := rfl

/-- The row-semigroup representation `(a,n) ↦ Uᵃ`. -/
noncomputable def representation : Multiplicative Point →ₙ* (H →L[ℂ] H) where
  toFun s := (shift s.toAdd.first).toLinearIsometry.toContinuousLinearMap
  map_mul' s t := by
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext k
    change x (k - (s.toAdd.first + t.toAdd.first)) = x (k - s.toAdd.first - t.toAdd.first)
    rw [show k - (s.toAdd.first + t.toAdd.first) =
      k - s.toAdd.first - t.toAdd.first by omega]

/-- The coordinate basis vector `e_a`. -/
noncomputable def basisVector (a : ℤ) : H := lp.single 2 a 1

theorem shift_single (a i : ℤ) (c : ℂ) :
    shift a (lp.single 2 i c : H) = lp.single 2 (i + a) c := by
  apply lp.ext
  funext k
  change (lp.single 2 i c : H) (k - a) = (lp.single 2 (i + a) c : H) k
  by_cases h : k = i + a
  · rw [h, lp.single_apply_self, show i + a - a = i by omega, lp.single_apply_self]
  · have hi : k - a ≠ i := by omega
    rw [lp.single_apply_ne (E := fun _ : ℤ ↦ ℂ) 2 i c hi,
      lp.single_apply_ne (E := fun _ : ℤ ↦ ℂ) 2 (i + a) c h]

theorem representation_e0 (s : Point) : representation (Multiplicative.ofAdd s) (basisVector 0) =
    basisVector s.first := by
  change shift s.first (lp.single 2 0 1 : H) = lp.single 2 s.first 1
  rw [shift_single, zero_add]

private theorem coord_norm_tendsto_zero (x : H) :
    Tendsto (fun k : ℤ ↦ ‖x k‖) cofinite (𝓝 0) := by
  have hs : Summable (fun k : ℤ ↦ ‖x k‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp x).summable positive_exponent
  have hz := (Real.continuous_sqrt.tendsto 0).comp hs.tendsto_cofinite_zero
  convert hz using 1
  · funext k
    change ‖x k‖ = Real.sqrt (‖x k‖ ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_norm]
  · rw [Real.sqrt_zero]

private theorem eval_shift_single_tendsto_zero (f : StrongDual ℂ H) (i : ℤ) (c : ℂ) :
    Tendsto (fun a : ℤ ↦ f (shift a (lp.single 2 i c : H))) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  let y := (InnerProductSpace.toDual ℂ H).symm f
  have ht : Tendsto (fun a : ℤ ↦ i + a) cofinite cofinite :=
    (Equiv.addLeft i).injective.tendsto_cofinite
  have hbound := ((coord_norm_tendsto_zero y).comp ht).mul_const ‖c‖
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_mul, Function.comp_apply] using hbound)
    (Eventually.of_forall fun a ↦ norm_nonneg _) (Eventually.of_forall fun a ↦ ?_)
  rw [shift_single, ← InnerProductSpace.toDual_symm_apply, lp.inner_single_right]
  exact norm_inner_le_norm (𝕜 := ℂ) _ _

/-- Every matrix coefficient of the shift tends to zero at infinity on `ℤ`. -/
theorem eval_shift_tendsto_zero (f : StrongDual ℂ H) (x : H) :
    Tendsto (fun a : ℤ ↦ f (shift a x)) cofinite (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  let δ := ε / (2 * (‖f‖ + 1))
  have hp : 0 < ‖f‖ + 1 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hx := lp.hasSum_single (p := 2) (by simp) x
  obtain ⟨F, hF⟩ := ((Metric.tendsto_nhds.1 hx δ hδ).exists)
  let w : H := ∑ i ∈ F, lp.single 2 i (x i)
  have hw : ‖x - w‖ < δ := by simpa only [← dist_eq_norm, dist_comm] using hF
  have hfinite : Tendsto (fun a : ℤ ↦ f (shift a w)) cofinite (𝓝 0) := by
    have hsum := tendsto_finsetSum F fun i _ ↦ eval_shift_single_tendsto_zero f i (x i)
    simpa only [w, map_sum, Finset.sum_const_zero] using hsum
  refine (Metric.tendsto_nhds.1 hfinite (ε / 2) (by positivity)).mono fun a ha ↦ ?_
  rw [dist_zero_right] at ha ⊢
  have hsmall : ‖f (shift a x) - f (shift a w)‖ < ε / 2 := calc
    ‖f (shift a x) - f (shift a w)‖ = ‖f (shift a (x - w))‖ := by rw [map_sub, map_sub]
    _ ≤ ‖f‖ * ‖shift a (x - w)‖ := f.le_opNorm _
    _ = ‖f‖ * ‖x - w‖ := by rw [(shift a).norm_map]
    _ ≤ (‖f‖ + 1) * ‖x - w‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (‖f‖ + 1) * δ := mul_lt_mul_of_pos_left hw hp
    _ = ε / 2 := by dsimp [δ]; field_simp
  calc
    ‖f (shift a x)‖ = ‖(f (shift a x) - f (shift a w)) + f (shift a w)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖f (shift a x) - f (shift a w)‖ + ‖f (shift a w)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hsmall ha
    _ = ε := by ring

theorem shiftWOT_tendsto_zero : Tendsto
    (fun a : ℤ ↦ weakRepresentation representation (Multiplicative.ofAdd ⟨a, 0⟩))
    cofinite (𝓝 (0 : H →WOT[ℂ] H)) := by
  refine ContinuousLinearMapWOT.tendsto_iff_forall_dual_apply_tendsto.2 fun x f ↦ ?_
  change Tendsto (fun a : ℤ ↦ f (shift a x)) cofinite (𝓝 (f 0))
  rw [map_zero]
  exact eval_shift_tendsto_zero f x

theorem range_shiftWOT : Set.range (weakRepresentation representation) =
    Set.range (fun a : ℤ ↦ weakRepresentation representation (Multiplicative.ofAdd ⟨a, 0⟩)) := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.toAdd.first, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.ofAdd ⟨a, 0⟩, rfl⟩

theorem zero_mem_closure : (0 : H →WOT[ℂ] H) ∈ weakOperatorClosure representation := by
  change (0 : H →WOT[ℂ] H) ∈ closure (Set.range (weakRepresentation representation))
  rw [range_shiftWOT]
  exact mem_closure_of_tendsto shiftWOT_tendsto_zero (Eventually.of_forall Set.mem_range_self)

theorem closure_compact : IsCompact (weakOperatorClosure representation : Set (H →WOT[ℂ] H)) := by
  change IsCompact (closure (Set.range (weakRepresentation representation)))
  rw [range_shiftWOT]
  have hc := shiftWOT_tendsto_zero.isCompact_insert_range_of_cofinite
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal (Set.subset_insert ..) hc.isClosed)

theorem admissible : IsJdLGAdmissible representation := by
  refine admissible_of_commutative closure_compact fun s t ↦ ?_
  rw [← map_mul, ← map_mul, mul_comm]

theorem e0_almost_weakly_stable :
    IsAlmostWeaklyStable (closureAction representation) (basisVector 0) :=
  ⟨⟨0, zero_mem_closure⟩, rfl⟩

/-- Weak convergence of the represented orbit along a set of times in the
discrete row semigroup, written using the continuous dual. -/
def WeakDecayOn (A : Set Point) : Prop :=
  ∀ f : StrongDual ℂ H,
    Tendsto (fun s : Point ↦ f (representation (Multiplicative.ofAdd s) (basisVector 0)))
      (cofinite ⊓ principal A) (𝓝 0)

theorem finite_vertical_fibers (A : Set Point) (hA : WeakDecayOn A) (a : ℤ) :
    {s ∈ A | s.first = a}.Finite := by
  let e := lp.evalCLM ℂ (fun _ : ℤ ↦ ℂ) 2 a
  have hsmall := Metric.tendsto_nhds.1 (hA e) (1 / 2) (by norm_num)
  have he := eventually_inf_principal.1 hsmall
  apply (eventually_cofinite.1 he).subset
  intro s hs hs'
  have hh := hs' hs.1
  rw [representation_e0, hs.2] at hh
  change dist ((lp.single 2 a (1 : ℂ) : H) a) 0 < 1 / 2 at hh
  rw [lp.single_apply_self, dist_zero_right, norm_one] at hh
  norm_num at hh

/-- Example 4.5. No weak-decay set for the shift vector has density one along
the manuscript's two-parameter row Følner net. -/
theorem no_density_one_weakDecayOn (A : Set Point) (hA : WeakDecayOn A) :
    ¬ Tendsto (PaperExamplesRows.rowDensity A) atTop (𝓝 1) :=
  PaperExamplesRows.no_density_one_of_finite_fibers A (finite_vertical_fibers A hA)

end JdLG.PaperExamplesBilateral
