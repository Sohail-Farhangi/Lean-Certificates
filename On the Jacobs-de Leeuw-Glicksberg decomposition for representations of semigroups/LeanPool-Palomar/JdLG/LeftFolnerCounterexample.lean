/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.HilbertCompactness
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic.NormNum

/-!
# A left Følner sequence with nonvanishing uniform coefficient averages

The finitary permutations of the natural numbers act unitarily on their
coordinate Hilbert space. Right cosets of the increasing finite subgroups
give a left Følner sequence whose averages of every fixed coefficient tend
to zero, while the coefficient supremum equals one at every stage.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace JdLG.LeftFolnerCounterexample

/-- Permutations that fix all sufficiently large natural numbers. -/
def finitaryPermutations : Subgroup (Equiv.Perm ℕ) where
  carrier := {g | ∃ N : ℕ, ∀ k > N, g k = k}
  one_mem' := ⟨0, fun _ _ ↦ rfl⟩
  mul_mem' := by
    rintro g h ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨max M N, fun k hk ↦ ?_⟩
    change g (h k) = k
    rw [hN k ((le_max_right _ _).trans_lt hk), hM k ((le_max_left _ _).trans_lt hk)]
  inv_mem' := by
    rintro g ⟨N, hN⟩
    refine ⟨N, fun k hk ↦ g.injective ?_⟩
    change g (g.symm k) = g k
    rw [g.apply_symm_apply, hN k hk]

abbrev G := finitaryPermutations

/-- The finite subgroup of permutations supported in `{0, …, n}`. -/
def level (n : ℕ) : Subgroup G where
  carrier := {g | ∀ k > n, g.val k = k}
  one_mem' := fun _ _ ↦ rfl
  mul_mem' := by
    intro g h hg hh k hk
    change g.val (h.val k) = k
    rw [hh k hk, hg k hk]
  inv_mem' := by
    intro g hg k hk
    apply g.val.injective
    change g.val (g.val.symm k) = g.val k
    rw [g.val.apply_symm_apply, hg k hk]

instance (n : ℕ) : Finite (level n) := by
  let encode (g : level n) (i : Fin (n + 1)) : Fin (n + 1) :=
    ⟨g.val.val i, by
      by_contra! h
      have hk : n < g.val.val i := by omega
      have he : g.val.val (g.val.val i) = g.val.val i := g.property _ hk
      have hh := g.val.val.injective he
      omega⟩
  apply Finite.of_injective encode
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext k
  by_cases hk : k < n + 1
  · exact congrArg Fin.val (congrFun he ⟨k, hk⟩)
  · have hkn : n < k := by omega
    exact (g.property k hkn).trans (h.property k hkn).symm

/-- The transposition carrying zero outside the support of `level n`. -/
noncomputable def swapOutside (n : ℕ) : G :=
  ⟨Equiv.swap 0 (n + 1), ⟨n + 1, fun k hk ↦
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)⟩⟩

/-- The right coset of the finite subgroup used as a Følner block. -/
noncomputable def block (n : ℕ) : Finset G := by
  classical
  letI := Fintype.ofFinite (level n)
  exact Finset.univ.image fun h : level n ↦ h.val * swapOutside n

theorem mem_block (g : G) (n : ℕ) :
    g ∈ block n ↔ ∃ h : G, h ∈ level n ∧ h * swapOutside n = g := by
  classical
  let := Fintype.ofFinite (level n)
  unfold block
  rw [Finset.mem_image]
  constructor
  · rintro ⟨h, _, rfl⟩
    exact ⟨h.val, h.property, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, Finset.mem_univ _, rfl⟩

theorem block_nonempty (n : ℕ) : (block n).Nonempty :=
  ⟨swapOutside n, (mem_block _ n).2 ⟨1, (level n).one_mem, one_mul _⟩⟩

/-- Each fixed left translation eventually fixes the entire block. In the
discrete group with counting measure this gives zero Følner deficit. -/
theorem eventually_leftTranslate_block (g : G) :
    ∀ᶠ n in atTop, (g * ·) '' (block n : Set G) = (block n : Set G) := by
  obtain ⟨N, hN⟩ := g.property
  filter_upwards [eventually_ge_atTop N] with n hn
  have hg : g ∈ level n := fun k hk ↦ hN k (hn.trans_lt hk)
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨h, hh, rfl⟩ := (mem_block s n).1 hs
    exact (mem_block _ n).2 ⟨g * h, (level n).mul_mem hg hh, mul_assoc _ _ _⟩
  · intro ht
    obtain ⟨h, hh, rfl⟩ := (mem_block t n).1 ht
    refine ⟨(g⁻¹ * h) * swapOutside n,
      (mem_block _ n).2 ⟨g⁻¹ * h, (level n).mul_mem ((level n).inv_mem hg) hh, rfl⟩, ?_⟩
    change g * ((g⁻¹ * h) * swapOutside n) = h * swapOutside n
    rw [← mul_assoc, mul_inv_cancel_left]

theorem block_apply_zero {g : G} {n : ℕ} (hg : g ∈ block n) : g.val 0 = n + 1 := by
  obtain ⟨h, hh, rfl⟩ := (mem_block g n).1 hg
  change h.val (Equiv.swap 0 (n + 1) 0) = n + 1
  rw [Equiv.swap_apply_left]
  exact hh _ (Nat.lt_succ_self _)

local notation "H" => lp (fun _ : ℕ ↦ ℂ) 2

private theorem positive_exponent : 0 < (2 : ℝ≥0∞).toReal := by norm_num

noncomputable def permutedVector (g : Equiv.Perm ℕ) (x : H) : H :=
  ⟨fun k ↦ x (g.symm k), memℓp_gen (by
    change Summable ((fun k ↦ ‖x k‖ ^ (2 : ℝ≥0∞).toReal) ∘ g.symm)
    exact g.symm.summable_iff.2 ((lp.memℓp x).summable positive_exponent))⟩

/-- The coordinate permutation is unitary. -/
noncomputable def permute (g : Equiv.Perm ℕ) : H ≃ₗᵢ[ℂ] H where
  toFun := permutedVector g
  invFun := permutedVector g.symm
  left_inv x := lp.ext (funext fun k ↦ by
    change x (g.symm (g k)) = x k
    rw [g.symm_apply_apply])
  right_inv x := lp.ext (funext fun k ↦ by
    change x (g (g.symm k)) = x k
    rw [g.apply_symm_apply])
  map_add' x y := lp.ext (funext fun k ↦ rfl)
  map_smul' c x := lp.ext (funext fun k ↦ rfl)
  norm_map' x := by
    change ‖permutedVector g x‖ = ‖x‖
    rw [lp.norm_eq_tsum_rpow positive_exponent, lp.norm_eq_tsum_rpow positive_exponent]
    congr 1
    exact g.symm.tsum_eq (fun k ↦ ‖x k‖ ^ (2 : ℝ≥0∞).toReal)

noncomputable def representation : G →ₙ* (H →L[ℂ] H) where
  toFun g := (permute g.val).toLinearIsometry.toContinuousLinearMap
  map_mul' _ _ := ContinuousLinearMap.ext fun _ ↦ lp.ext (funext fun _ ↦ rfl)

noncomputable def e (k : ℕ) : H := lp.single 2 k 1

theorem representation_e (g : G) (k : ℕ) : representation g (e k) = e (g.val k) := by
  apply lp.ext
  funext i
  change (lp.single 2 k (1 : ℂ) : H) (g.val.symm i) =
    (lp.single 2 (g.val k) (1 : ℂ) : H) i
  by_cases hi : i = g.val k
  · rw [hi, g.val.symm_apply_apply, lp.single_apply_self, lp.single_apply_self]
  · have hk : g.val.symm i ≠ k := fun h ↦
      hi ((g.val.apply_symm_apply i).symm.trans (congrArg g.val h))
    rw [lp.single_apply_ne (E := fun _ : ℕ ↦ ℂ) 2 k 1 hk,
      lp.single_apply_ne (E := fun _ : ℕ ↦ ℂ) 2 (g.val k) 1 hi]

/-- The absolute coefficient average with respect to normalized counting measure. -/
noncomputable def average (n : ℕ) (f : StrongDual ℂ H) : ℝ :=
  (∑ g ∈ block n, ‖f (representation g (e 0))‖) / (block n).card

theorem average_eq (n : ℕ) (f : StrongDual ℂ H) : average n f = ‖f (e (n + 1))‖ := by
  unfold average
  have hsum : (∑ g ∈ block n, ‖f (representation g (e 0))‖) =
      ∑ _g ∈ block n, ‖f (e (n + 1))‖ := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [representation_e, block_apply_zero hg]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀]
  exact_mod_cast (block_nonempty n).card_ne_zero

theorem average_tendsto_zero (f : StrongDual ℂ H) :
    Tendsto (fun n ↦ average n f) atTop (𝓝 0) := by
  let y := (InnerProductSpace.toDual ℂ H).symm f
  have hs : Summable (fun k : ℕ ↦ ‖y k‖ ^ (2 : ℕ)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp y).summable positive_exponent
  have hindex : Tendsto (fun n : ℕ ↦ n + 1) atTop cofinite :=
    (tendsto_add_atTop_nat 1).mono_right Nat.cofinite_eq_atTop.ge
  have hz := ((Real.continuous_sqrt.tendsto 0).comp hs.tendsto_cofinite_zero).comp hindex
  rw [Real.sqrt_zero] at hz
  convert hz using 1
  funext n
  change average n f = Real.sqrt (‖y (n + 1)‖ ^ 2)
  rw [average_eq, ← InnerProductSpace.toDual_symm_apply, e, lp.inner_single_right,
    RCLike.inner_apply, one_mul, RCLike.norm_conj, Real.sqrt_sq_eq_abs, abs_norm]

theorem norm_e (k : ℕ) : ‖e k‖ = 1 := by
  rw [e, lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞)), norm_one]

theorem weakly_compact :
    IsCompact (weakOperatorClosure representation : Set (H →WOT[ℂ] H)) :=
  compact_weakOperatorClosure_hilbert_contractions representation fun g ↦
    (permute g.val).toLinearIsometry.norm_toContinuousLinearMap_le

theorem e_zero_almostWeaklyStable :
    IsAlmostWeaklyStable (closureAction representation) (e 0) := by
  apply (stable_iff_zero_mem_weakOrbitClosure weakly_compact _).2
  have hi : Function.Injective (topDualPairing ℂ H).flip :=
    separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℂ H)
  let orbit (n : ℕ) := toWeakSpace ℂ H (representation (swapOutside n) (e 0))
  have hweak := WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℂ H).flip hi
    (f := orbit) (x := 0) (l := atTop)
  have ht : Tendsto orbit atTop (𝓝 0) := by
    apply hweak.2
    intro f
    change Tendsto (fun n ↦ f (representation (swapOutside n) (e 0))) atTop (𝓝 (f 0))
    rw [map_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.2
    have h (n : ℕ) : ‖f (representation (swapOutside n) (e 0))‖ = average n f := by
      rw [average_eq, representation_e]
      rfl
    simpa only [h] using average_tendsto_zero f
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun n ↦ ⟨swapOutside n, rfl⟩)

theorem uniform_average_eq_one (n : ℕ) :
    sSup {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ = 1 ∧ average n f = r} = 1 := by
  have hbound : ∀ r ∈ {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ = 1 ∧ average n f = r}, r ≤ 1 := by
    rintro r ⟨f, hf, rfl⟩
    rw [average_eq]
    simpa only [hf, norm_e, one_mul] using f.le_opNorm (e (n + 1))
  let f := InnerProductSpace.toDual ℂ H (e (n + 1))
  have hfnorm : ‖f‖ = 1 := ((InnerProductSpace.toDual ℂ H).norm_map _).trans (norm_e _)
  have hfaverage : average n f = 1 := by
    rw [average_eq]
    change ‖inner ℂ (e (n + 1)) (lp.single 2 (n + 1) 1 : H)‖ = 1
    rw [lp.inner_single_right, e, lp.single_apply_self, RCLike.inner_apply]
    simp
  have hone : 1 ∈ {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ = 1 ∧ average n f = r} :=
    ⟨f, hfnorm, hfaverage⟩
  exact le_antisymm (csSup_le ⟨1, hone⟩ hbound) (le_csSup ⟨1, hbound⟩ hone)

/-- The normalized absolute coefficient moment at a specified real power. -/
noncomputable def powerAverage (p : ℝ) (n : ℕ) (f : StrongDual ℂ H) : ℝ :=
  (∑ g ∈ block n, ‖f (representation g (e 0))‖ ^ p) / (block n).card

theorem powerAverage_eq (p : ℝ) (n : ℕ) (f : StrongDual ℂ H) :
    powerAverage p n f = average n f ^ p := by
  unfold powerAverage
  have hsum : (∑ g ∈ block n, ‖f (representation g (e 0))‖ ^ p) =
      ∑ _g ∈ block n, ‖f (e (n + 1))‖ ^ p := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [representation_e, block_apply_zero hg]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_comm, mul_div_cancel_right₀, average_eq]
  exact_mod_cast (block_nonempty n).card_ne_zero

theorem powerAverage_tendsto_zero {p : ℝ} (hp : 0 < p) (f : StrongDual ℂ H) :
    Tendsto (fun n ↦ powerAverage p n f) atTop (𝓝 0) := by
  simp_rw [powerAverage_eq]
  have hc := (continuous_id.rpow_const (fun _ : ℝ ↦ Or.inr hp.le)).continuousAt
    (x := (0 : ℝ))
  simpa only [Function.comp_def, id_eq, Real.zero_rpow hp.ne'] using
    hc.tendsto.comp (average_tendsto_zero f)

theorem uniform_powerAverage_eq_one {p : ℝ} (hp : 0 < p) (n : ℕ) :
    sSup {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ ≤ 1 ∧ powerAverage p n f = r} = 1 := by
  have hbound : ∀ r ∈ {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ ≤ 1 ∧ powerAverage p n f = r},
      r ≤ 1 := by
    rintro r ⟨f, hf, rfl⟩
    rw [powerAverage_eq, average_eq, ← Real.one_rpow p]
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
    exact (f.le_opNorm (e (n + 1))).trans (by simpa only [norm_e, mul_one] using hf)
  let f := InnerProductSpace.toDual ℂ H (e (n + 1))
  have hfnorm : ‖f‖ = 1 := ((InnerProductSpace.toDual ℂ H).norm_map _).trans (norm_e _)
  have hfaverage : powerAverage p n f = 1 := by
    rw [powerAverage_eq, average_eq]
    change ‖inner ℂ (e (n + 1)) (lp.single 2 (n + 1) 1 : H)‖ ^ p = 1
    rw [lp.inner_single_right, e, lp.single_apply_self, RCLike.inner_apply]
    simp
  have hone : 1 ∈ {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ ≤ 1 ∧ powerAverage p n f = r} :=
    ⟨f, hfnorm.le, hfaverage⟩
  exact le_antisymm (csSup_le ⟨1, hone⟩ hbound) (le_csSup ⟨1, hbound⟩ hone)

/-- The uniform-average conclusion fails with left Følner blocks even for
an almost weakly stable vector in a weakly compact unitary representation. -/
theorem printed_uniform_average_counterexample :
    (∀ n, (block n).Nonempty) ∧
    (∀ g : G, ∀ᶠ n in atTop, (g * ·) '' (block n : Set G) = (block n : Set G)) ∧
    IsCompact (weakOperatorClosure representation : Set (H →WOT[ℂ] H)) ∧
    IsAlmostWeaklyStable (closureAction representation) (e 0) ∧
    (∀ f : StrongDual ℂ H, Tendsto (fun n ↦ average n f) atTop (𝓝 0)) ∧
    ∀ n, sSup {r : ℝ | ∃ f : StrongDual ℂ H, ‖f‖ = 1 ∧ average n f = r} = 1 :=
  ⟨block_nonempty, eventually_leftTranslate_block, weakly_compact, e_zero_almostWeaklyStable,
    average_tendsto_zero, uniform_average_eq_one⟩

end JdLG.LeftFolnerCounterexample
