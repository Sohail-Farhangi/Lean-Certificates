/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-! # The irrational circle-rotation example -/

@[expose] public section

open AddCircle MeasureTheory Module.End Set

namespace JdLG

/-- Monomials on the circle, viewed as the additive circle of period one. -/
noncomputable abbrev circleMonomial : ℤ → C(UnitAddCircle, ℂ) := fourier (T := 1)

private theorem circleMonomial_add (n : ℤ) (x y : UnitAddCircle) :
    circleMonomial n (x + y) = circleMonomial n x * circleMonomial n y := by
  simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]

/-- The action on continuous functions by rotation through integer multiples of
a fixed point on the circle. The integers are given their multiplication notation here. -/
noncomputable def circleRotation (a : UnitAddCircle) :
    Multiplicative ℤ →* (C(UnitAddCircle, ℂ) →L[ℂ] C(UnitAddCircle, ℂ)) where
  toFun n := ContinuousMap.compCLM ℂ ℂ ⟨fun x ↦ x + n.toAdd • a,
    continuous_id.add continuous_const⟩
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro x
    change f (x + (0 : ℤ) • a) = f x
    rw [zero_zsmul, add_zero]
  map_mul' m n := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousMap.ext
    intro x
    change f (x + (m.toAdd + n.toAdd) • a) = f ((x + m.toAdd • a) + n.toAdd • a)
    rw [add_zsmul, add_assoc]

/-- Each circle monomial is an eigenvector of every rotation. -/
theorem circleRotation_monomial (a : UnitAddCircle) (k : ℤ) (n : Multiplicative ℤ) :
    circleRotation a n (circleMonomial k) = circleMonomial k (n.toAdd • a) • circleMonomial k := by
  apply ContinuousMap.ext
  intro x
  change circleMonomial k (x + n.toAdd • a) =
    circleMonomial k (n.toAdd • a) * circleMonomial k x
  rw [circleMonomial_add, mul_comm]

/-- The monomial eigenvalues of a rotation through an irrational angle are distinct. -/
theorem injective_circleMonomial_eval_irrational {a : ℝ} (ha : Irrational a) :
    Function.Injective (fun n : ℤ ↦ circleMonomial n (a : UnitAddCircle)) := by
  intro m n h
  have he : m • (a : UnitAddCircle) = n • (a : UnitAddCircle) :=
    injective_toCircle (T := 1) one_ne_zero (Subtype.ext h)
  have hzero : (m - n) • (a : UnitAddCircle) = 0 := by rw [sub_zsmul, he, add_neg_cancel]
  have hdense : DenseRange (fun k : ℤ ↦ k • (a : UnitAddCircle)) :=
    denseRange_zsmul_coe_iff.2 (by simpa only [div_one] using ha)
  have ho : addOrderOf (a : UnitAddCircle) = 0 := denseRange_zsmul_iff.1 hdense
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.2 hzero
  rw [ho, Nat.cast_zero, zero_dvd_iff] at hd
  exact sub_eq_zero.1 hd

private theorem circleFourierCoeff_injective :
    Function.Injective (fun f : C(UnitAddCircle, ℂ) ↦ fourierCoeff f) := by
  intro f g h
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) (μ := haarAddCircle)
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr, fourierCoeff_toLp, congrFun h n]

private theorem circleRotation_fourierCoeff (a : UnitAddCircle)
    (f : C(UnitAddCircle, ℂ)) (n : ℤ) :
    fourierCoeff (circleRotation a (Multiplicative.ofAdd (1 : ℤ)) f) n =
      circleMonomial n a * fourierCoeff f n := by
  change (∫ x : UnitAddCircle, circleMonomial (-n) x * f (x + (1 : ℤ) • a) ∂haarAddCircle) =
    circleMonomial n a * (∫ x : UnitAddCircle, circleMonomial (-n) x * f x ∂haarAddCircle)
  rw [one_zsmul, ← integral_const_mul]
  have hz : circleMonomial n a * circleMonomial (-n) a = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  calc
    _ = ∫ x : UnitAddCircle,
        circleMonomial n a * (circleMonomial (-n) (x + a) * f (x + a)) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards with x
      rw [circleMonomial_add]
      calc
        _ = (circleMonomial n a * circleMonomial (-n) a) *
            (circleMonomial (-n) x * f (x + a)) := by rw [hz, one_mul]
        _ = _ := by ring
    _ = _ := integral_add_right_eq_self
      (μ := haarAddCircle) (fun x : UnitAddCircle ↦ circleMonomial n a *
        (circleMonomial (-n) x * f x)) a

/-- An eigenfunction of an irrational rotation is a scalar multiple of one
circle monomial. -/
theorem exists_smul_monomial_of_circleRotation_eigenfunction {a : ℝ} (ha : Irrational a)
    {f : C(UnitAddCircle, ℂ)} (hf : f ≠ 0) {eig : ℂ}
    (he : circleRotation (a : UnitAddCircle) (Multiplicative.ofAdd (1 : ℤ)) f = eig • f) :
    ∃ (n : ℤ) (c : ℂ), c ≠ 0 ∧ f = c • circleMonomial n := by
  have hrec (k : ℤ) :
      eig * fourierCoeff f k = circleMonomial k (a : UnitAddCircle) * fourierCoeff f k := by
    have h := circleRotation_fourierCoeff (a : UnitAddCircle) f k
    rw [he, ContinuousMap.coe_smul, fourierCoeff.const_smul, smul_eq_mul] at h
    exact h
  have hex : ∃ n, fourierCoeff f n ≠ 0 := by
    by_contra! h
    apply hf (circleFourierCoeff_injective ?_)
    funext n
    simpa [fourierCoeff] using h n
  obtain ⟨n, hn⟩ := hex
  have heig : eig = circleMonomial n (a : UnitAddCircle) := mul_right_cancel₀ hn (hrec n)
  have hvan (m : ℤ) (hm : m ≠ n) : fourierCoeff f m = 0 := by
    by_contra h
    exact hm (injective_circleMonomial_eval_irrational ha
      ((mul_right_cancel₀ h (hrec m)).symm.trans heig))
  refine ⟨n, fourierCoeff f n, hn, circleFourierCoeff_injective ?_⟩
  funext m
  change fourierCoeff f m = fourierCoeff (fourierCoeff f n • circleMonomial n) m
  rw [ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier]
  rcases eq_or_ne m n with rfl | hm
  · simp
  · simp [hvan m hm, Pi.single_eq_of_ne hm]

private theorem circleMonomial_ne_zero (n : ℤ) : circleMonomial n ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : C(UnitAddCircle, ℂ) ↦ f 0) h
  exact one_ne_zero (by simpa only [fourier_eval_zero, ContinuousMap.zero_apply] using h0)

/-- The finite-dimensional irreducible subrepresentations in the paper's
irrational-rotation example are exactly the one-dimensional monomial spaces. -/
theorem circleRotation_irreducible_iff_monomial {a : ℝ} (ha : Irrational a)
    (W : Submodule ℂ C(UnitAddCircle, ℂ)) [FiniteDimensional ℂ W]
    (hWnz : W ≠ ⊥)
    (hW : ∀ s, ∀ f ∈ W, circleRotation (a : UnitAddCircle) s f ∈ W) :
    (∀ V ≤ W, (∀ s, ∀ f ∈ V, circleRotation (a : UnitAddCircle) s f ∈ V) →
      V = ⊥ ∨ V = W) ↔ ∃ n, W = ℂ ∙ circleMonomial n := by
  constructor
  · intro hirr
    let : Nontrivial W :=
      not_subsingleton_iff_nontrivial.1 fun h ↦ hWnz (Submodule.subsingleton_iff_eq_bot.1 h)
    let g := Multiplicative.ofAdd (1 : ℤ)
    let A : W →L[ℂ] W := (circleRotation (a : UnitAddCircle) g).restrict (hW g)
    let A' : Module.End ℂ W := A.toLinearMap
    obtain ⟨eig, heig⟩ := Module.End.exists_eigenvalue (K := ℂ) (V := W) A'
    obtain ⟨w, hw⟩ := heig.exists_hasEigenvector
    have hwne : (w : C(UnitAddCircle, ℂ)) ≠ 0 :=
      fun e ↦ hw.2 (Subtype.ext e)
    have hex : circleRotation (a : UnitAddCircle) g (w : C(UnitAddCircle, ℂ)) =
        eig • (w : C(UnitAddCircle, ℂ)) :=
      congrArg Subtype.val hw.apply_eq_smul
    obtain ⟨n, c, hc, he⟩ := exists_smul_monomial_of_circleRotation_eigenfunction ha hwne hex
    have hmem : circleMonomial n ∈ W := by
      have h := W.smul_mem c⁻¹ w.2
      simpa only [he, smul_smul, inv_mul_cancel₀ hc, one_smul] using h
    have hline : ∀ s f, f ∈ ℂ ∙ circleMonomial n →
        circleRotation (a : UnitAddCircle) s f ∈ ℂ ∙ circleMonomial n := by
      intro s f hf
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hf
      rw [map_smul, circleRotation_monomial]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    rcases hirr _ ((Submodule.span_singleton_le_iff_mem (circleMonomial n) W).2 hmem) hline
      with hz | heq
    · exact False.elim (circleMonomial_ne_zero n (Submodule.span_singleton_eq_bot.1 hz))
    · exact ⟨n, heq.symm⟩
  · rintro ⟨n, h⟩ V hV _
    by_cases hnz : V = ⊥
    · exact Or.inl hnz
    · right
      obtain ⟨v, hv, hvz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnz
      have hvm : v ∈ ℂ ∙ circleMonomial n := h ▸ hV hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hvm
      have hcnz : c ≠ 0 := fun he ↦ hvz (by simpa only [he, zero_smul] using hc.symm)
      apply le_antisymm hV
      rw [h, Submodule.span_singleton_le_iff_mem]
      have hm := V.smul_mem c⁻¹ hv
      rwa [← hc, smul_smul, inv_mul_cancel₀ hcnz, one_smul] at hm

private theorem circleMonomial_span_coeff_finite {f : C(UnitAddCircle, ℂ)}
    (hf : f ∈ Submodule.span ℂ (range circleMonomial)) :
    ∃ s : Finset ℤ, ∀ n ∉ s, fourierCoeff f n = 0 := by
  classical
  have hi (g : C(UnitAddCircle, ℂ)) : Integrable g haarAddCircle :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine Submodule.span_induction (p := fun (g : C(UnitAddCircle, ℂ)) _ ↦
    ∃ s : Finset ℤ, ∀ n ∉ s, fourierCoeff g n = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨m, rfl⟩
    refine ⟨{m}, fun n hn ↦ ?_⟩
    rw [fourierCoeff_fourier]
    have hne : n ≠ m := fun h ↦ hn (Finset.mem_singleton.2 h)
    simp [hne]
  · exact ⟨∅, fun n _ ↦ by simp [fourierCoeff]⟩
  · intro g k _ _ hg hk
    obtain ⟨s, hs⟩ := hg
    obtain ⟨t, ht⟩ := hk
    refine ⟨s ∪ t, fun n hn ↦ ?_⟩
    simp only [Finset.mem_union, not_or] at hn
    rw [ContinuousMap.coe_add, fourierCoeff.add (hi g) (hi k), Pi.add_apply,
      hs n hn.1, ht n hn.2, add_zero]
  · intro c g _ hg
    obtain ⟨s, hs⟩ := hg
    refine ⟨s, fun n hn ↦ ?_⟩
    rw [ContinuousMap.coe_smul, fourierCoeff.const_smul, hs n hn, smul_zero]

/-- A continuous circle function with infinitely many nonzero Fourier coefficients:
the monomial spaces do not form an algebraic direct sum equal to all continuous functions. -/
theorem exists_circleFunction_not_mem_monomial_span :
    ∃ f : C(UnitAddCircle, ℂ), f ∉ Submodule.span ℂ (range circleMonomial) ∧
      ∀ n : ℤ, fourierCoeff f n ≠ 0 := by
  let r : ℂ := 1 / 2
  have hr : ‖r‖ < 1 := by norm_num [r, norm_div]
  let c : ℤ → ℂ := fun n ↦ r ^ Equiv.intEquivNat n
  have hc : Summable (fun n ↦ ‖c n‖) :=
    Equiv.intEquivNat.summable_iff.2 (summable_norm_geometric_of_norm_lt_one hr)
  have hg : Summable (fun n : ℤ ↦ c n • circleMonomial n) := Summable.of_norm (by
    simpa only [norm_smul, fourier_norm, mul_one] using hc)
  let f : C(UnitAddCircle, ℂ) := ∑' n, c n • circleMonomial n
  have hcf : fourierCoeff f = c := by
    refine fourierCoeff_eq_of_hasSum_of_summable_norm (fun x ↦ ?_) hc
    have h := (ContinuousMap.evalCLM ℂ x).hasSum hg.hasSum
    simpa [f, smul_eq_mul, mul_comm] using h
  have hfnz (n : ℤ) : fourierCoeff f n ≠ 0 := by
    rw [hcf]
    exact pow_ne_zero _ (by norm_num [r])
  refine ⟨f, ?_, hfnz⟩
  intro hf
  obtain ⟨s, hs⟩ := circleMonomial_span_coeff_finite hf
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset s
  exact hfnz n (hs n hn)


/-- The monomial subspaces cannot be realized as an orthogonal Hilbert direct
sum by a bounded linear isomorphism from the continuous functions. The sup norm
of the sum of the first N monomials grows linearly while a sum of N pairwise
orthogonal uniformly bounded vectors has norm at most a constant times √N. -/
theorem circleMonomial_no_orthogonalHilbertEquivalence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : C(UnitAddCircle, ℂ) ≃L[ℂ] H) :
    ¬ Pairwise (fun m n ↦ inner ℂ (L (circleMonomial m)) (L (circleMonomial n)) = 0) := by
  intro horth
  let C := ‖L.symm.toContinuousLinearMap‖
  let D := ‖L.toContinuousLinearMap‖
  obtain ⟨N, hN⟩ := exists_nat_gt ((C * D) ^ 2)
  have hNpos : 0 < (N : ℝ) := (sq_nonneg _).trans_lt hN
  let F := ∑ n ∈ Finset.range N, circleMonomial (n : ℤ)
  let y (n : ℕ) := L (circleMonomial (n : ℤ))
  have hF0 : F 0 = (N : ℂ) := by
    let eval : C(UnitAddCircle, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ (0 : UnitAddCircle)
    change eval (∑ n ∈ Finset.range N, circleMonomial (n : ℤ)) = (N : ℂ)
    rw [map_sum]
    simp only [eval, ContinuousMap.evalCLM_apply, fourier_eval_zero, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  have hFl : (N : ℝ) ≤ ‖F‖ := by
    have h := F.norm_coe_le_norm 0
    rw [hF0, Complex.norm_natCast] at h
    exact h
  have hFu : ‖F‖ ≤ C * ‖L F‖ := by
    have h := L.symm.toContinuousLinearMap.le_opNorm (L F)
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using h
  have hy (n : ℕ) : ‖y n‖ ≤ D := by
    have h := L.toContinuousLinearMap.le_opNorm (circleMonomial (n : ℤ))
    change ‖L.toContinuousLinearMap (circleMonomial (n : ℤ))‖ ≤ ‖L.toContinuousLinearMap‖
    simpa only [fourier_norm, mul_one] using h
  have hsum : L F = ∑ n ∈ Finset.range N, y n := map_sum L _ _
  have hinner :
      inner ℂ (∑ n ∈ Finset.range N, y n) (∑ n ∈ Finset.range N, y n) =
        ∑ n ∈ Finset.range N, inner ℂ (y n) (y n) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [inner_sum]
    apply Finset.sum_eq_single n
    · intro m _ hmn
      exact horth (fun h ↦ hmn ((Int.ofNat.inj h).symm))
    · intro hk
      exact False.elim (hk hn)
  have hLsq : ‖L F‖ ^ 2 ≤ (N : ℝ) * D ^ 2 := by
    calc
      ‖L F‖ ^ 2 = RCLike.re (∑ n ∈ Finset.range N, inner ℂ (y n) (y n)) := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ), hsum, hinner]
      _ = ∑ n ∈ Finset.range N, ‖y n‖ ^ 2 := by
        change RCLike.reCLM (∑ n ∈ Finset.range N, inner ℂ (y n) (y n)) = _
        rw [map_sum]
        exact Finset.sum_congr rfl fun n _ ↦ (norm_sq_eq_re_inner (𝕜 := ℂ) (y n)).symm
      _ ≤ ∑ _ ∈ Finset.range N, D ^ 2 :=
        Finset.sum_le_sum fun n _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hy n) 2
      _ = (N : ℝ) * D ^ 2 := by simp [nsmul_eq_mul]
  have hlast : (N : ℝ) * N ≤ (C * D) ^ 2 * (N : ℝ) := calc
    (N : ℝ) * N = (N : ℝ) ^ 2 := (pow_two _).symm
    _ ≤ (C * ‖L F‖) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (hFl.trans hFu) 2
    _ = C ^ 2 * ‖L F‖ ^ 2 := mul_pow _ _ _
    _ ≤ C ^ 2 * ((N : ℝ) * D ^ 2) := mul_le_mul_of_nonneg_left hLsq (sq_nonneg _)
    _ = (C * D) ^ 2 * (N : ℝ) := by ring
  exact (not_lt_of_ge (le_of_mul_le_mul_right hlast hNpos)) hN


end JdLG
