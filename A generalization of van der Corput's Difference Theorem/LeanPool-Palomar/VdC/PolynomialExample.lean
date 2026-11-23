/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.CubeDifference
public import VdC.PolynomialPhases
public import VdC.ResidueAverages
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! The polynomial-like example in Section 4. The real expressions are interpreted
modulo one, and the two parity classes are averaged separately. -/

@[expose] public section

open Filter Function Finset MeasureTheory
open scoped Topology BigOperators

namespace VdC

noncomputable section

/-- The integer coefficient of `α` in the manuscript's polynomial-like sequence. -/
def polynomialLikeIndex (n : ℕ) : ℤ :=
  if n % 2 = 0 then (n : ℤ) ^ 2 else 2 * ((n : ℤ) - 1) ^ 2

@[simp] theorem polynomialLikeIndex_even (j : ℕ) :
    polynomialLikeIndex (2 * j) = 4 * (j : ℤ) ^ 2 := by
  simp only [polynomialLikeIndex, show (2 * j) % 2 = 0 by omega, ite_true,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

@[simp] theorem polynomialLikeIndex_odd (j : ℕ) :
    polynomialLikeIndex (2 * j + 1) = 8 * (j : ℤ) ^ 2 := by
  simp only [polynomialLikeIndex, show ¬(2 * j + 1) % 2 = 0 by omega, ite_false,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

private def squarePair (α : ℝ) (A B : ℤ) (q n : ℕ) : ℂ :=
  phase (α * ((A : ℝ) * (n : ℝ)^2 + (B : ℝ) * ((n + q : ℕ) : ℝ)^2))

private theorem squarePair_tendsto_zero {α : ℝ} (hα : Irrational α) (A B : ℤ) (q : ℕ)
    (h : A + B ≠ 0 ∨ B ≠ 0 ∧ 0 < q) :
    Tendsto (cesaro (squarePair α A B q)) atTop (𝓝 0) := by
  let L : ℤ := 2 * B * (q : ℤ)
  let C : ℤ := B * (q : ℤ)^2
  have he : squarePair α A B q = fun n : ℕ ↦
      phase (α * (((A + B : ℤ) : ℝ) * (n : ℝ)^2 + (L : ℝ) * (n : ℝ) + (C : ℝ))) := by
    funext n
    unfold squarePair L C
    congr 1
    push_cast
    ring
  rw [he]
  apply tendsto_cesaro_integer_quadratic_phase hα
  rcases h with h | ⟨hB, hq⟩
  · exact Or.inl h
  · exact Or.inr (mul_ne_zero (mul_ne_zero (by norm_num) hB) (by omega))

private theorem squarePair_tendsto_of_shift {α : ℝ} (hα : Irrational α) {A B : ℤ} {q : ℕ}
    (h : A ≠ 0 ∨ B ≠ 0) (hq : 0 < q) : Tendsto (cesaro (squarePair α A B q)) atTop (𝓝 0) := by
  apply squarePair_tendsto_zero hα
  by_cases hB : B = 0
  · exact Or.inl (by simpa only [hB, add_zero] using h.resolve_right (by simpa only [not_not] using hB))
  · exact Or.inr ⟨hB, hq⟩

private def polynomialPairPhase (α : ℝ) (a b : ℤ) (h n : ℕ) : ℂ :=
  phase (α * ((a : ℝ) * (polynomialLikeIndex n : ℝ) +
    (b : ℝ) * (polynomialLikeIndex (n + h) : ℝ)))

private theorem polynomialPairPhase_even_even (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q) (2 * n) = squarePair α (4 * a) (4 * b) q n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + 2 * q = 2 * (n + q) by omega,
    polynomialLikeIndex_even, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_odd_even (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q) (2 * n + 1) = squarePair α (8 * a) (8 * b) q n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + 1 + 2 * q = 2 * (n + q) + 1 by omega,
    polynomialLikeIndex_odd, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_even_odd (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q + 1) (2 * n) = squarePair α (4 * a) (8 * b) q n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + (2 * q + 1) = 2 * (n + q) + 1 by omega,
    polynomialLikeIndex_even, polynomialLikeIndex_odd, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_odd_odd (α : ℝ) (a b : ℤ) (q n : ℕ) :
    polynomialPairPhase α a b (2 * q + 1) (2 * n + 1) = squarePair α (8 * a) (4 * b) (q + 1) n := by
  simp only [polynomialPairPhase, squarePair, show 2 * n + 1 + (2 * q + 1) = 2 * (n + (q + 1)) by omega,
    polynomialLikeIndex_even, polynomialLikeIndex_odd, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast]
  congr 1
  ring

private theorem polynomialPairPhase_bounded (α : ℝ) (a b : ℤ) (h : ℕ) :
    BoundedSeq (polynomialPairPhase α a b h) := ⟨1, zero_le_one, fun _ ↦ (norm_phase _).le⟩

private theorem tendsto_cesaro_of_two_residues {u : ℕ → ℂ} (hu : BoundedSeq u) {a b : ℂ}
    (he : Tendsto (cesaro (fun n ↦ u (2*n))) atTop (𝓝 a))
    (ho : Tendsto (cesaro (fun n ↦ u (2*n+1))) atTop (𝓝 b)) :
    Tendsto (cesaro u) atTop (𝓝 ((a + b) / 2)) := by
  have h := tendsto_cesaro_of_residue_limits (r := 2) (by decide) hu (fun t ↦ if t = 0 then a else b) (by
    intro t ht
    interval_cases t
    · simpa only [add_zero, ite_true] using he
    · simpa using ho)
  simpa [Finset.sum_range_succ] using h

private theorem polynomialPairPhase_tendsto_zero {α : ℝ} (hα : Irrational α) {a b : ℤ} {h : ℕ}
    (hnz : a ≠ 0 ∨ b ≠ 0) (hh : 1 < h) :
    Tendsto (cesaro (polynomialPairPhase α a b h)) atTop (𝓝 0) := by
  have hnz_mul {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) : c * a ≠ 0 ∨ d * b ≠ 0 :=
    hnz.imp (mul_ne_zero hc) (mul_ne_zero hd)
  have hex : ∃ q, h = 2 * q ∨ h = 2 * q + 1 := ⟨h / 2, by omega⟩
  rw [show (0 : ℂ) = (0 + 0) / 2 by norm_num]
  apply tendsto_cesaro_of_two_residues (polynomialPairPhase_bounded α a b h)
  · obtain ⟨q, rfl | rfl⟩ := hex
    · simp_rw [polynomialPairPhase_even_even]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)
    · simp_rw [polynomialPairPhase_even_odd]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)
  · obtain ⟨q, rfl | rfl⟩ := hex
    · simp_rw [polynomialPairPhase_odd_even]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)
    · simp_rw [polynomialPairPhase_odd_odd]
      exact squarePair_tendsto_of_shift hα (hnz_mul (by norm_num) (by norm_num)) (by omega)

private theorem polynomialDifferencePhase_tendsto_zero {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) {h : ℕ} (hh : 0 < h) :
    Tendsto (cesaro (polynomialPairPhase α (-m) m h)) atTop (𝓝 0) := by
  by_cases he : h = 1
  · subst h
    have he' : Tendsto (cesaro (fun n ↦ polynomialPairPhase α (-m) m (2 * 0 + 1) (2*n)))
        atTop (𝓝 0) := by
      simp_rw [polynomialPairPhase_even_odd]
      exact squarePair_tendsto_zero hα _ _ _ (Or.inl (by omega))
    have ho : Tendsto (cesaro (fun n ↦ polynomialPairPhase α (-m) m (2 * 0 + 1) (2*n+1)))
        atTop (𝓝 0) := by
      simp_rw [polynomialPairPhase_odd_odd]
      exact squarePair_tendsto_of_shift hα (Or.inr (mul_ne_zero (by norm_num) hm)) (by decide)
    simpa using tendsto_cesaro_of_two_residues (polynomialPairPhase_bounded α (-m) m 1) he' ho
  · exact polynomialPairPhase_tendsto_zero hα (Or.inr hm) (by omega)

private theorem polynomialPairPhase_lagOne {α : ℝ} (hα : Irrational α) :
    Tendsto (cesaro (polynomialPairPhase α 2 (-1) 1)) atTop (𝓝 ((1 : ℂ) / 2)) := by
  have he (n : ℕ) : polynomialPairPhase α 2 (-1) 1 (2*n) = 1 := by
    change polynomialPairPhase α 2 (-1) (2*0+1) (2*n) = _
    rw [polynomialPairPhase_even_odd]
    unfold squarePair
    rw [show α * (((4 * 2 : ℤ) : ℝ) * (n : ℝ)^2 +
      ((8 * (-1) : ℤ) : ℝ) * ((n + 0 : ℕ) : ℝ)^2) = 0 by simp, phase_zero]
  have hEven : Tendsto (cesaro (fun n ↦ polynomialPairPhase α 2 (-1) 1 (2*n))) atTop (𝓝 1) := by
    simpa only [he] using cesaro_tendsto_const (1 : ℂ)
  have hOdd : Tendsto (cesaro (fun n ↦ polynomialPairPhase α 2 (-1) (2*0+1) (2*n+1))) atTop (𝓝 0) := by
    simp_rw [polynomialPairPhase_odd_odd]
    exact squarePair_tendsto_zero hα _ _ _ (Or.inl (by norm_num))
  simpa using tendsto_cesaro_of_two_residues (polynomialPairPhase_bounded α 2 (-1) 1) hEven hOdd

/-- The torus representation of the polynomial-like sequence. -/
def polynomialLikeTorus (α : ℝ) (n : ℕ) : Torus 1 :=
  fun _ ↦ ((α * (polynomialLikeIndex n : ℝ) : ℝ) : UnitAddCircle)

/-- The two-coordinate lag-pair torus sequence. -/
def polynomialLikeLagPair (α : ℝ) (h n : ℕ) : Torus 2 :=
  ![polynomialLikeTorus α n 0, polynomialLikeTorus α (n + h) 0]

private theorem polynomialLikeLagPair_character (α : ℝ) (h n : ℕ) (m : Fin 2 → ℤ) :
    torusCharacter m (polynomialLikeLagPair α h n) = polynomialPairPhase α (m 0) (m 1) h n := by
  rw [torusCharacter_apply, Fin.prod_univ_two]
  change fourier (m 0) ((α * (polynomialLikeIndex n : ℝ) : ℝ) : UnitAddCircle) *
    fourier (m 1) ((α * (polynomialLikeIndex (n + h) : ℝ) : ℝ) : UnitAddCircle) = _
  rw [phase_frequency, phase_frequency, ← phase_add]
  unfold polynomialPairPhase
  congr 1
  ring

private theorem polynomialLikeDifference_character (α : ℝ) (h n : ℕ) (m : Fin 1 → ℤ) :
    torusCharacter m (polynomialLikeTorus α (n + h) - polynomialLikeTorus α n) =
      polynomialPairPhase α (-(m 0)) (m 0) h n := by
  rw [torusCharacter_apply, Fin.prod_univ_one]
  change fourier (m 0) (((α * (polynomialLikeIndex (n + h) : ℝ) : ℝ) : UnitAddCircle) -
    ((α * (polynomialLikeIndex n : ℝ) : ℝ) : UnitAddCircle)) = _
  rw [← AddCircle.coe_sub, phase_frequency]
  unfold polynomialPairPhase
  congr 1
  push_cast
  ring

private theorem nonzero_pair_frequency {m : Fin 2 → ℤ} (hm : m ≠ 0) : m 0 ≠ 0 ∨ m 1 ≠ 0 := by
  by_contra! h
  apply hm
  ext i
  fin_cases i <;> simp [h]

/-- Every positive-lag difference of the polynomial example is uniformly distributed. -/
theorem polynomialLike_differences_equidistributed {α : ℝ} (hα : Irrational α) {h : ℕ} (hh : 0 < h) :
    Equidistributed (torusHaar 1) (fun n ↦ polynomialLikeTorus α (n + h) - polynomialLikeTorus α n) := by
  apply (equidistributed_torus_iff _).2
  intro m hm
  have hm0 : m 0 ≠ 0 := by
    intro he
    apply hm
    ext i
    fin_cases i
    exact he
  simpa only [polynomialLikeDifference_character] using polynomialDifferencePhase_tendsto_zero hα hm0 hh

/-- At lag one, the character of frequency `(2,-1)` has limiting average `1/2`. -/
theorem polynomialLike_lag_one_fourier_half {α : ℝ} (hα : Irrational α) :
    Tendsto (cesaro (fun n ↦ torusCharacter (![2, -1] : Fin 2 → ℤ) (polynomialLikeLagPair α 1 n)))
      atTop (𝓝 ((1 : ℂ) / 2)) := by
  simpa only [polynomialLikeLagPair_character, Matrix.cons_val_zero, Matrix.cons_val_one] using
    polynomialPairPhase_lagOne hα

/-- The lag pairs are uniformly distributed exactly at lags greater than one. -/
theorem polynomialLike_lag_pairs_equidistributed_iff {α : ℝ} (hα : Irrational α) (h : ℕ) :
    Equidistributed (torusHaar 2) (polynomialLikeLagPair α h) ↔ 1 < h := by
  rw [equidistributed_torus_iff]
  constructor
  · intro hUD
    by_contra! hh
    interval_cases h
    · let m : Fin 2 → ℤ := ![1, -1]
      have hm : m ≠ 0 := by intro he; have h0 := congrFun he 0; norm_num [m] at h0
      have hlim := hUD m hm
      have he (n : ℕ) : torusCharacter m (polynomialLikeLagPair α 0 n) = 1 := by
        rw [polynomialLikeLagPair_character]
        unfold m polynomialPairPhase
        simp
      have hone : Tendsto (cesaro (fun n ↦ torusCharacter m (polynomialLikeLagPair α 0 n))) atTop (𝓝 1) := by
        simpa only [he] using cesaro_tendsto_const (1 : ℂ)
      exact one_ne_zero (tendsto_nhds_unique hone hlim)
    · let m : Fin 2 → ℤ := ![2, -1]
      have hm : m ≠ 0 := by intro he; have h0 := congrFun he 0; norm_num [m] at h0
      have hlim := hUD m hm
      have hone : Tendsto (cesaro (fun n ↦ torusCharacter m (polynomialLikeLagPair α 1 n)))
          atTop (𝓝 ((1 : ℂ) / 2)) := by
        exact polynomialLike_lag_one_fourier_half hα
      have := tendsto_nhds_unique hone hlim
      norm_num at this
  · intro hh m hm
    simpa only [polynomialLikeLagPair_character] using polynomialPairPhase_tendsto_zero hα
      (nonzero_pair_frequency hm) hh

/-- The closed-interval representatives of the manuscript's sequence, reduced modulo one. -/
def polynomialLikeSequence (α : ℝ) (n : ℕ) : Cube 1 :=
  fun i ↦ unitRepresentative (polynomialLikeTorus α n i)

@[simp] theorem cubeToTorus_polynomialLikeSequence (α : ℝ) (n : ℕ) :
    cubeToTorus (polynomialLikeSequence α n) = polynomialLikeTorus α n := by
  funext i
  exact unitRepresentative_coe _

/-- The closed-cube lag pair, with the two samples as its two coordinates. -/
def polynomialLikeCubePair (α : ℝ) (h n : ℕ) : Cube 2 :=
  ![polynomialLikeSequence α n 0, polynomialLikeSequence α (n + h) 0]

@[simp] theorem cubeToTorus_polynomialLikeCubePair (α : ℝ) (h n : ℕ) :
    cubeToTorus (polynomialLikeCubePair α h n) = polynomialLikeLagPair α h n := by
  funext i
  fin_cases i <;> simp [cubeToTorus, polynomialLikeCubePair, polynomialLikeLagPair,
    polynomialLikeSequence, unitRepresentative_coe]

theorem polynomialLike_cube_pairs_equidistributed_iff {α : ℝ} (hα : Irrational α) (h : ℕ) :
    Equidistributed (cubeLebesgue 2) (polynomialLikeCubePair α h) ↔ 1 < h := by
  rw [← polynomialLike_lag_pairs_equidistributed_iff hα h]
  constructor
  · intro H
    simpa only [cubeToTorus_polynomialLikeCubePair] using equidistributed_cubeToTorus H
  · intro H
    apply equidistributed_of_cubeToTorus
    simpa only [cubeToTorus_polynomialLikeCubePair] using H

/-- The modulo-one positive-lag difference sequence in the closed interval. -/
def polynomialLikeDifference (α : ℝ) (h n : ℕ) : Cube 1 :=
  fun i ↦ unitRepresentative ((polynomialLikeTorus α (n + h) - polynomialLikeTorus α n) i)

theorem polynomialLike_cube_differences_equidistributed {α : ℝ} (hα : Irrational α)
    {h : ℕ} (hh : 0 < h) : Equidistributed (cubeLebesgue 1) (polynomialLikeDifference α h) := by
  apply equidistributed_of_cubeToTorus
  have he (n : ℕ) : cubeToTorus (polynomialLikeDifference α h n) =
      polynomialLikeTorus α (n + h) - polynomialLikeTorus α n := by
    funext i
    exact unitRepresentative_coe _
  simpa only [he] using polynomialLike_differences_equidistributed hα hh

theorem polynomialLike_spectrallyLebesgue {α : ℝ} (hα : Irrational α) :
    SpectrallyLebesgueDistribution (cubeLebesgue 1) (polynomialLikeSequence α) := by
  apply (cube_sLebesgue_iff_characters _).2
  intro m hm
  let u (n : ℕ) := torusCharacter m (polynomialLikeTorus α n)
  simp only [cubeToTorus_polynomialLikeSequence]
  change SpectrallyLebesgue u
  have hu : BoundedSeq u := bounded_test (torusCharacter m) (polynomialLikeTorus α)
  apply spectrallyLebesgue_of_limsup_square_summable hu
  have hcorr (h : ℕ) : Tendsto (corr u u (h + 1)) atTop (𝓝 0) := by
    have hep := (equidistributed_torus_iff _).1
      (polynomialLike_differences_equidistributed hα (Nat.succ_pos h)) m hm
    unfold corr
    simpa only [torusCharacter_point_sub, u, Nat.succ_eq_add_one] using hep
  have hzero (h : ℕ) : limsup (fun N ↦ ‖corr u u (h + 1) N‖ ^ 2) atTop = 0 := by
    have ht : Tendsto (fun N ↦ ‖corr u u (h + 1) N‖ ^ 2) atTop (𝓝 0) := by
      simpa using (hcorr h).norm.pow 2
    exact ht.limsup_eq
  change Summable (fun h : ℕ ↦ limsup (fun N ↦ ‖corr u u (h + 1) N‖ ^ 2) atTop)
  simpa only [hzero] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))

private def polynomialCubeCharacter (k : ℤ) : C(Cube 1, ℂ) :=
  (torusCharacter (fun _ ↦ k)).comp ⟨cubeToTorus, continuous_cubeToTorus 1⟩

private theorem testMean_polynomialCubeCharacter (k : ℤ) (hk : k ≠ 0) :
    testMean (cubeLebesgue 1) (polynomialCubeCharacter k) = 0 := by
  let g : C(Torus 1, ℂ) := torusCharacter (fun _ ↦ k)
  have hg : testMean (cubeLebesgue 1) (polynomialCubeCharacter k) = testMean (torusHaar 1) g := by
    unfold testMean
    rw [← (cubeToTorus_measurePreserving 1).map_eq,
      integral_map_of_stronglyMeasurable (continuous_cubeToTorus 1).measurable g.continuous.stronglyMeasurable]
    rfl
  have hfreq : (fun _ : Fin 1 ↦ k) ≠ 0 := fun h ↦ hk (congrFun h 0)
  rw [hg]
  simp only [g, testMean_torusCharacter, ite_eq_right hfreq]

theorem polynomialLike_not_orthogonal {α : ℝ} (hα : Irrational α) :
    ¬ OrthogonalDistribution (cubeLebesgue 1) (polynomialLikeSequence α) := by
  intro ho
  have hp := (cube_orthogonal_iff_lag_pairs _).1 ho 1 (by decide)
  let f := polynomialCubeCharacter 2
  let g := polynomialCubeCharacter (-1)
  have htest := hp (productTest f g)
  have hmean : testMean ((cubeLebesgue 1).prod (cubeLebesgue 1)) (productTest f g) = 0 := by
    calc
      _ = testMean (cubeLebesgue 1) f * testMean (cubeLebesgue 1) g := integral_prod_mul _ _
      _ = 0 := by
        rw [show testMean (cubeLebesgue 1) f = 0 from testMean_polynomialCubeCharacter 2 (by norm_num), zero_mul]
  rw [hmean] at htest
  have he (n : ℕ) : productTest f g (polynomialLikeSequence α n, polynomialLikeSequence α (n + 1)) =
      polynomialPairPhase α 2 (-1) 1 n := by
    have ht := polynomialLikeLagPair_character α 1 n ![2, -1]
    simpa only [productTest_apply, f, g, polynomialCubeCharacter, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, cubeToTorus_polynomialLikeSequence, torusCharacter_apply,
      Fin.prod_univ_one, Fin.prod_univ_two, polynomialLikeLagPair, Matrix.cons_val_zero,
      Matrix.cons_val_one] using ht
  have hz : Tendsto (cesaro (polynomialPairPhase α 2 (-1) 1)) atTop (𝓝 0) := by
    simpa only [he] using htest
  have := tendsto_nhds_unique (polynomialPairPhase_lagOne hα) hz
  norm_num at this

/-- The polynomial-like example in the manuscript, including all positive-lag
differences and the exact lag-pair classification. -/
theorem polynomialLikeCounterExample {α : ℝ} (hα : Irrational α) :
    SpectrallyLebesgueDistribution (cubeLebesgue 1) (polynomialLikeSequence α) ∧
      ¬ OrthogonalDistribution (cubeLebesgue 1) (polynomialLikeSequence α) ∧
      (∀ h : ℕ, 0 < h → Equidistributed (cubeLebesgue 1) (polynomialLikeDifference α h)) ∧
      (∀ h : ℕ, Equidistributed (cubeLebesgue 2) (polynomialLikeCubePair α h) ↔ 1 < h) :=
  ⟨polynomialLike_spectrallyLebesgue hα, polynomialLike_not_orthogonal hα,
    fun _ ↦ polynomialLike_cube_differences_equidistributed hα,
    polynomialLike_cube_pairs_equidistributed_iff hα⟩

end

end VdC
