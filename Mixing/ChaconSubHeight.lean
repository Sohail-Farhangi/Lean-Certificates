/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconColumnCorrelations

@[expose] public section
noncomputable section
namespace Mixing

open MeasureTheory Set
open scoped Classical ENNReal

/-- The shift of a nonnegative observable has the same integral as the
observable. Dropping main levels can only decrease that integral. -/
private theorem chaconColumn_partialNorm_le (n : ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range (chaconTowerHeight n))
    {F : ChaconOdometer × Bool → ℂ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) (q : ℤ) :
    chaconColumnWeight n * (∑ l ∈ I, ∫ x, ‖F (chaconColumnPoint n (q+l) x)‖
      ∂chaconOdometerMeasure) ≤ ∫ x, ‖F x‖ ∂chaconTowerSystem.measure := by
  let S := chaconTowerSystem
  let v (x : ChaconOdometer × Bool) := ‖F x‖
  let w := v ∘ S.act (Multiplicative.ofAdd q)
  have hM : Measurable w := hF.norm.comp (S.preserves _).measurable
  have hC' (x : ChaconOdometer × Bool) : ‖w x‖ ≤ C := by
    change ‖‖F (S.act (Multiplicative.ofAdd q) x)‖‖ ≤ C
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC _
  have hShift : (∫ x, w x ∂S.measure) = ∫ x, v x ∂S.measure := by
    have he := integral_map (μ := S.measure)
      (S.preserves (Multiplicative.ofAdd q)).measurable.aemeasurable hF.norm.aestronglyMeasurable
    rw [(S.preserves _).map_eq] at he
    exact he.symm
  rw [← hShift, integral_chaconColumn hM hC' n]
  change chaconColumnWeight n * _ ≤ chaconColumnWeight n * _
  apply mul_le_mul_of_nonneg_left _ (chaconColumnWeight_nonneg n)
  simp_rw [← chaconColumnPoint_shift]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hI
    (fun _ _ _ ↦ integral_nonneg (fun _ ↦ norm_nonneg _))).trans ?_
  apply le_add_of_nonneg_right
  exact integral_nonneg (fun _ ↦ norm_nonneg _)

private theorem chaconColumn_correlation_norm_le (n l : ℕ) (q : ℤ)
    {f g : ChaconOdometer × Bool → ℂ} (hf : Measurable f) (hg : Measurable g)
    {C D : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖g x‖ ≤ D) :
    ‖∫ x, g (chaconColumnPoint n (l : ℤ) x) * f (chaconColumnPoint n (q+l) x)
        ∂chaconOdometerMeasure‖ ≤
      D * ∫ x, ‖f (chaconColumnPoint n (q+l) x)‖ ∂chaconOdometerMeasure := by
  let F := f ∘ chaconColumnPoint n (q+l)
  let G := g ∘ chaconColumnPoint n l
  have hF : Integrable F chaconOdometerMeasure := Integrable.of_bound
    (hf.comp (measurable_chaconColumnPoint _ _)).aestronglyMeasurable C
    (ae_of_all _ fun _ ↦ hC _)
  have hD₀ : 0 ≤ D := (norm_nonneg _).trans (hD (0, false))
  have hFG : Integrable (fun x ↦ ‖G x * F x‖) chaconOdometerMeasure :=
    Integrable.of_bound ((hg.comp (measurable_chaconColumnPoint _ _)).mul
      (hf.comp (measurable_chaconColumnPoint _ _))).norm.aestronglyMeasurable (D*C)
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul]
        exact mul_le_mul (hD _) (hC _) (norm_nonneg _) hD₀)
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono hFG (hF.norm.const_mul _)
  intro x
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)

private theorem chaconColumn_badLevels_card (h m q : ℕ) :
    ((Finset.range h).filter fun l ↦
      ¬(m ≤ l+q ∧ l+q < h) ∧ ¬(h+m+1 ≤ l+q)).card ≤ 2*m+1 := by
  let I := (Finset.range h).filter fun l ↦ ¬(m ≤ l+q ∧ l+q < h) ∧ ¬(h+m+1 ≤ l+q)
  let J := Finset.range m ∪ Finset.Ico h (h+m+1)
  have he : I.card ≤ J.card := by
    refine Finset.card_le_card_of_injOn (fun l ↦ l+q) ?_ (fun _ _ _ _ h ↦ Nat.add_right_cancel h)
    intro l hl
    have hp := (Finset.mem_filter.mp hl).2
    apply Finset.mem_union.mpr
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  refine he.trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range, Nat.card_Ico]
  omega

/-- At a time between two consecutive fixed height multiples, levels that
stay in the first column and levels that enter the next column contribute
the two adjacent height polynomials. The error comes from at most
`2*m+2` levels, including the optional extra spacer. -/
theorem norm_chaconTower_subHeight_correlation_le (n m q : ℕ) (hq : q < chaconTowerHeight n)
    {N : ℕ} (hN : N ≤ n) {f g : ChaconOdometer × Bool → ℂ}
    (hf₀ : IsChaconPrefixTest N f) (hg₀ : IsChaconPrefixTest N g)
    (hf : Measurable f) (hg : Measurable g) {C D : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖g x‖ ≤ D) :
    ‖∫ x, g x * f (chaconTowerSystem.act (Multiplicative.ofAdd
      ((m * chaconTowerHeight n + q : ℕ) : ℤ)) x) ∂chaconTowerSystem.measure‖ ≤
      D * ((∫ x, ‖chaconHeightObservable m f x‖ ∂chaconTowerSystem.measure) +
        ∫ x, ‖chaconHeightObservable (m+1) f x‖ ∂chaconTowerSystem.measure) +
      chaconColumnWeight n * (2*m+2 : ℝ) * (D*C) := by
  let S := chaconTowerSystem
  let h := chaconTowerHeight n
  let μ := chaconOdometerMeasure
  let w := chaconColumnWeight n
  let K := Finset.range h
  let I := K.filter fun l ↦ m ≤ l+q ∧ l+q < h
  let J := K.filter fun l ↦ h+m+1 ≤ l+q
  let B := K.filter fun l ↦ ¬(m ≤ l+q ∧ l+q < h) ∧ ¬(h+m+1 ≤ l+q)
  let t : ℤ := ((m*h+q : ℕ) : ℤ)
  let F (x : ChaconOdometer × Bool) := g x * f (S.act (Multiplicative.ofAdd t) x)
  let A (l : ℕ) := ∫ x, F (chaconColumnPoint n (l : ℤ) x) ∂μ
  let E := ∫ x in chaconSpacer, F (chaconColumnPoint n (h : ℤ) x) ∂μ
  have hD₀ : 0 ≤ D := (norm_nonneg _).trans (hD (0, false))
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC (0, false))
  have hFM : Measurable F := hg.mul (hf.comp (S.preserves _).measurable)
  have hFb (x : ChaconOdometer × Bool) : ‖F x‖ ≤ D*C := by
    change ‖g x * f (S.act (Multiplicative.ofAdd t) x)‖ ≤ D*C
    rw [norm_mul]
    exact mul_le_mul (hD _) (hC _) (norm_nonneg _) hD₀
  have hE : ‖E‖ ≤ D*C := by
    calc
      _ ≤ (D*C) * μ.real chaconSpacer :=
        norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr (measure_ne_top _ _))
          (fun x _ ↦ hFb (chaconColumnPoint n (h : ℤ) x))
      _ ≤ _ := mul_le_of_le_one_right (mul_nonneg hD₀ hC₀)
        ((measureReal_mono (subset_univ _) (measure_ne_top _ _)).trans_eq (by simp))
  have hB (l : ℕ) : ‖A l‖ ≤ D*C := by
    simpa using norm_integral_le_of_norm_le_const (μ := μ) (C := D*C)
      (ae_of_all _ fun x ↦ hFb (chaconColumnPoint n (l : ℤ) x))
  have hPart :
      (∑ l ∈ K, A l) = (∑ l ∈ I, A l) + (∑ l ∈ J, A l) + ∑ l ∈ B, A l := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    by_cases hi : m ≤ l+q ∧ l+q < h
    · have hj : ¬h+m+1 ≤ l+q := by omega
      simp [hi, hj]
    · by_cases hj : h+m+1 ≤ l+q <;> simp [hi, hj]
  have hBranch (M : ℕ) (r : ℤ) (I' : Finset ℕ) (hI' : I' ⊆ K)
      (ht : t = ((M*h : ℕ) : ℤ) + r)
      (hl : ∀ l ∈ I', (M : ℤ) ≤ r+l ∧ r+l < h) :
      w * ‖∑ l ∈ I', A l‖ ≤ D * ∫ x, ‖chaconHeightObservable M f x‖ ∂S.measure := by
    let f' := chaconHeightObservable M f
    have hf' := measurable_chaconHeightObservable M hf
    have hC' := norm_chaconHeightObservable_le M hC
    have he (l : ℕ) (hm : l ∈ I') :
        A l = ∫ x, g (chaconColumnPoint n (l : ℤ) x) * f' (chaconColumnPoint n (r+l) x) ∂μ := by
      simp only [A, F, S, chaconColumnPoint_shift, ht]
      exact integral_chaconColumn_shift_eq_heightObservable n M l r hN hf₀ hg₀
        (Finset.mem_range.mp (hI' hm)) (hl l hm).1 (hl l hm).2
    have hL (l : ℕ) (hm : l ∈ I') : ‖A l‖ ≤
        D * ∫ x, ‖f' (chaconColumnPoint n (r+l) x)‖ ∂μ := by
      rw [he l hm]
      exact chaconColumn_correlation_norm_le n l r hf' hg hC' hD
    calc
      _ ≤ w * (∑ l ∈ I', D * ∫ x, ‖f' (chaconColumnPoint n (r+l) x)‖ ∂μ) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hL))
          (chaconColumnWeight_nonneg n)
      _ ≤ _ := by
        rw [← Finset.mul_sum, mul_left_comm]
        exact mul_le_mul_of_nonneg_left
          (chaconColumn_partialNorm_le n I' hI' hf' hC' r) hD₀
  have hI := hBranch m q I (Finset.filter_subset _ _) (by simp [t]) (by
    intro l hl
    have he := (Finset.mem_filter.mp hl).2
    rw [add_comm l q] at he
    exact_mod_cast he)
  have hJ := hBranch (m+1) ((q : ℤ)-h) J (Finset.filter_subset _ _) (by
    simp only [t, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring) (by
    intro l hl
    have hlow := (Finset.mem_filter.mp hl).2
    have hup := Finset.mem_range.mp (Finset.mem_filter.mp hl).1
    omega)
  have hBad : w * (‖∑ l ∈ B, A l‖ + ‖E‖) ≤ w * (2*m+2 : ℝ) * (D*C) := by
    have hh : ‖∑ l ∈ B, A l‖ ≤ (B.card : ℝ) * (D*C) := by
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun l _ ↦ hB l).trans_eq (by simp))
    have hcard : (B.card : ℝ) ≤ 2*m+1 := by exact_mod_cast chaconColumn_badLevels_card h m q
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (chaconColumnWeight_nonneg n)
    calc
      _ ≤ (B.card : ℝ) * (D*C) + D*C := add_le_add hh hE
      _ ≤ (2*m+1 : ℝ) * (D*C) + D*C :=
        add_le_add (mul_le_mul_of_nonneg_right hcard (mul_nonneg hD₀ hC₀)) le_rfl
      _ = _ := by ring
  change ‖∫ x, F x ∂S.measure‖ ≤ _
  rw [integral_chaconColumn hFM hFb n]
  change ‖w • ((∑ l ∈ K, A l) + E)‖ ≤ _
  rw [hPart, norm_smul, Real.norm_of_nonneg (chaconColumnWeight_nonneg n)]
  calc
    _ ≤ w * (‖∑ l ∈ I, A l‖ + ‖∑ l ∈ J, A l‖ + (‖∑ l ∈ B, A l‖ + ‖E‖)) := by
      apply mul_le_mul_of_nonneg_left _ (chaconColumnWeight_nonneg n)
      have h₁ := norm_add_le (∑ l ∈ I, A l) (∑ l ∈ J, A l)
      have h₂ := norm_add_le ((∑ l ∈ I, A l) + (∑ l ∈ J, A l)) (∑ l ∈ B, A l)
      have h₃ := norm_add_le ((∑ l ∈ I, A l) + (∑ l ∈ J, A l) + (∑ l ∈ B, A l)) E
      linarith
    _ ≤ _ := by
      rw [mul_add w, mul_add w, mul_add D]
      exact add_le_add (add_le_add hI hJ) hBad

end Mixing
