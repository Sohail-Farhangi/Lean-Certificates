module

public import Mixing.StrongMixing
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section

noncomputable section

namespace Mixing

open MeasureTheory Set
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The lower bound used in Proposition 7(i). -/
theorem norm_ge_of_partialRigidity {T M : H →L[ℂ] H} {a : ℝ}
    (ha : 0 ≤ a) (ha₁ : a ≤ 1) (hM : ‖M‖ ≤ 1)
    (hT : T = (a : ℂ) • 1 + ((1 - a : ℝ) : ℂ) • M) (f : H) :
    (2 * a - 1) * ‖f‖ ≤ ‖T f‖ := by
  have hf' : ‖M f‖ ≤ ‖f‖ :=
    (M.le_opNorm f).trans (by grw [hM, one_mul])
  have hnorm : ‖((1 - a : ℝ) : ℂ) • M f‖ ≤ (1 - a) * ‖f‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha₁)]
    exact mul_le_mul_of_nonneg_left hf' (sub_nonneg.mpr ha₁)
  have htriangle := norm_sub_le (T f) (((1 - a : ℝ) : ℂ) • M f)
  have hsum : T f - ((1 - a : ℝ) : ℂ) • M f = (a : ℂ) • f := by
    rw [hT]
    simp
  rw [hsum, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] at htriangle
  linarith [mul_add ‖f‖ a a, sub_mul 1 a ‖f‖]

/-- Proposition 7(i) at the Markov-operator step: only contractivity of the residual is needed. -/
theorem injective_of_partialRigidity {T M : H →L[ℂ] H} {a : ℝ}
    (ha : 1 / 2 < a) (ha₁ : a ≤ 1) (hM : ‖M‖ ≤ 1)
    (hT : T = (a : ℂ) • 1 + ((1 - a : ℝ) : ℂ) • M) :
    Function.Injective T := by
  intro f g hfg
  have h := norm_ge_of_partialRigidity (by linarith) ha₁ hM hT (f - g)
  have hTf : T (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  by_contra hne
  rw [hTf, norm_zero] at h
  exact (not_le_of_gt (mul_pos (by linarith) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))) h

/-- Proposition 7(ii) on the mean-zero space, where the constants projection vanishes. -/
theorem injective_of_partialWeakMixing {T : H →L[ℂ] H} {a : ℝ} (ha : a < 1)
    (hT : T = ((1 - a : ℝ) : ℂ) • 1) : Function.Injective T := by
  intro f g h
  rw [hT] at h
  have hne : ((1 - a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_pos.mpr ha).ne'
  exact smul_right_injective _ hne h

section Atoms

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A uniform lower bound on all neighbourhood balls transfers to the singleton. -/
theorem measure_singleton_ge_of_ball_lower_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {a : ℝ≥0∞} {x : X} (hgap : ∀ r : ℝ, 0 < r → a ≤ μ (Metric.ball x r)) :
    a ≤ μ {x} := by
  let B (n : ℕ) := Metric.ball x (1 / ((n : ℝ) + 1))
  have hB : Antitone B := fun i j hij ↦
    Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij))
  have hi : (⋂ n, B n) = {x} := by
    ext y
    simp only [mem_iInter, B, Metric.mem_ball, mem_singleton_iff]
    constructor
    · intro hy
      by_contra hne
      have hdist : 0 < dist y x := dist_pos.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / dist y x)
      have hd : 1 / ((n : ℝ) + 1) < dist y x := by
        apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
        have h₁ := (div_lt_iff₀ hdist).mp hn
        nlinarith
      exact (not_lt_of_ge hd.le) (hy n)
    · rintro rfl n
      simpa using (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  rw [← hi, hB.measure_iInter (fun _ ↦ Metric.isOpen_ball.nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  exact le_iInf fun n ↦ hgap _ (by positivity)

/-- The positive gap in fibre masses in Theorem 5.2 forces finite atomic support.

The bound on the cardinality is stated without rounding, as `card * a ≤ 1`. -/
theorem finite_support_of_support_ball_lower_bound [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {a : ℝ≥0∞} (ha : 0 < a) (ha₁ : a ≤ 1)
    (hgap : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r → a ≤ μ (Metric.ball x r)) :
    ∃ s : Finset X, (s : Set X) = μ.support ∧ μ (s : Set X)ᶜ = 0 ∧
      (s.card : ℝ≥0∞) * a ≤ 1 := by
  classical
  have hfinset (s : Finset X) (hs : (s : Set X) ⊆ μ.support) : (s.card : ℝ≥0∞) * a ≤ 1 := by
    have hd : (↑s : Set X).PairwiseDisjoint (fun x ↦ ({x} : Set X)) :=
      fun _ _ _ _ hne ↦ disjoint_singleton.mpr hne
    calc
      (s.card : ℝ≥0∞) * a = ∑ _x ∈ s, a := by simp
      _ ≤ ∑ x ∈ s, μ {x} := Finset.sum_le_sum fun x hx ↦
        measure_singleton_ge_of_ball_lower_bound μ (hgap x (hs hx))
      _ = μ (⋃ x ∈ s, ({x} : Set X)) :=
        (measure_biUnion_finset hd fun x _ ↦ measurableSet_singleton x).symm
      _ ≤ 1 := prob_le_one
  have hs : μ.support.Finite := by
    by_contra hnot
    have hinf : μ.support.Infinite := hnot
    have hatop : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha₁
    have hareal : 0 < a.toReal := ENNReal.toReal_pos ha.ne' hatop
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / a.toReal)
    obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq n
    have hbound := hfinset s hs
    have hreal := ENNReal.toReal_mono ENNReal.one_ne_top hbound
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one, hcard] at hreal
    exact (not_lt_of_ge hreal) ((div_lt_iff₀ hareal).mp hn)
  exact ⟨hs.toFinset, hs.coe_toFinset, by rw [hs.coe_toFinset]; exact μ.measure_compl_support,
    hfinset _ (by rw [hs.coe_toFinset])⟩

/-- A probability measure with a positive gap in its nonzero measurable set
masses has finite support, with the cardinality bound of Theorem 5.2. -/
theorem finite_support_of_measure_gap [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] {a : ℝ≥0∞} (ha : 0 < a) (ha₁ : a ≤ 1)
    (hgap : ∀ B, MeasurableSet B → μ B ≠ 0 → a ≤ μ B) :
    ∃ s : Finset X, (s : Set X) = μ.support ∧ μ (s : Set X)ᶜ = 0 ∧
      (s.card : ℝ≥0∞) * a ≤ 1 :=
  finite_support_of_support_ball_lower_bound μ ha ha₁ fun x hx r hr ↦
    hgap (Metric.ball x r) Metric.isOpen_ball.measurableSet
      ((Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds _ hr)).ne'

end Atoms

end Mixing
