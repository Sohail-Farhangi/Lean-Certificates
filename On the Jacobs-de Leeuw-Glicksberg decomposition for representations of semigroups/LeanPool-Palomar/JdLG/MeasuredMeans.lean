/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Means on essentially bounded measurable functions

The positive functional and the return-time arguments in Theorem 4.2 of
arXiv:2509.24003v3 use Mathlib's real `Lp` at exponent `∞`. This works for
infinite base measure and requires no countable additivity of the mean.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace JdLG

variable {S : Type*} [MeasurableSpace S] {μ : Measure S}

/-- Constant functions are essentially bounded on an arbitrary measure space. -/
theorem memLp_top_constant (c : ℝ) : MemLp (fun _ : S ↦ c) ∞ μ :=
  memLp_top_of_bound aestronglyMeasurable_const ‖c‖ (ae_of_all _ fun _ ↦ le_rfl)

/-- A positive normalized linear functional on real `L∞(μ)`. Positivity is
expressed using the almost everywhere order on representatives. -/
structure MeasuredMean (μ : Measure S) where
  functional : Lp ℝ ∞ μ →ₗ[ℝ] ℝ
  monotone' : ∀ a b, (∀ᵐ x ∂μ, a x ≤ b x) → functional a ≤ functional b
  unit' : functional ((memLp_top_constant (μ := μ) 1).toLp (fun _ ↦ 1)) = 1

namespace MeasuredMean

variable (m : MeasuredMean μ)

/-- Evaluate the mean on an essentially bounded measurable representative. -/
noncomputable def value (f : S → ℝ) (hf : MemLp f ∞ μ) : ℝ := m.functional (hf.toLp f)

theorem value_congr_ae {f g : S → ℝ} {hf : MemLp f ∞ μ} {hg : MemLp g ∞ μ}
    (h : f =ᵐ[μ] g) : m.value f hf = m.value g hg := by
  apply congrArg m.functional
  exact Lp.ext ((MemLp.coeFn_toLp hf).trans (h.trans (MemLp.coeFn_toLp hg).symm))

theorem value_mono {f g : S → ℝ} {hf : MemLp f ∞ μ} {hg : MemLp g ∞ μ}
    (h : ∀ᵐ x ∂μ, f x ≤ g x) : m.value f hf ≤ m.value g hg := by
  apply m.monotone'
  filter_upwards [h, MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x hx hfx hgx
  rwa [hfx, hgx]

theorem value_add {f g : S → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    m.value (f + g) (hf.add hg) = m.value f hf + m.value g hg := by
  exact (congrArg m.functional (MemLp.toLp_add hf hg)).trans (map_add m.functional _ _)

theorem value_smul (c : ℝ) {f : S → ℝ} (hf : MemLp f ∞ μ) :
    m.value (c • f) (hf.const_smul c) = c * m.value f hf := by
  exact (congrArg m.functional (MemLp.toLp_const_smul c hf)).trans (map_smul m.functional c _)

theorem value_one : m.value (fun _ ↦ 1) (memLp_top_constant 1) = 1 := m.unit'

theorem value_constant (c : ℝ) : m.value (fun _ ↦ c) (memLp_top_constant c) = c := by
  calc
    _ = m.value (c • (fun _ ↦ 1)) ((memLp_top_constant 1).const_smul c) :=
      m.value_congr_ae (ae_of_all _ fun _ ↦ (mul_one c).symm)
    _ = c * m.value (fun _ ↦ 1) (memLp_top_constant 1) := m.value_smul c _
    _ = c := by rw [m.value_one, mul_one]

theorem value_nonneg {f : S → ℝ} (hf : MemLp f ∞ μ) (h : ∀ᵐ x ∂μ, 0 ≤ f x) :
    0 ≤ m.value f hf := by
  rw [← m.value_constant 0]
  exact m.value_mono h

theorem memLp_indicator_one {A : Set S} (hA : MeasurableSet A) :
    MemLp (A.indicator (fun _ ↦ (1 : ℝ))) ∞ μ := by
  have hm : Measurable (A.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hA
  apply memLp_top_of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun x ↦ by
    by_cases hx : x ∈ A <;> simp [hx]

/-- The mass of a measurable set is the value of its indicator. -/
noncomputable def mass (A : Set S) (hA : MeasurableSet A) : ℝ :=
  m.value (A.indicator (fun _ ↦ 1)) (memLp_indicator_one hA)

theorem mass_nonneg {A : Set S} (hA : MeasurableSet A) : 0 ≤ m.mass A hA := by
  refine m.value_nonneg _ (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ A <;> simp [hx]

theorem mass_mono {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) :
    m.mass A hA ≤ m.mass B hB := by
  apply m.value_mono
  refine ae_of_all _ fun x ↦ ?_
  by_cases hx : x ∈ A
  · simp [hx, h hx]
  · by_cases hy : x ∈ B <;> simp [hx, hy]

theorem mass_univ : m.mass Set.univ MeasurableSet.univ = 1 := by
  rw [← m.value_one]
  apply m.value_congr_ae
  exact ae_of_all _ fun x ↦ Set.indicator_of_mem (Set.mem_univ x) _

theorem mass_le_one {A : Set S} (hA : MeasurableSet A) : m.mass A hA ≤ 1 :=
  (m.mass_mono hA MeasurableSet.univ (subset_univ A)).trans_eq m.mass_univ

theorem mass_compl_add {A : Set S} (hA : MeasurableSet A) :
    m.mass A hA + m.mass Aᶜ hA.compl = 1 := by
  calc
    _ = m.value _ ((memLp_indicator_one hA).add (memLp_indicator_one hA.compl)) :=
      (m.value_add _ _).symm
    _ = m.value (fun _ ↦ 1) (memLp_top_constant 1) := by
      apply m.value_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      by_cases hx : x ∈ A <;> simp [Pi.add_apply, hx]
    _ = 1 := m.value_one

theorem mass_union_le {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    m.mass (A ∪ B) (hA.union hB) ≤ m.mass A hA + m.mass B hB := by
  refine le_trans ?_ (m.value_add (memLp_indicator_one hA) (memLp_indicator_one hB)).le
  apply m.value_mono
  refine ae_of_all _ fun x ↦ ?_
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
    simp [Pi.add_apply, ha, hb]

theorem mass_inter_eq_one {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ha : m.mass A hA = 1) (hb : m.mass B hB = 1) : m.mass (A ∩ B) (hA.inter hB) = 1 := by
  have ha' : m.mass Aᶜ hA.compl = 0 := by linarith [m.mass_compl_add hA]
  have hb' : m.mass Bᶜ hB.compl = 0 := by linarith [m.mass_compl_add hB]
  have hz : m.mass (Aᶜ ∪ Bᶜ) (hA.compl.union hB.compl) = 0 := by
    apply le_antisymm _ (m.mass_nonneg (hA.compl.union hB.compl))
    simpa only [ha', hb', zero_add] using m.mass_union_le hA.compl hB.compl
  have hz' : m.mass (A ∩ B)ᶜ (hA.inter hB).compl = 0 := by
    simpa only [compl_inter] using hz
  linarith [m.mass_compl_add (hA.inter hB)]

/-- Supersets of measurable sets of full mean form a filter. -/
noncomputable def fullMassFilter : Filter S where
  sets := {A | ∃ B : Set S, ∃ hB : MeasurableSet B, m.mass B hB = 1 ∧ B ⊆ A}
  univ_sets := ⟨Set.univ, MeasurableSet.univ, m.mass_univ, Subset.rfl⟩
  sets_of_superset := fun ⟨B, hB, hm, hsub⟩ h ↦ ⟨B, hB, hm, hsub.trans h⟩
  inter_sets := fun ⟨A, hA, ha, hsubA⟩ ⟨B, hB, hb, hsubB⟩ ↦
    ⟨A ∩ B, hA.inter hB, m.mass_inter_eq_one hA hB ha hb, inter_subset_inter hsubA hsubB⟩

theorem mem_fullMassFilter_iff {A : Set S} (hA : MeasurableSet A) :
    A ∈ m.fullMassFilter ↔ m.mass A hA = 1 := by
  constructor
  · rintro ⟨B, hB, hb, hsub⟩
    exact le_antisymm (m.mass_le_one hA) (hb ▸ m.mass_mono hB hA hsub)
  · exact fun h ↦ ⟨A, hA, h, Subset.rfl⟩

/-- A left-invariant mean has the same value on a function and each of its
left translates. The measured-semigroup hypotheses ensure the translates
admit the indicated `L∞` representatives. -/
def IsLeftInvariant [Mul S] : Prop :=
  ∀ (s : S) (f : S → ℝ) (hf : MemLp f ∞ μ) (ht : MemLp (f ∘ (s * ·)) ∞ μ),
    m.value (f ∘ (s * ·)) ht = m.value f hf

/-- The Markov-inequality and boundedness arguments from Theorem 4.2(ii) and
(iii), applied to one nonnegative test function. -/
theorem value_eq_zero_iff_mass_tail_eq_zero {f : S → ℝ} (hfm : Measurable f)
    (hf : MemLp f ∞ μ) (hnonneg : ∀ x, 0 ≤ f x) (C : ℝ) (hbound : ∀ x, f x ≤ C) :
    m.value f hf = 0 ↔ ∀ ε : ℝ, 0 < ε →
      m.mass {x | ε ≤ f x} (measurableSet_le measurable_const hfm) = 0 := by
  constructor
  · intro h ε hε
    let A : Set S := {x | ε ≤ f x}
    have hA : MeasurableSet A := measurableSet_le measurable_const hfm
    have hmono : ε * m.mass A hA ≤ m.value f hf := by
      rw [mass, ← m.value_smul]
      apply m.value_mono
      refine ae_of_all _ fun x ↦ ?_
      by_cases hx : x ∈ A
      · have hfx : ε ≤ f x := hx
        simpa only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hx, mul_one] using hfx
      · simpa only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hx, mul_zero]
          using hnonneg x
    rw [h] at hmono
    exact le_antisymm (nonpos_of_mul_nonpos_right hmono hε) (m.mass_nonneg hA)
  · intro h
    apply le_antisymm _ (m.value_nonneg hf (ae_of_all _ hnonneg))
    apply le_of_forall_pos_le_add
    intro ε hε
    let A : Set S := {x | ε ≤ f x}
    have hA : MeasurableSet A := measurableSet_le measurable_const hfm
    have hmono : m.value f hf ≤ ε + C * m.mass A hA := by
      rw [mass, ← m.value_smul, ← m.value_constant ε, ← m.value_add]
      apply m.value_mono
      refine ae_of_all _ fun x ↦ ?_
      by_cases hx : x ∈ A
      · simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem hx, smul_eq_mul, mul_one]
        linarith [hbound x]
      · have hlt : f x < ε := lt_of_not_ge hx
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, hx] using hlt.le
    have hzero : m.mass A hA = 0 := h ε hε
    simpa [hzero] using hmono

end MeasuredMean
end JdLG
