/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ErgodicBarycenters
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Equal weights of finite fibres in ergodic extensions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory

namespace Mixing

variable {G X Y : Type*} [Group G] [MeasurableSpace X] [MeasurableSpace Y]

private theorem fibreAtomMass_measurable [MeasurableEq X] (f : X → Y) (hf : Measurable f)
    (κ : Kernel Y X) [IsMarkovKernel κ] : Measurable (fun x ↦ κ (f x) {x}) := by
  have hD : MeasurableSet {z : (Y × X) × X | z.1.2 = z.2} :=
    measurableSet_eq_fun measurable_fst.snd measurable_snd
  have hm := (Kernel.prodMkRight X κ).measurable_kernel_prodMk_left hD
  have he (x : X) : Prod.mk (f x, x) ⁻¹' {z : (Y × X) × X | z.1.2 = z.2} = {x} := by
    ext z
    exact eq_comm
  simpa only [Function.comp_def, id_eq, he, Kernel.prodMkRight_apply] using
    hm.comp (hf.prodMk measurable_id)

private theorem system_act_injective (S : System G X) (g : G) : Function.Injective (S.act g) := by
  have h : S.act g⁻¹ ∘ S.act g = id := by rw [← S.act_mul, inv_mul_cancel, S.act_one]
  exact Function.LeftInverse.injective fun x ↦ congrFun h x

private theorem supportFinset_singleton_pos [MetricSpace X] [BorelSpace X] {μ : Measure X}
    {s : Finset X} (hs : (s : Set X) = μ.support) (hnull : μ (s : Set X)ᶜ = 0)
    {x : X} (hx : x ∈ s) : 0 < μ {x} := by
  classical
  let U := ((s.erase x : Finset X) : Set X)ᶜ
  have hU : IsOpen U := (s.erase x).finite_toSet.isClosed.isOpen_compl
  have hxU : x ∈ U := by simp [U]
  have hxS : x ∈ μ.support := hs ▸ hx
  have hpos := (Measure.mem_support_iff_forall x).mp hxS U (hU.mem_nhds hxU)
  refine hpos.trans_le ?_
  calc
    μ U ≤ μ ({x} ∪ (s : Set X)ᶜ) := by
      apply measure_mono
      intro z hz
      by_cases hzx : z = x
      · exact Or.inl hzx
      · refine Or.inr fun hzs ↦ hz ?_
        exact Finset.mem_erase.mpr ⟨hzx, hzs⟩
    _ ≤ μ {x} + μ (s : Set X)ᶜ := measure_union_le _ _
    _ = μ {x} := by rw [hnull, add_zero]

private theorem measure_finset_mass [MeasurableSingletonClass X] (μ : Measure X) (s : Finset X) :
    μ (s : Set X) = ∑ x ∈ s, μ {x} := by
  classical
  have hs : (s : Set X) = ⋃ x ∈ s, ({x} : Set X) := by
    ext x
    simp
  rw [hs, measure_biUnion_finset]
  · intro i hi j hj hij
    exact Set.disjoint_singleton.mpr hij
  · exact fun x _ ↦ measurableSet_singleton x

/-- A covariant disintegration of an ergodic system into finite fibres
has a single common cardinality, with uniform conditional weights. -/
theorem ae_uniform_fibre_support_of_ergodic [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]
    {S : System G X} {T : System G Y} (hS : S.IsErgodic) (F : FactorMap S T)
    (κ : Kernel Y X) [IsMarkovKernel κ] (hκ : κ ∘ₘ T.measure = S.measure)
    (hfibre : ∀ᵐ y ∂T.measure, ∀ᵐ x ∂κ y, F.toFun x = y)
    (hequiv : ∀ g, ∀ᵐ y ∂T.measure, (κ y).map (S.act g) = κ (T.act g y))
    (a : ℝ≥0∞)
    (hfinite : ∀ᵐ y ∂T.measure, ∃ s : Finset X, (s : Set X) = (κ y).support ∧
      (κ y) (s : Set X)ᶜ = 0 ∧ (s.card : ℝ≥0∞) * a ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ≥0∞) * a ≤ 1 ∧
      ∀ᵐ y ∂T.measure, ∃ s : Finset X, (s : Set X) = (κ y).support ∧
        (κ y) (s : Set X)ᶜ = 0 ∧ s.card = n ∧
          ∀ x ∈ s, F.toFun x = y ∧ κ y {x} = (n : ℝ≥0∞)⁻¹ := by
  classical
  let w : X → ℝ≥0∞ := fun x ↦ κ (F.toFun x) {x}
  have hw := fibreAtomMass_measurable F.toFun F.preserves.measurable κ
  have hwinv (g : G) : w ∘ S.act g =ᵐ[S.measure] w := by
    filter_upwards [F.preserves.quasiMeasurePreserving.ae (hequiv g)] with x hx
    have hFx : F.toFun (S.act g x) = T.act g (F.toFun x) := congrFun (F.equivariant g) x
    have hh : S.act g ⁻¹' {S.act g x} = {x} := by
      ext z
      simp only [mem_preimage, mem_singleton_iff]
      exact (system_act_injective S g).eq_iff
    change κ (F.toFun (S.act g x)) {S.act g x} = κ (F.toFun x) {x}
    rw [hFx, ← hx, Measure.map_apply (S.preserves g).measurable (measurableSet_singleton _), hh]
  obtain ⟨c, hc⟩ := System.ae_eq_const_of_invariance hS hw hwinv
  rw [← hκ] at hc
  have hY : ∀ᵐ y ∂T.measure, ∀ᵐ x ∂κ y, κ y {x} = c := by
    filter_upwards [Measure.ae_ae_of_ae_comp hc, hfibre] with y hy hF
    filter_upwards [hy, hF] with x hx hxy
    change κ (F.toFun x) {x} = c at hx
    simpa only [hxy] using hx
  have huniform : ∀ᵐ y ∂T.measure, ∃ s : Finset X, (s : Set X) = (κ y).support ∧
      (κ y) (s : Set X)ᶜ = 0 ∧ (s.card : ℝ≥0∞) * a ≤ 1 ∧
      (s.card : ℝ≥0∞) * c = 1 ∧ ∀ x ∈ s, κ y {x} = c := by
    filter_upwards [hY, hfinite] with y hy hfy
    obtain ⟨s, hs, hnull, hbound⟩ := hfy
    have hatom : ∀ x ∈ s, κ y {x} = c := by
      intro x hx
      by_contra hxc
      have hzero : κ y ({x} : Set X) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hy] with z hz hzx
        exact hxc (by simpa only [mem_singleton_iff.mp hzx] using hz)
      exact (supportFinset_singleton_pos hs hnull hx).ne' hzero
    have hsum : (s.card : ℝ≥0∞) * c = 1 := by
      rw [← measure_univ (μ := κ y), ← measure_of_measure_compl_eq_zero hnull,
        measure_finset_mass, Finset.sum_congr rfl hatom, Finset.sum_const, nsmul_eq_mul]
    exact ⟨s, hs, hnull, hbound, hsum, hatom⟩
  obtain ⟨y₀, s₀, _, _, hbound, hsum, _⟩ := huniform.exists
  have hn : 0 < s₀.card := by
    by_contra! hn
    have hn' := Nat.eq_zero_of_le_zero hn
    simp [hn'] at hsum
  have hc₀ : c ≠ 0 := by
    intro hc₀
    simp [hc₀] at hsum
  have hcfin : c ≠ ⊤ := by
    intro hcfin
    simp [hcfin, hn.ne'] at hsum
  have hn₀ : (s₀.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hcInv : c = (s₀.card : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.mul_right_inj hn₀ (ENNReal.natCast_ne_top _)).mp
    rw [hsum, ENNReal.mul_inv_cancel hn₀ (ENNReal.natCast_ne_top _)]
  refine ⟨s₀.card, hn, hbound, ?_⟩
  filter_upwards [huniform, hfibre] with y hy hyF
  obtain ⟨s, hs, hnull, _, hsum', hatom⟩ := hy
  have hcard := (ENNReal.mul_left_inj hc₀ hcfin).mp (hsum'.trans hsum.symm)
  refine ⟨s, hs, hnull, by exact_mod_cast hcard, fun x hx ↦ ⟨?_, (hatom x hx).trans hcInv⟩⟩
  by_contra hxy
  have hzero : κ y ({x} : Set X) = 0 := measure_eq_zero_iff_ae_notMem.mpr (by
    filter_upwards [hyF] with z hz hzx
    exact hxy (by simpa only [mem_singleton_iff.mp hzx] using hz))
  exact (supportFinset_singleton_pos hs hnull hx).ne' hzero

end Mixing
