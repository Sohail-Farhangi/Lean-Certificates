/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesPowers
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Compactification.StoneCech

/-!
# Weak compactness of the perfect-powers indicator orbit

The proof uses the finite intersections between distinct translates.
From a hypothetical obstruction to weak convergence, one can select
arbitrarily many indicators with no point in more than two supports.
Their normalized phase-weighted sums contradict boundedness of a
continuous linear functional.
-/

@[expose] public section

namespace JdLG.PaperExamplesPowers

open Filter
open scoped ENNReal Topology ComplexConjugate

local notation "W" => lp (fun _ : ℤ ↦ ℂ) ∞

private theorem weakPairing_injective : Function.Injective (topDualPairing ℂ W).flip := by
  intro x y h
  by_contra hne
  obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℂ) hne
  exact hf (LinearMap.congr_fun h f)

open Classical in
private theorem select_bounded_overlap (A : ℤ → Set ℤ)
    (hfinite : ∀ a b, a ≠ b → (A a ∩ A b).Finite)
    {u : Filter ℤ} (hu : u ≤ cofinite) (hpoint : ∀ x, ∀ᶠ a in u, x ∉ A a)
    (P : ℤ → Prop) (hP : ∃ᶠ a in u, P a) (n : ℕ) :
    ∃ F : Finset ℤ, F.card = n ∧ (∀ a ∈ F, P a) ∧
      ∀ x : ℤ, (F.filter fun a ↦ x ∈ A a).card ≤ 2 := by
  classical
  induction n with
  | zero => exact ⟨∅, by simp⟩
  | succ n ih =>
    obtain ⟨F, hn, hFP, hcount⟩ := ih
    let I := (F.product F).filter fun p ↦ p.1 ≠ p.2
    let X : Set ℤ := ⋃ p ∈ (I : Set (ℤ × ℤ)), A p.1 ∩ A p.2
    have hX : X.Finite := I.finite_toSet.biUnion fun p hp ↦
      hfinite p.1 p.2 (Finset.mem_filter.1 hp).2
    have hfresh : ∀ᶠ a in u, a ∉ F :=
      hu (F.finite_toSet.compl_mem_cofinite)
    have havoid : ∀ᶠ a in u, ∀ x ∈ X, x ∉ A a :=
      hX.eventually_all.2 (fun x _ ↦ hpoint x)
    obtain ⟨a, ha, haF, haX⟩ := (hP.and_eventually (hfresh.and havoid)).exists
    refine ⟨insert a F, by rw [Finset.card_insert_of_notMem haF, hn], ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact ha
      · exact hFP b hb
    · intro x
      rw [Finset.filter_insert]
      by_cases hx : x ∈ A a
      · rw [ite_eq_left hx, Finset.card_insert_of_notMem (fun hm ↦ haF (Finset.mem_filter.1 hm).1)]
        have hle : (F.filter fun b ↦ x ∈ A b).card ≤ 1 := by
          apply Finset.card_le_one.2
          intro b hb c hc
          by_contra hbc
          obtain ⟨hbF, hxb⟩ := Finset.mem_filter.1 hb
          obtain ⟨hcF, hxc⟩ := Finset.mem_filter.1 hc
          have hbcI : (b, c) ∈ I :=
            Finset.mem_filter.2 ⟨Finset.mk_mem_product hbF hcF, hbc⟩
          exact haX x (Set.mem_iUnion.2 ⟨(b, c), Set.mem_iUnion.2 ⟨hbcI, hxb, hxc⟩⟩) hx
        omega
      · rw [ite_eq_right hx]
        exact hcount x

open Classical in
private theorem norm_sum_indicator_smul_le (A : ℤ → Set ℤ) (F : Finset ℤ) (w : ℤ → ℂ)
    (hw : ∀ a ∈ F, ‖w a‖ ≤ 1) (hcount : ∀ x : ℤ, (F.filter fun a ↦ x ∈ A a).card ≤ 2) :
    ‖∑ a ∈ F, w a • boundedIndicator (A a)‖ ≤ 2 := by
  classical
  apply lp.norm_le_of_forall_le (by norm_num : (0 : ℝ) ≤ 2)
  intro x
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, boundedIndicator_apply]
  have hsum : (∑ a ∈ F, w a * (if x ∈ A a then (1 : ℂ) else 0)) =
      ∑ a ∈ F.filter (fun a ↦ x ∈ A a), w a := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hsum]
  calc
    _ ≤ ∑ a ∈ F.filter (fun a ↦ x ∈ A a), ‖w a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ F.filter (fun a ↦ x ∈ A a), (1 : ℝ) :=
      Finset.sum_le_sum fun a ha ↦ hw a (Finset.mem_filter.1 ha).1
    _ ≤ _ := by simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
      (show ((F.filter fun a ↦ x ∈ A a).card : ℝ) ≤ 2 by exact_mod_cast hcount x)

private theorem phase_weights (z : ℂ) (hz : z ≠ 0) :
    ‖conj z / (‖z‖ : ℂ)‖ = 1 ∧ (conj z / (‖z‖ : ℂ)) * z = (‖z‖ : ℂ) := by
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hcast : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
  constructor
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      div_self hnorm]
  · rw [div_mul_eq_mul_div, Complex.conj_mul', pow_two, mul_div_cancel_right₀ _ hcast]

private theorem eval_tendsto_zero_of_pointwise_avoid (A : ℤ → Set ℤ)
    (hfinite : ∀ a b, a ≠ b → (A a ∩ A b).Finite)
    {u : Filter ℤ} (hu : u ≤ cofinite) (hpoint : ∀ x, ∀ᶠ a in u, x ∉ A a)
    (f : StrongDual ℂ W) :
    Tendsto (fun a ↦ f (boundedIndicator (A a))) u (𝓝 0) := by
  classical
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  simp only [dist_zero_right]
  by_contra hsmall
  let z (a : ℤ) := f (boundedIndicator (A a))
  have hP : ∃ᶠ a in u, ε ≤ ‖z a‖ := by
    simpa only [Filter.Frequently, not_le, z] using hsmall
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖f‖ / ε)
  obtain ⟨F, hF, hbad, hoverlap⟩ := select_bounded_overlap A hfinite hu hpoint _ hP n
  let w (a : ℤ) := conj (z a) / (‖z a‖ : ℂ)
  have hphase (a : ℤ) (ha : a ∈ F) : ‖w a‖ = 1 ∧ w a * z a = (‖z a‖ : ℂ) :=
    phase_weights _ (norm_pos_iff.1 (hε.trans_le (hbad a ha)))
  let v : W := ∑ a ∈ F, w a • boundedIndicator (A a)
  have hv : ‖v‖ ≤ 2 := norm_sum_indicator_smul_le A F w
    (fun a ha ↦ (hphase a ha).1.le) hoverlap
  have hfv : f v = (∑ a ∈ F, ‖z a‖ : ℝ) := by
    simp only [v, map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun a ha ↦ (hphase a ha).2
  have hupper : (∑ a ∈ F, ‖z a‖) ≤ 2 * ‖f‖ := by
    have hle := (f.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg f))
    rw [hfv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
      (fun a _ ↦ norm_nonneg (z a))), mul_comm] at hle
    exact hle
  have hlower : (n : ℝ) * ε ≤ ∑ a ∈ F, ‖z a‖ := by
    simpa only [Finset.sum_const, hF, nsmul_eq_mul] using (Finset.sum_le_sum hbad)
  exact (not_lt_of_ge (hlower.trans hupper)) ((div_lt_iff₀ hε).1 hn)

/-- Translating toward negative infinity makes each fixed coordinate vanish
eventually. The finite-intersection argument upgrades this to weak convergence. -/
theorem translate_weakly_zero_atBot {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun a : ℤ ↦ toWeakSpace ℂ W (boundedIndicator (translateSupport k a)))
      atBot (𝓝 0) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ weakPairing_injective).2
  intro f
  change Tendsto (fun a ↦ f (boundedIndicator (translateSupport k a))) atBot (𝓝 (f 0))
  rw [map_zero]
  apply eval_tendsto_zero_of_pointwise_avoid _ (fun _ _ h ↦ finite_inter_translateSupport hk h)
    atBot_le_cofinite
  intro x
  filter_upwards [eventually_lt_atBot (-x)] with a ha hax
  obtain ⟨n, hn⟩ := hax
  have hn' : 0 ≤ ((n + 1 : ℕ) : ℤ) ^ k := by positivity
  change ((n + 1 : ℕ) : ℤ) ^ k = a + x at hn
  omega

private theorem indicator_diff_add {A C : Set ℤ} (hC : C ⊆ A) :
    boundedIndicator (A \ C) + boundedIndicator C = boundedIndicator A := by
  classical
  apply lp.ext
  funext x
  simp only [lp.coeFn_add, Pi.add_apply, boundedIndicator_apply, Set.mem_sdiff]
  by_cases hx : x ∈ C
  · simp [hx, hC hx]
  · simp [hx]

private theorem translate_ultrafilter_converges {k : ℕ} (hk : 2 ≤ k) (u : Ultrafilter ℤ) :
    ∃ y : WeakSpace ℂ W,
      Tendsto (fun a : ℤ ↦ toWeakSpace ℂ W (boundedIndicator (translateSupport k a)))
        (u : Filter ℤ) (𝓝 y) := by
  classical
  rcases u.le_cofinite_or_eq_pure with hu | ⟨a, rfl⟩
  · let C : Set ℤ := {x | ∀ᶠ a in (u : Filter ℤ), x ∈ translateSupport k a}
    have hC : C.Subsingleton := by
      intro x hx y hy
      by_contra hxy
      have hxyfinite : {a | x ∈ translateSupport k a ∧ y ∈ translateSupport k a}.Finite := by
        convert finite_inter_translateSupport hk hxy using 1
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, translateSupport]
        rw [add_comm a x, add_comm a y]
      have hin : {a | x ∈ translateSupport k a ∧ y ∈ translateSupport k a} ∈ u :=
        (show _ from (show ∀ᶠ a in (u : Filter ℤ), _ from hx).and hy)
      exact (Filter.compl_notMem (f := (u : Filter ℤ)) hin) (hu hxyfinite.compl_mem_cofinite)
    have hcontain : ∀ᶠ a in (u : Filter ℤ), C ⊆ translateSupport k a :=
      hC.finite.eventually_all.2 fun _ hx ↦ hx
    let A (a : ℤ) := translateSupport k a \ C
    have hfinite (a b : ℤ) (h : a ≠ b) : (A a ∩ A b).Finite :=
      (finite_inter_translateSupport hk h).subset fun _ hx ↦ ⟨hx.1.1, hx.2.1⟩
    have hpoint (x : ℤ) : ∀ᶠ a in (u : Filter ℤ), x ∉ A a := by
      by_cases hx : x ∈ C
      · exact Eventually.of_forall fun _ h ↦ h.2 hx
      · have hnot : {a | x ∈ translateSupport k a} ∉ u := hx
        have hcompl := Ultrafilter.compl_mem_iff_notMem.2 hnot
        exact (show ∀ᶠ a in (u : Filter ℤ), x ∉ translateSupport k a from hcompl).mono
          fun _ h hx' ↦ h hx'.1
    refine ⟨toWeakSpace ℂ W (boundedIndicator C),
      (WeakBilin.tendsto_iff_forall_eval_tendsto _ weakPairing_injective).2 fun f ↦ ?_⟩
    change Tendsto (fun a ↦ f (boundedIndicator (translateSupport k a)))
      (u : Filter ℤ) (𝓝 (f (boundedIndicator C)))
    have ht := (eval_tendsto_zero_of_pointwise_avoid A hfinite hu hpoint f).add_const
      (f (boundedIndicator C))
    replace ht : Tendsto (fun a ↦ f (boundedIndicator (A a)) + f (boundedIndicator C))
        (u : Filter ℤ) (𝓝 (f (boundedIndicator C))) := by
      simpa only [zero_add] using ht
    refine ht.congr' (hcontain.mono fun a ha ↦ ?_)
    rw [← map_add, indicator_diff_add ha]
  · rw [Ultrafilter.coe_pure]
    exact ⟨_, tendsto_pure_nhds _ a⟩

/-- The indicator of the perfect powers is weakly almost periodic. This
formalizes the weak compactness assertion cited to Ruppert in Example 5.4. -/
theorem powersIndicator_weakly_almost_periodic {k : ℕ} (hk : 2 ≤ k) :
    IsCompact (closure (Set.range (fun a : ℤ ↦ toWeakSpace ℂ W
      (translation (Multiplicative.ofAdd a) (powersIndicator k))))) := by
  let f := fun a : ℤ ↦ toWeakSpace ℂ W (boundedIndicator (translateSupport k a))
  have hext : Continuous (Ultrafilter.extend f) := by
    let : TopologicalSpace ℤ := ⊥
    refine isDenseInducing_pure.continuous_extend fun u ↦ ?_
    obtain ⟨y, hy⟩ := translate_ultrafilter_converges hk u
    exact ⟨y, hy.mono_left (ultrafilter_comap_pure_nhds u)⟩
  have hc := isCompact_range hext
  have hsub : Set.range f ⊆ Set.range (Ultrafilter.extend f) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨pure a, ultrafilter_extend_pure f a⟩
  change IsCompact (closure (Set.range f))
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hsub hc.isClosed)

/-- The zero function lies in the weak orbit closure of the powers indicator. -/
theorem zero_mem_powersIndicator_weakOrbitClosure {k : ℕ} (hk : 2 ≤ k) :
    (0 : WeakSpace ℂ W) ∈ closure (Set.range (fun a : ℤ ↦ toWeakSpace ℂ W
      (translation (Multiplicative.ofAdd a) (powersIndicator k)))) := by
  exact mem_closure_of_tendsto (translate_weakly_zero_atBot hk)
    (Eventually.of_forall Set.mem_range_self)

/-- A continuous translation-invariant mean on any subspace containing the
orbit assigns the powers indicator mean zero. -/
theorem powersIndicator_mean_zero {k : ℕ} (hk : 2 ≤ k) (E : Submodule ℂ W)
    (hE : ∀ a : ℤ, boundedIndicator (translateSupport k a) ∈ E)
    (m : StrongDual ℂ E)
    (hinv : ∀ a : ℤ, m ⟨boundedIndicator (translateSupport k a), hE a⟩ =
      m ⟨boundedIndicator (translateSupport k 0), hE 0⟩) :
    m ⟨boundedIndicator (translateSupport k 0), hE 0⟩ = 0 := by
  obtain ⟨f, hf, -⟩ := exists_extension_norm_eq E m
  have hlim := (WeakBilin.tendsto_iff_forall_eval_tendsto _ weakPairing_injective).1
    (translate_weakly_zero_atBot hk) f
  change Tendsto (fun a ↦ f (boundedIndicator (translateSupport k a))) atBot (𝓝 (f 0)) at hlim
  have hconst : (fun a ↦ f (boundedIndicator (translateSupport k a))) =
      fun _ : ℤ ↦ m ⟨boundedIndicator (translateSupport k 0), hE 0⟩ := by
    funext a
    exact (hf ⟨_, hE a⟩).trans (hinv a)
  rw [hconst, map_zero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end JdLG.PaperExamplesPowers
