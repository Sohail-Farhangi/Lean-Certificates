/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.SeparateAveraging
public import JdLG.UltrafilterMoreMeasure
public import JdLG.UltrafilterMoreResults
public import Mathlib.Topology.UrysohnsLemma

/-! # Density-zero weak returns and projection limits along essential ultrafilters -/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace JdLG

attribute [local instance] stoneCechClopenMeasurableSpace

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

private theorem continuous_stoneCech_average {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (m : LeftInvariantSetMean S)
    (F : X → Ultrafilter S → ℝ) (hleft : ∀ p, Continuous (fun a ↦ F a p))
    (hright : ∀ a, Continuous (F a)) (hBound : ∀ a p, ‖F a p‖ ≤ 1) :
    Continuous fun a ↦ ∫ p, F a p ∂m.stoneCechMeasure := by
  apply continuous_iff_isClosed.2
  intro D hD
  apply isClosed_of_closure_subset
  intro a ha
  obtain ⟨u, hu, hulim⟩ :=
    exists_seq_pointwise_of_mem_closure_of_separatelyContinuous F hleft hright ha
  have hlim := tendsto_integral_of_dominated_convergence (μ := m.stoneCechMeasure) (fun _ ↦ (1 : ℝ))
    (fun n ↦ (stoneCechClopenMeasurable_of_continuous (hright (u n))).aestronglyMeasurable)
    (integrable_const 1) (fun n ↦ ae_of_all _ (hBound (u n))) (ae_of_all _ hulim)
  exact hD.mem_of_tendsto hlim (Eventually.of_forall hu)

private theorem zero_average_of_groupIdeal {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) (K : GroupIdeal (weakOperatorClosure π))
    (m : LeftInvariantSetMean S) (ψ : C(weakOperatorClosure π, ℝ))
    (hZero : EqOn ψ 0 K.carrier) (hB : ∀ a, ψ a ∈ Icc (0 : ℝ) 1) :
    (∫ p, ψ (Ultrafilter.extend (closureInclusion π) p) ∂m.stoneCechMeasure) = 0 := by
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  let A := Ultrafilter.extend (closureInclusion π)
  have hA : Continuous A := continuous_ultrafilter_extend _
  let F (a : weakOperatorClosure π) (p : Ultrafilter S) := ψ (a * A p)
  have hleft (p : Ultrafilter S) : Continuous (fun a ↦ F a p) :=
    ψ.continuous.comp (continuous_mul_const _)
  have hright (a : weakOperatorClosure π) : Continuous (F a) :=
    ψ.continuous.comp ((continuous_const_mul _).comp hA)
  have hBound (a : weakOperatorClosure π) (p : Ultrafilter S) : ‖F a p‖ ≤ 1 := by
    exact (Real.norm_of_nonneg (hB (a * A p)).1).trans_le (hB (a * A p)).2
  let avg (a : weakOperatorClosure π) := ∫ p, F a p ∂m.stoneCechMeasure
  have havg : Continuous avg := continuous_stoneCech_average m F hleft hright hBound
  have hBase : Continuous (fun p ↦ ψ (A p)) := ψ.continuous.comp hA
  let c := ∫ p, ψ (A p) ∂m.stoneCechMeasure
  have hConst (s : S) : avg (closureInclusion π s) = c := by
    let f : Ultrafilter S → Ultrafilter S := ((pure s : Ultrafilter S) * ·)
    have hf : Continuous f := by
      simpa only [f, pure_mul_as_map] using continuous_ultrafilter_map (s * ·)
    have hm := stoneCechClopenMeasurable_of_continuous_selfmap f hf
    have hint := integral_map (μ := m.stoneCechMeasure) hm.aemeasurable
      (stoneCechClopenMeasurable_of_continuous hBase).aestronglyMeasurable
    have hmul (p : Ultrafilter S) : A (f p) = closureInclusion π s * A p := by
      change Ultrafilter.extend (closureInclusion π) ((pure s : Ultrafilter S) * p) = _
      rw [ultrafilterExtend_mul continuous_const_mul continuous_mul_const,
        ultrafilter_extend_pure]
    change (∫ p, ψ (closureInclusion π s * A p) ∂m.stoneCechMeasure) = c
    simp_rw [← hmul]
    rw [← hint, m.stoneCechMeasure_map_principal_left s]
  have hAll : avg = fun _ ↦ c :=
    havg.ext_on (denseRange_closureInclusion π) continuous_const
      (by rintro _ ⟨s, rfl⟩; exact hConst s)
  have hEval : ∀ p, F K.identity p = 0 := fun p ↦
    hZero (K.mul_mem_right K.identity_mem (A p))
  have hAt : avg K.identity = 0 := by simp [avg, hEval]
  exact (congrFun hAll K.identity).symm.trans hAt

/-- In the discrete setting, every left invariant set mean vanishes on the weak bad
sets of an almost weakly stable vector. -/
theorem badSetsMeanZero_of_almostWeaklyStable {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) {x : E} (hx : IsAlmostWeaklyStable (closureAction π) x) :
    WeakBadSetsMeanZero π x := by
  intro U hU h0 m
  obtain ⟨K, hK⟩ := exists_groupIdeal_of_admissible hπ
  let : CompactSpace (weakOperatorClosure π) := isCompact_iff_compactSpace.mp hπ.1
  let eval : weakOperatorClosure π → WeakSpace 𝕜 E :=
    fun a ↦ toWeakSpace 𝕜 E (closureAction π a x)
  have hEval : Continuous eval := continuous_weakOrbit_eval π x
  let B := (eval ⁻¹' U)ᶜ
  have hB : IsClosed B := (hU.preimage hEval).isClosed_compl
  have hZero := (K.stable_iff_projection_eq_zero (closureAction π) x).mp hx
  have hSep : Disjoint K.carrier B := by
    apply Set.disjoint_left.mpr
    intro a ha hBad
    have hKx : eval a = 0 := by
      change toWeakSpace 𝕜 E (closureAction π a x) = 0
      rw [← K.identity_mul ha, K.identity_mul_eq_mul_identity, map_mul]
      change toWeakSpace 𝕜 E (closureAction π a (K.projection (closureAction π) x)) = 0
      rw [hZero, map_zero, map_zero]
    apply hBad
    change eval a ∈ U
    rwa [hKx]
  obtain ⟨ψ, hψ0, hψ1, hψB⟩ := exists_continuous_zero_one_of_isClosed hK.isClosed hB hSep
  let A := Ultrafilter.extend (closureInclusion π)
  let A₀ : Set S := {s | toWeakSpace 𝕜 E (π s x) ∉ U}
  let C : Set (Ultrafilter S) := {p | A₀ ∈ p}
  have hC : IsClopen C := ⟨ultrafilter_isClosed_basic A₀, ultrafilter_isOpen_basic A₀⟩
  have hψC : C ⊆ {p | ψ (A p) ≠ 0} := by
    intro p hp
    have hlim := (ψ.continuous.tendsto (A p)).comp
      (tendsto_ultrafilterExtend (closureInclusion π) p)
    have hone : ψ (A p) ∈ ({1} : Set ℝ) := isClosed_singleton.mem_of_tendsto hlim <|
      mem_of_superset hp fun s hs ↦ show ψ (closureInclusion π s) = 1 from hψ1 hs
    exact fun h ↦ one_ne_zero (hone.symm.trans h)
  let g : Ultrafilter S → ℝ := ψ ∘ A
  have hg : Continuous g := ψ.continuous.comp (continuous_ultrafilter_extend _)
  have hgm := (stoneCechClopenMeasurable_of_continuous hg).aestronglyMeasurable
    (μ := m.stoneCechMeasure)
  have hgB : ∀ p, ‖g p‖ ≤ 1 := fun p ↦
    (Real.norm_of_nonneg (hψB (A p)).1).trans_le (hψB (A p)).2
  have hgI : Integrable g m.stoneCechMeasure :=
    ⟨hgm, HasFiniteIntegral.of_bounded (ae_of_all _ hgB)⟩
  have hAE : g =ᵐ[m.stoneCechMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p ↦ (hψB (A p)).1) hgI).mp
      (zero_average_of_groupIdeal hπ K m ψ hψ0 hψB)
  have hNull : m.stoneCechMeasure C = 0 := measure_mono_null hψC (ae_iff.mp hAE)
  have hp : (pure ⁻¹' C : Set S) = A₀ := by
    ext s
    exact Ultrafilter.mem_pure
  rw [m.stoneCechMeasure_clopen hC, hp] at hNull
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hNull) (m.nonneg A₀)

/-- Lemma 5.1(iv). Essential ultrafilters send almost weakly stable vectors weakly to zero. -/
theorem stable_tendsto_of_essential {π : S →ₙ* (E →L[𝕜] E)}
    (hπ : IsJdLGAdmissible π) {x : E} (hx : IsAlmostWeaklyStable (closureAction π) x)
    {p : Ultrafilter S} (hp : p ∈ essentialUltrafilters S) :
    Tendsto (fun s ↦ toWeakSpace 𝕜 E (π s x)) (p : Filter S) (𝓝 0) :=
  weak_tendsto_zero_of_essential_of_badSetsMeanZero (badSetsMeanZero_of_almostWeaklyStable hπ hx) hp

/-- Theorem 5.2(ii). An essential idempotent has the JdLG projection as WOT limit. -/
theorem GroupIdeal.tendsto_projection_of_essential_idempotent
    {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) {p : Ultrafilter S}
    (hp : p ∈ essentialUltrafilters S) (hpp : p * p = p) :
    Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (K.identity : E →WOT[𝕜] E)) :=
  K.tendsto_projection_of_essential_idempotent_of_badSetsMeanZero hπ
    (fun _ hx ↦ badSetsMeanZero_of_almostWeaklyStable hπ hx) hp hpp

/-- Theorem 5.2(iv). A difference product of an essential ultrafilter has the JdLG
projection as WOT limit. -/
theorem GroupIdeal.tendsto_projection_of_inverse_product_essential {G : Type*} [Group G]
    [CompleteSpace E] {π : S →ₙ* (E →L[𝕜] E)} (hπ : IsJdLGAdmissible π)
    (K : GroupIdeal (weakOperatorClosure π)) {ι : S →ₙ* G} (hι : IsGroupOfRightQuotients ι)
    {p q : Ultrafilter S} (hq : q ∈ essentialUltrafilters S)
    (hp : p.map ι = ultrafilterInverse (q.map ι) * q.map ι) :
    Tendsto (weakRepresentation π) (p : Filter S) (𝓝 (K.identity : E →WOT[𝕜] E)) :=
  K.tendsto_projection_of_inverse_product_essential_of_badSetsMeanZero hπ
    (fun _ hx ↦ badSetsMeanZero_of_almostWeaklyStable hπ hx) hι hq hp

end JdLG
