module

public import Mixing.MainTheorems

@[expose] public section

noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped Topology

universe u

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- The L² equivalence class of the indicator of a measurable event. -/
def eventVector (S : System G X) {A : Set X} (hA : MeasurableSet A) :
    Lp ℂ 2 S.measure := indicatorConstLp 2 hA (measure_ne_top _ _) 1

/-- The mean of the indicator of an event is its probability. -/
theorem integral_eventVector (S : System G X) {A : Set X} (hA : MeasurableSet A) :
    ∫ x, eventVector S hA x ∂S.measure = (S.measure.real A : ℂ) := by
  exact (integral_congr_ae indicatorConstLp_coeFn).trans (by rw [integral_indicator hA]; simp)

theorem koopman_event_coeff (S : System G X) (g : G) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℂ (eventVector S hA) (S.koopmanRep g (eventVector S hB)) =
      (S.measure.real (A ∩ S.act g ⁻¹' B) : ℂ) := by
  change inner ℂ (eventVector S hA)
    (Lp.compMeasurePreserving (S.act g) (S.preserves g) (eventVector S hB)) = _
  rw [eventVector, eventVector, Lp.indicatorConstLp_compMeasurePreserving]
  exact L2.inner_indicatorConstLp_one_indicatorConstLp_one _ _

/-- The event formulation in part (iii) of Theorem 1.3. `Measure.real` represents
the values of the probability measure as real numbers. -/
def System.IsUMixingEvents (S : System G X) (P : Set (Ultrafilter G)) : Prop :=
  ∀ p ∈ P, ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
    Tendsto (fun g ↦ S.measure.real (A ∩ S.act g ⁻¹' B)) (p : Filter G)
      (𝓝 (S.measure.real A * S.measure.real B))

/-- A bounded operator vanishes if all its matrix coefficients on event indicators vanish. -/
theorem zero_of_event_coefficients (S : System G X) (D : Lp ℂ 2 S.measure →L[ℂ] Lp ℂ 2 S.measure)
    (hD : ∀ A B : Set X, ∀ (hA : MeasurableSet A) (hB : MeasurableSet B),
      inner ℂ (eventVector S hA) (D (eventVector S hB)) = 0) : D = 0 := by
  have hind : ∀ (z : ℂ) (A : Set X) (hA : MeasurableSet A),
      (Lp.simpleFunc.indicatorConst (μ := S.measure) 2 hA (measure_ne_top _ _) z : Lp ℂ 2 S.measure) =
        z • eventVector S hA := by
    intro z A hA
    let e := Lp.simpleFunc.indicatorConst (μ := S.measure) 2 hA (measure_ne_top _ _) z
    have he := (Lp.simpleFunc.toSimpleFunc_eq_toFun e).symm.trans
      (Lp.simpleFunc.toSimpleFunc_indicatorConst hA (measure_ne_top _ _) z)
    apply Lp.ext
    filter_upwards [he, Lp.coeFn_smul z (eventVector S hA),
      indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top S.measure A) (c := (1 : ℂ))]
      with x hx hc heA
    rw [hx, hc]
    change _ = z * eventVector S hA x
    rw [show eventVector S hA x = _ from heA]
    classical
    by_cases h : x ∈ A <;> simp [h]
  have hleft : ∀ (f : Lp ℂ 2 S.measure) (B : Set X) (hB : MeasurableSet B),
      inner ℂ f (D (eventVector S hB)) = 0 := by
    intro f B hB
    refine Lp.induction (μ := S.measure) (p := 2) (by norm_num)
      (fun f ↦ inner ℂ f (D (eventVector S hB)) = 0) ?_ ?_ ?_ f
    · intro c A hA hmass
      rw [hind c A hA, inner_smul_left, hD A B hA hB, mul_zero]
    · intro x y hx₀ hy₀ _ hx hy
      change inner ℂ ((hx₀.add hy₀).toLp (x + y)) (D (eventVector S hB)) = 0
      rw [MemLp.toLp_add hx₀ hy₀, inner_add_left, hx, hy, add_zero]
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
  apply ContinuousLinearMap.ext
  intro k
  apply ext_inner_left ℂ
  intro f
  rw [zero_apply, inner_zero_right]
  refine Lp.induction (μ := S.measure) (p := 2) (by norm_num)
    (fun k ↦ inner ℂ f (D k) = 0) ?_ ?_ ?_ k
  · intro c B hB hmass
    rw [hind c B hB, map_smul, inner_smul_right, hleft f B hB, mul_zero]
  · intro x y hx₀ hy₀ _ hx hy
    change inner ℂ f (D ((hx₀.add hy₀).toLp (x + y))) = 0
    rw [MemLp.toLp_add hx₀ hy₀, map_add, inner_add_right, hx, hy, add_zero]
  · exact isClosed_eq (continuous_const.inner D.continuous) continuous_const

/-- Equivalence of the event and Koopman formulations of Theorem 1.3(iii). -/
theorem System.isUMixing_iff_events (S : System G X) (P : Set (Ultrafilter G)) :
    S.IsUMixing P ↔ S.IsUMixingEvents P := by
  rw [S.isUMixing_iff_lp_correlations]
  constructor
  · intro h p hp A B hA hB
    have hlim := h p hp (eventVector S hA) (eventVector S hB)
    simp only [koopman_event_coeff, integral_eventVector, Complex.star_def, Complex.conj_ofReal,
      ← Complex.ofReal_mul] at hlim
    simpa only [Function.comp_def, Complex.ofReal_re] using (Complex.continuous_re.tendsto _).comp hlim
  · intro h p hp f k
    let c := constantOne S.measure
    let Q := InnerProductSpace.rankOne ℂ c c
    let A := ultrafilterOperator S.koopmanRep p
    have hQ (f k : Lp ℂ 2 S.measure) :
        inner ℂ f (Q k) = star (∫ x, f x ∂S.measure) * ∫ x, k x ∂S.measure := by
      simp only [Q, InnerProductSpace.rankOne_apply, inner_smul_right]
      rw [mul_comm, ← inner_conj_symm]
      exact congrArg₂ (· * ·) (congrArg star (inner_constantOne_left _ f))
        (inner_constantOne_left _ k)
    have hzero : A - Q = 0 := by
      apply zero_of_event_coefficients S
      intro C D hC hD
      have hc := (Complex.continuous_ofReal.tendsto _).comp (h p hp C D hC hD)
      have hl := tendsto_ultrafilterOperator_coeff S.koopmanRep p (eventVector S hC) (eventVector S hD)
      simp only [koopman_event_coeff] at hl
      have he := tendsto_nhds_unique hl hc
      rw [sub_apply, inner_sub_right, hQ, integral_eventVector,
        integral_eventVector, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      exact sub_eq_zero.mpr he
    have hAQ : A = Q := sub_eq_zero.mp hzero
    have hl := tendsto_ultrafilterOperator_coeff S.koopmanRep p f k
    change Tendsto _ _ (𝓝 (inner ℂ f (A k))) at hl
    rwa [hAQ, hQ] at hl

/-- Theorem 1.3 with part (iii) stated directly in terms of measurable events. -/
theorem theorem1_3_events {G : Type*} {X : Type u} [CommGroup G] [MeasurableSpace X]
    (S : System G X) (P : Set (Ultrafilter G)) :
    (S.IsUMixingEvents P ↔
      ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (V : G →* (K ≃ₗᵢ[ℂ] K)), IsUGenerated V P →
        SpectrallyDisjoint S.koopmanZeroRep V) ∧
    (S.IsUMixingEvents P ↔
      ∀ (Y : Type u) [MeasurableSpace Y] (T : System G Y), T.IsUGenerated P → Disjoint S T) :=
  ⟨(S.isUMixing_iff_events P).symm.trans (theorem1_3 S P).1,
    (S.isUMixing_iff_events P).symm.trans (theorem1_3 S P).2⟩

end Mixing
