module

public import Mixing.RigidEventBounds
public import Mixing.FactorJoiningLift
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal ProbabilityTheory

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- The orbit observations associated with a sequence of L² functions. -/
def System.observe (S : System G X) (v : ℕ → Lp ℂ 2 S.measure) :
    X → (G × ℕ → ℂ) :=
  fun x i ↦ v i.2 (S.act i.1 x)

theorem System.observe_measurable (S : System G X) (v : ℕ → Lp ℂ 2 S.measure) :
    Measurable (S.observe v) := by
  apply Measurable.of_eval
  intro i
  exact (Lp.stronglyMeasurable (v i.2)).measurable.comp (S.preserves i.1).measurable

/-- Translation of the group coordinate of an orbit observation. -/
def shiftObservation (g : G) (y : G × ℕ → ℂ) : G × ℕ → ℂ :=
  fun i ↦ y (i.1 * g, i.2)

theorem System.observe_equivariant (S : System G X) (v : ℕ → Lp ℂ 2 S.measure) (g : G) :
    S.observe v ∘ S.act g = shiftObservation g ∘ S.observe v := by
  funext x i
  change v i.2 (S.act i.1 (S.act g x)) = v i.2 (S.act (i.1 * g) x)
  rw [S.act_mul]
  rfl

/-- The shift system of the observed names of a sequence of L² functions.
Its underlying space is standard Borel because the coordinate set is countable. -/
def System.observationSystem (S : System G X) (v : ℕ → Lp ℂ 2 S.measure) :
    System G (G × ℕ → ℂ) where
  measure := S.measure.map (S.observe v)
  probability := (Measure.isProbabilityMeasure_map_iff (S.observe_measurable v).aemeasurable).2
    S.probability
  act := shiftObservation
  act_one := by funext y i; simp [shiftObservation]
  act_mul g h := by funext y i; simp [shiftObservation, mul_assoc]
  preserves g := by
    have hm : Measurable (shiftObservation (G := G) g) :=
      Measurable.of_eval fun i ↦ measurable_pi_apply (i.1 * g, i.2)
    refine ⟨hm, ?_⟩
    rw [Measure.map_map hm (S.observe_measurable v), ← S.observe_equivariant v g,
      ← Measure.map_map (S.observe_measurable v) (S.preserves g).measurable,
      (S.preserves g).map_eq]

def System.observationFactor (S : System G X) (v : ℕ → Lp ℂ 2 S.measure) :
    FactorMap S (S.observationSystem v) :=
  ⟨S.observe v, ⟨S.observe_measurable v, rfl⟩, S.observe_equivariant v⟩

private theorem System.observation_mem_range (S : System G X) (v : ℕ → Lp ℂ 2 S.measure)
    (n : ℕ) : v n ∈ Set.range (S.observationFactor v).pullback := by
  let F := S.observationFactor v
  let f : (G × ℕ → ℂ) → ℂ := fun y ↦ y (1, n)
  have hf : Measurable f := measurable_pi_apply (1, n)
  have hcomp : f ∘ F.toFun = (v n : X → ℂ) := by
    funext x
    change v n (S.act 1 x) = v n x
    rw [S.act_one]
    rfl
  have hm : MemLp f 2 (S.observationSystem v).measure := by
    have hh : MemLp (f ∘ F.toFun) 2 S.measure := hcomp.symm ▸ Lp.memLp (v n)
    change MemLp f 2 (S.measure.map F.toFun)
    exact (memLp_map_measure_iff hf.aestronglyMeasurable F.preserves.aemeasurable).2 hh
  refine ⟨hm.toLp f, Lp.ext ?_⟩
  exact (Lp.coeFn_compMeasurePreserving (hm.toLp f) F.preserves).trans
    ((F.preserves.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp).trans
      (EventuallyEq.of_eq hcomp))

variable (S : System G X) [SeparableSpace (Lp ℂ 2 S.measure)]

/-- A standard Borel realization of the generated factor for a singleton family,
using the names of the images of a dense sequence under the Koopman ultrafilter limit. -/
def System.standardGeneratedFactor (p : Ultrafilter G) : System G (G × ℕ → ℂ) :=
  S.observationSystem fun n ↦ ultrafilterOperator S.koopmanRep p (denseSeq _ n)

def System.standardGeneratedFactorMap (p : Ultrafilter G) :
    FactorMap S (S.standardGeneratedFactor p) :=
  S.observationFactor fun n ↦ ultrafilterOperator S.koopmanRep p (denseSeq _ n)

theorem System.range_ultrafilterOperator_le_standardFactor (p : Ultrafilter G) :
    Set.range (ultrafilterOperator S.koopmanRep p) ⊆
      Set.range (S.standardGeneratedFactorMap p).pullback := by
  let A := ultrafilterOperator S.koopmanRep p
  let F := S.standardGeneratedFactorMap p
  have hClosed : IsClosed (A ⁻¹' Set.range F.pullback) :=
    F.pullback.isometry.isClosedEmbedding.isClosed_range.preimage A.continuous
  have hDense : Set.range (denseSeq (Lp ℂ 2 S.measure)) ⊆ A ⁻¹' Set.range F.pullback := by
    rintro _ ⟨n, rfl⟩
    exact S.observation_mem_range (fun i ↦ A (denseSeq _ i)) n
  have h := closure_minimal hDense hClosed
  rw [(denseRange_denseSeq _).closure_range] at h
  rintro _ ⟨f, rfl⟩
  exact h (mem_univ f)

/-- The defining observations of the standard realization are measurable for
the generated σ-algebra. -/
theorem System.standardGeneratedFactorMap_generatedSigma (p : Ultrafilter G) :
    @Measurable X (G × ℕ → ℂ) (S.generatedSigma {p}) _ (S.standardGeneratedFactorMap p).toFun := by
  apply @Measurable.of_eval _ _ _ (S.generatedSigma {p})
  intro i
  exact ((S.generatedSigma_measurable_image {p} (mem_singleton p) (denseSeq _ i.2)).comp
    (S.generatedSigma_act_measurable {p} i.1))

/-- The pullback σ-algebra with the ambient measurable null sets adjoined. -/
@[instance_reducible]
def completedPullbackSigma {Y : Type*} [MeasurableSpace Y] (μ : Measure X) (f : X → Y) :
    MeasurableSpace X :=
  MeasurableSpace.generateFrom {A | (MeasurableSet A ∧ μ A = 0) ∨
    ∃ B : Set Y, MeasurableSet B ∧ A = f ⁻¹' B}

/-- The standard Borel realization in Theorem 5.2 has exactly the generated
σ-algebra when its pullbacks are considered modulo ambient null sets. -/
theorem System.standardGeneratedFactorMap_completedPullbackSigma (p : Ultrafilter G) :
    completedPullbackSigma S.measure (S.standardGeneratedFactorMap p).toFun = S.generatedSigma {p} := by
  let F := S.standardGeneratedFactorMap p
  have hNull {A : Set X} (hA : MeasurableSet A) (h0 : S.measure A = 0) :
      @MeasurableSet X (completedPullbackSigma S.measure F.toFun) A :=
    MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨hA, h0⟩)
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro A (⟨hA, h0⟩ | ⟨B, hB, rfl⟩)
    · exact S.generatedSigma_measurableSet_null {p} hA h0
    · exact S.standardGeneratedFactorMap_generatedSigma p hB
  · apply MeasurableSpace.generateFrom_le
    rintro _ (⟨hA, h0⟩ | ⟨q, hq, f, B, hB, rfl⟩)
    · exact hNull hA h0
    · have heq : q = p := mem_singleton_iff.mp hq
      subst q
      let v := ultrafilterOperator S.koopmanRep p f
      obtain ⟨w, hw⟩ := S.range_ultrafilterOperator_le_standardFactor p ⟨f, rfl⟩
      have hAe : (v : X → ℂ) =ᵐ[S.measure] w ∘ F.toFun := by
        change F.pullback w = v at hw
        rw [← hw]
        exact Lp.coeFn_compMeasurePreserving w F.preserves
      let A := v ⁻¹' B
      let D := (w ∘ F.toFun) ⁻¹' B
      have hA : MeasurableSet A := (Lp.stronglyMeasurable v).measurable hB
      have hD' : MeasurableSet (w ⁻¹' B) := (Lp.stronglyMeasurable w).measurable hB
      have hD : MeasurableSet D := F.preserves.measurable hD'
      have hMD : @MeasurableSet X (completedPullbackSigma S.measure F.toFun) D :=
        MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨w ⁻¹' B, hD', rfl⟩)
      have hAD : S.measure (A \ D) = 0 := by
        apply measure_mono_null _ (ae_iff.mp hAe)
        intro x hx he
        exact hx.2 (show (w ∘ F.toFun) x ∈ B from he ▸ hx.1)
      have hDA : S.measure (D \ A) = 0 := by
        apply measure_mono_null _ (ae_iff.mp hAe)
        intro x hx he
        exact hx.2 (show v x ∈ B from he.symm ▸ hx.1)
      have he : A = (A \ D) ∪ (D \ (D \ A)) := by
        ext x
        simp only [Set.mem_union, Set.mem_sdiff]
        tauto
      change @MeasurableSet X (completedPullbackSigma S.measure F.toFun) A
      rw [he]
      exact (hNull (hA.diff hD) hAD).union (hMD.diff (hNull (hD.diff hA) hDA))

/-- The standard Borel realization is generated by the singleton family of
ultrafilters from which its observations were constructed. -/
theorem System.standardGeneratedFactor_isUGenerated (p : Ultrafilter G) :
    (S.standardGeneratedFactor p).IsUGenerated {p} := by
  let A := ultrafilterOperator S.koopmanRep p
  let T := S.standardGeneratedFactor p
  let F := S.standardGeneratedFactorMap p
  let F' := T.generatedFactorMap {p}
  let J := F.pullback.comp F'.pullback
  have hsq : Set.range (⇑(A ^ 2 : Lp ℂ 2 S.measure →L[ℂ] Lp ℂ 2 S.measure)) ⊆
      Set.range J := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨f', hf'⟩ := S.range_ultrafilterOperator_le_standardFactor p ⟨f, rfl⟩
    obtain ⟨f'', hf''⟩ := T.range_ultrafilterOperator_le_generatedFactor_pullback {p}
      (mem_singleton p) ⟨f', rfl⟩
    refine ⟨f'', ?_⟩
    change F.pullback (F'.pullback f'') = (A ^ 2) f
    calc
      _ = F.pullback (ultrafilterOperator T.koopmanRep p f') := congrArg _ hf''
      _ = A (F.pullback f') := F.intertwines_pullback.ultrafilter p f'
      _ = (A ^ 2) f := by rw [hf', pow_two]; rfl
  have hcl := closure_minimal hsq J.isometry.isClosedEmbedding.isClosed_range
  rw [closure_range_sq A (ultrafilterOperator_normal S.koopmanRep p)] at hcl
  have hEval (n : ℕ) :
      @Measurable (G × ℕ → ℂ) ℂ (T.generatedSigma {p}) _ (fun y ↦ y (1, n)) := by
    let w := A (denseSeq _ n)
    let f : (G × ℕ → ℂ) → ℂ := fun y ↦ y (1, n)
    obtain ⟨v, hv⟩ := hcl (subset_closure (show w ∈ Set.range A from ⟨denseSeq _ n, rfl⟩))
    have hv' : F.pullback (F'.pullback v) = w := hv
    have hfA : f ∘ F.toFun = (w : X → ℂ) := by
      funext x
      change w (S.act 1 x) = w x
      rw [S.act_one]
      rfl
    have hW := (Lp.coeFn_compMeasurePreserving (F'.pullback v) F.preserves).trans
      (F.preserves.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving v F'.preserves))
    have hA : (w : X → ℂ) =ᵐ[S.measure] fun x ↦ v (F.toFun x) := by
      rw [← hv']
      exact hW
    have hm₀ : @Measurable (G × ℕ → ℂ) ℂ (T.generatedSigma {p}) _ v :=
      (Lp.stronglyMeasurable v).measurable
    have hm : Measurable (fun y : G × ℕ → ℂ ↦ v y) := fun B hB ↦
      T.generatedSigma_le {p} _ (hm₀ hB)
    have hf : Measurable f := measurable_pi_apply (1, n)
    have heq : f =ᵐ[T.measure] fun y : G × ℕ → ℂ ↦ v y := by
      rw [← F.preserves.map_eq]
      apply (ae_map_iff F.preserves.aemeasurable (measurableSet_eq_fun hf hm)).2
      exact (EventuallyEq.of_eq hfA).trans hA
    exact T.generatedSigma_measurable_of_ae_eq {p} hf hm₀ heq
  apply T.isUGenerated_of_generatedSigma_eq
  apply le_antisymm (T.generatedSigma_le {p})
  have hid : @Measurable (G × ℕ → ℂ) (G × ℕ → ℂ) (T.generatedSigma {p}) _ id := by
    apply @Measurable.of_eval _ _ _ (T.generatedSigma {p})
    intro i
    have h := (hEval i.2).comp (T.generatedSigma_act_measurable {p} i.1)
    have he : (fun y ↦ (T.act i.1 y) (1, i.2)) = fun y ↦ y i := by
      funext y
      change y (1 * i.1, i.2) = y i
      rw [one_mul]
    change @Measurable _ _ (T.generatedSigma {p}) _ (fun y ↦ y i)
    rw [← he]
    exact h
  simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hid

/-- The first part of Theorem 5.2, with a concrete standard Borel realization
of the generated factor. -/
theorem theorem5_2_finiteFibres [Countable G] [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]
    [StandardBorelSpace X] [Nonempty X]
    (p : Ultrafilter G) {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1)
    (hrigid : S.IsPartiallyRigidAlong p a) :
    let T := S.standardGeneratedFactor p
    let F := S.standardGeneratedFactorMap p
    let κ := (coordinateGraph S.measure F.toFun).condKernel
    ∀ᵐ y ∂T.measure, ∃ s : Finset X, (s : Set X) = (κ y).support ∧
      (κ y) (s : Set X)ᶜ = 0 ∧ (s.card : ℝ≥0∞) * ENNReal.ofReal a ≤ 1 := by
  dsimp only
  let T := S.standardGeneratedFactor p
  let F := S.standardGeneratedFactorMap p
  exact ae_finite_fibre_support_of_partialRigidity F F.conditionalKernel F.comp_conditionalKernel
    F.ae_conditionalKernel_fibre p ha ha₁ hrigid (S.range_ultrafilterOperator_le_standardFactor p)

end Mixing
