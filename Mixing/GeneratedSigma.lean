module

public import Mixing.Koopman
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Trim

@[expose] public section

noncomputable section

namespace Mixing

open MeasureTheory Set Filter

variable {G X : Type*} [CommGroup G] [m : MeasurableSpace X]

/-- The sub-σ-algebra generated modulo null sets by the images of the ultrafilter operators. -/
@[instance_reducible]
def System.generatedSigma (S : System G X) (P : Set (Ultrafilter G)) : MeasurableSpace X :=
  MeasurableSpace.generateFrom
    {A | MeasurableSet A ∧ S.measure A = 0 ∨
      ∃ p ∈ P, ∃ f : Lp ℂ 2 S.measure, ∃ B : Set ℂ,
        MeasurableSet B ∧ A = (ultrafilterOperator S.koopmanRep p f) ⁻¹' B}

theorem System.generatedSigma_le (S : System G X) (P : Set (Ultrafilter G)) :
    S.generatedSigma P ≤ m := by
  apply MeasurableSpace.generateFrom_le
  rintro A (⟨hA, _⟩ | ⟨p, _, f, B, hB, rfl⟩)
  · exact hA
  · exact (Lp.stronglyMeasurable _).measurable hB

theorem System.generatedSigma_measurableSet_null (S : System G X) (P : Set (Ultrafilter G))
    {A : Set X} (hA : MeasurableSet A) (hnull : S.measure A = 0) :
    @MeasurableSet X (S.generatedSigma P) A :=
  MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨hA, hnull⟩)

theorem System.generatedSigma_measurable_image (S : System G X) (P : Set (Ultrafilter G))
    {p : Ultrafilter G} (hp : p ∈ P) (f : Lp ℂ 2 S.measure) :
    @Measurable X ℂ (S.generatedSigma P) _ (ultrafilterOperator S.koopmanRep p f) :=
  fun B hB ↦ MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨p, hp, f, B, hB, rfl⟩)

theorem System.generatedSigma_measurable_of_ae_eq (S : System G X) (P : Set (Ultrafilter G))
    {f h : X → ℂ} (hf : Measurable f) (hh : @Measurable X ℂ (S.generatedSigma P) _ h)
    (heq : f =ᵐ[S.measure] h) : @Measurable X ℂ (S.generatedSigma P) _ f := by
  intro B hB
  let A := f ⁻¹' B
  let C := h ⁻¹' B
  have hC : @MeasurableSet X (S.generatedSigma P) C := hh hB
  have hAm : MeasurableSet A := hf hB
  have hCm : MeasurableSet C := S.generatedSigma_le P C hC
  have hAC : S.measure (A \ C) = 0 := by
    apply measure_mono_null _ (ae_iff.mp heq)
    intro x hx he
    apply hx.2
    change h x ∈ B
    rw [← he]
    exact hx.1
  have hCA : S.measure (C \ A) = 0 := by
    apply measure_mono_null _ (ae_iff.mp heq)
    intro x hx he
    apply hx.2
    change f x ∈ B
    rw [he]
    exact hx.1
  have he : A = (A \ C) ∪ (C \ (C \ A)) := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  show @MeasurableSet X (S.generatedSigma P) A
  rw [he]
  exact (S.generatedSigma_measurableSet_null P (hAm.diff hCm) hAC).union
    (hC.diff (S.generatedSigma_measurableSet_null P (hCm.diff hAm) hCA))

/-- Ultrafiltration commutes with the original action, so the generated σ-algebra is invariant. -/
theorem System.generatedSigma_act_measurable (S : System G X) (P : Set (Ultrafilter G)) (g : G) :
    @Measurable X X (S.generatedSigma P) (S.generatedSigma P) (S.act g) := by
  apply @measurable_generateFrom _ _ (S.generatedSigma P)
  rintro A (⟨hA, hzero⟩ | ⟨p, hp, f, B, hB, rfl⟩)
  · apply S.generatedSigma_measurableSet_null P ((S.preserves g).measurable hA)
    rw [(S.preserves g).measure_preimage hA.nullMeasurableSet, hzero]
  · have hmeas := S.generatedSigma_measurable_image P hp (S.koopmanRep g f)
    have hc := Lp.coeFn_compMeasurePreserving (ultrafilterOperator S.koopmanRep p f) (S.preserves g)
    change S.koopmanRep g (ultrafilterOperator S.koopmanRep p f) =ᵐ[S.measure]
      (ultrafilterOperator S.koopmanRep p f) ∘ S.act g at hc
    rw [ultrafilterOperator_commute S.koopmanRep p g f] at hc
    exact (S.generatedSigma_measurable_of_ae_eq P
      ((Lp.stronglyMeasurable _).measurable.comp (S.preserves g).measurable) hmeas hc.symm) hB

/-- A copy of a type carrying the indicated measurable space. -/
def WithSigma {X : Type*} (_ : MeasurableSpace X) : Type _ := X

instance {X : Type*} (m' : MeasurableSpace X) : MeasurableSpace (WithSigma m') := m'

/-- The factor endowed with the generated σ-algebra and the restricted measure. -/
def System.generatedFactor (S : System G X) (P : Set (Ultrafilter G)) :
    System G (WithSigma (S.generatedSigma P)) := by
  change @System G X _ (S.generatedSigma P)
  let μ' : @Measure X (S.generatedSigma P) := S.measure.trim (S.generatedSigma_le P)
  refine @System.mk G X _ (S.generatedSigma P) μ' ⟨?_⟩ S.act S.act_one S.act_mul ?_
  · rw [trim_measurableSet_eq _ (@MeasurableSet.univ X (S.generatedSigma P)), measure_univ]
  · intro g
    let h := S.generatedSigma_le P
    have hmeas := S.generatedSigma_act_measurable P g
    refine @MeasurePreserving.mk X X (S.generatedSigma P) (S.generatedSigma P)
      (S.act g) μ' μ' hmeas ?_
    refine @Measure.ext X (S.generatedSigma P) _ _ ?_
    intro A hA
    rw [@Measure.map_apply X X (S.generatedSigma P) (S.generatedSigma P) μ' (S.act g) hmeas A hA,
      trim_measurableSet_eq h (hmeas hA),
      trim_measurableSet_eq h hA, (S.preserves g).measure_preimage (h A hA).nullMeasurableSet]

/-- The identity on points is the factor map to the generated sub-σ-algebra. -/
def System.generatedFactorMap (S : System G X) (P : Set (Ultrafilter G)) :
    FactorMap S (S.generatedFactor P) := by
  refine ⟨id, ⟨?_, ?_⟩, fun _ ↦ rfl⟩
  · exact measurable_id'' (S.generatedSigma_le P)
  · exact (trim_eq_map (S.generatedSigma_le P)).symm

theorem System.mem_range_generatedFactor_pullback {S : System G X} {P : Set (Ultrafilter G)}
    {f : Lp ℂ 2 S.measure} (hf : @Measurable X ℂ (S.generatedSigma P) _ f) :
    f ∈ Set.range (S.generatedFactorMap P).pullback := by
  have hm := S.generatedSigma_le P
  let f' : WithSigma (S.generatedSigma P) → ℂ := f
  have hmf : MemLp f' 2 (S.generatedFactor P).measure := by
    change @eLpNorm X ℂ _ _ (S.generatedSigma P) f 2 (S.measure.trim hm) < ⊤
    rw [eLpNorm_trim hm hf.stronglyMeasurable]
    exact (Lp.memLp f).eLpNorm_lt_top
  refine ⟨hmf.toLp f', Lp.ext ?_⟩
  have he := Lp.coeFn_compMeasurePreserving (hmf.toLp f') (S.generatedFactorMap P).preserves
  have he' := (S.generatedFactorMap P).preserves.quasiMeasurePreserving.ae_eq_comp hmf.coeFn_toLp
  exact he.trans he'

/-- In Lemma 8, the image of each Koopman ultrafilter operator pulls back from
the factor generated by the family of its images. -/
theorem System.range_ultrafilterOperator_le_generatedFactor_pullback
    (S : System G X) (P : Set (Ultrafilter G)) {p : Ultrafilter G} (hp : p ∈ P) :
    Set.range (ultrafilterOperator S.koopmanRep p) ⊆ Set.range (S.generatedFactorMap P).pullback := by
  rintro _ ⟨f, rfl⟩
  exact S.mem_range_generatedFactor_pullback (S.generatedSigma_measurable_image P hp f)

/-- A bounded normal operator and its square have the same closed range. -/
theorem closure_range_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (hA : IsStarNormal A) :
    closure (Set.range (⇑(A ^ 2 : H →L[ℂ] H))) = closure (Set.range A) := by
  let _ : IsStarNormal A := hA
  have h : (A ^ 2 : H →L[ℂ] H).range.topologicalClosure = A.range.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, ← Submodule.orthogonal_orthogonal_eq_closure,
      normal_range_orthogonal (A ^ 2) (inferInstance : IsStarNormal (A ^ 2)),
      normal_range_orthogonal A hA, normal_ker_pow A hA (by decide)]
  exact congrArg (fun W : Submodule ℂ H ↦ (W : Set H)) h

/-- The iterated generated factor still contains the images of all the ultrafilter
operators on the original space, as pulled-back L² vectors. -/
theorem System.range_ultrafilterOperator_le_iteratedFactor_pullback
    (S : System G X) (P : Set (Ultrafilter G)) {p : Ultrafilter G} (hp : p ∈ P) :
    Set.range (ultrafilterOperator S.koopmanRep p) ⊆
      Set.range ((S.generatedFactorMap P).pullback.comp
        ((S.generatedFactor P).generatedFactorMap P).pullback) := by
  let A := ultrafilterOperator S.koopmanRep p
  let F := S.generatedFactorMap P
  let F' := (S.generatedFactor P).generatedFactorMap P
  let J := F.pullback.comp F'.pullback
  have hA := ultrafilterOperator_normal S.koopmanRep p
  have hsq : Set.range (⇑(A ^ 2 : Lp ℂ 2 S.measure →L[ℂ] Lp ℂ 2 S.measure)) ⊆ Set.range J := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨f', hf'⟩ := S.range_ultrafilterOperator_le_generatedFactor_pullback P hp ⟨f, rfl⟩
    obtain ⟨f'', hf''⟩ := (S.generatedFactor P).range_ultrafilterOperator_le_generatedFactor_pullback
      P hp ⟨f', rfl⟩
    refine ⟨f'', ?_⟩
    change F.pullback (F'.pullback f'') = (A ^ 2) f
    calc
      _ = F.pullback (ultrafilterOperator (S.generatedFactor P).koopmanRep p f') := congrArg _ hf''
      _ = A (F.pullback f') := F.intertwines_pullback.ultrafilter p f'
      _ = (A ^ 2) f := by rw [hf', pow_two]; rfl
  have heq := closure_range_sq A hA
  have hcl := closure_minimal hsq J.isometry.isClosedEmbedding.isClosed_range
  rw [heq] at hcl
  exact subset_closure.trans hcl

/-- Lemma 8 in its σ-algebra formulation. Forming the generated factor twice gives
the same σ-algebra on the underlying points. -/
theorem System.generatedSigma_idempotent (S : System G X) (P : Set (Ultrafilter G)) :
    (S.generatedFactor P).generatedSigma P = S.generatedSigma P := by
  let T := S.generatedFactor P
  let F := S.generatedFactorMap P
  let F' := T.generatedFactorMap P
  apply le_antisymm (T.generatedSigma_le P)
  apply MeasurableSpace.generateFrom_le
  rintro A (⟨hA, hzero⟩ | ⟨p, hp, f, B, hB, rfl⟩)
  · have hMeas := S.generatedSigma_measurableSet_null P hA hzero
    apply T.generatedSigma_measurableSet_null P hMeas
    exact (trim_measurableSet_eq (S.generatedSigma_le P) hMeas).trans hzero
  · let v := ultrafilterOperator S.koopmanRep p f
    have hv := S.generatedSigma_measurable_image P hp f
    obtain ⟨w, hw⟩ := S.range_ultrafilterOperator_le_iteratedFactor_pullback P hp ⟨f, rfl⟩
    have h1 := Lp.coeFn_compMeasurePreserving w F'.preserves
    have h2 := Lp.coeFn_compMeasurePreserving (F'.pullback w) F.preserves
    have hwv : (w : WithSigma (T.generatedSigma P) → ℂ) =ᵐ[S.measure] v :=
      ((h2.trans (F.preserves.quasiMeasurePreserving.ae_eq_comp h1)).symm).trans
        (Filter.EventuallyEq.of_eq (congrArg (fun u : Lp ℂ 2 S.measure ↦ (u : X → ℂ)) hw))
    have hwm := (Lp.stronglyMeasurable w).measurable
    have hwm' : @Measurable X ℂ (S.generatedSigma P) _ w :=
      fun B hB ↦ T.generatedSigma_le P (w ⁻¹' B) (hwm hB)
    have hwv' : (w : WithSigma (T.generatedSigma P) → ℂ) =ᵐ[T.measure] v :=
      ae_eq_trim_of_measurable (S.generatedSigma_le P) hwm' hv hwv
    exact T.generatedSigma_measurable_of_ae_eq P hv hwm hwv'.symm hB

/-- A factor map pulls sets in the generated σ-algebra back into the corresponding
generated σ-algebra of the extension. -/
theorem FactorMap.measurable_generatedSigma {Y : Type*} [MeasurableSpace Y]
    {S : System G X} {T : System G Y} (f : FactorMap S T) {P Q : Set (Ultrafilter G)}
    (hPQ : P ⊆ Q) :
    @Measurable X Y (S.generatedSigma Q) (T.generatedSigma P) f.toFun := by
  apply @measurable_generateFrom _ _ (S.generatedSigma Q)
  rintro A (⟨hA, hzero⟩ | ⟨p, hp, v, B, hB, rfl⟩)
  · apply S.generatedSigma_measurableSet_null Q (f.preserves.measurable hA)
    rw [f.preserves.measure_preimage hA.nullMeasurableSet, hzero]
  · have hMeas := S.generatedSigma_measurable_image Q (hPQ hp) (f.pullback v)
    have he := Lp.coeFn_compMeasurePreserving (ultrafilterOperator T.koopmanRep p v) f.preserves
    change f.pullback (ultrafilterOperator T.koopmanRep p v) =ᵐ[S.measure]
      (ultrafilterOperator T.koopmanRep p v) ∘ f.toFun at he
    have hcomm : f.pullback (ultrafilterOperator T.koopmanRep p v) =
        ultrafilterOperator S.koopmanRep p (f.pullback v) :=
      f.intertwines_pullback.ultrafilter p v
    rw [hcomm] at he
    exact (S.generatedSigma_measurable_of_ae_eq Q
      ((Lp.stronglyMeasurable _).measurable.comp f.preserves.measurable) hMeas he.symm) hB

end Mixing
