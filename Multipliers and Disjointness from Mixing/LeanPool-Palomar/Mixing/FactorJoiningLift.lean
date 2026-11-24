module

public import Mixing.JoiningDisintegration
public import Mixing.MainTheorems
public import Mixing.RigidRepresentations
public import Mathlib.Probability.Kernel.CompProdEqIff

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {G X X' Y Z : Type*} [Group G]
variable [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Z]

private theorem act_inv_act (S : System G X) (g : G) (x : X) :
    S.act g⁻¹ (S.act g x) = x := by
  change (S.act g⁻¹ ∘ S.act g) x = x
  rw [← S.act_mul, inv_mul_cancel, S.act_one]
  rfl

variable [StandardBorelSpace X] [Nonempty X]
variable {T : System G X} {T' : System G X'}

/-- The conditional law of the extension over a factor point. -/
def FactorMap.conditionalKernel (f : FactorMap T T') : Kernel X' X :=
  (coordinateGraph T.measure f.toFun).condKernel

instance (f : FactorMap T T') : IsMarkovKernel f.conditionalKernel :=
  inferInstanceAs (IsMarkovKernel (coordinateGraph T.measure f.toFun).condKernel)

/-- The joint law of the factor and extension disintegrates over the factor measure. -/
theorem FactorMap.compProd_conditionalKernel (f : FactorMap T T') :
    T'.measure ⊗ₘ f.conditionalKernel = coordinateGraph T.measure f.toFun := by
  have hfst : (coordinateGraph T.measure f.toFun).fst = T'.measure :=
    (coordinateGraph_fst _ f.preserves.measurable).trans f.preserves.map_eq
  rw [← hfst]
  unfold FactorMap.conditionalKernel
  exact (coordinateGraph T.measure f.toFun).disintegrate _

/-- Integrating the conditional laws recovers the extension measure. -/
theorem FactorMap.comp_conditionalKernel (f : FactorMap T T') :
    f.conditionalKernel ∘ₘ T'.measure = T.measure := by
  rw [← Measure.snd_compProd, f.compProd_conditionalKernel,
    coordinateGraph_snd _ f.preserves.measurable]

/-- Almost every conditional law is supported on its own fibre. -/
theorem FactorMap.ae_conditionalKernel_fibre [MeasurableEq X'] (f : FactorMap T T') :
    ∀ᵐ y ∂T'.measure, ∀ᵐ x ∂f.conditionalKernel y, f.toFun x = y := by
  apply Measure.ae_ae_of_ae_compProd (p := fun w => f.toFun w.2 = w.1)
  rw [f.compProd_conditionalKernel]
  apply (ae_map_iff (f.preserves.measurable.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun (f.preserves.measurable.comp measurable_snd) measurable_fst)).2
  exact Eventually.of_forall fun _ => rfl

/-- Applying the extension action transports conditional laws along the factor action. -/
theorem FactorMap.ae_conditionalKernel_equivariant (f : FactorMap T T') (g : G) :
    ∀ᵐ y ∂T'.measure,
      (f.conditionalKernel y).map (T.act g) = f.conditionalKernel (T'.act g y) := by
  let κ := f.conditionalKernel
  let ρ := coordinateGraph T.measure f.toFun
  let I := Prod.map (id : X' → X') (T.act g)
  let J := Prod.map (T'.act g⁻¹) (id : X → X)
  have hI : Measurable I := measurable_id.prodMap (T.preserves g).measurable
  have hJ : Measurable J := (T'.preserves g⁻¹).measurable.prodMap measurable_id
  have hAct : Measurable (T'.prodAct T g) :=
    (T'.preserves g).measurable.prodMap (T.preserves g).measurable
  have hgraph : Measurable (fun x : X => (f.toFun x, x)) :=
    f.preserves.measurable.prodMk measurable_id
  have hρInv : ρ.map (T'.prodAct T g) = ρ := by
    change (T.measure.map fun x => (f.toFun x, x)).map (T'.prodAct T g) = _
    rw [Measure.map_map hAct hgraph]
    have hcomm : T'.prodAct T g ∘ (fun x => (f.toFun x, x)) =
        (fun x => (f.toFun x, x)) ∘ T.act g := by
      funext x
      exact Prod.ext (congrFun (f.equivariant g).symm x) rfl
    rw [hcomm, ← Measure.map_map hgraph (T.preserves g).measurable, (T.preserves g).map_eq]
    rfl
  have hIJ : ρ.map I = ρ.map J := by
    have hcomp : J ∘ T'.prodAct T g = I := by
      funext w
      exact Prod.ext (act_inv_act T' g w.1) rfl
    rw [← hcomp, ← Measure.map_map hJ hAct, hρInv]
  have hLeft : ρ.map I = T'.measure ⊗ₘ κ.map (T.act g) := by
    have hρ : T'.measure ⊗ₘ κ = ρ := f.compProd_conditionalKernel
    rw [← hρ]
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.map_apply hI (hA.prod hB)]
    change (T'.measure ⊗ₘ κ) (A ×ˢ ((T.act g) ⁻¹' B)) = _
    rw [Measure.compProd_apply_prod hA ((T.preserves g).measurable hB),
      Measure.compProd_apply_prod hA hB]
    simp_rw [Kernel.map_apply' _ (T.preserves g).measurable _ hB]
  have hRight : ρ.map J = T'.measure ⊗ₘ κ.comap (T'.act g) (T'.preserves g).measurable := by
    have hρ : T'.measure ⊗ₘ κ = ρ := f.compProd_conditionalKernel
    rw [← hρ]
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.map_apply hJ (hA.prod hB)]
    change (T'.measure ⊗ₘ κ) (((T'.act g⁻¹) ⁻¹' A) ×ˢ B) = _
    rw [Measure.compProd_apply_prod ((T'.preserves g⁻¹).measurable hA) hB,
      Measure.compProd_apply_prod hA hB, ← lintegral_indicator ((T'.preserves g⁻¹).measurable hA),
      ← lintegral_indicator hA]
    let F := ((T'.act g⁻¹) ⁻¹' A).indicator (fun y => κ y B)
    calc
      ∫⁻ y, F y ∂T'.measure = ∫⁻ y, F (T'.act g y) ∂T'.measure :=
        ((T'.preserves g).lintegral_comp
          ((κ.measurable_coe hB).indicator ((T'.preserves g⁻¹).measurable hA))).symm
      _ = _ := by
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ A <;>
          simp [F, Set.mem_preimage, act_inv_act, hy, Kernel.comap_apply]
  have heq : T'.measure ⊗ₘ κ.map (T.act g) =
      T'.measure ⊗ₘ κ.comap (T'.act g) (T'.preserves g).measurable :=
    hLeft.symm.trans (hIJ.trans hRight)
  filter_upwards [Kernel.ae_eq_of_compProd_eq heq] with y hy
  simpa only [Kernel.map_apply κ (T.preserves g).measurable, Kernel.comap_apply] using hy

/-- Every joining of a factor with a third system lifts to a joining of the
extension with that system. The lift uses the conditional law of the extension. -/
theorem FactorMap.exists_joining_lift [MeasurableEq X'] (f : FactorMap T T')
    {R : System G Y} {σ : Measure (X' × Y)} (hσ : IsJoining T' R σ) :
    ∃ τ, IsJoining T R τ ∧ τ.map (Prod.map f.toFun id) = σ := by
  let := hσ.probability
  let κ := f.conditionalKernel
  let K : Kernel (X' × Y) (X × Y) := κ ∥ₖ Kernel.id
  have hK (w : X' × Y) : K w = (κ w.1).prod (Measure.dirac w.2) := by
    rw [Kernel.parallelComp_apply, Kernel.id_apply]
  let τ := K ∘ₘ σ
  have hfst : τ.map Prod.fst = T.measure := by
    rw [Measure.map_comp _ _ measurable_fst]
    have hfirst (w : X' × Y) : (K.map Prod.fst) w = κ w.1 := by
      rw [Kernel.map_apply K measurable_fst, hK, Measure.map_fst_prod, measure_univ, one_smul]
    calc
      (K.map Prod.fst) ∘ₘ σ = κ ∘ₘ (σ.map Prod.fst) := by
        rw [Measure.bind_map measurable_fst.aemeasurable κ.aemeasurable]
        congr
        exact funext hfirst
      _ = T.measure := hσ.fst.map_eq ▸ f.comp_conditionalKernel
  have hsnd : τ.map Prod.snd = R.measure := by
    rw [Measure.map_comp _ _ measurable_snd]
    have hsecond (w : X' × Y) : (K.map Prod.snd) w = Measure.dirac w.2 := by
      rw [Kernel.map_apply K measurable_snd, hK, Measure.map_snd_prod, measure_univ, one_smul]
    calc
      (K.map Prod.snd) ∘ₘ σ = (σ.map Prod.snd).bind Measure.dirac := by
        rw [Measure.bind_map measurable_snd.aemeasurable Measure.measurable_dirac.aemeasurable]
        congr
        exact funext hsecond
      _ = R.measure := Measure.bind_dirac.trans hσ.snd.map_eq
  have hinv (g : G) : MeasurePreserving (T.prodAct R g) τ τ := by
    have hact : Measurable (T.prodAct R g) :=
      (T.preserves g).measurable.prodMap (R.preserves g).measurable
    refine ⟨hact, ?_⟩
    rw [Measure.map_comp _ _ hact]
    let L := K.comap (T'.prodAct R g) (hσ.invariant g).measurable
    have heq : ∀ᵐ w ∂σ, K.map (T.prodAct R g) w = L w := by
      filter_upwards [hσ.fst.quasiMeasurePreserving.ae (f.ae_conditionalKernel_equivariant g)]
        with w hw
      rw [Kernel.map_apply K hact, Kernel.comap_apply, hK, hK]
      change ((κ w.1).prod (Measure.dirac w.2)).map (Prod.map (T.act g) (R.act g)) =
        (κ (T'.act g w.1)).prod (Measure.dirac (R.act g w.2))
      rw [← Measure.map_prod_map _ _ (T.preserves g).measurable (R.preserves g).measurable,
        Measure.map_dirac' (R.preserves g).measurable, hw]
    calc
      (K.map (T.prodAct R g)) ∘ₘ σ = L ∘ₘ σ := Measure.comp_congr heq
      _ = K ∘ₘ σ := by
        change σ.bind (fun w => K (T'.prodAct R g w)) = σ.bind K
        rw [← Measure.bind_map (hσ.invariant g).measurable.aemeasurable K.aemeasurable,
          (hσ.invariant g).map_eq]
  refine ⟨τ, ⟨inferInstanceAs (IsProbabilityMeasure (K ∘ₘ σ)), ⟨measurable_fst, hfst⟩,
    ⟨measurable_snd, hsnd⟩, hinv⟩, ?_⟩
  have hπ : Measurable (Prod.map f.toFun (id : Y → Y)) :=
    f.preserves.measurable.prodMap measurable_id
  rw [Measure.map_comp _ _ hπ]
  have heq : ∀ᵐ w ∂σ, (K.map (Prod.map f.toFun (id : Y → Y))) w = Measure.dirac w := by
    filter_upwards [hσ.fst.quasiMeasurePreserving.ae f.ae_conditionalKernel_fibre] with w hw
    rw [Kernel.map_apply K hπ, hK,
      ← Measure.map_prod_map _ _ f.preserves.measurable measurable_id, Measure.map_id,
      Measure.map_congr (show f.toFun =ᵐ[κ w.1] fun _ => w.1 from hw), Measure.map_const,
      measure_univ, one_smul, Measure.dirac_prod_dirac]
  calc
    (K.map (Prod.map f.toFun (id : Y → Y))) ∘ₘ σ = σ.bind Measure.dirac :=
      Measure.bind_congr_right heq
    _ = σ := Measure.bind_dirac

/-- The multiplier property descends to factors. The joinings in the
definition are lifted twice, once for each joining coordinate. -/
theorem FactorMap.disjoint_joining_of_extension [StandardBorelSpace X'] [StandardBorelSpace Y]
    [Nonempty Y] (f : FactorMap T T') {S : System G Y} {R : System G Z}
    (hMult : ∀ (τ : Measure (X × Y)) (hτ : IsJoining T S τ), Disjoint hτ.system R)
    {σ : Measure (X' × Y)} (hσ : IsJoining T' S σ) : Disjoint hσ.system R := by
  obtain ⟨τ, hτ, hpush⟩ := f.exists_joining_lift hσ
  let F : FactorMap hτ.system hσ.system :=
    ⟨Prod.map f.toFun id, ⟨f.preserves.measurable.prodMap measurable_id, hpush⟩,
      fun g => by
        funext w
        exact Prod.ext (congrFun (f.equivariant g) w.1) rfl⟩
  intro ξ hξ
  obtain ⟨ξ', hξ', hξpush⟩ := F.exists_joining_lift hξ
  calc
    ξ = ξ'.map (Prod.map F.toFun id) := hξpush.symm
    _ = (τ.prod R.measure).map (Prod.map F.toFun id) :=
      congrArg (Measure.map (Prod.map F.toFun id)) (hMult τ hτ ξ' hξ')
    _ = σ.prod R.measure := (F.preserves.prod (MeasurePreserving.id R.measure)).map_eq

section GeneratedMultipliers

variable {Γ : Type*} [CommGroup Γ] [StandardBorelSpace X'] [StandardBorelSpace Y] [Nonempty Y]
variable {T₀ : System Γ X} {T₁ : System Γ X'} {S : System Γ Y} {R : System Γ Z}

/-- Corollary 7(i). Every factor of a U-generated system is a multiplier for
U-mixing systems. In the paper, those factors constitute the characteristic
closure of the class of U-generated systems. -/
theorem corollary7_i (f : FactorMap T₀ T₁) {U : Set (Ultrafilter Γ)}
    (hGen : T₀.IsUGenerated U) (hMix : R.IsUMixing U) (hDisjoint : Disjoint S R)
    {σ : Measure (X' × Y)} (hσ : IsJoining T₁ S σ) : Disjoint hσ.system R :=
  f.disjoint_joining_of_extension
    (fun _ hτ => System.disjoint_joining_of_isUGenerated hτ hGen hMix hDisjoint) hσ

/-- The strongly mixing specialization of Corollary 7(i). -/
theorem corollary7_i_stronglyMixing (f : FactorMap T₀ T₁)
    (hGen : T₀.IsUGenerated (freeUltrafilters Γ))
    (hMix : IsStronglyMixing R.koopmanZeroRep) (hDisjoint : Disjoint S R)
    {σ : Measure (X' × Y)} (hσ : IsJoining T₁ S σ) : Disjoint hσ.system R :=
  corollary7_i f hGen ((isStronglyMixing_iff_isUMixing_free _).1 hMix) hDisjoint hσ

/-- First inclusion in Corollary 7(ii). A rigid system is generated by the
free idempotents, so it also belongs to the class of factors of such systems. -/
theorem corollary7_ii_rigid_generated (V : System Γ Z)
    (hRigid : IsRigidRepresentation V.koopmanRep) :
    V.IsUGenerated (freeIdempotentUltrafilters Γ) := by
  obtain ⟨p, hp, he⟩ := exists_freeIdempotent_operator_eq_one_of_rigid V.koopmanRep hRigid
  apply V.isUGenerated_of_koopmanIsUGenerated
  unfold IsUGenerated
  apply top_unique
  intro x _
  apply (Submodule.span ℂ _).le_topologicalClosure
  apply Submodule.subset_span
  apply Set.mem_iUnion.2
  refine ⟨⟨p, hp⟩, x, ?_⟩
  rw [he]
  rfl

/-- Second inclusion in Corollary 7(ii). Factors of systems generated by the
free idempotents are multipliers for mildly mixing systems. -/
theorem corollary7_ii [Countable Γ] (f : FactorMap T₀ T₁)
    (hGen : T₀.IsUGenerated (freeIdempotentUltrafilters Γ))
    (hMix : IsMildlyMixing R.koopmanZeroRep) (hDisjoint : Disjoint S R)
    {σ : Measure (X' × Y)} (hσ : IsJoining T₁ S σ) : Disjoint hσ.system R :=
  corollary7_i f hGen ((isMildlyMixing_iff_isUMixing_freeIdempotents _).1 hMix) hDisjoint hσ

end GeneratedMultipliers

end Mixing
