module

public import Mixing.ErgodicBarycenters

@[expose] public section

noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {X Y Z G : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

private theorem map_compProd_second {ν : Measure Z} [IsFiniteMeasure ν]
    (κ : Kernel Z X) [IsMarkovKernel κ] {f : X → Y} (hf : Measurable f) :
    (ν ⊗ₘ κ).map (Prod.map id f) = ν ⊗ₘ κ.map f := by
  apply Measure.ext_prod
  intro A B hA hB
  have hmap : Measurable (Prod.map (id : Z → Z) f) := measurable_id.prodMap hf
  rw [Measure.map_apply hmap (hA.prod hB)]
  change (ν ⊗ₘ κ) (A ×ˢ (f ⁻¹' B)) = _
  rw [Measure.compProd_apply_prod hA (hf hB), Measure.compProd_apply_prod hA hB]
  simp_rw [Kernel.map_apply' _ hf _ hB]

/-- The joint law of a measurable coordinate and the original point. -/
def coordinateGraph (μ : Measure X) (π : X → Z) : Measure (Z × X) :=
  μ.map fun x ↦ (π x, x)

instance (μ : Measure X) [IsFiniteMeasure μ] (π : X → Z) :
    IsFiniteMeasure (coordinateGraph μ π) := Measure.isFiniteMeasure_map μ _

theorem coordinateGraph_fst (μ : Measure X) {π : X → Z} (hπ : Measurable π) :
    (coordinateGraph μ π).fst = μ.map π :=
  Measure.fst_map_prodMk hπ measurable_id

theorem coordinateGraph_snd (μ : Measure X) {π : X → Z} (hπ : Measurable π) :
    (coordinateGraph μ π).snd = μ := by
  change (μ.map fun x ↦ (π x, id x)).snd = μ
  rw [Measure.snd_map_prodMk hπ measurable_id, Measure.map_id]

theorem coordinateGraph_map {μ : Measure X} {f : X → Y} {π : Y → Z} (hf : Measurable f)
    (hπ : Measurable π) :
    (coordinateGraph μ (π ∘ f)).map (Prod.map id f) = coordinateGraph (μ.map f) π := by
  have h₁ : Measurable (fun x : X ↦ ((π ∘ f) x, x)) := (hπ.comp hf).prodMk measurable_id
  have h₂ : Measurable (fun y : Y ↦ (π y, y)) := hπ.prodMk measurable_id
  simp only [coordinateGraph]
  rw [Measure.map_map (measurable_id.prodMap hf) h₁, Measure.map_map h₂ hf]
  rfl

/-- Conditional measures for an invariant observable are themselves invariant. -/
theorem ae_preserves_condKernel_coordinateGraph [StandardBorelSpace X] [Nonempty X]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : X → Z} (hπ : Measurable π)
    {f : X → X} (hf : MeasurePreserving f μ μ) (hfix : π ∘ f = π) :
    ∀ᵐ z ∂μ.map π, MeasurePreserving f ((coordinateGraph μ π).condKernel z)
      ((coordinateGraph μ π).condKernel z) := by
  let ρ := coordinateGraph μ π
  have hprob : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff (hπ.prodMk measurable_id).aemeasurable).2 inferInstance
  let κ := ρ.condKernel
  have hfst := coordinateGraph_fst μ hπ
  have hρ : ρ = ρ.fst ⊗ₘ κ := (ρ.disintegrate κ).symm
  have hmap : ρ = ρ.fst ⊗ₘ κ.map f := by
    rw [← map_compProd_second κ hf.measurable, ← hρ]
    have he := coordinateGraph_map hf.measurable hπ (μ := μ)
    rw [hfix, hf.map_eq] at he
    exact he.symm
  have hae := eq_condKernel_of_measure_eq_compProd (κ.map f) hmap
  rw [← hfst]
  filter_upwards [hae] with z hz
  exact ⟨hf.measurable, (Kernel.map_apply κ hf.measurable z).symm.trans hz⟩

/-- The disintegration of a joining over an invariant factor of its second
coordinate has the correct marginals and diagonal invariance. This is Lemma 1(i). -/
theorem lemma1_i [Group G] [Countable G] [StandardBorelSpace X] [StandardBorelSpace Y]
    [Nonempty X] [Nonempty Y] {S : System G X} {T : System G Y}
    (hS : S.IsErgodic) {joining : Measure (X × Y)} [IsProbabilityMeasure joining]
    (hj : IsJoining S T joining)
    {π : Y → Z} (hπ : Measurable π) (hfix : ∀ g, π ∘ T.act g = π) :
    ∀ᵐ z ∂T.measure.map π,
      MeasurePreserving Prod.fst
        ((coordinateGraph joining (π ∘ Prod.snd)).condKernel z) S.measure ∧
      MeasurePreserving Prod.snd
        ((coordinateGraph joining (π ∘ Prod.snd)).condKernel z)
        ((coordinateGraph T.measure π).condKernel z) ∧
      ∀ g, MeasurePreserving (S.prodAct T g)
        ((coordinateGraph joining (π ∘ Prod.snd)).condKernel z)
        ((coordinateGraph joining (π ∘ Prod.snd)).condKernel z) := by
  let ν := T.measure.map π
  have hν : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2
    inferInstance
  let q := π ∘ (Prod.snd : X × Y → Y)
  have hq : Measurable q := hπ.comp measurable_snd
  have hbase : joining.map q = ν := by rw [← Measure.map_map hπ measurable_snd, hj.snd.map_eq]
  let ρ := coordinateGraph joining q
  let κ := ρ.condKernel
  have hfst : ρ.fst = ν := (coordinateGraph_fst joining hq).trans hbase
  have hρ : ρ = ν ⊗ₘ κ := by
    rw [← hfst]
    exact (ρ.disintegrate κ).symm
  have hinv (g : G) : ∀ᵐ z ∂ν, MeasurePreserving (S.prodAct T g) (κ z) (κ z) := by
    rw [← hbase]
    refine ae_preserves_condKernel_coordinateGraph hq (hj.invariant g) ?_
    funext w
    exact congrFun (hfix g) w.2
  have hleftavg : (κ.map Prod.fst) ∘ₘ ν = S.measure := by
    rw [← Measure.map_comp ν κ measurable_fst, ← Measure.snd_compProd, ← hρ,
      coordinateGraph_snd joining hq, hj.fst.map_eq]
  have hleftinv (g : G) : ∀ᵐ z ∂ν,
      MeasurePreserving (S.act g) ((κ.map Prod.fst) z) ((κ.map Prod.fst) z) := by
    filter_upwards [hinv g] with z hz
    rw [Kernel.map_apply κ measurable_fst]
    refine ⟨(S.preserves g).measurable, ?_⟩
    have hcomm : S.act g ∘ Prod.fst = Prod.fst ∘ S.prodAct T g := rfl
    rw [Measure.map_map (S.preserves g).measurable measurable_fst, hcomm,
      ← Measure.map_map measurable_fst hz.measurable, hz.map_eq]
  have hMarkov : IsMarkovKernel (κ.map Prod.fst) := Kernel.IsMarkovKernel.map κ measurable_fst
  have hleft := ae_kernel_eq_of_ergodic_barycenter hS ν (κ.map Prod.fst) hleftavg hleftinv
  let σ := coordinateGraph T.measure π
  have hσfst : σ.fst = ν := coordinateGraph_fst T.measure hπ
  have hrightEq : σ = σ.fst ⊗ₘ κ.map Prod.snd := by
    rw [hσfst, ← map_compProd_second κ measurable_snd, ← hρ,
      coordinateGraph_map measurable_snd hπ, hj.snd.map_eq]
  have hright := eq_condKernel_of_measure_eq_compProd (κ.map Prod.snd) hrightEq
  rw [hσfst] at hright
  filter_upwards [hleft, hright, ae_all_iff.2 hinv] with z hz₁ hz₂ hz₃
  exact ⟨⟨measurable_fst, (Kernel.map_apply κ measurable_fst z).symm.trans hz₁⟩,
    ⟨measurable_snd, (Kernel.map_apply κ measurable_snd z).symm.trans hz₂⟩, hz₃⟩

/-- The system with the same action and a new invariant probability measure. -/
def System.withInvariantMeasure [Group G] (T : System G Y) (μ : Measure Y)
    [IsProbabilityMeasure μ] (h : ∀ g, MeasurePreserving (T.act g) μ μ) : System G Y :=
  ⟨μ, inferInstance, T.act, T.act_one, T.act_mul, h⟩

/-- The componentwise-to-global direction of Lemma 1(iii). -/
theorem lemma1_iii_of_componentwise_disjoint
    [Group G] [Countable G] [StandardBorelSpace X] [StandardBorelSpace Y]
    [Nonempty X] [Nonempty Y] {S : System G X} {T : System G Y}
    (hS : S.IsErgodic) {π : Y → Z} (hπ : Measurable π) (hfix : ∀ g, π ∘ T.act g = π)
    (hdis : ∀ᵐ z ∂T.measure.map π,
      ∀ hInv : ∀ g, MeasurePreserving (T.act g) ((coordinateGraph T.measure π).condKernel z)
        ((coordinateGraph T.measure π).condKernel z),
      Disjoint S (T.withInvariantMeasure ((coordinateGraph T.measure π).condKernel z) hInv)) :
    Disjoint S T := by
  intro joining hj
  have hprob : IsProbabilityMeasure joining := hj.probability
  let ν := T.measure.map π
  have hν : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2
    inferInstance
  let q := π ∘ (Prod.snd : X × Y → Y)
  have hq : Measurable q := hπ.comp measurable_snd
  let ρ := coordinateGraph joining q
  let σ := coordinateGraph T.measure π
  let κ := ρ.condKernel
  let η := σ.condKernel
  have hρfst : ρ.fst = ν := by
    rw [coordinateGraph_fst joining hq]
    change joining.map (π ∘ Prod.snd) = _
    rw [← Measure.map_map hπ measurable_snd, hj.snd.map_eq]
  have hσfst : σ.fst = ν := coordinateGraph_fst T.measure hπ
  have hκ : κ ∘ₘ ν = joining := by
    rw [← hρfst, ← Measure.snd_compProd, ρ.disintegrate κ, coordinateGraph_snd joining hq]
  have hη : η ∘ₘ ν = T.measure := by
    rw [← hσfst, ← Measure.snd_compProd, σ.disintegrate η, coordinateGraph_snd T.measure hπ]
  have hInv : ∀ᵐ z ∂ν, ∀ g, MeasurePreserving (T.act g) (η z) (η z) := by
    apply ae_all_iff.2
    intro g
    exact ae_preserves_condKernel_coordinateGraph hπ (T.preserves g) (hfix g)
  have hJoin := lemma1_i hS hj hπ hfix
  have heq : ∀ᵐ z ∂ν, κ z = S.measure.prod (η z) := by
    filter_upwards [hInv, hJoin, hdis] with z hIz hz hd
    exact hd hIz (κ z) ⟨inferInstance, hz.1, hz.2.1, hz.2.2⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.prod_prod, ← hκ, ← hη]
  change ν.bind κ (A ×ˢ B) = S.measure A * ν.bind η B
  rw [Measure.bind_apply (hA.prod hB) κ.aemeasurable, Measure.bind_apply hB η.aemeasurable,
    ← lintegral_const_mul _ (η.measurable_coe hB)]
  apply lintegral_congr_ae
  filter_upwards [heq] with z hz
  rw [hz, Measure.prod_prod]

end Mixing
