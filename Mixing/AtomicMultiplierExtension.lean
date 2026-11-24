module

public import Mixing.FactorJoiningLift
public import Mixing.JoiningExtreme
public import Mixing.StandardGeneratedFactor
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {G X X' Y Z : Type*} [CommGroup G]
variable [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y] [MeasurableSpace Z]

/-- If a factor is a multiplier against a system mixing along an ultrafilter,
then so is an extension whose conditional atoms have a uniform positive mass.
The original joining is dominated by a product obtained by reinstating the
extension coordinate independently conditional on the factor. -/
theorem FactorMap.disjoint_joining_of_uniform_atoms
    {T : System G X} {T' : System G X'} {S : System G Y} {R : System G Z}
    (f : FactorMap T T') (κ : Kernel X' X) [IsMarkovKernel κ]
    {a : ℝ≥0∞} (ha : 0 < a) (haTop : a ≠ ∞)
    (hAtoms : ∀ᵐ x ∂T.measure, a ≤ κ (f.toFun x) {x})
    (p : Ultrafilter G) (hMix : R.IsUMixing {p})
    (hMult : ∀ (σ' : Measure (X' × Y)) (hσ' : IsJoining T' S σ'), Disjoint hσ'.system R)
    {σ : Measure (X × Y)} (hσ : IsJoining T S σ) : Disjoint hσ.system R := by
  let SId : FactorMap S S := ⟨id, MeasurePreserving.id _, fun _ => rfl⟩
  let RId : FactorMap R R := ⟨id, MeasurePreserving.id _, fun _ => rfl⟩
  let π := Prod.map f.toFun (id : Y → Y)
  let σ' := σ.map π
  have hσ' : IsJoining T' S σ' := hσ.map f SId
  let F : FactorMap hσ.system hσ'.system :=
    ⟨π, ⟨f.preserves.measurable.prodMap measurable_id, rfl⟩, fun g => by
      funext w
      exact Prod.ext (congrFun (f.equivariant g) w.1) rfl⟩
  intro η hη
  let τ := η.map Prod.swap
  have hτ : IsJoining R hσ.system τ := hη.swap
  let πZ := Prod.map (id : Z → Z) π
  have hπZ : MeasurePreserving πZ τ (R.measure.prod σ') := by
    have hj : IsJoining R hσ'.system (τ.map πZ) := hτ.map RId F
    exact ⟨measurable_id.prodMap F.preserves.measurable, (hMult σ' hσ').symm _ hj⟩
  let J : Kernel (X' × Y) (X × Y) := κ ∥ₖ Kernel.id
  let K : Kernel (Z × (X' × Y)) (Z × (X × Y)) := Kernel.id ∥ₖ J
  let := hσ'.probability
  let := hτ.probability
  let ν := J ∘ₘ σ'
  have hlarge : ∀ᵐ w ∂τ, a ≤ κ (f.toFun w.2.1) {w.2.1} :=
    ((hσ.fst.comp hτ.snd).quasiMeasurePreserving.ae hAtoms)
  have hdom : a • τ ≤ R.measure.prod ν := by
    rw [Measure.prod_comp_right]
    apply Measure.le_iff.2
    intro A hA
    rw [smul_apply, smul_eq_mul, Measure.bind_apply hA K.aemeasurable,
      ← hπZ.lintegral_comp (K.measurable_coe hA), ← lintegral_indicator_const hA]
    apply lintegral_mono_ae
    filter_upwards [hlarge] with w hw
    by_cases hwA : w ∈ A
    · rw [indicator_of_mem hwA]
      change a ≤ K (πZ w) A
      rw [Kernel.parallelComp_apply, Kernel.id_apply, Kernel.parallelComp_apply,
        Kernel.id_apply, Measure.dirac_prod, Measure.prod_dirac, Measure.map_map
          measurable_prodMk_left measurable_prodMk_right,
        Measure.map_apply (measurable_prodMk_left.comp measurable_prodMk_right) hA]
      apply hw.trans
      apply measure_mono
      intro x hx
      have hx' : x = w.2.1 := hx
      change (w.1, (x, w.2.2)) ∈ A
      rwa [hx']
    · simp [hwA]
  have he := dominated_joining_eq_prod_of_reference hτ (ENNReal.inv_ne_top.mpr ha.ne')
    (le_inv_smul_of_smul_le ha.ne' haTop hdom) p hMix
  calc
    η = τ.map Prod.swap := by
      rw [Measure.map_map measurable_swap measurable_swap]
      exact Measure.map_id.symm
    _ = σ.prod R.measure := by rw [he]; exact Measure.prod_swap

/-- The partially rigid multiplier conclusion, using a generated factor that
contains the weak-limit image. -/
theorem corollary7_iii_of_generated_factor
    [MetricSpace X] [SecondCountableTopology X] [BorelSpace X]
    [StandardBorelSpace X] [Nonempty X] [MeasurableEq X']
    {T : System G X} {T' : System G X'} {S : System G Y} {R : System G Z}
    (f : FactorMap T T') (p : Ultrafilter G) (hp : p ∈ freeUltrafilters G)
    {a : ℝ} (ha : 0 < a) (hRigid : T.IsPartiallyRigidAlong p a)
    (hGen : T'.IsUGenerated {p})
    (hRange : Set.range (ultrafilterOperator T.koopmanRep p) ⊆ Set.range f.pullback)
    (hMix : IsStronglyMixing R.koopmanZeroRep) (hDisjoint : Disjoint S R)
    {σ : Measure (X × Y)} (hσ : IsJoining T S σ) : Disjoint hσ.system R := by
  have hMix' : R.IsUMixing {p} := by
    intro q hq
    have he : q = p := mem_singleton_iff.mp hq
    subst q
    exact (isStronglyMixing_iff_isUMixing_free _).1 hMix p hp
  have hAtoms := ae_atom_mass_of_partialRigidity f f.conditionalKernel f.comp_conditionalKernel
    f.ae_conditionalKernel_fibre p ha hRigid hRange
  exact f.disjoint_joining_of_uniform_atoms f.conditionalKernel (ENNReal.ofReal_pos.2 ha)
    ENNReal.ofReal_ne_top hAtoms p hMix'
    (fun _ hσ' => System.disjoint_joining_of_isUGenerated hσ' hGen hMix' hDisjoint) hσ

/-- Corollary 7(iii). A partially rigid system is a multiplier for every
strongly mixing system. -/
theorem corollary7_iii [Countable G]
    [StandardBorelSpace X] {T : System G X} {S : System G Y} {R : System G Z}
    (p : Ultrafilter G) (hp : p ∈ freeUltrafilters G)
    {a : ℝ} (ha : 0 < a) (hRigid : T.IsPartiallyRigidAlong p a)
    (hMix : IsStronglyMixing R.koopmanZeroRep) (hDisjoint : Disjoint S R)
    {σ : Measure (X × Y)} (hσ : IsJoining T S σ) : Disjoint hσ.system R := by
  let := nonempty_of_isProbabilityMeasure T.measure
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let := upgradeStandardBorel X
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact corollary7_iii_of_generated_factor (T.standardGeneratedFactorMap p) p hp ha hRigid
    (T.standardGeneratedFactor_isUGenerated p) (T.range_ultrafilterOperator_le_standardFactor p)
    hMix hDisjoint hσ

end Mixing
