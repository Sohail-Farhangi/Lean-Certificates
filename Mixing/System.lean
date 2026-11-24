module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

namespace Mixing

open MeasureTheory

/-- A probability-preserving action, with the probability space left explicit. -/
structure System (G X : Type*) [Group G] [MeasurableSpace X] where
  measure : Measure X
  probability : IsProbabilityMeasure measure
  act : G → X → X
  act_one : act 1 = id
  act_mul : ∀ g h, act (g * h) = act g ∘ act h
  preserves : ∀ g, MeasurePreserving (act g) measure measure

attribute [instance] System.probability

variable {G X Y Z W : Type*} [Group G]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

namespace System

/-- The diagonal action on two probability-preserving systems. -/
def prodAct (S : System G X) (T : System G Y) (g : G) : X × Y → X × Y :=
  Prod.map (S.act g) (T.act g)

@[simp]
theorem prodAct_one (S : System G X) (T : System G Y) : S.prodAct T 1 = id := by
  ext <;> simp [prodAct, S.act_one, T.act_one]

theorem prodAct_mul (S : System G X) (T : System G Y) (g h : G) :
    S.prodAct T (g * h) = S.prodAct T g ∘ S.prodAct T h := by
  ext <;> simp [prodAct, S.act_mul, T.act_mul]

end System

/-- A factor map intertwines the two actions and pushes forward the probability measure. -/
structure FactorMap (S : System G X) (T : System G Y) where
  toFun : X → Y
  preserves : MeasurePreserving toFun S.measure T.measure
  equivariant : ∀ g, toFun ∘ S.act g = T.act g ∘ toFun

/-- An invariant probability measure with the displayed marginals, as in Section 2.2. -/
structure IsJoining (S : System G X) (T : System G Y) (joining : Measure (X × Y)) : Prop where
  probability : IsProbabilityMeasure joining
  fst : MeasurePreserving Prod.fst joining S.measure
  snd : MeasurePreserving Prod.snd joining T.measure
  invariant : ∀ g, MeasurePreserving (S.prodAct T g) joining joining

/-- Disjointness of probability-preserving systems. -/
def Disjoint (S : System G X) (T : System G Y) : Prop :=
  ∀ joining, IsJoining S T joining → joining = S.measure.prod T.measure

theorem product_isJoining (S : System G X) (T : System G Y) :
    IsJoining S T (S.measure.prod T.measure) where
  probability := inferInstance
  fst := measurePreserving_fst
  snd := measurePreserving_snd
  invariant g := (S.preserves g).prod (T.preserves g)

/-- The independent product system. -/
noncomputable def System.prod (S : System G X) (T : System G Y) : System G (X × Y) where
  measure := S.measure.prod T.measure
  probability := inferInstance
  act := S.prodAct T
  act_one := S.prodAct_one T
  act_mul := S.prodAct_mul T
  preserves := (product_isJoining S T).invariant

/-- Composition of factor maps. -/
def FactorMap.comp {R : System G X} {S : System G Y} {T : System G Z}
    (f : FactorMap S T) (k : FactorMap R S) : FactorMap R T where
  toFun := f.toFun ∘ k.toFun
  preserves := f.preserves.comp k.preserves
  equivariant g := by
    rw [Function.comp_assoc, k.equivariant g, ← Function.comp_assoc, f.equivariant g,
      Function.comp_assoc]

/-- Independent products of factor maps between product systems. -/
noncomputable def FactorMap.prod {S : System G X} {T : System G Y} {S' : System G Z} {T' : System G W}
    (f : FactorMap S S') (k : FactorMap T T') : FactorMap (S.prod T) (S'.prod T') where
  toFun := Prod.map f.toFun k.toFun
  preserves := f.preserves.prod k.preserves
  equivariant g := by
    funext x
    exact Prod.ext (congrFun (f.equivariant g) x.1) (congrFun (k.equivariant g) x.2)

namespace IsJoining

variable {S : System G X} {T : System G Y} {joining : Measure (X × Y)}

/-- A joining defines a system on the product space. -/
def system (h : IsJoining S T joining) : System G (X × Y) where
  measure := joining
  probability := h.probability
  act := S.prodAct T
  act_one := S.prodAct_one T
  act_mul := S.prodAct_mul T
  preserves := h.invariant

/-- The first coordinate of a joining is a factor. -/
def fstFactor (h : IsJoining S T joining) : FactorMap h.system S where
  toFun := Prod.fst
  preserves := h.fst
  equivariant _ := rfl

/-- The second coordinate of a joining is a factor. -/
def sndFactor (h : IsJoining S T joining) : FactorMap h.system T where
  toFun := Prod.snd
  preserves := h.snd
  equivariant _ := rfl

/-- Pushing a joining forward by factor maps gives a joining of the factors. -/
theorem map (h : IsJoining S T joining) {S' : System G Z} {T' : System G W}
    (f : FactorMap S S') (k : FactorMap T T') :
    IsJoining S' T' (joining.map (Prod.map f.toFun k.toFun)) := by
  let π := Prod.map f.toFun k.toFun
  have hπ : Measurable π := f.preserves.measurable.prodMap k.preserves.measurable
  refine ⟨(Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 h.probability, ⟨measurable_fst, ?_⟩,
    ⟨measurable_snd, ?_⟩, fun g ↦ ⟨(S'.preserves g).measurable.prodMap
      (T'.preserves g).measurable, ?_⟩⟩
  · rw [Measure.map_map measurable_fst hπ]
    exact ((f.preserves).comp h.fst).map_eq
  · rw [Measure.map_map measurable_snd hπ]
    exact ((k.preserves).comp h.snd).map_eq
  · have haction : Measurable (S'.prodAct T' g) :=
      (S'.preserves g).measurable.prodMap (T'.preserves g).measurable
    have hcommute : S'.prodAct T' g ∘ π = π ∘ S.prodAct T g := by
      funext x
      exact Prod.ext (congrFun (f.equivariant g).symm x.1)
        (congrFun (k.equivariant g).symm x.2)
    rw [Measure.map_map haction hπ, hcommute, ← Measure.map_map hπ (h.invariant g).measurable,
      (h.invariant g).map_eq]

end IsJoining

/-- The graph measure of a factor map joins the extension with the factor. -/
theorem FactorMap.graph_isJoining {S : System G X} {T : System G Y} (f : FactorMap S T) :
    IsJoining S T (S.measure.map fun x ↦ (x, f.toFun x)) := by
  let π : X → X × Y := fun x ↦ (x, f.toFun x)
  have hπ : Measurable π := measurable_id.prodMk f.preserves.measurable
  refine ⟨(Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 S.probability, ⟨measurable_fst, ?_⟩,
    ⟨measurable_snd, ?_⟩, fun g ↦ ⟨(S.preserves g).measurable.prodMap
      (T.preserves g).measurable, ?_⟩⟩
  · rw [Measure.map_map measurable_fst hπ]
    exact Measure.map_id
  · rw [Measure.map_map measurable_snd hπ]
    exact f.preserves.map_eq
  · have haction : Measurable (S.prodAct T g) :=
      (S.preserves g).measurable.prodMap (T.preserves g).measurable
    have hcommute : S.prodAct T g ∘ π = π ∘ S.act g := by
      funext x
      exact Prod.ext rfl (congrFun (f.equivariant g).symm x)
    rw [Measure.map_map haction hπ, hcommute, ← Measure.map_map hπ (S.preserves g).measurable,
      (S.preserves g).map_eq]

end Mixing
