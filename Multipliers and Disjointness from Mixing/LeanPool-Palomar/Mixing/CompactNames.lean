/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.FactorJoiningLift

@[expose] public section
noncomputable section

namespace Mixing

open Function MeasureTheory MeasurableSpace Set TopologicalSpace

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-- The compact space of Boolean orbit names for a countable group. -/
abbrev CompactNames (G : Type*) := G × ℕ → Bool

/-- Send each point to the orbit names of the measurable generators. -/
def System.compactName [CountablyGenerated X] (S : System G X) (x : X) : CompactNames G :=
  fun i ↦ mapNatBool X (S.act i.1 x) i.2

theorem System.measurable_compactName [CountablyGenerated X] (S : System G X) :
    Measurable S.compactName := by
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i.2).comp ((measurable_mapNatBool (α := X)).comp
    (S.preserves i.1).measurable)

theorem System.injective_compactName [CountablyGenerated X] [SeparatesPoints X]
    (S : System G X) : Injective S.compactName := by
  intro x y he
  apply injective_mapNatBool X
  funext n
  have h := congrFun he (1, n)
  change mapNatBool X (S.act 1 x) n = mapNatBool X (S.act 1 y) n at h
  simpa only [S.act_one, id_eq] using h

/-- The right shift on the group coordinate of an orbit name. -/
def compactNameShift (g : G) (u : CompactNames G) : CompactNames G :=
  fun i ↦ u (i.1 * g, i.2)

theorem continuous_compactNameShift (g : G) : Continuous (compactNameShift g) := by
  apply continuous_pi
  intro i
  exact continuous_apply (i.1 * g, i.2)

theorem System.compactName_equivariant [CountablyGenerated X] (S : System G X) (g : G) :
    S.compactName ∘ S.act g = compactNameShift g ∘ S.compactName := by
  funext x i
  change mapNatBool X (S.act i.1 (S.act g x)) i.2 =
    mapNatBool X (S.act (i.1 * g) x) i.2
  rw [S.act_mul]
  rfl

/-- A compact continuous-action model equipped with the measure carried by the
orbit naming map of a standard probability system. -/
def System.compactNameSystem [CountablyGenerated X] (S : System G X) :
    System G (CompactNames G) where
  measure := S.measure.map S.compactName
  probability := (Measure.isProbabilityMeasure_map_iff S.measurable_compactName.aemeasurable).2
    S.probability
  act := compactNameShift
  act_one := by funext u i; simp [compactNameShift]
  act_mul := by intro g h; funext u i; simp [compactNameShift, mul_assoc]
  preserves g := by
    have hm : Measurable (compactNameShift g) := Measurable.of_eval fun i ↦
      measurable_pi_apply (i.1 * g, i.2)
    refine ⟨hm, ?_⟩
    rw [Measure.map_map hm S.measurable_compactName, ← S.compactName_equivariant g,
      ← Measure.map_map S.measurable_compactName (S.preserves g).measurable, (S.preserves g).map_eq]

def System.compactNameFactor [CountablyGenerated X] (S : System G X) :
    FactorMap S S.compactNameSystem :=
  ⟨S.compactName, ⟨S.measurable_compactName, rfl⟩, S.compactName_equivariant⟩

theorem System.measurableEmbedding_compactName [Countable G] [StandardBorelSpace X]
    (S : System G X) : MeasurableEmbedding S.compactName :=
  S.measurable_compactName.measurableEmbedding S.injective_compactName

end Mixing
