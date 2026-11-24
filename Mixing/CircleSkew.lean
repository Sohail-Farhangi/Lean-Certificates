module

public import Mixing.System
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

namespace Mixing

open MeasureTheory

local notation "𝕋" => UnitAddCircle
local notation "m" => (AddCircle.haarAddCircle : Measure 𝕋)

/-- The rotation skew product over an arbitrary probability measure on the base circle. -/
noncomputable def circleSkew (μ : Measure 𝕋) [IsProbabilityMeasure μ] (c : ℤ) :
    System (Multiplicative ℤ) (𝕋 × 𝕋) where
  measure := μ.prod m
  probability := inferInstance
  act g x := (x.1, x.2 + (g.toAdd * c) • x.1)
  act_one := by
    funext x
    simp
  act_mul g h := by
    funext x
    change (x.1, x.2 + ((g.toAdd + h.toAdd) * c) • x.1) =
      (x.1, x.2 + (h.toAdd * c) • x.1 + (g.toAdd * c) • x.1)
    rw [add_mul, add_zsmul]
    congr 1
    abel
  preserves g := by
    refine (MeasurePreserving.id μ).skew_product
      (g := fun x y ↦ y + (g.toAdd * c) • x) (by fun_prop) ?_
    exact ae_of_all _ fun x ↦ (measurePreserving_add_right m ((g.toAdd * c) • x)).map_eq

/-- Doubling the fibre coordinate intertwines the two actions in Example 7. -/
noncomputable def circleSkew_doubleFactor (μ : Measure 𝕋) [IsProbabilityMeasure μ] :
    FactorMap (circleSkew μ 1) (circleSkew μ 2) where
  toFun := Prod.map id (fun y : 𝕋 ↦ (2 : ℤ) • y)
  preserves := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_zsmul m (by decide : (2 : ℤ) ≠ 0))
  equivariant g := by
    funext x
    change (x.1, (2 : ℤ) • (x.2 + (g.toAdd * 1) • x.1)) =
      (x.1, (2 : ℤ) • x.2 + (g.toAdd * 2) • x.1)
    rw [zsmul_add, smul_smul, mul_one, mul_comm (2 : ℤ)]

/-- The map `(w,x,y,z) ↦ (w,x,y,2z)` in Example 7, using paired coordinates. -/
noncomputable def example7_productFactor (μ : Measure 𝕋) [IsProbabilityMeasure μ] :
    FactorMap ((circleSkew μ 1).prod (circleSkew μ 1))
      ((circleSkew μ 1).prod (circleSkew μ 2)) :=
  FactorMap.prod
    ⟨id, MeasurePreserving.id _, fun _ ↦ rfl⟩
    (circleSkew_doubleFactor μ)

/-- For a nonzero base-four integer, its least significant nonzero digit or that of
its double is two. The decomposition gives the digit and its position. -/
theorem example6_baseFour_digit_two (n : ℕ) (hn : n ≠ 0) :
    (∃ k q : ℕ, n = 4 ^ k * (4 * q + 2)) ∨
      (∃ k q : ℕ, 2 * n = 4 ^ k * (4 * q + 2)) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hmod : n % 4 = 0
    · have hdiv := Nat.mod_add_div n 4
      rw [hmod, zero_add] at hdiv
      have hlt : n / 4 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have hne : n / 4 ≠ 0 := by omega
      rcases ih (n / 4) hlt hne with ⟨k, q, heq⟩ | ⟨k, q, heq⟩
      · left
        exact ⟨k + 1, q, by rw [← hdiv, heq, pow_succ]; ac_rfl⟩
      · right
        refine ⟨k + 1, q, ?_⟩
        calc
          2 * n = 4 * (2 * (n / 4)) := by omega
          _ = 4 ^ (k + 1) * (4 * q + 2) := by rw [heq, pow_succ]; ac_rfl
    · by_cases htwo : n % 4 = 2
      · exact Or.inl ⟨0, n / 4, by simp; omega⟩
      · exact Or.inr ⟨0, n / 2, by simp; omega⟩

end Mixing
