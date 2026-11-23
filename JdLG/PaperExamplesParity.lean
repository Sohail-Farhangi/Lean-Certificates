/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The parity example from Section 4

The example uses the literal semigroup from Example 4.4, with height `n ≥ 1`
stored as `n - 1`. The right translates of the even-principal-ideal indicator
are the two constant bounded functions.
-/

@[expose] public section

namespace JdLG.PaperExamplesParity

/-- The point denoting `(first, heightIndex + 1)` in the manuscript. -/
structure Point where
  first : ℕ
  heightIndex : ℕ
  deriving DecidableEq

@[ext] theorem Point.ext {a b : Point} (hfirst : a.first = b.first)
    (hheight : a.heightIndex = b.heightIndex) : a = b := by
  cases a
  cases b
  simp_all

instance : Semigroup Point where
  mul a b := ⟨2 ^ (b.heightIndex + 1) * a.first + b.first,
    a.heightIndex + b.heightIndex + 1⟩
  mul_assoc a b c := by
    apply Point.ext
    · change 2 ^ (c.heightIndex + 1) * (2 ^ (b.heightIndex + 1) * a.first + b.first) +
          c.first = 2 ^ (b.heightIndex + c.heightIndex + 1 + 1) * a.first +
          (2 ^ (c.heightIndex + 1) * b.first + c.first)
      have hpow : (2 : ℕ) ^ (b.heightIndex + c.heightIndex + 1 + 1) =
          2 ^ (c.heightIndex + 1) * 2 ^ (b.heightIndex + 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow, mul_add]
      ac_rfl
    · change a.heightIndex + b.heightIndex + 1 + c.heightIndex + 1 =
        a.heightIndex + (b.heightIndex + c.heightIndex + 1) + 1
      omega

theorem left_multiplication_injective (s : Point) : Function.Injective (s * ·) := by
  intro a b h
  have hh := congrArg Point.heightIndex h
  change s.heightIndex + a.heightIndex + 1 = s.heightIndex + b.heightIndex + 1 at hh
  have hab : a.heightIndex = b.heightIndex := by omega
  have hf := congrArg Point.first h
  change 2 ^ (a.heightIndex + 1) * s.first + a.first =
      2 ^ (b.heightIndex + 1) * s.first + b.first at hf
  rw [hab] at hf
  exact Point.ext (Nat.add_left_cancel hf) hab

theorem right_multiplication_injective (s : Point) : Function.Injective (· * s) := by
  intro a b h
  have hh := congrArg Point.heightIndex h
  change a.heightIndex + s.heightIndex + 1 = b.heightIndex + s.heightIndex + 1 at hh
  have hab : a.heightIndex = b.heightIndex := by omega
  have hf := congrArg Point.first h
  change 2 ^ (s.heightIndex + 1) * a.first + s.first =
      2 ^ (s.heightIndex + 1) * b.first + s.first at hf
  exact Point.ext
    (Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) (Nat.add_right_cancel hf)) hab

/-- The two generators of the disjoint principal left ideals. -/
def evenPoint : Point := ⟨0, 0⟩

/-- This point has first coordinate one and height one. -/
def oddPoint : Point := ⟨1, 0⟩

theorem first_mod_two_mul (s t : Point) : (s * t).first % 2 = t.first % 2 := by
  change (2 ^ (t.heightIndex + 1) * s.first + t.first) % 2 = t.first % 2
  simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.add_mod]

theorem even_ideal_shape (s : Point) :
    s ∈ Set.range (· * evenPoint) ↔ s.first % 2 = 0 ∧ 0 < s.heightIndex := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨first_mod_two_mul r evenPoint, Nat.succ_pos _⟩
  · rintro ⟨hm, hn⟩
    refine ⟨⟨s.first / 2, s.heightIndex - 1⟩, Point.ext ?_ ?_⟩
    · change 2 * (s.first / 2) + 0 = s.first
      omega
    · change s.heightIndex - 1 + 0 + 1 = s.heightIndex
      omega

theorem odd_ideal_shape (s : Point) :
    s ∈ Set.range (· * oddPoint) ↔ s.first % 2 = 1 ∧ 0 < s.heightIndex := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨first_mod_two_mul r oddPoint, Nat.succ_pos _⟩
  · rintro ⟨hm, hn⟩
    refine ⟨⟨s.first / 2, s.heightIndex - 1⟩, Point.ext ?_ ?_⟩
    · change 2 * (s.first / 2) + 1 = s.first
      omega
    · change s.heightIndex - 1 + 0 + 1 = s.heightIndex
      omega

theorem principal_left_ideals_disjoint :
    Disjoint (Set.range (· * evenPoint)) (Set.range (· * oddPoint)) := by
  refine Set.disjoint_left.2 fun s he ho ↦ ?_
  exact Nat.zero_ne_one (((even_ideal_shape s).1 he).1.symm.trans ((odd_ideal_shape s).1 ho).1)

open scoped ENNReal

local notation "W" => lp (fun _ : Point ↦ ℂ) ∞

/-- The indicator of the first principal left ideal, in the bounded-function space. -/
noncomputable def indicator : W :=
  ⟨fun s ↦ if s.first % 2 = 0 ∧ 0 < s.heightIndex then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨s, rfl⟩
    change ‖(if s.first % 2 = 0 ∧ 0 < s.heightIndex then 1 else 0 : ℂ)‖ ≤ 1
    split_ifs <;> simp⟩⟩

open Classical in
theorem indicator_apply (s : Point) :
    indicator s = if s ∈ Set.range (· * evenPoint) then 1 else 0 := by
  classical
  change (if s.first % 2 = 0 ∧ 0 < s.heightIndex then 1 else 0) = _
  simp only [even_ideal_shape]

/-- Right translation as a linear map before packaging the norm bound. -/
noncomputable def rightTranslateLinear (s : Point) : W →ₗ[ℂ] W where
  toFun f := ⟨fun t ↦ f (t * s), memℓp_infty ⟨‖f‖, by
    rintro _ ⟨t, rfl⟩
    exact lp.norm_apply_le_norm (by simp) f (t * s)⟩⟩
  map_add' f g := lp.ext (funext fun t ↦ rfl)
  map_smul' c f := lp.ext (funext fun t ↦ rfl)

/-- Right translations act as contractions on the bounded-function space. -/
noncomputable def rightTranslation : Point →ₙ* (W →L[ℂ] W) where
  toFun s := (rightTranslateLinear s).mkContinuous 1 fun f ↦ by
    simp only [one_mul]
    apply lp.norm_le_of_forall_le (norm_nonneg f)
    intro t
    exact lp.norm_apply_le_norm (by simp) f (t * s)
  map_mul' s t := by
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext u
    change f (u * (s * t)) = f ((u * s) * t)
    rw [mul_assoc]

theorem rightTranslation_indicator (s : Point) :
    rightTranslation s indicator = if s.first % 2 = 0 then 1 else 0 := by
  apply lp.ext
  funext t
  change indicator (t * s) = ((if s.first % 2 = 0 then 1 else 0 : W) t)
  classical
  rw [indicator_apply, even_ideal_shape, first_mod_two_mul]
  have h : 0 < (t * s).heightIndex := by
    change 0 < t.heightIndex + s.heightIndex + 1
    omega
  simp only [h, and_true]
  split_ifs <;> rfl

theorem rightTranslation_indicator_evenPoint : rightTranslation evenPoint indicator = 1 := by
  rw [rightTranslation_indicator]
  rfl

theorem rightTranslation_indicator_oddPoint : rightTranslation oddPoint indicator = 0 := by
  rw [rightTranslation_indicator]
  rfl

theorem indicator_orbit : Set.range (fun s ↦ rightTranslation s indicator) = ({0, 1} : Set W) := by
  ext f
  constructor
  · rintro ⟨s, rfl⟩
    change rightTranslation s indicator ∈ ({0, 1} : Set W)
    rw [rightTranslation_indicator]
    split_ifs <;> simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨oddPoint, rightTranslation_indicator_oddPoint⟩
    · exact ⟨evenPoint, rightTranslation_indicator_evenPoint⟩

theorem indicator_weakly_almost_periodic :
    IsCompact (closure (Set.range (fun s ↦
      toWeakSpace ℂ W (rightTranslation s indicator)))) := by
  have hrange : Set.range (fun s ↦ toWeakSpace ℂ W (rightTranslation s indicator)) =
      (toWeakSpace ℂ W) '' Set.range (fun s ↦ rightTranslation s indicator) :=
    Set.range_comp (toWeakSpace ℂ W) (fun s ↦ rightTranslation s indicator)
  rw [hrange, indicator_orbit]
  have hf : ((toWeakSpace ℂ W) '' ({0, 1} : Set W)).Finite :=
    ((Set.finite_singleton (1 : W)).insert 0).image _
  rw [hf.isClosed.closure_eq]
  exact hf.isCompact

theorem indicator_almost_weakly_stable : IsAlmostWeaklyStable (closureAction rightTranslation)
    indicator :=
  ⟨closureInclusion rightTranslation oddPoint, rightTranslation_indicator_oddPoint⟩

/-- A normalized right-invariant mean cannot exist even on the orbit and
constants occurring in this example. -/
theorem no_right_invariant_mean_on_indicator (m : W → ℂ) (hzero : m 0 = 0)
    (hone : m 1 = 1) (hinv : ∀ s, m (rightTranslation s indicator) = m indicator) : False := by
  have he := hinv evenPoint
  have ho := hinv oddPoint
  rw [rightTranslation_indicator_evenPoint, hone] at he
  rw [rightTranslation_indicator_oddPoint, hzero] at ho
  exact zero_ne_one (ho.trans he.symm)

/-- The normalized counting integral in (15) is one on every nonempty finite
set contained in the even principal left ideal. -/
theorem normalized_coefficient_average_on_even_ideal (F : Finset Point) (hF : F.Nonempty)
    (hsupport : (F : Set Point) ⊆ Set.range (· * evenPoint)) (s₀ : Point) :
    (∑ s ∈ F, ‖rightTranslation s indicator s₀‖) / (F.card : ℝ) = 1 := by
  have hconst : ∀ s ∈ F, ‖rightTranslation s indicator s₀‖ = 1 := by
    intro s hs
    have he := ((even_ideal_shape s).1 (hsupport hs)).1
    rw [rightTranslation_indicator, ite_eq_left he]
    change ‖(1 : ℂ)‖ = 1
    exact norm_one
  rw [Finset.sum_congr rfl hconst]
  simp [ne_of_gt hF.card_pos]

end JdLG.PaperExamplesParity
