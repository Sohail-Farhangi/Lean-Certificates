/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.StrongMixing
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Algebra.Semigroup

/-! # Rigid vectors and mild mixing -/

@[expose] public section

open Filter Set
open scoped InnerProductSpace Mixing Topology

namespace Mixing

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (U : G →* (H ≃ₗᵢ[ℂ] H))

/-- The free idempotents `E(G*)`. -/
def freeIdempotentUltrafilters (G : Type*) [Group G] : Set (Ultrafilter G) :=
  {p | p ∈ freeUltrafilters G ∧ p * p = p}

omit [Group G] in
theorem isClosed_freeUltrafilters : IsClosed (freeUltrafilters G) := by
  have h : freeUltrafilters G = ⋂ S : {S : Set G // S ∈ (cofinite : Filter G)}, {p | S.val ∈ p} := by
    ext p
    simp only [freeUltrafilters, Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
    rfl
  rw [h]
  exact isClosed_iInter fun S => ultrafilter_isClosed_basic S.val

theorem mul_mem_freeUltrafilters {p q : Ultrafilter G} (hq : q ∈ freeUltrafilters G) :
    p * q ∈ freeUltrafilters G := by
  intro S hS
  change ∀ᶠ a in ((p * q : Ultrafilter G) : Filter G), a ∈ S
  rw [Ultrafilter.eventually_mul]
  filter_upwards with a
  exact hq (((mul_right_injective a).tendsto_cofinite) hS)

/-- Weak convergence of the orbit of `x` to `x` along the displayed sequence. -/
def IsRigidAlong (g : ℕ → G) (x : H) : Prop :=
  ∀ y : H, Tendsto (fun n => ⟪y, U (g n) x⟫_ℂ) atTop (𝓝 ⟪y, x⟫_ℂ)

/-- A vector is rigid if its orbit returns weakly along a sequence escaping finite sets. -/
def IsRigidVector (x : H) : Prop :=
  ∃ g : ℕ → G, Tendsto g atTop cofinite ∧ IsRigidAlong U g x

/-- Mild mixing means that zero is the only rigid vector. -/
def IsMildlyMixing : Prop := ∀ x : H, IsRigidVector U x → x = 0

/-- Lemma 6. A rigid sequence yields a free idempotent ultrafilter fixing the vector. -/
theorem exists_freeIdempotent_fixed_of_rigidAlong (g : ℕ → G) (hg : Tendsto g atTop cofinite)
    (x : H) (hx : IsRigidAlong U g x) :
    ∃ p ∈ freeIdempotentUltrafilters G, ultrafilterOperator U p x = x := by
  let S : Set (Ultrafilter G) := {p | p ∈ freeUltrafilters G ∧ ultrafilterOperator U p x = x}
  have hNonempty : S.Nonempty := by
    obtain ⟨p, hp⟩ := exists_ultrafilter_le (Filter.map g atTop)
    refine ⟨p, hp.trans hg, ?_⟩
    apply ext_inner_left ℂ
    intro y
    have hlim : Tendsto (fun a : G => ⟪y, U a x⟫_ℂ) (Filter.map g atTop) (𝓝 ⟪y, x⟫_ℂ) :=
      Filter.tendsto_map'_iff.mpr (hx y)
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p y x)
      (hlim.mono_left hp)
  have hClosed : IsClosed S := by
    have hFix : IsClosed (⋂ y : H, {p | ⟪y, ultrafilterOperator U p x⟫_ℂ = ⟪y, x⟫_ℂ}) := by
      apply isClosed_iInter
      intro y
      exact isClosed_eq
        ((ContinuousLinearMapWOT.continuous_dual_apply x (InnerProductSpace.toDual ℂ H y)).comp
          (continuous_ultrafilterOperator_wot U)) continuous_const
    have he : S = freeUltrafilters G ∩ ⋂ y : H,
        {p | ⟪y, ultrafilterOperator U p x⟫_ℂ = ⟪y, x⟫_ℂ} := by
      ext p
      simp only [S, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact and_congr_right fun _ => ⟨fun h y => congrArg (inner ℂ y) h, ext_inner_left ℂ⟩
    rw [he]
    exact isClosed_freeUltrafilters.inter hFix
  have hMul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S := by
    rintro p ⟨_, hp⟩ q ⟨hq₁, hq₂⟩
    refine ⟨mul_mem_freeUltrafilters hq₁, ?_⟩
    rw [ultrafilterOperator_mul]
    change ultrafilterOperator U p (ultrafilterOperator U q x) = x
    rw [hq₂, hp]
  obtain ⟨p, ⟨hp, hfix⟩, hidem⟩ := exists_idempotent_in_compact_subsemigroup
    Ultrafilter.continuous_mul_left S hNonempty hClosed.isCompact hMul
  exact ⟨p, ⟨hp, hidem⟩, hfix⟩

/-- Lemma 7. A free idempotent acts as a self-adjoint idempotent. -/
theorem ultrafilterOperator_isOrthogonalProjection (p : Ultrafilter G)
    (hp : p ∈ freeIdempotentUltrafilters G) :
    ultrafilterOperator U p * ultrafilterOperator U p = ultrafilterOperator U p ∧
      IsSelfAdjoint (ultrafilterOperator U p) := by
  have hIdem : ultrafilterOperator U p * ultrafilterOperator U p = ultrafilterOperator U p := by
    rw [← ultrafilterOperator_mul, hp.2]
  exact ⟨hIdem, isSelfAdjoint_of_idempotent_contraction _ hIdem
    (ultrafilterOperator_norm_le_one U p)⟩

/-- If the weak ultrafilter limit of a vector equals the vector itself, then
the unitary orbit also converges to that vector in norm along the ultrafilter. -/
theorem tendsto_orbit_of_ultrafilter_fixed (p : Ultrafilter G) (x : H)
    (hx : ultrafilterOperator U p x = x) :
    Tendsto (fun g => U g x) (p : Filter G) (𝓝 x) := by
  have hCoeff := tendsto_ultrafilterOperator_coeff U p x x
  rw [hx] at hCoeff
  have hRe := (Complex.continuous_re.tendsto _).comp hCoeff
  have hSq : Tendsto (fun g => ‖U g x - x‖ ^ 2) (p : Filter G) (𝓝 (0 : ℝ)) := by
    have hRe' : Tendsto (fun g => (⟪x, U g x⟫_ℂ).re) (p : Filter G) (𝓝 (‖x‖ ^ 2)) := by
      have heq : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
      simpa only [Function.comp_def, heq] using hRe
    have hlim := (tendsto_const_nhds (x := ‖x‖ ^ 2 + ‖x‖ ^ 2)).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hRe')
    have hEq (g : G) : ‖U g x - x‖ ^ 2 = ‖x‖ ^ 2 + ‖x‖ ^ 2 - 2 * (⟪x, U g x⟫_ℂ).re := by
      rw [norm_sub_sq (𝕜 := ℂ), (U g).norm_map, ← inner_conj_symm (U g x) x]
      change ‖x‖ ^ 2 - 2 * (star (⟪x, U g x⟫_ℂ)).re + ‖x‖ ^ 2 = _
      rw [Complex.star_def, Complex.conj_re]
      ring
    have hz : ‖x‖ ^ 2 + ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 = 0 := by ring
    simpa only [hEq, hz] using hlim
  rw [Metric.tendsto_nhds] at hSq ⊢
  intro ε hε
  filter_upwards [hSq (ε ^ 2) (sq_pos_of_pos hε)] with g hg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)] at hg
  rw [dist_eq_norm]
  by_contra! h
  exact hg.not_ge (pow_le_pow_left₀ hε.le h 2)

/-- A vector fixed by a free ultrafilter is rigid along an escaping sequence. -/
theorem isRigidVector_of_ultrafilter_fixed [Countable G] (p : Ultrafilter G)
    (hp : p ∈ freeUltrafilters G) (x : H) (hx : ultrafilterOperator U p x = x) :
    IsRigidVector U x := by
  obtain ⟨e, he⟩ := exists_injective_nat G
  let _ : (cofinite : Filter G).IsCountablyGenerated := by
    rw [← he.comap_cofinite_eq, Nat.cofinite_eq_atTop]
    infer_instance
  let f := fun g : G => U g x
  let l : Filter G := cofinite ⊓ comap f (𝓝 x)
  have hpl : (p : Filter G) ≤ l :=
    le_inf hp (tendsto_orbit_of_ultrafilter_fixed U p x hx).le_comap
  let _ : NeBot l := neBot_of_le hpl
  obtain ⟨g, hg⟩ := Filter.exists_seq_tendsto l
  refine ⟨g, hg.mono_right inf_le_left, ?_⟩
  intro y
  have hnorm : Tendsto (f ∘ g) atTop (𝓝 x) := tendsto_comap.comp (hg.mono_right inf_le_right)
  exact ((InnerProductSpace.toDual ℂ H y).continuous.tendsto x).comp hnorm

/-- Proposition 5. Mild mixing is precisely mixing along all free idempotent
ultrafilters. -/
theorem isMildlyMixing_iff_isUMixing_freeIdempotents [Countable G] :
    IsMildlyMixing U ↔ IsUMixing U (freeIdempotentUltrafilters G) := by
  constructor
  · intro h p hp
    apply ContinuousLinearMap.ext
    intro x
    apply h
    have hIdem := (ultrafilterOperator_isOrthogonalProjection U p hp).1
    exact isRigidVector_of_ultrafilter_fixed U p hp.1 _
      (congrArg (fun T : H →L[ℂ] H => T x) hIdem)
  · rintro h x ⟨g, hg, hx⟩
    obtain ⟨p, hp, hfix⟩ := exists_freeIdempotent_fixed_of_rigidAlong U g hg x hx
    rw [h p hp, zero_apply] at hfix
    exact hfix.symm

end Mixing
