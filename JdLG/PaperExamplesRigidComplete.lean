/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.PaperExamplesRigidityExistence
public import JdLG.PaperExamplesRigidityAWS

/-!
# The completed rigid counterexamples of Section 4

Example 4.6 uses one rigid weakly mixing unitary representation.
Example 4.7 takes the Hilbert direct sum over all lacunary sequences.
-/

@[expose] public section

namespace JdLG.PaperExamplesRigid

open Filter
open scoped Topology ENNReal

/-- Example 4.6. The unitary integer action is strongly rigid and all its
vectors are almost weakly stable. Its nonzero vector cannot decay weakly
on a set of lower Banach density one. -/
theorem example46 :
    ∃ (U : Multiplicative ℤ →* (RigidityHilbert ≃ₗᵢ[ℂ] RigidityHilbert))
      (u : ℕ → ℤ) (ξ : RigidityHilbert), ξ ≠ 0 ∧
      (∀ x, IsAlmostWeaklyStable (closureAction (unitaryIntegerAction U)) x) ∧
      Tendsto u atTop cofinite ∧
      (∀ x, Tendsto (fun n ↦ U (Multiplicative.ofAdd (u n)) x) atTop (𝓝 x)) ∧
      ∀ A : Set ℤ, (∀ F : ℕ → Finset ℤ, IntegerFolner F →
        Tendsto (fun n ↦ sampleDensity A (F n)) atTop (𝓝 1)) →
          ¬ WeakDecayOn (fun s ↦ U (Multiplicative.ofAdd s) ξ) A := by
  obtain ⟨v, -, hv, hpos, hratio⟩ :=
    exists_lacunary_subsequence (Set.univ : Set ℕ) Set.infinite_univ
  obtain ⟨U, hU, hEig⟩ := exists_rigid_unitary_component ⟨v, hv, hpos, hratio⟩
  let u (n : ℕ) : ℤ := v n
  have hi : Function.Injective u :=
    (show Function.Injective (Nat.cast : ℕ → ℤ) from
      fun _ _ h ↦ Int.ofNat_inj.mp h).comp hv.injective
  have hu : Tendsto u atTop cofinite := by
    simpa only [Nat.cofinite_eq_atTop] using hi.tendsto_cofinite
  have hm (a b : ℤ) : U (Multiplicative.ofAdd (a + b)) =
      (U (Multiplicative.ofAdd b)).trans (U (Multiplicative.ofAdd a)) := by
    change U (Multiplicative.ofAdd a * Multiplicative.ofAdd b) =
      U (Multiplicative.ofAdd a) * U (Multiplicative.ofAdd b)
    rw [map_mul]
  refine ⟨U, u, rigidityOne, rigidityOne_ne_zero, all_aws_of_no_unitary_eigenvectors U hEig,
    hu, hU, fun A hA ↦ ?_⟩
  exact not_weakDecayOn_of_rigid_lowerBanachDensityOne (fun s ↦ U (Multiplicative.ofAdd s)) hm
    rigidityOne rigidityOne_ne_zero u hu (hU rigidityOne) A hA

/-- The chosen strongly rigid unitary component for each lacunary sequence. -/
noncomputable def rigidComponent (r : LacunarySequence) :
    Multiplicative ℤ →* (RigidityHilbert ≃ₗᵢ[ℂ] RigidityHilbert) :=
  (exists_rigid_unitary_component r).choose

theorem rigidComponent_strong (r : LacunarySequence) (x : RigidityHilbert) :
    Tendsto (fun n ↦ rigidComponent r (Multiplicative.ofAdd (r.value n : ℤ)) x) atTop (𝓝 x) :=
  (exists_rigid_unitary_component r).choose_spec.1 x

theorem rigidComponent_no_eigenvector (r : LacunarySequence) (c : ℂ) (x : RigidityHilbert)
    (h : rigidComponent r (Multiplicative.ofAdd 1) x = c • x) : x = 0 :=
  (exists_rigid_unitary_component r).choose_spec.2 c x h

/-- The Hilbert direct sum indexed by all lacunary sequences in Example 4.7. -/
noncomputable abbrev RigiditySum := lp (fun _ : LacunarySequence ↦ RigidityHilbert) 2

/-- The unitary direct sum in Example 4.7. -/
noncomputable def rigidSumRepresentation :
    Multiplicative ℤ →* (RigiditySum ≃ₗᵢ[ℂ] RigiditySum) :=
  hilbertSumRepresentation rigidComponent

theorem rigidSumRepresentation_all_aws (x : RigiditySum) :
    IsAlmostWeaklyStable (closureAction (unitaryIntegerAction rigidSumRepresentation)) x := by
  apply all_aws_of_no_unitary_eigenvectors
  exact hilbertSum_no_nonzero_eigenvector
    (fun r s ↦ rigidComponent r (Multiplicative.ofAdd s)) rigidComponent_no_eigenvector

/-- Example 4.7. Every infinite set fails to give simultaneous weak decay for
the almost weakly stable vectors in the literal direct sum. -/
theorem example47 (A : Set ℕ) (hA : A.Infinite) :
    ∃ x : RigiditySum,
      IsAlmostWeaklyStable (closureAction (unitaryIntegerAction rigidSumRepresentation)) x ∧
        ¬ WeakDecayOn (fun s ↦ rigidSumRepresentation (Multiplicative.ofAdd s) x) ((↑) '' A) := by
  obtain ⟨x, hx⟩ := no_common_weakDecayOn_of_rigidComponents
    (fun r s ↦ rigidComponent r (Multiplicative.ofAdd s))
    (fun r ↦ ⟨rigidityOne, rigidityOne_ne_zero, rigidComponent_strong r rigidityOne⟩) A hA
  exact ⟨x, rigidSumRepresentation_all_aws x, hx⟩

private def bitLacunaryValues (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 1 + (b 0).toNat
  | n + 1 => (n + 2) * bitLacunaryValues b n + 1 + (b (n + 1)).toNat

private theorem bitLacunaryValues_positive (b : ℕ → Bool) (n : ℕ) :
    0 < bitLacunaryValues b n := by
  cases n <;> simp only [bitLacunaryValues] <;> omega

private def bitLacunarySequence (b : ℕ → Bool) : LacunarySequence where
  value := bitLacunaryValues b
  positive := bitLacunaryValues_positive b
  strictlyIncreasing := strictMono_nat_of_lt_succ fun n ↦ by
    have hmul : bitLacunaryValues b n ≤ (n + 2) * bitLacunaryValues b n :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [bitLacunaryValues]
    omega
  ratiosDiverge := by
    apply tendsto_atTop.2
    intro C
    obtain ⟨N, hN⟩ := exists_nat_ge C
    refine (eventually_ge_atTop N).mono fun n hn ↦ ?_
    change C ≤ (Nat.cast (bitLacunaryValues b (n + 1)) : ℝ) / Nat.cast (bitLacunaryValues b n)
    have hpos : (0 : ℝ) < Nat.cast (bitLacunaryValues b n) :=
      Nat.cast_pos.2 (bitLacunaryValues_positive b n)
    have hcast : (Nat.cast ((n + 2) * bitLacunaryValues b n) : ℝ) ≤
        Nat.cast (bitLacunaryValues b (n + 1)) :=
      Nat.cast_le.2 (by simp only [bitLacunaryValues]; omega)
    have hlower : (n : ℝ) + 2 ≤
        (Nat.cast (bitLacunaryValues b (n + 1)) : ℝ) / Nat.cast (bitLacunaryValues b n) :=
      (le_div_iff₀ hpos).2 (by
        simpa only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add] using hcast)
    exact hN.trans (((Nat.cast_le.2 hn : (N : ℝ) ≤ (n : ℝ)).trans (by linarith)).trans hlower)

private theorem bitLacunarySequence_injective : Function.Injective bitLacunarySequence := by
  intro a b h
  have hv (n : ℕ) : bitLacunaryValues a n = bitLacunaryValues b n :=
    congrFun (congrArg LacunarySequence.value h) n
  funext n
  have hb : (a n).toNat = (b n).toNat := by
    cases n with
    | zero =>
      have h₀ := hv 0
      simp only [bitLacunaryValues] at h₀
      omega
    | succ n =>
      have h₁ := hv (n + 1)
      simp only [bitLacunaryValues, hv n] at h₁
      omega
  cases ha : a n <;> cases hb' : b n <;> simp [ha, hb'] at hb ⊢

theorem lacunarySequences_not_countable : ¬ Countable LacunarySequence := by
  intro hc
  let : Countable LacunarySequence := hc
  let : Countable (ℕ → Bool) := bitLacunarySequence_injective.countable
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hf (fun n ↦ !(f n n))
  exact (Bool.not_eq_self (f n n)).1 (congrFun hn n).symm

/-- The literal direct sum in Example 4.7 is nonseparable in norm. -/
theorem rigiditySum_not_separable : ¬ TopologicalSpace.SeparableSpace RigiditySum := by
  classical
  intro hs
  let : TopologicalSpace.SeparableSpace RigiditySum := hs
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense RigiditySum
  let e (r : LacunarySequence) : RigiditySum := lp.single 2 r rigidityOne
  let ε := ‖rigidityOne‖ / 3
  have hε : 0 < ε := by dsimp [ε]; exact div_pos (norm_pos_iff.2 rigidityOne_ne_zero) (by norm_num)
  choose d hd hx using fun r : LacunarySequence ↦ hDdense.exists_dist_lt (e r) hε
  have hinj : Function.Injective (fun r ↦ (⟨d r, hd r⟩ : D)) := by
    intro r s h
    by_contra hne
    have heq : d r = d s := congrArg Subtype.val h
    have hlt : dist (e r) (e s) < 2 * ε := by
      have htriangle := dist_triangle (e r) (d r) (e s)
      have hr := hx r
      rw [heq] at hr
      rw [dist_comm (d r) (e s), heq] at htriangle
      linarith [hr, hx s]
    have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (e r - e s) r
    simp only [lp.coeFn_sub, Pi.sub_apply, e, lp.single_apply_self,
      lp.single_apply_ne _ _ _ hne, sub_zero, ← dist_eq_norm] at hcoord
    change ‖rigidityOne‖ ≤ dist (e r) (e s) at hcoord
    dsimp [ε] at hlt
    linarith [norm_pos_iff.2 rigidityOne_ne_zero]
  let : Countable D := hDcount
  exact lacunarySequences_not_countable hinj.countable

end JdLG.PaperExamplesRigid
