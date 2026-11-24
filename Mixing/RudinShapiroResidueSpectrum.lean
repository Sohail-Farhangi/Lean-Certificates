/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroResidues
public import Mixing.PurePointLebesgue
public import Mixing.EventMixing
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # The pure point spectrum of the dyadic Rudin–Shapiro phases -/

@[expose] public section
noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators InnerProductSpace Topology

namespace Mixing

local instance (k : ℕ) : NeZero (2^k : ℕ) := ⟨by positivity⟩

/-- The finite cyclic phase of a Rudin–Shapiro word. On the subshift exactly
one summand contributes. The finite formula also defines it off the subshift. -/
def rudinShapiroResidueMap (k : ℕ) (w : SignWords) : ZMod (2^k) := by
  classical
  exact ∑ a : Fin (2^k), if rudinShapiroResidue k a w then (a.val : ZMod (2^k)) else 0

theorem measurable_rudinShapiroResidueMap (k : ℕ) : Measurable (rudinShapiroResidueMap k) := by
  classical
  exact Finset.measurable_sum _ fun a _ => Measurable.ite (measurableSet_rudinShapiroResidue k a)
    measurable_const measurable_const

theorem rudinShapiroResidueMap_eq_of_mem {k : ℕ} {w : SignWords} (hw : w ∈ rudinShapiroSubshift)
    (a : Fin (2^k)) (ha : rudinShapiroResidue k a w) : rudinShapiroResidueMap k w = a.val := by
  classical
  obtain ⟨b, hb, hUniq⟩ := rudinShapiroResidue_existsUnique_of_mem hw k
  unfold rudinShapiroResidueMap
  rw [Finset.sum_eq_single a]
  · exact ite_eq_left ha
  · intro t _ ht
    exact ite_eq_right (fun hc => ht ((hUniq _ hc).trans (hUniq _ ha).symm))
  · simp

theorem rudinShapiroResidueMap_eq_iff_of_mem {k : ℕ} {w : SignWords} (hw : w ∈ rudinShapiroSubshift)
    (a : Fin (2^k)) : rudinShapiroResidueMap k w = a.val ↔ rudinShapiroResidue k a w := by
  constructor
  · intro h
    obtain ⟨b, hb, _⟩ := rudinShapiroResidue_existsUnique_of_mem hw k
    rw [rudinShapiroResidueMap_eq_of_mem hw b hb] at h
    have hba : b = a := Fin.ext (by
      have hv := congrArg ZMod.val h
      rwa [ZMod.val_cast_of_lt b.isLt, ZMod.val_cast_of_lt a.isLt] at hv)
    exact hba ▸ hb
  · exact rudinShapiroResidueMap_eq_of_mem hw a

theorem rudinShapiroResidueMap_shift_of_mem {k : ℕ} {w : SignWords} (hw : w ∈ rudinShapiroSubshift)
    (t : ℤ) (ht : signWordShift t w ∈ rudinShapiroSubshift) :
    rudinShapiroResidueMap k (signWordShift t w) = rudinShapiroResidueMap k w + (t : ZMod (2^k)) := by
  obtain ⟨a, ha, _⟩ := rudinShapiroResidue_existsUnique_of_mem hw k
  obtain ⟨b, hb, _⟩ := rudinShapiroResidue_existsUnique_of_mem ht k
  rw [rudinShapiroResidueMap_eq_of_mem ht b hb, rudinShapiroResidueMap_eq_of_mem hw a ha]
  have he := rudinShapiroResidue_shift_of_mem hw k t a b ha hb
  have hpow : (2 : ℤ)^k = ((2^k : ℕ) : ℤ) := by norm_cast
  rw [hpow] at he
  have hc := congrArg (fun n : ℤ => (n : ZMod (2^k))) he
  simpa only [Int.cast_natCast, ZMod.intCast_mod, Int.cast_add] using hc

/-- The cyclic phase map intertwines the shift with addition, almost everywhere. -/
theorem ae_rudinShapiroResidueMap_shift (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (k : ℕ) (t : ℤ) :
    ∀ᵐ w ∂(rudinShapiroOrbitLaw p : Measure SignWords),
      rudinShapiroResidueMap k (signWordShift t w) = rudinShapiroResidueMap k w + (t : ZMod (2^k)) := by
  have hw := ae_mem_rudinShapiroSubshift p hp
  have ht := (rudinShapiroOrbitLaw_preserving p hp t).quasiMeasurePreserving.ae hw
  filter_upwards [hw, ht] with w h₀ h₁
  exact rudinShapiroResidueMap_shift_of_mem h₀ t h₁

variable (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) (k : ℕ)

theorem memLp_residuePullback (f : ZMod (2^k) → ℂ) :
    MemLp (f ∘ rudinShapiroResidueMap k) 2 (rudinShapiroOrbitSystem p hp).measure := by
  have hf : Measurable f := measurable_of_countable f
  apply MemLp.of_bound (hf.comp (measurable_rudinShapiroResidueMap k)).aestronglyMeasurable
    (∑ a : ZMod (2^k), ‖f a‖)
  exact Eventually.of_forall (fun w =>
    Finset.single_le_sum (fun a _ => norm_nonneg (f a)) (Finset.mem_univ (rudinShapiroResidueMap k w)))

/-- L² pullback of functions on a finite dyadic phase. -/
def rudinShapiroResiduePullback : (ZMod (2^k) → ℂ) →ₗ[ℂ] Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure where
  toFun f := (memLp_residuePullback p hp k f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_residuePullback p hp k (f+g)).coeFn_toLp,
      (memLp_residuePullback p hp k f).coeFn_toLp, (memLp_residuePullback p hp k g).coeFn_toLp,
      Lp.coeFn_add ((memLp_residuePullback p hp k f).toLp _) ((memLp_residuePullback p hp k g).toLp _)]
      with w hfg hf hg hs
    rw [hfg, hs, Pi.add_apply, hf, hg]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_residuePullback p hp k (c • f)).coeFn_toLp,
      (memLp_residuePullback p hp k f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_residuePullback p hp k f).toLp _)] with w hcf hf hs
    rw [RingHom.id_apply, hcf, hs, Pi.smul_apply, hf]
    rfl

theorem ae_rudinShapiroResiduePullback (f : ZMod (2^k) → ℂ) :
    rudinShapiroResiduePullback p hp k f =ᵐ[(rudinShapiroOrbitSystem p hp).measure] f ∘ rudinShapiroResidueMap k :=
  (memLp_residuePullback p hp k f).coeFn_toLp

private theorem residue_character_eigen (ψ : AddChar (ZMod (2^k)) ℂ) :
    rudinShapiroResiduePullback p hp k ψ ∈ unitaryEigenvectors (rudinShapiroOrbitSystem p hp).koopmanRep := by
  let ψc := AddChar.circleEquivComplex.symm ψ
  let χ : Multiplicative ℤ →* Circle :=
    { toFun := fun g => ψc (g.toAdd : ZMod (2^k))
      map_one' := by change ψc ((0 : ℤ) : ZMod (2^k)) = 1; rw [Int.cast_zero, AddChar.map_zero_eq_one]
      map_mul' := fun g h => by
        change ψc ((g.toAdd + h.toAdd : ℤ) : ZMod (2^k)) = _
        rw [Int.cast_add, AddChar.map_add_eq_mul] }
  let S := rudinShapiroOrbitSystem p hp
  let f := rudinShapiroResiduePullback p hp k ψ
  have hf := ae_rudinShapiroResiduePullback p hp k ψ
  refine ⟨χ, fun g => ?_⟩
  have hPull := (Lp.coeFn_compMeasurePreserving f (S.preserves g)).trans
    ((S.preserves g).quasiMeasurePreserving.ae_eq_comp hf)
  have hχ : (χ g : ℂ) = ψ (g.toAdd : ZMod (2^k)) := by
    change (AddChar.circleEquivComplex ψc) (g.toAdd : ZMod (2^k)) = _
    rw [show AddChar.circleEquivComplex ψc = ψ from AddChar.circleEquivComplex.apply_symm_apply ψ]
  apply Lp.ext
  change (↑↑(S.koopmanRep g f) : SignWords → ℂ) =ᵐ[S.measure]
    (↑↑((χ g : ℂ) • f) : SignWords → ℂ)
  filter_upwards [hPull, Lp.coeFn_smul (χ g : ℂ) f, hf, ae_rudinShapiroResidueMap_shift p hp k g.toAdd]
    with w hAct hSM hw hPhase
  change S.koopmanRep g f w = ψ (rudinShapiroResidueMap k (signWordShift g.toAdd w)) at hAct
  rw [hAct, hSM, Pi.smul_apply, hw, hPhase, Function.comp_apply, hχ, AddChar.map_add_eq_mul, smul_eq_mul, mul_comm]

/-- Every function of a finite dyadic phase is in the pure point part. -/
theorem rudinShapiroResiduePullback_mem_purePointPart (f : ZMod (2^k) → ℂ) :
    rudinShapiroResiduePullback p hp k f ∈ purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep := by
  let W := purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep
  let L := rudinShapiroResiduePullback p hp k
  have h : (⊤ : Submodule ℂ (ZMod (2^k) → ℂ)) ≤ W.comap L := by
    rw [← (AddChar.complexBasis (ZMod (2^k))).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨ψ, rfl⟩
    rw [AddChar.complexBasis_apply]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (residue_character_eigen p hp k ψ))
  exact h Submodule.mem_top

/-- The complex indicator of a specified dyadic residue cylinder. -/
def rudinShapiroResidueIndicator (a : Fin (2^k)) : Lp ℂ 2 (rudinShapiroOrbitSystem p hp).measure :=
  eventVector (rudinShapiroOrbitSystem p hp) (measurableSet_rudinShapiroResidue k a)

theorem ae_rudinShapiroResidueIndicator (a : Fin (2^k)) :
    rudinShapiroResidueIndicator p hp k a =ᵐ[(rudinShapiroOrbitSystem p hp).measure]
      ({w | rudinShapiroResidue k a w} : Set SignWords).indicator (fun _ => (1:ℂ)) :=
  indicatorConstLp_coeFn (hs := measurableSet_rudinShapiroResidue k a)
    (hμs := measure_ne_top _ _)

/-- Each residue-cylinder indicator is in the Kronecker subspace. -/
theorem rudinShapiroResidueIndicator_mem_purePointPart (a : Fin (2^k)) :
    rudinShapiroResidueIndicator p hp k a ∈ purePointPart (rudinShapiroOrbitSystem p hp).koopmanRep := by
  classical
  let f (s : ZMod (2^k)) : ℂ := if s = a.val then 1 else 0
  have he : rudinShapiroResidueIndicator p hp k a = rudinShapiroResiduePullback p hp k f := by
    apply Lp.ext
    filter_upwards [ae_rudinShapiroResidueIndicator p hp k a, ae_rudinShapiroResiduePullback p hp k f,
      ae_mem_rudinShapiroSubshift p hp] with w hi hf hw
    rw [hi, hf, Function.comp_apply]
    change ({w | rudinShapiroResidue k a w} : Set SignWords).indicator (fun _ => (1:ℂ)) w =
      (if rudinShapiroResidueMap k w = a.val then 1 else 0)
    by_cases h : rudinShapiroResidue k a w
    · rw [indicator_of_mem h, ite_eq_left ((rudinShapiroResidueMap_eq_iff_of_mem hw a).2 h)]
    · rw [indicator_of_notMem h, ite_eq_right (fun he => h ((rudinShapiroResidueMap_eq_iff_of_mem hw a).1 he))]
  rw [he]
  exact rudinShapiroResiduePullback_mem_purePointPart p hp k f

end Mixing
