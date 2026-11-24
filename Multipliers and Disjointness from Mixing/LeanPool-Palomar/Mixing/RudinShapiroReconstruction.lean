/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.RudinShapiroResidueLaw

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory Set
open scoped BigOperators Classical ENNReal Topology

private theorem rudinShapiro_reconstruct_sample (k a j : ℕ) (i : ℤ)
    (ha : a < 2 ^ (k + 1)) (hj : j % 2 ^ (k + 1) = a)
    (hlo : 0 ≤ (a : ℤ) + i) (hhi : (a : ℤ) + i < (2 : ℤ) ^ (k + 1))
    (hhalf : a / 2 ^ k = ((a : ℤ) + i).toNat / 2 ^ k) :
    signValue (signWordShift j rudinShapiroWord 0) *
      signValue (signWordShift j rudinShapiroWord i) =
      rudinShapiro a * rudinShapiro ((a : ℤ) + i).toNat := by
  let B := (2 : ℕ) ^ (k + 1)
  let q := j / B
  let b := ((a : ℤ) + i).toNat
  have hb : b < B := by
    have h : (b : ℤ) < (B : ℤ) := by
      simpa only [b, Int.toNat_of_nonneg hlo, B, Nat.cast_pow, Nat.cast_ofNat] using hhi
    exact_mod_cast h
  have hj' : j = B * q + a := by
    have hjB : j % B = a := hj
    calc
      j = j % B + B * q := (Nat.mod_add_div j B).symm
      _ = B * q + a := by rw [hjB, add_comm]
  have hcast : (B * q + b : ℕ) = (i + j).toNat := by
    have hb' : (b : ℤ) = (a : ℤ) + i := Int.toNat_of_nonneg hlo
    have hj'' : (j : ℤ) = (B : ℤ) * (q : ℤ) + a := by exact_mod_cast hj'
    have hc : (i + j : ℤ) = (B * q + b : ℕ) := by
      rw [Nat.cast_add, Nat.cast_mul, hb', hj'']
      ring
    exact (congrArg Int.toNat hc).symm
  change signValue (rudinShapiroWord (0 + j)) * signValue (rudinShapiroWord (i + j)) = _
  rw [zero_add, signValue_rudinShapiroWord, signValue_rudinShapiroWord, Int.toNat_natCast, ← hcast, hj']
  change rudinShapiro (2 ^ (k + 1) * q + a) * rudinShapiro (2 ^ (k + 1) * q + b) =
    rudinShapiro a * rudinShapiro b
  rw [rudinShapiro_binary_block k q a ha, rudinShapiro_binary_block k q b hb, ← hhalf]
  let e := q % 2 * (a / 2 ^ k)
  have he : ((-1 : ℝ) ^ e) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  calc
    _ = rudinShapiro q ^ 2 * ((-1 : ℝ) ^ e) ^ 2 * (rudinShapiro a * rudinShapiro b) := by
      dsimp [e]
      ring
    _ = _ := by rw [rudinShapiro_sq, he, one_mul, one_mul]

/-- On a dyadic residue whose centre and tested coordinate lie in the same
half of the block, the two signs have a fixed product. -/
theorem rudinShapiro_signProduct_of_residue {w : SignWords} (hw : w ∈ rudinShapiroSubshift)
    (k a : ℕ) (i : ℤ) (ha : a < 2 ^ (k + 1)) (hr : rudinShapiroResidue (k + 1) a w)
    (hlo : 0 ≤ (a : ℤ) + i) (hhi : (a : ℤ) + i < (2 : ℤ) ^ (k + 1))
    (hhalf : a / 2 ^ k = ((a : ℤ) + i).toNat / 2 ^ k) :
    signValue (w 0) * signValue (w i) = rudinShapiro a * rudinShapiro ((a : ℤ) + i).toNat := by
  let J := rudinShapiroResidueWindow (k + 1) a
  refine (rudinShapiro_local_property
    (P := fun v ↦ rudinShapiroResidue (k + 1) a v →
      signValue (v 0) * signValue (v i) = rudinShapiro a * rudinShapiro ((a : ℤ) + i).toNat)
    (insert 0 (insert i J)) ?_ 0 ?_ hw) hr
  · intro u v h huv hv
    have he := rudinShapiroResidue_iff_of_agree (k + 1) a u v
      (fun j hj ↦ h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hj)))
    rw [← h 0 (Finset.mem_insert_self _ _),
      ← h i (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))]
    exact huv (he.mpr hv)
  · intro j _ hrj
    exact rudinShapiro_reconstruct_sample k a j i ha
      ((rudinShapiroResidue_on_sample (k + 1) a j ha).mp hrj) hlo hhi hhalf

/-- A phase is regular if each tested coordinate eventually lies in the same
half of a sufficiently large dyadic block as the centre. -/
def RudinShapiroRegularPhase (w : SignWords) : Prop :=
  ∀ i : ℤ, ∃ k a : ℕ, a < 2 ^ (k + 1) ∧ rudinShapiroResidue (k + 1) a w ∧
    0 ≤ (a : ℤ) + i ∧ (a : ℤ) + i < (2 : ℤ) ^ (k + 1) ∧
    a / 2 ^ k = ((a : ℤ) + i).toNat / 2 ^ k

private theorem goodHalf_of_interior (k a : ℕ) (i : ℤ) (ha : a < 2 ^ (k + 1))
    (hlo : i.natAbs ≤ a % (2 ^ k)) (hhi : a % (2 ^ k) + i.natAbs < 2 ^ k) :
    0 ≤ (a : ℤ) + i ∧ (a : ℤ) + i < (2 : ℤ) ^ (k + 1) ∧
      a / 2 ^ k = ((a : ℤ) + i).toNat / 2 ^ k := by
  let B := (2 : ℕ) ^ k
  let q := a / B
  let r := a % B
  have hp : 0 < B := by dsimp [B]; positivity
  have hr : r < B := Nat.mod_lt _ hp
  have he : a = r + B * q := (Nat.mod_add_div _ _).symm
  have hB : 2 ^ (k + 1) = B * 2 := pow_succ _ _
  have hQ : q < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by simpa only [hB, mul_comm B 2] using ha)
  have hD : -i ≤ (i.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -i))
  have hU : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
  have hl : 0 ≤ (r : ℤ) + i := by change i.natAbs ≤ r at hlo; omega
  have hh : (r : ℤ) + i < B := by change r + i.natAbs < B at hhi; omega
  let s := ((r : ℤ) + i).toNat
  have hs : (s : ℤ) = (r : ℤ) + i := Int.toNat_of_nonneg hl
  have hsb : s < B := by omega
  have hAbs : (a : ℤ) + i = (s + B * q : ℕ) := by
    push_cast
    rw [hs, show (a : ℤ) = r + (B : ℤ) * q by exact_mod_cast he]
    ring
  rw [hAbs, Int.toNat_natCast]
  refine ⟨Int.natCast_nonneg _, ?_, ?_⟩
  · have hCast : (2 : ℤ) ^ (k + 1) = ((2 ^ (k + 1) : ℕ) : ℤ) := by norm_cast
    rw [hCast, hB]
    exact_mod_cast (show s + B * q < B * 2 from by
      have hq : q = 0 ∨ q = 1 := by
        generalize q = d at hQ ⊢
        omega
      rcases hq with heq | heq <;> simp [heq] <;> omega)
  · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hsb, zero_add]

/-- Uniformity of the finite dyadic phase laws makes the regular phase
condition conull. -/
theorem rudinShapiro_ae_regularPhase_of_uniform (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop)
    (hLaw : ∀ k (a : Fin (2 ^ k)), (rudinShapiroOrbitLaw p : Measure SignWords)
      {w | rudinShapiroResidue k a w} = ((2 : ℝ≥0∞) ^ k)⁻¹) :
    ∀ᵐ w ∂(rudinShapiroOrbitLaw p : Measure SignWords), RudinShapiroRegularPhase w := by
  let ν := (rudinShapiroOrbitLaw p : Measure SignWords)
  apply ae_all_iff.2
  intro i
  let m := i.natAbs
  let D := {w : SignWords | w ∈ rudinShapiroSubshift ∧
    ¬ ∃ k a : ℕ, a < 2 ^ (k + 1) ∧ rudinShapiroResidue (k + 1) a w ∧
      0 ≤ (a : ℤ) + i ∧ (a : ℤ) + i < (2 : ℤ) ^ (k + 1) ∧
      a / 2 ^ k = ((a : ℤ) + i).toNat / 2 ^ k}
  have hSmall (k : ℕ) : ν D ≤ (2 * m : ℕ) * ((2 : ℝ≥0∞) ^ k)⁻¹ := by
    let B := (2 : ℕ) ^ k
    let I := (Finset.range B).filter fun r ↦ r < m ∨ B ≤ r + m
    have hCard : I.card ≤ 2 * m := by
      have hIncl : I ⊆ Finset.range m ∪ Finset.Ico (B - m) B := by
        intro r hr
        obtain ⟨hr', hbad⟩ := Finset.mem_filter.mp hr
        apply Finset.mem_union.mpr
        rcases hbad with h | h
        · exact Or.inl (Finset.mem_range.mpr h)
        · exact Or.inr (Finset.mem_Ico.mpr ⟨by omega, Finset.mem_range.mp hr'⟩)
      refine (Finset.card_le_card hIncl).trans ((Finset.card_union_le _ _).trans ?_)
      rw [Finset.card_range, Nat.card_Ico]
      omega
    have hCover : D ⊆ ⋃ r ∈ I, {w | rudinShapiroResidue k r w} := by
      intro w hw
      obtain ⟨hW, hFail⟩ : w ∈ rudinShapiroSubshift ∧ _ := hw
      obtain ⟨r, hr, _⟩ := rudinShapiroResidue_existsUnique_of_mem hW k
      obtain ⟨a, ha, _⟩ := rudinShapiroResidue_existsUnique_of_mem hW (k + 1)
      have hCompat := rudinShapiroResidue_succ_coherence_of_mem hW k a r ha hr
      refine mem_iUnion.mpr ⟨r.val, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨
        Finset.mem_range.mpr r.isLt, ?_⟩, hr⟩⟩
      by_contra! h
      obtain ⟨hlo, hhi, hh⟩ := goodHalf_of_interior k a.val i a.isLt
        (by simpa only [hCompat] using h.1) (by simpa only [hCompat] using h.2)
      exact hFail ⟨k, a.val, a.isLt, ha, hlo, hhi, hh⟩
    refine (measure_mono hCover).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc
      _ = I.card * ((2 : ℝ≥0∞) ^ k)⁻¹ := by
        have he (a : ℕ) (ha : a ∈ I) :
            ν {w | rudinShapiroResidue k a w} = ((2 : ℝ≥0∞) ^ k)⁻¹ :=
          hLaw k ⟨a, Finset.mem_range.mp (Finset.mem_filter.mp ha).1⟩
        rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr
  have hReal (k : ℕ) : ν.real D ≤ (2 * m : ℝ) * ((1 / 2 : ℝ) ^ k) := by
    have hFin : ((2 * m : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ k)⁻¹ ≠ ∞ := by
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr (by positivity))
    have he := ENNReal.toReal_mono hFin (hSmall k)
    simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ← inv_pow, one_div] using he
  have hLim : Tendsto (fun k : ℕ ↦ (2 * m : ℝ) * ((1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul
        (2 * m : ℝ)
  have hNull : ν D = 0 := (measureReal_eq_zero_iff (measure_ne_top ν D)).mp <|
    le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hLim hReal) measureReal_nonneg
  have hAE : ∀ᵐ w ∂ν, w ∉ D := ae_iff.mpr (by simpa using hNull)
  filter_upwards [ae_mem_rudinShapiroSubshift p hp, hAE] with w hw hD
  by_contra h
  exact hD ⟨hw, h⟩

/-- The measured Rudin–Shapiro system has regular phase almost everywhere. -/
theorem rudinShapiro_ae_regularPhase (p : Ultrafilter ℕ) (hp : (p : Filter ℕ) ≤ atTop) :
    ∀ᵐ w ∂(rudinShapiroOrbitLaw p : Measure SignWords), RudinShapiroRegularPhase w :=
  rudinShapiro_ae_regularPhase_of_uniform p hp (measure_rudinShapiro_residue p hp)

/-- At a regular phase, the dyadic residues and one sign determine the
entire two-sided word. -/
theorem rudinShapiro_eq_of_regular_phase_and_sign {u v : SignWords}
    (hu : u ∈ rudinShapiroSubshift) (hv : v ∈ rudinShapiroSubshift)
    (hReg : RudinShapiroRegularPhase u) (hSign : u 0 = v 0)
    (hPhase : ∀ k a, a < 2 ^ k → (rudinShapiroResidue k a u ↔ rudinShapiroResidue k a v)) :
    u = v := by
  funext i
  obtain ⟨k, a, ha, hr, hlo, hhi, hhalf⟩ := hReg i
  have he := (rudinShapiro_signProduct_of_residue hu k a i ha hr hlo hhi hhalf).trans
    (rudinShapiro_signProduct_of_residue hv k a i ha ((hPhase _ _ ha).mp hr) hlo hhi hhalf).symm
  rw [hSign] at he
  have hne : signValue (v 0) ≠ 0 := by cases h : v 0 <;> norm_num [signValue, h]
  have hs := mul_left_cancel₀ hne he
  cases h₁ : u i <;> cases h₂ : v i
  all_goals first
    | rfl
    | norm_num [signValue, h₁, h₂] at hs

end Mixing
