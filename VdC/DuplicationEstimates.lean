/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import VdC.DuplicationBlocks
public import VdC.PolynomialPhases
public import VdC.ResidueAverages

/-! Uniform exponential-sum estimates for the duplicated blocks. -/

@[expose] public section

open Filter Finset
open scoped Topology BigOperators

namespace VdC

noncomputable section

/-- The amount subtracted from an index in the second half of its group. -/
def duplicationOffset (p r : ℕ) : ℤ := if r < p then 0 else (p : ℤ)

/-- The change in the original index under a lag inside one stage. -/
def duplicationGap (p h r : ℕ) : ℤ :=
  (h : ℤ) + duplicationOffset p r - duplicationOffset p ((r+h) % (2*p))

theorem duplicationGap_eq_zero_iff {p h r : ℕ} (hp : 0 < p) (hh : 0 < h) :
    duplicationGap p h r = 0 ↔ p = h ∧ r < p := by
  constructor
  · intro he
    by_cases h₁ : r < p <;> by_cases h₂ : (r+h) % (2*p) < p
    all_goals simp [duplicationGap, duplicationOffset, h₁, h₂] at he ⊢
    all_goals omega
  · rintro ⟨rfl, hr'⟩
    rw [duplicationGap, duplicationOffset, ite_eq_left hr',
      Nat.mod_eq_of_lt (by omega : r+p < 2*p), duplicationOffset, ite_eq_right (by omega)]
    ring

/-- The coincidences prescribed by the block construction. -/
def duplicationMask (p h t : ℕ) : Prop := p = h ∧ t % (2*p) < p

instance (p h t : ℕ) : Decidable (duplicationMask p h t) := by
  unfold duplicationMask
  infer_instance

def localIndex (A p t : ℕ) : ℤ :=
  (A : ℤ) + t - duplicationOffset p (t % (2*p))

/-- The masked exponential on a stage extended periodically beyond its right boundary. -/
def localMaskedPhase (α : ℝ) (m : ℤ) (A p h t : ℕ) : ℂ :=
  if duplicationMask p h t then 0
  else phase ((m : ℝ) * α *
    ((localIndex A p (t+h) : ℝ)^2 - (localIndex A p t : ℝ)^2))

private theorem norm_localMaskedPhase_le (α : ℝ) (m : ℤ) (A p h t : ℕ) :
    ‖localMaskedPhase α m A p h t‖ ≤ 1 := by
  unfold localMaskedPhase
  split <;> simp

def stageSlopeInt (m : ℤ) (p h r : ℕ) : ℤ :=
  4 * (p : ℤ) * m * duplicationGap p h r

private def stageIntercept (α : ℝ) (m : ℤ) (A p h r : ℕ) : ℝ :=
  (m : ℝ) * α * ((localIndex A p (r+h) : ℝ)^2 - (localIndex A p r : ℝ)^2)

private theorem localIndex_block (A p j r : ℕ) :
    localIndex A p ((2*p)*j+r) = (2*p : ℕ) * (j : ℤ) + localIndex A p r := by
  simp only [localIndex, Nat.mul_add_mod, Nat.cast_add, Nat.cast_mul]
  ring

private theorem localIndex_gap {A p h r : ℕ} (hr : r < 2*p) :
    localIndex A p (r+h) - localIndex A p r = duplicationGap p h r := by
  simp only [localIndex, duplicationGap, Nat.cast_add, Nat.mod_eq_of_lt hr]
  ring

private theorem localMaskedPhase_block {α : ℝ} {m : ℤ} {A p h r : ℕ}
    (hr : r < 2*p) (hn : ¬ (p = h ∧ r < p)) (j : ℕ) :
    localMaskedPhase α m A p h ((2*p)*j+r) =
      phase ((α * stageSlopeInt m p h r) * (j : ℝ) + stageIntercept α m A p h r) := by
  have hmask : ¬ duplicationMask p h ((2*p)*j+r) := by
    simpa [duplicationMask, Nat.mul_add_mod, Nat.mod_eq_of_lt hr] using hn
  rw [localMaskedPhase, ite_eq_right hmask]
  rw [add_assoc, localIndex_block, localIndex_block]
  have he := congrArg (fun x : ℤ ↦ (x : ℝ)) (localIndex_gap (A := A) (h := h) hr)
  push_cast at he
  congr 1
  simp only [stageSlopeInt, stageIntercept]
  push_cast
  rw [← he]
  ring

def residuePhaseBound (α : ℝ) (m : ℤ) (p h r : ℕ) : ℝ :=
  if p = h ∧ r < p then 0 else 2 / ‖phase (α * stageSlopeInt m p h r) - 1‖

private theorem residuePhaseBound_nonneg (α : ℝ) (m : ℤ) (p h r : ℕ) :
    0 ≤ residuePhaseBound α m p h r := by
  unfold residuePhaseBound
  split <;> positivity

private theorem norm_sum_residueMaskedPhase_le {α : ℝ} (hα : Irrational α) {m : ℤ}
    (hm : m ≠ 0) {p h r : ℕ} (hp : 0 < p) (hh : 0 < h) (hr : r < 2*p) (A L : ℕ) :
    ‖∑ j ∈ range L, localMaskedPhase α m A p h ((2*p)*j+r)‖ ≤ residuePhaseBound α m p h r := by
  by_cases hz : p = h ∧ r < p
  · have he (j : ℕ) : duplicationMask p h ((2*p)*j+r) := by
      simpa [duplicationMask, Nat.mul_add_mod, Nat.mod_eq_of_lt hr] using hz
    simp only [localMaskedPhase, he, ite_true, Finset.sum_const_zero, norm_zero]
    rw [residuePhaseBound, ite_eq_left hz]
  · simp_rw [localMaskedPhase_block hr hz]
    rw [residuePhaseBound, ite_eq_right hz]
    apply norm_sum_linear_phase_le
    apply phase_ne_one_of_irrational
    apply hα.mul_intCast
    have hg := mt (duplicationGap_eq_zero_iff (r := r) hp hh).mp hz
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hp.ne')) hm) hg

/-- Intercept-independent bound for every prefix of a masked stage, including the
incomplete group and the right-boundary terms of the actual construction. -/
def stagePhaseBound (α : ℝ) (m : ℤ) (p h : ℕ) : ℝ :=
  (∑ r ∈ range (2*p), residuePhaseBound α m p h r) + (2*p : ℕ) + 2*(h : ℝ)

theorem stagePhaseBound_nonneg (α : ℝ) (m : ℤ) (p h : ℕ) :
    0 ≤ stagePhaseBound α m p h := by
  have h := Finset.sum_nonneg (s := range (2*p)) (fun r _ ↦ residuePhaseBound_nonneg α m p h r)
  unfold stagePhaseBound
  positivity

private theorem norm_sum_localMaskedPhase_le {α : ℝ} (hα : Irrational α) {m : ℤ}
    (hm : m ≠ 0) {p h : ℕ} (hp : 0 < p) (hh : 0 < h) (A L : ℕ) :
    ‖∑ t ∈ range L, localMaskedPhase α m A p h t‖ ≤
      (∑ r ∈ range (2*p), residuePhaseBound α m p h r) + (2*p : ℕ) := by
  let u := localMaskedPhase α m A p h
  let k := L / (2*p)
  let s := L % (2*p)
  have he : (2*p)*k+s = L := by
    simpa [k, s, add_comm] using Nat.mod_add_div L (2*p)
  have hs : s ≤ 2*p := (Nat.mod_lt _ (by omega)).le
  rw [← he, Finset.sum_range_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [sum_range_mul_residue]
    exact (norm_sum_le _ _).trans (sum_le_sum fun r hr ↦
      norm_sum_residueMaskedPhase_le hα hm hp hh (mem_range.mp hr) A k)
  · apply (norm_sum_le _ _).trans
    exact (sum_le_sum (g := fun _ ↦ (1 : ℝ)) fun t _ ↦ norm_localMaskedPhase_le ..).trans
      (by simp; exact_mod_cast hs)

theorem duplicationBlock_bounds (request : ℕ → ℕ) (n : ℕ) :
    duplicationStart request (duplicationBlock request n) ≤ n ∧
      n < duplicationStart request (duplicationBlock request n+1) := by
  have he : ∃ q, n < duplicationStart request (q+1) :=
    ⟨n, (Nat.lt_succ_self n).trans_le (le_duplicationStart request (n+1))⟩
  obtain ⟨hh, hmin⟩ := (Nat.find_eq_iff he).mp (rfl : Nat.find he = Nat.find he)
  change duplicationStart request (Nat.find he) ≤ n ∧ _
  refine ⟨?_, hh⟩
  rcases e : Nat.find he with _ | q
  · exact Nat.zero_le _
  · simpa only [not_lt] using hmin q (by rw [e]; omega)

/-- The intentional coincidences in the doubled-square construction at lag `h`. -/
def duplicationCoincidence (request : ℕ → ℕ) (h n : ℕ) : Prop :=
  let q := duplicationBlock request n
  duplicationMask (duplicationLag q) h (n - duplicationStart request q)

instance (request : ℕ → ℕ) (h n : ℕ) : Decidable (duplicationCoincidence request h n) := by
  unfold duplicationCoincidence
  infer_instance

/-- The actual masked Fourier exponential of a lagged difference. -/
def duplicationMaskedPhase (request : ℕ → ℕ) (α : ℝ) (m : ℤ) (h n : ℕ) : ℂ :=
  if duplicationCoincidence request h n then 0
  else phase ((m : ℝ) * α *
    ((duplicationIndex request (n+h) : ℝ)^2 - (duplicationIndex request n : ℝ)^2))

private theorem norm_duplicationMaskedPhase_le (request : ℕ → ℕ) (α : ℝ) (m : ℤ) (h n : ℕ) :
    ‖duplicationMaskedPhase request α m h n‖ ≤ 1 := by
  unfold duplicationMaskedPhase
  split <;> simp

private theorem duplicationIndex_eq_localIndex {request : ℕ → ℕ} {q t : ℕ}
    (ht : duplicationStart request q + t < duplicationStart request (q+1)) :
    (duplicationIndex request (duplicationStart request q+t) : ℤ) =
      localIndex (duplicationStart request q) (duplicationLag q) t := by
  let A := duplicationStart request q
  let p := duplicationLag q
  have hb := duplicationBlock_eq (Nat.le_add_right A t) ht
  unfold duplicationIndex
  rw [hb]
  change (↑(if (A+t-A) % (2*p) < p then A+t else A+t-p) : ℤ) = localIndex A p t
  rw [Nat.add_sub_cancel_left]
  by_cases hr : t % (2*p) < p
  · simp [localIndex, duplicationOffset, hr]
  · rw [ite_eq_right hr, Nat.cast_sub ((not_lt.mp hr).trans ((Nat.mod_le ..).trans (Nat.le_add_left ..)))]
    simp [localIndex, duplicationOffset, hr]

private theorem duplicationMaskedPhase_eq_local {request : ℕ → ℕ} {α : ℝ} {m : ℤ}
    {q h t : ℕ}
    (ht : duplicationStart request q + t + h < duplicationStart request (q+1)) :
    duplicationMaskedPhase request α m h (duplicationStart request q+t) =
      localMaskedPhase α m (duplicationStart request q) (duplicationLag q) h t := by
  let A := duplicationStart request q
  have ht' : A + t < duplicationStart request (q+1) := by omega
  have ht'' : A + (t+h) < duplicationStart request (q+1) := by omega
  have hb := duplicationBlock_eq (Nat.le_add_right A t) ht'
  have hindex := congrArg (fun x : ℤ ↦ (x : ℝ)) (duplicationIndex_eq_localIndex ht')
  have hindex' := congrArg (fun x : ℤ ↦ (x : ℝ)) (duplicationIndex_eq_localIndex ht'')
  push_cast at hindex hindex'
  have he : duplicationCoincidence request h (A+t) ↔ duplicationMask (duplicationLag q) h t := by
    unfold duplicationCoincidence
    dsimp only
    rw [hb, Nat.add_sub_cancel_left]
  change duplicationMaskedPhase request α m h (A+t) = localMaskedPhase α m A (duplicationLag q) h t
  unfold duplicationMaskedPhase localMaskedPhase
  by_cases hs : duplicationMask (duplicationLag q) h t
  · rw [ite_eq_left (he.mpr hs), ite_eq_left hs]
  · rw [ite_eq_right (mt he.mp hs), ite_eq_right hs, add_assoc, hindex, hindex']

/-- Every stage prefix, including any terms whose lag crosses the stage boundary,
has a uniformly bounded masked exponential sum. -/
theorem norm_sum_duplicationMaskedPhase_stage_le {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) (request : ℕ → ℕ) (q : ℕ) {h L : ℕ} (hh : 0 < h)
    (hL : duplicationStart request q + L ≤ duplicationStart request (q+1)) :
    ‖∑ t ∈ range L, duplicationMaskedPhase request α m h (duplicationStart request q+t)‖ ≤
      stagePhaseBound α m (duplicationLag q) h := by
  let A := duplicationStart request q
  let p := duplicationLag q
  let B := duplicationStart request (q+1)
  let S := min L (B-A-h)
  let u := fun t ↦ duplicationMaskedPhase request α m h (A+t)
  have hs : S ≤ L := min_le_left _ _
  have ht : L-S ≤ h := by
    have hh' : L ≤ B-A := by omega
    dsimp [S]
    omega
  have he : L = S+(L-S) := by omega
  change ‖∑ t ∈ range L, u t‖ ≤ _
  rw [he, Finset.sum_range_add]
  have hu : (∑ t ∈ range S, u t) =
      ∑ t ∈ range S, localMaskedPhase α m A p h t := by
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := mem_range.mp ht
    apply duplicationMaskedPhase_eq_local (q := q)
    dsimp [S] at ht'
    omega
  rw [hu]
  have htail : ‖∑ t ∈ range (L-S), u (S+t)‖ ≤ (h : ℝ) := by
    apply (norm_sum_le _ _).trans
    exact (sum_le_sum (g := fun _ ↦ (1 : ℝ)) fun t _ ↦ norm_duplicationMaskedPhase_le ..).trans
      (by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]; exact_mod_cast ht)
  have hmain := norm_sum_localMaskedPhase_le hα hm (duplicationLag_pos q) hh A S
  have hsum := (norm_add_le _ _).trans (add_le_add hmain htail)
  exact hsum.trans (by unfold stagePhaseBound; dsimp [p] at *; linarith)

private theorem norm_sum_duplicationMaskedPhase_stages_le {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) (request : ℕ → ℕ) {h : ℕ} (hh : 0 < h) (q : ℕ) :
    ‖∑ t ∈ range (duplicationStart request q), duplicationMaskedPhase request α m h t‖ ≤
      ∑ i ∈ range q, stagePhaseBound α m (duplicationLag i) h := by
  induction q with
  | zero => simp [duplicationStart]
  | succ q ih =>
    let A := duplicationStart request q
    let L := (2 * duplicationLag q) * duplicationGroups request q
    have hL : A+L = duplicationStart request (q+1) := (duplicationStart_succ request q).symm
    rw [← hL, Finset.sum_range_add, Finset.sum_range_succ]
    exact (norm_add_le ..).trans (add_le_add ih
      (norm_sum_duplicationMaskedPhase_stage_le hα hm request q hh hL.le))

/-- Growth sufficient to make all complete and partial stage errors negligible. -/
def duplicationGrowth (α : ℝ) (q : ℕ) : ℕ :=
  (q+1) * ⌈∑ h ∈ range (q+1), ∑ m ∈ Icc (-(q : ℤ)) (q : ℤ),
    ∑ i ∈ range (q+1), stagePhaseBound α m (duplicationLag i) h⌉₊

private theorem request_le_start (request : ℕ → ℕ) {q : ℕ} (hq : 0 < q) :
    request q ≤ duplicationStart request q := by
  rcases q with _ | q
  · omega
  rw [duplicationStart_succ]
  have hp := duplicationLag_pos q
  have hm : 1 ≤ 2 * duplicationLag q := by omega
  have hh : duplicationGroups request q ≤ 2 * duplicationLag q * duplicationGroups request q := by
    simpa only [one_mul] using Nat.mul_le_mul_right (duplicationGroups request q) hm
  exact (Nat.le_add_left _ _).trans (hh.trans (Nat.le_add_left _ _))

private theorem prefix_error_le_start (α : ℝ) {m : ℤ} {h q : ℕ} (hq : 0 < q)
    (hhq : h ≤ q) (hmq : m ∈ Icc (-(q : ℤ)) (q : ℤ)) :
    ((q : ℝ)+1) * (∑ i ∈ range (q+1), stagePhaseBound α m (duplicationLag i) h) ≤
      (duplicationStart (duplicationGrowth α) q : ℝ) := by
  let E (j : ℕ) (k : ℤ) := ∑ i ∈ range (q+1), stagePhaseBound α k (duplicationLag i) j
  have hE j k : 0 ≤ E j k :=
    Finset.sum_nonneg fun i _ ↦ stagePhaseBound_nonneg α k (duplicationLag i) j
  have hsum : E h m ≤ ∑ j ∈ range (q+1), ∑ k ∈ Icc (-(q : ℤ)) (q : ℤ), E j k :=
    (single_le_sum (fun k _ ↦ hE h k) hmq).trans
      (single_le_sum (fun j _ ↦ Finset.sum_nonneg fun k _ ↦ hE j k) (mem_range.mpr (by omega)))
  have hc : ((duplicationGrowth α q : ℕ) : ℝ) ≤
      (duplicationStart (duplicationGrowth α) q : ℝ) := by
    exact_mod_cast request_le_start (duplicationGrowth α) hq
  refine (mul_le_mul_of_nonneg_left (hsum.trans (Nat.le_ceil _)) (by positivity)).trans ?_
  simpa only [duplicationGrowth, Nat.cast_mul, Nat.cast_add, Nat.cast_one, E] using hc

/-- Once the intentional coincidences are removed, every positive-lag nonzero Fourier
average tends to zero. The masked averages keep their original denominator. -/
theorem tendsto_cesaro_duplicationMaskedPhase_zero {α : ℝ} (hα : Irrational α)
    {m : ℤ} (hm : m ≠ 0) {h : ℕ} (hh : 0 < h) :
    Tendsto (cesaro (duplicationMaskedPhase (duplicationGrowth α) α m h)) atTop (𝓝 0) := by
  let request := duplicationGrowth α
  let u := duplicationMaskedPhase request α m h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1/ε)
  let Q := max (max K 1) (max h m.natAbs)
  refine ⟨duplicationStart request Q, fun N hN ↦ ?_⟩
  let q := duplicationBlock request N
  let A := duplicationStart request q
  obtain ⟨hA, hB⟩ := duplicationBlock_bounds request N
  change A ≤ N at hA
  change N < duplicationStart request (q+1) at hB
  have hQ : Q ≤ q := by
    by_contra! hn
    exact (not_lt_of_ge hN) (hB.trans_le ((duplicationStart_strictMono request).monotone (by omega)))
  have hKq : K ≤ q := (le_max_left K 1).trans ((le_max_left _ _).trans hQ)
  have h1q : 0 < q := (le_max_right K 1).trans ((le_max_left _ _).trans hQ)
  have hhq : h ≤ q := (le_max_left h m.natAbs).trans ((le_max_right _ _).trans hQ)
  have hmq' : m.natAbs ≤ q := (le_max_right h m.natAbs).trans ((le_max_right _ _).trans hQ)
  have hmq : m ∈ Icc (-(q : ℤ)) (q : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  have hNr : 0 < (N : ℝ) := by
    exact_mod_cast (h1q.trans_le ((le_duplicationStart request q).trans hA))
  have hqr : 0 < (q : ℝ)+1 := by positivity
  have hN' : N = A+(N-A) := by omega
  have hL : A+(N-A) ≤ duplicationStart request (q+1) := by omega
  let E := ∑ i ∈ range (q+1), stagePhaseBound α m (duplicationLag i) h
  have he : ‖∑ t ∈ range N, u t‖ ≤ E := by
    rw [hN', Finset.sum_range_add]
    apply (norm_add_le ..).trans
    change ‖∑ t ∈ range A, u t‖ + ‖∑ t ∈ range (N-A), u (A+t)‖ ≤ E
    dsimp only [E]
    rw [Finset.sum_range_succ]
    exact add_le_add (norm_sum_duplicationMaskedPhase_stages_le hα hm request hh q)
      (norm_sum_duplicationMaskedPhase_stage_le hα hm request q hh hL)
  have hEN : ((q : ℝ)+1)*E ≤ (N : ℝ) :=
    (prefix_error_le_start α h1q hhq hmq).trans (by exact_mod_cast hA)
  have hEdiv : E / (N : ℝ) ≤ 1 / ((q : ℝ)+1) := by
    rw [div_le_div_iff₀ hNr hqr, one_mul, mul_comm]
    exact hEN
  have hKqr : (K : ℝ) ≤ q := by exact_mod_cast hKq
  have hεq : (1 : ℝ) / ((q : ℝ)+1) < ε := by
    rw [div_lt_iff₀ hqr]
    have hf := (div_lt_iff₀ hε).mp hK
    have hg := mul_le_mul_of_nonneg_right (show (K : ℝ) ≤ (q : ℝ)+1 by linarith) hε.le
    nlinarith only [hf, hg]
  rw [dist_zero_right, cesaro, norm_div, Complex.norm_natCast]
  exact ((div_le_div_of_nonneg_right he hNr.le).trans hEdiv).trans_lt hεq

theorem duplicationCoincidence_lag {request : ℕ → ℕ} {h n : ℕ}
    (hc : duplicationCoincidence request h n) :
    duplicationLag (duplicationBlock request n) = h := hc.1

/-- Each prescribed coincidence pairs a first-half index with its second-half copy. -/
theorem duplicationCoincidence_pair {request : ℕ → ℕ} {h n : ℕ}
    (hc : duplicationCoincidence request h n) :
    duplicationIndex request (n+h) = duplicationIndex request n ∧
      ¬ duplicationCoincidence request h (n+h) := by
  let q := duplicationBlock request n
  let A := duplicationStart request q
  let p := duplicationLag q
  let k := (n-A)/(2*p)
  let r := (n-A)%(2*p)
  have hp : p = h := hc.1
  have hr : r < p := hc.2
  obtain ⟨ha, hb⟩ := duplicationBlock_bounds request n
  change A ≤ n at ha
  change n < duplicationStart request (q+1) at hb
  have hd : (2*p)*k+r = n-A := by
    simpa [k, r, add_comm] using Nat.mod_add_div (n-A) (2*p)
  have hn : n = A+(2*p)*k+r := by omega
  have hb' : duplicationStart request (q+1) = A+2*p*duplicationGroups request q :=
    duplicationStart_succ request q
  have hk : k < duplicationGroups request q := by
    by_contra! hh
    have hm := Nat.mul_le_mul_left (2*p) hh
    omega
  have hx := duplicationIndex_first_half request q k r hk hr
  change duplicationIndex request (A+(2*p)*k+r) = A+(2*p)*k+r ∧
      duplicationIndex request (A+(2*p)*k+r+p) = A+(2*p)*k+r at hx
  rw [← hn, hp] at hx
  refine ⟨hx.2.trans hx.1.symm, ?_⟩
  have hm := Nat.mul_le_mul_left (2*p) (by omega : k+1 ≤ duplicationGroups request q)
  rw [Nat.mul_succ] at hm
  have ht : n+h < duplicationStart request (q+1) := by omega
  have hq' := duplicationBlock_eq (show A ≤ n+h by omega) ht
  have hs : n+h-A = (2*p)*k+(r+p) := by omega
  have hr' : (n+h-A) % (2*p) = r+p := by
    rw [hs, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  intro hc'
  have he := hc'.2
  change (n+h-duplicationStart request (duplicationBlock request (n+h))) %
      (2*duplicationLag (duplicationBlock request (n+h))) <
        duplicationLag (duplicationBlock request (n+h)) at he
  rw [hq'] at he
  change (n+h-A)%(2*p) < p at he
  rw [hr'] at he
  omega

end

end VdC
