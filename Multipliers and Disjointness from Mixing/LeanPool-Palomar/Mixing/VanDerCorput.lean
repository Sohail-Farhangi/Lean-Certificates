module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # The nested ultrafilter van der Corput lemma -/

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace Mixing

/-- Ordered product of ultrafilters. The limit in the second variable is taken first. -/
def fubiniUltrafilter {A B : Type*} (p : Ultrafilter A) (q : Ultrafilter B) :
    Ultrafilter (A × B) :=
  p.bind (fun a => q.map (fun b => (a, b)))

theorem eventually_fubiniUltrafilter {A B : Type*} {p : Ultrafilter A}
    {q : Ultrafilter B} {P : A × B → Prop} :
    (∀ᶠ w in (fubiniUltrafilter p q : Filter (A × B)), P w) ↔
      ∀ᶠ a in (p : Filter A), ∀ᶠ b in (q : Filter B), P (a, b) :=
  Iff.rfl

theorem map_fubiniUltrafilter {A B C D : Type*} (p : Ultrafilter A)
    (q : Ultrafilter B) (f : A → C) (g : B → D) :
    (fubiniUltrafilter p q).map (Prod.map f g) = fubiniUltrafilter (p.map f) (q.map g) :=
  Ultrafilter.coe_injective rfl

@[simp]
theorem map_fubiniUltrafilter_fst {A B : Type*} (p : Ultrafilter A) (q : Ultrafilter B) :
    (fubiniUltrafilter p q).map Prod.fst = p := by
  apply Ultrafilter.coe_injective
  ext s
  change (∀ᶠ a in (p : Filter A), ∀ᶠ _ in (q : Filter B), a ∈ s) ↔ s ∈ (p : Filter A)
  change (∀ᶠ a in (p : Filter A), ∀ᶠ _ in (q : Filter B), a ∈ s) ↔
    ∀ᶠ a in (p : Filter A), a ∈ s
  exact eventually_congr (Filter.Eventually.of_forall fun _ => eventually_const)

@[simp]
theorem map_fubiniUltrafilter_snd {A B : Type*} (p : Ultrafilter A) (q : Ultrafilter B) :
    (fubiniUltrafilter p q).map Prod.snd = q := by
  apply Ultrafilter.coe_injective
  ext s
  change (∀ᶠ _ in (p : Filter A), ∀ᶠ b in (q : Filter B), b ∈ s) ↔ s ∈ (q : Filter B)
  exact eventually_const

/-- Iterated sampling with one ultrafilter for each coordinate. -/
def coordinateUltrafilter {S : Type*} :
    {n : ℕ} → (Fin n → Ultrafilter S) → Ultrafilter (Fin n → S)
  | 0, _ => pure Fin.elim0
  | n + 1, p =>
      (fubiniUltrafilter (p 0) (coordinateUltrafilter (fun i : Fin n => p i.succ))).map
        (fun v => Fin.cons v.1 v.2)

@[simp]
theorem map_coordinateUltrafilter {S : Type*} {n : ℕ} (p : Fin n → Ultrafilter S)
    (i : Fin n) : (coordinateUltrafilter p).map (fun a => a i) = p i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      change (coordinateUltrafilter p).map (fun a => a 0) = p 0
      rw [coordinateUltrafilter, Ultrafilter.map_map]
      change (fubiniUltrafilter (p 0) (coordinateUltrafilter (fun i : Fin n => p i.succ))).map
        Prod.fst = p 0
      exact map_fubiniUltrafilter_fst _ _
    | succ i =>
      have hk : i < n := Nat.lt_of_succ_lt_succ hi
      change (coordinateUltrafilter p).map (fun a => a (Fin.succ ⟨i, hk⟩)) = _
      rw [coordinateUltrafilter, Ultrafilter.map_map]
      change (fubiniUltrafilter (p 0) (coordinateUltrafilter (fun i : Fin n => p i.succ))).map
        ((fun a => a ⟨i, hk⟩) ∘ Prod.snd) = p (Fin.succ ⟨i, hk⟩)
      rw [← Ultrafilter.map_map, map_fubiniUltrafilter_snd, ih]

theorem map_coordinateUltrafilter_pair {S : Type*} {n : ℕ} (p : Fin n → Ultrafilter S)
    {i j : Fin n} (h : i < j) :
    (coordinateUltrafilter p).map (fun a => (a i, a j)) = fubiniUltrafilter (p i) (p j) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ h).elim
      | succ j =>
        rw [coordinateUltrafilter, Ultrafilter.map_map]
        change (fubiniUltrafilter (p 0) (coordinateUltrafilter (fun k : Fin n => p k.succ))).map
          (Prod.map id (fun a => a j)) = _
        rw [map_fubiniUltrafilter, Ultrafilter.map_id, map_coordinateUltrafilter]
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Nat.not_lt_zero _ h).elim
      | succ j =>
        rw [coordinateUltrafilter, Ultrafilter.map_map]
        change (fubiniUltrafilter (p 0) (coordinateUltrafilter (fun k : Fin n => p k.succ))).map
          ((fun a => (a i, a j)) ∘ Prod.snd) = _
        rw [← Ultrafilter.map_map, map_fubiniUltrafilter_snd,
          ih (fun k : Fin n => p k.succ) (Fin.succ_lt_succ_iff.mp h)]

/-- A scalar ultrafilter limit, used only for families bounded in norm. -/
noncomputable def scalarUltralimit {A K : Type*} [TopologicalSpace K] [Nonempty K]
    (p : Ultrafilter A) (f : A → K) : K :=
  limUnder (p : Filter A) f

theorem tendsto_scalarUltralimit {A K : Type*} [NormedAddCommGroup K] [ProperSpace K]
    (p : Ultrafilter A) {f : A → K} {M : ℝ} (hb : ∀ a, ‖f a‖ ≤ M) :
    Tendsto f (p : Filter A) (𝓝 (scalarUltralimit p f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : K) M).ultrafilter_le_nhds' (p.map f)
    (Ultrafilter.mem_map.mpr (Filter.Eventually.of_forall fun a =>
      Metric.mem_closedBall.mpr (by simpa using hb a)))
  exact ⟨z, hz⟩

theorem norm_scalarUltralimit_le {A K : Type*} [NormedAddCommGroup K] [ProperSpace K]
    (p : Ultrafilter A) {f : A → K} {M : ℝ} (hb : ∀ a, ‖f a‖ ≤ M) :
    ‖scalarUltralimit p f‖ ≤ M :=
  le_of_tendsto' (tendsto_scalarUltralimit p hb).norm hb

theorem tendsto_fubiniUltrafilter {A B Z : Type*} [TopologicalSpace Z]
    {p : Ultrafilter A} {q : Ultrafilter B} {f : A × B → Z} {g : A → Z} {z : Z}
    (hf : ∀ a, Tendsto (fun b => f (a, b)) (q : Filter B) (𝓝 (g a)))
    (hg : Tendsto g (p : Filter A) (𝓝 z)) :
    Tendsto f (fubiniUltrafilter p q : Filter (A × B)) (𝓝 z) := by
  refine tendsto_def.mpr fun s hs => ?_
  change ∀ᶠ w in (fubiniUltrafilter p q : Filter (A × B)), f w ∈ s
  rw [eventually_fubiniUltrafilter]
  obtain ⟨t, hts, ht, hzt⟩ := mem_nhds_iff.mp hs
  filter_upwards [hg.eventually (ht.mem_nhds hzt)] with a hat
  exact (hf a).eventually (mem_of_superset (ht.mem_nhds hat) hts)

theorem scalarUltralimit_fubini {A B K : Type*} [NormedAddCommGroup K] [ProperSpace K]
    (p : Ultrafilter A) (q : Ultrafilter B) {f : A × B → K}
    {M : ℝ} (hb : ∀ v, ‖f v‖ ≤ M) :
    scalarUltralimit (fubiniUltrafilter p q) f =
      scalarUltralimit p (fun a => scalarUltralimit q (fun b => f (a, b))) :=
  tendsto_nhds_unique (tendsto_scalarUltralimit _ hb) <|
    tendsto_fubiniUltrafilter
      (fun a => tendsto_scalarUltralimit q (fun b => hb (a, b)))
      (tendsto_scalarUltralimit p (fun a => norm_scalarUltralimit_le q (fun b => hb (a, b))))

private theorem tendsto_along_ultrafilter_map {A B Z : Type*} [TopologicalSpace Z]
    {p : Ultrafilter A} {q : Ultrafilter B} {f : A → B} {g : B → Z} {L : Filter Z}
    (hm : p.map f = q) (hg : Tendsto g (q : Filter B) L) :
    Tendsto (g ∘ f) (p : Filter A) L := by
  have hf : Tendsto f (p : Filter A) (q : Filter B) := by
    change Filter.map f (p : Filter A) ≤ (q : Filter B)
    rw [← Ultrafilter.coe_map, hm]
  exact hg.comp hf

private theorem map_fubini_middle {A B C D : Type*}
    (q : Ultrafilter A) (p : Ultrafilter B) (w : Ultrafilter C) (g : B → D) :
    (fubiniUltrafilter q (fubiniUltrafilter p w)).map (Prod.map id (Prod.map g id)) =
      fubiniUltrafilter q (fubiniUltrafilter (p.map g) w) := by
  rw [map_fubiniUltrafilter, map_fubiniUltrafilter, Ultrafilter.map_id, Ultrafilter.map_id]

private theorem norm_sum_sq_decomposition {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : Fin N → E) :
    ‖∑ i, v i‖ ^ 2 =
      (∑ i, ‖v i‖ ^ 2) + ∑ i, ∑ j ∈ Finset.univ.erase i, (inner ℂ (v i) (v j)).re := by
  classical
  conv_lhs => rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner]
  change (∑ x, inner ℂ (v x) (∑ i, v i)).re = _
  simp only [inner_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (v i)
  change (inner ℂ (v i) (v i)).re = _ at h
  rw [← h, add_comm]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm

/-- Lemma 10, with the coordinates before and after the selected one grouped into two blocks.
The ordered ultrafilter product takes limits from the innermost variable to the outermost.
Taking either block to be a one-point type covers the first or last coordinate. -/
theorem tendsto_inner_zero_of_fubini_correlations {A S B E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (q : Ultrafilter A) (p : Ultrafilter S) (w : Ultrafilter B)
    (x : A → S → B → E) (y : A → B → E)
    {X Y : ℝ} (hx : ∀ a s b, ‖x a s b‖ ≤ X) (hy : ∀ a b, ‖y a b‖ ≤ Y)
    (hc : Tendsto (fun v : A × ((S × S) × B) =>
        inner ℂ (x v.1 v.2.1.1 v.2.2) (x v.1 v.2.1.2 v.2.2))
      (fubiniUltrafilter q (fubiniUltrafilter (fubiniUltrafilter p p) w) : Filter _)
      (𝓝 0)) :
    Tendsto (fun v : A × (S × B) => inner ℂ (y v.1 v.2.2) (x v.1 v.2.1 v.2.2))
      (fubiniUltrafilter q (fubiniUltrafilter p w) : Filter _) (𝓝 0) := by
  classical
  let coeff (v : A × (S × B)) : ℂ := inner ℂ (y v.1 v.2.2) (x v.1 v.2.1 v.2.2)
  let P := fubiniUltrafilter q (fubiniUltrafilter p w)
  let L := scalarUltralimit P coeff
  have hprod (v : A × (S × B)) : ‖coeff v‖ ≤ Y * X :=
    (norm_inner_le_norm _ _).trans
      (mul_le_mul (hy v.1 v.2.2) (hx v.1 v.2.1 v.2.2) (norm_nonneg _)
        ((norm_nonneg _).trans (hy v.1 v.2.2)))
  have hL : Tendsto coeff (P : Filter _) (𝓝 L) := tendsto_scalarUltralimit P hprod
  suffices L = 0 by simpa only [← this] using hL
  have hbound (N : ℕ) (hN : 0 < N) : (N : ℝ) * ‖L‖ ^ 2 ≤ Y ^ 2 * X ^ 2 := by
    let reps := coordinateUltrafilter (fun _ : Fin N => p)
    let P' := fubiniUltrafilter q (fubiniUltrafilter reps w)
    let V (v : A × ((Fin N → S) × B)) (i : Fin N) := x v.1 (v.2.1 i) v.2.2
    let z (v : A × ((Fin N → S) × B)) := y v.1 v.2.2
    have hSingle (i : Fin N) : Tendsto (fun v => inner ℂ (z v) (V v i))
        (P' : Filter _) (𝓝 L) := by
      have hm : P'.map (Prod.map id (Prod.map (fun a => a i) id)) = P := by
        simp [P', P, reps, map_fubini_middle]
      exact tendsto_along_ultrafilter_map hm hL
    have hOrdered (i j : Fin N) (hij : i < j) :
        Tendsto (fun v => (inner ℂ (V v i) (V v j)).re) (P' : Filter _) (𝓝 0) := by
      have hm : P'.map (Prod.map id (Prod.map (fun a => (a i, a j)) id)) =
          fubiniUltrafilter q (fubiniUltrafilter (fubiniUltrafilter p p) w) := by
        dsimp only [P', reps]
        rw [map_fubini_middle, map_coordinateUltrafilter_pair _ hij]
      have h := (Complex.continuous_re.tendsto _).comp (tendsto_along_ultrafilter_map hm hc)
      simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, V, Complex.zero_re] using h
    have hDouble (i j : Fin N) (hij : i ≠ j) :
        Tendsto (fun v => (inner ℂ (V v i) (V v j)).re) (P' : Filter _) (𝓝 0) := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hOrdered i j h
      · convert hOrdered j i h using 1
        funext v
        exact inner_re_symm (𝕜 := ℂ) _ _
    let off (v : A × ((Fin N → S) × B)) :=
      ∑ i, ∑ j ∈ Finset.univ.erase i, (inner ℂ (V v i) (V v j)).re
    have hOff : Tendsto off (P' : Filter _) (𝓝 0) := by
      have hRow (i : Fin N) :
          Tendsto (fun v => ∑ j ∈ Finset.univ.erase i, (inner ℂ (V v i) (V v j)).re)
            (P' : Filter _) (𝓝 0) := by
        simpa only [Finset.sum_const_zero] using
          tendsto_finsetSum (Finset.univ.erase i) (fun j hj =>
            hDouble i j (Finset.ne_of_mem_erase hj).symm)
      simpa only [off, Finset.sum_const_zero] using
        tendsto_finsetSum Finset.univ (fun i _ => hRow i)
    let vSum (v : A × ((Fin N → S) × B)) := ∑ i, V v i
    have hs : Tendsto (fun v => inner ℂ (z v) (vSum v)) (P' : Filter _)
        (𝓝 ((N : ℂ) * L)) := by
      simpa [vSum, inner_sum, nsmul_eq_mul] using
        tendsto_finsetSum Finset.univ (fun i _ => hSingle i)
    have hGram (v : A × ((Fin N → S) × B)) : ‖vSum v‖ ^ 2 ≤ (N : ℝ) * X ^ 2 + off v := by
      have hDiag : (∑ i : Fin N, ‖V v i‖ ^ 2) ≤ (N : ℝ) * X ^ 2 := by
        calc
          _ ≤ ∑ _i : Fin N, X ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hx v.1 (v.2.1 i) v.2.2) _
          _ = _ := by simp [nsmul_eq_mul]
      exact (norm_sum_sq_decomposition (V v)).le.trans (add_le_add_left hDiag _)
    have hCauchy (v : A × ((Fin N → S) × B)) :
        ‖inner ℂ (z v) (vSum v)‖ ^ 2 ≤ Y ^ 2 * ((N : ℝ) * X ^ 2 + off v) := calc
      _ ≤ (‖z v‖ * ‖vSum v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) _
      _ = ‖z v‖ ^ 2 * ‖vSum v‖ ^ 2 := mul_pow _ _ _
      _ ≤ Y ^ 2 * ‖vSum v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hy _ _) _) (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hGram v) (sq_nonneg _)
    have hrhs : Tendsto (fun v => Y ^ 2 * ((N : ℝ) * X ^ 2 + off v))
        (P' : Filter _) (𝓝 (Y ^ 2 * ((N : ℝ) * X ^ 2))) := by
      simpa only [add_zero] using tendsto_const_nhds.mul (tendsto_const_nhds.add hOff)
    have h := le_of_tendsto_of_tendsto' (hs.norm.pow 2) hrhs hCauchy
    rw [norm_mul, Complex.norm_natCast, mul_pow] at h
    apply (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hN : 0 < (N : ℝ))).mp
    convert h using 1 <;> ring
  by_contra hz
  have hPos : 0 < ‖L‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (Y ^ 2 * X ^ 2 / ‖L‖ ^ 2)
  have hNpos : 0 < N := Nat.cast_pos.mp
    ((div_nonneg (mul_nonneg (sq_nonneg Y) (sq_nonneg X)) hPos.le).trans_lt hN)
  exact ((div_lt_iff₀ hPos).mp hN).not_ge (hbound N hNpos)

/-- The first-coordinate case of Lemma 10, used in the proof of Lemma 11. -/
theorem tendsto_inner_zero_of_fubini_correlations_first {S B E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (p : Ultrafilter S) (w : Ultrafilter B)
    (x : S → B → E) (y : B → E)
    {X Y : ℝ} (hx : ∀ s b, ‖x s b‖ ≤ X) (hy : ∀ b, ‖y b‖ ≤ Y)
    (hc : Tendsto (fun v : (S × S) × B => inner ℂ (x v.1.1 v.2) (x v.1.2 v.2))
      (fubiniUltrafilter (fubiniUltrafilter p p) w : Filter _) (𝓝 0)) :
    Tendsto (fun v : S × B => inner ℂ (y v.2) (x v.1 v.2))
      (fubiniUltrafilter p w : Filter _) (𝓝 0) := by
  have h := tendsto_inner_zero_of_fubini_correlations (pure ()) p w (fun _ => x)
    (fun _ => y) (fun _ => hx) (fun _ => hy)
    (tendsto_fubiniUltrafilter (fun _ => hc) tendsto_const_nhds)
  have hm : (fubiniUltrafilter p w).map (fun v => ((), v)) =
      fubiniUltrafilter (pure ()) (fubiniUltrafilter p w) := by
    apply Ultrafilter.coe_injective
    rfl
  exact tendsto_along_ultrafilter_map hm h

/-- The one-variable van der Corput consequence used for product joinings. -/
theorem tendsto_inner_zero_of_fubini_correlations_single {S E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (p : Ultrafilter S)
    (x : S → E) {C : ℝ} (hx : ∀ s, ‖x s‖ ≤ C)
    (hc : Tendsto (fun v : S × S => inner ℂ (x v.1) (x v.2))
      (fubiniUltrafilter p p : Filter _) (𝓝 0)) (z : E) :
    Tendsto (fun s => inner ℂ z (x s)) (p : Filter _) (𝓝 0) := by
  let w : Ultrafilter Unit := pure ()
  have hCorr : Tendsto (fun v : (S × S) × Unit => inner ℂ (x v.1.1) (x v.1.2))
      (fubiniUltrafilter (fubiniUltrafilter p p) w : Filter _) (𝓝 0) :=
    tendsto_fubiniUltrafilter (fun _ => tendsto_const_nhds) hc
  have h := tendsto_inner_zero_of_fubini_correlations_first p w
    (fun s _ => x s) (fun _ => z) (fun s _ => hx s) (fun _ => le_rfl) hCorr
  have hm : p.map (fun s => (s, ())) = fubiniUltrafilter p w := by
    apply Ultrafilter.coe_injective
    rfl
  exact tendsto_along_ultrafilter_map
    (g := fun v : S × Unit => inner ℂ z (x v.1)) hm h

/-- Hilbert coefficients give convergence for the weak topology. -/
theorem tendsto_weakSpace_of_tendsto_inner {I E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {l : Filter I} {f : I → E} {v : E}
    (h : ∀ z, Tendsto (fun i => inner ℂ z (f i)) l (𝓝 (inner ℂ z v))) :
    Tendsto (fun i => toWeakSpace ℂ E (f i)) l (𝓝 (toWeakSpace ℂ E v)) := by
  have hB : Function.Injective (topDualPairing ℂ E).flip := by
    intro x y hxy
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro a
    exact DFunLike.congr_fun hxy a
  refine (WeakBilin.tendsto_iff_forall_eval_tendsto _ hB).2 ?_
  intro a
  change Tendsto (fun i => a (f i)) l (𝓝 (a v))
  obtain ⟨z, rfl⟩ := (InnerProductSpace.toDual ℂ E).surjective a
  exact h z

/-- The weak-limit conclusion of Lemma 10. -/
theorem tendsto_weak_zero_of_fubini_correlations {A S B E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (q : Ultrafilter A) (p : Ultrafilter S) (w : Ultrafilter B)
    (x : A → S → B → E) {X : ℝ} (hx : ∀ a s b, ‖x a s b‖ ≤ X)
    (hc : Tendsto (fun v : A × ((S × S) × B) =>
        inner ℂ (x v.1 v.2.1.1 v.2.2) (x v.1 v.2.1.2 v.2.2))
      (fubiniUltrafilter q (fubiniUltrafilter (fubiniUltrafilter p p) w) : Filter _)
      (𝓝 0)) :
    Tendsto (fun v : A × (S × B) => toWeakSpace ℂ E (x v.1 v.2.1 v.2.2))
      (fubiniUltrafilter q (fubiniUltrafilter p w) : Filter _) (𝓝 0) := by
  rw [← map_zero (toWeakSpace ℂ E)]
  apply tendsto_weakSpace_of_tendsto_inner
  intro z
  simpa only [inner_zero_right] using
    tendsto_inner_zero_of_fubini_correlations q p w x (fun _ _ => z) hx
      (fun _ _ => le_rfl) hc

end Mixing

