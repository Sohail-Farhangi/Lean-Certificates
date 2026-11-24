module

public import Mixing.System
public import Mixing.VanDerCorput
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Van der Corput for correlations of a joining -/

@[expose] public section

open Filter MeasureTheory
open scoped BigOperators ComplexConjugate Topology

namespace Mixing

/-- A bounded measurable representative of an essentially bounded complex function. -/
structure BoundedObservable (X : Type*) [MeasurableSpace X] where
  toFun : X → ℂ
  measurable : Measurable toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x, ‖toFun x‖ ≤ bound

namespace BoundedObservable

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

instance : CoeFun (BoundedObservable X) (fun _ => X → ℂ) :=
  ⟨toFun⟩

/-- The product of bounded measurable functions. -/
def mul (f g : BoundedObservable X) : BoundedObservable X where
  toFun x := f x * g x
  measurable := f.measurable.mul g.measurable
  bound := f.bound * g.bound
  bound_nonneg := mul_nonneg f.bound_nonneg g.bound_nonneg
  norm_le x := by
    rw [norm_mul]
    exact mul_le_mul (f.norm_le x) (g.norm_le x) (norm_nonneg _) f.bound_nonneg

/-- The difference of bounded measurable functions. -/
def sub (f g : BoundedObservable X) : BoundedObservable X where
  toFun x := f x - g x
  measurable := f.measurable.sub g.measurable
  bound := f.bound + g.bound
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  norm_le x := (norm_sub_le _ _).trans (add_le_add (f.norm_le x) (g.norm_le x))

/-- The constant observable. -/
noncomputable def const (c : ℂ) : BoundedObservable X where
  toFun _ := c
  measurable := measurable_const
  bound := ‖c‖
  bound_nonneg := norm_nonneg c
  norm_le _ := le_rfl

/-- Pointwise complex conjugation. -/
def conjugate (f : BoundedObservable X) : BoundedObservable X where
  toFun x := conj (f x)
  measurable := Complex.continuous_conj.measurable.comp f.measurable
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  norm_le x := by simpa using f.norm_le x

/-- Pullback along a measurable map. -/
def comp (f : BoundedObservable Y) (π : X → Y) (hπ : Measurable π) : BoundedObservable X where
  toFun x := f (π x)
  measurable := f.measurable.comp hπ
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  norm_le x := f.norm_le (π x)

/-- Finite products of bounded observables. -/
def prod {ι : Type*} (s : Finset ι) (f : ι → BoundedObservable X) :
    BoundedObservable X where
  toFun x := ∏ i ∈ s, f i x
  measurable := Finset.measurable_prod s (fun i _ => (f i).measurable)
  bound := ∏ i ∈ s, (f i).bound
  bound_nonneg := Finset.prod_nonneg (fun i _ => (f i).bound_nonneg)
  norm_le x := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => (f i).norm_le x)

@[simp] theorem mul_apply (f g : BoundedObservable X) (x : X) : f.mul g x = f x * g x := rfl
@[simp] theorem sub_apply (f g : BoundedObservable X) (x : X) : f.sub g x = f x - g x := rfl
@[simp] theorem const_apply (c : ℂ) (x : X) : (const c : BoundedObservable X) x = c := rfl
@[simp] theorem conjugate_apply (f : BoundedObservable X) (x : X) :
    f.conjugate x = conj (f x) := rfl
@[simp] theorem comp_apply (f : BoundedObservable Y) (π : X → Y) (hπ : Measurable π) (x : X) :
    f.comp π hπ x = f (π x) := rfl
@[simp] theorem prod_apply {ι : Type*} (s : Finset ι) (f : ι → BoundedObservable X) (x : X) :
    prod s f x = ∏ i ∈ s, f i x := rfl

theorem memLp (f : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] (p : ENNReal) :
    MemLp f p μ :=
  MemLp.of_bound f.measurable.aestronglyMeasurable f.bound (Eventually.of_forall f.norm_le)

theorem integrable (f : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ :=
  memLp_one_iff_integrable.mp (f.memLp μ 1)

/-- Regard a bounded observable as a vector in the probability-space Hilbert space. -/
noncomputable def l2 (f : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    Lp ℂ 2 μ :=
  (f.memLp μ 2).toLp f

theorem coe_l2 (f : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    f.l2 μ =ᵐ[μ] f :=
  (f.memLp μ 2).coeFn_toLp

theorem norm_l2_le (f : BoundedObservable X) (μ : Measure X) [IsProbabilityMeasure μ] :
    ‖f.l2 μ‖ ≤ f.bound := by
  have h := Lp.norm_le_of_ae_bound (f := f.l2 μ) f.bound_nonneg
    ((f.coe_l2 μ).mono fun x h => h ▸ f.norm_le x)
  simpa [measureUnivNNReal, measure_univ] using h

theorem inner_l2 (f g : BoundedObservable X) (μ : Measure X) [IsFiniteMeasure μ] :
    inner ℂ (f.l2 μ) (g.l2 μ) = ∫ x, conj (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coe_l2 μ, g.coe_l2 μ] with x hfx hgx
  rw [hfx, hgx, RCLike.inner_apply']

theorem norm_integral_le (f : BoundedObservable X) (μ : Measure X) [IsProbabilityMeasure μ] :
    ‖∫ x, f x ∂μ‖ ≤ f.bound := by
  simpa using norm_integral_le_of_norm_le_const
    (Eventually.of_forall f.norm_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ f.bound)

theorem integral_comp_of_preserving (f : BoundedObservable Y)
    {μ : Measure X} {ν : Measure Y} {π : X → Y} (hπ : MeasurePreserving π μ ν) :
    (∫ x, f (π x) ∂μ) = ∫ y, f y ∂ν := by
  rw [← hπ.map_eq]
  exact (integral_map hπ.measurable.aemeasurable f.measurable.aestronglyMeasurable).symm

end BoundedObservable

namespace System

variable {G X : Type*} [Group G] [MeasurableSpace X]

/-- The translate of a bounded observable by the system action. -/
def translated (S : System G X) (g : G) (f : BoundedObservable X) : BoundedObservable X :=
  f.comp (S.act g) (S.preserves g).measurable

@[simp] theorem translated_apply (S : System G X) (g : G) (f : BoundedObservable X) (x : X) :
    S.translated g f x = f (S.act g x) := rfl

@[simp] theorem translated_bound (S : System G X) (g : G) (f : BoundedObservable X) :
    (S.translated g f).bound = f.bound := rfl

end System

section Joining

variable {G X Y Z : Type*} [CommGroup G]
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- The coefficient formulation of U-mixing on bounded observables. -/
def HasMixingCorrelations (R : System G Z) (U : Set (Ultrafilter G)) : Prop :=
  ∀ p ∈ U, ∀ f h : BoundedObservable Z,
    Tendsto (fun g => ∫ z, conj (f z) * h (R.act g z) ∂R.measure) (p : Filter G)
      (𝓝 (conj (∫ z, f z ∂R.measure) * ∫ z, h z ∂R.measure))

private def translatedProduct {n : ℕ}
    (T : System G X) (f : Fin n → BoundedObservable X) (g : Fin n → G) : BoundedObservable X :=
  BoundedObservable.prod Finset.univ (fun i => T.translated (g i) (f i))

private def joiningTest {n : ℕ} (T : System G X)
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (g : Fin n → G) :
    BoundedObservable (X × Y) :=
  ((translatedProduct T f g).comp Prod.fst measurable_fst).mul
    (F.comp Prod.snd measurable_snd)

private def joiningTest₃ {n : ℕ} (T : System G X)
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z)
    (g : Fin n → G) : BoundedObservable ((X × Y) × Z) :=
  ((joiningTest T f F g).comp Prod.fst measurable_fst).mul
    (H.comp Prod.snd measurable_snd)

/-- A two-coordinate correlation at the given translates. -/
noncomputable def joiningCorrelation {n : ℕ} (T : System G X) (σ : Measure (X × Y))
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (g : Fin n → G) : ℂ :=
  ∫ w, (∏ i, f i (T.act (g i) w.1)) * F w.2 ∂σ

/-- A three-coordinate correlation at the given translates. -/
noncomputable def joiningCorrelation₃ {n : ℕ} (T : System G X) (τ : Measure ((X × Y) × Z))
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z)
    (g : Fin n → G) : ℂ :=
  ∫ w, (∏ i, f i (T.act (g i) w.1.1)) * F w.1.2 * H w.2 ∂τ

private theorem norm_joiningCorrelation_le {n : ℕ} (T : System G X) (σ : Measure (X × Y))
    [IsProbabilityMeasure σ] (f : Fin n → BoundedObservable X) (F : BoundedObservable Y)
    (g : Fin n → G) :
    ‖joiningCorrelation T σ f F g‖ ≤ (∏ i, (f i).bound) * F.bound :=
  (joiningTest T f F g).norm_integral_le σ

private theorem diff_joiningCorrelation₃ {n : ℕ}
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z)
    (c : ℂ) (g : Fin n → G) :
    joiningCorrelation₃ T τ f F (H.sub (BoundedObservable.const c)) g =
      joiningCorrelation₃ T τ f F H g - joiningCorrelation T σ f F g * c := by
  let := hτ.probability
  let v := joiningTest T f F g
  let vc := v.comp Prod.fst (measurable_fst (β := Z))
  let C : BoundedObservable ((X × Y) × Z) := BoundedObservable.const c
  change (∫ w, v w.1 * (H w.2 - c) ∂τ) =
    (∫ w, v w.1 * H w.2 ∂τ) - (∫ w, v w ∂σ) * c
  simp_rw [mul_sub]
  have hfirst : Integrable (fun w : (X × Y) × Z => v w.1 * H w.2) τ :=
    (joiningTest₃ T f F H g).integrable τ
  have hsecond : Integrable (fun w : (X × Y) × Z => v w.1 * c) τ :=
    (vc.mul C).integrable τ
  rw [integral_sub hfirst hsecond]
  rw [integral_mul_const, v.integral_comp_of_preserving hτ.fst]
  rfl

private theorem joiningCorrelation₃_empty
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    (hDisjoint : Disjoint S R) (f : Fin 0 → BoundedObservable X)
    (F : BoundedObservable Y) (H : BoundedObservable Z) (g : Fin 0 → G) :
    joiningCorrelation₃ T τ f F H g =
      joiningCorrelation T σ f F g * ∫ z, H z ∂R.measure := by
  let idR : FactorMap R R := ⟨id, MeasurePreserving.id _, fun _ => rfl⟩
  have hmap := hDisjoint _ (hτ.map hσ.sndFactor idR)
  have hπ : MeasurePreserving (fun w : (X × Y) × Z => (w.1.2, w.2))
      τ (S.measure.prod R.measure) :=
    ⟨measurable_snd.comp measurable_fst |>.prodMk measurable_snd, hmap⟩
  let φ := (F.comp Prod.fst (measurable_fst (β := Z))).mul
    (H.comp Prod.snd (measurable_snd (α := Y)))
  have h₃ := φ.integral_comp_of_preserving hπ
  have h₂ := F.integral_comp_of_preserving hσ.snd
  simpa [joiningCorrelation₃, joiningCorrelation, joiningTest₃,
    joiningTest, translatedProduct, φ, h₂, integral_prod_mul] using h₃

private def orbitPair (T : System G X) (d : G) (f : BoundedObservable X) :
    BoundedObservable X :=
  f.conjugate.mul (T.translated d f)

private def joiningShift {n : ℕ}
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z)
    (a : G) (g : Fin n → G) : BoundedObservable ((X × Y) × Z) :=
  (joiningTest₃ T f F H g).comp (hσ.system.prodAct R a⁻¹)
    (hτ.invariant a⁻¹).measurable

private theorem act_mul_at {M : Type*} [MeasurableSpace M]
    (Q : System G M) (g h : G) (x : M) : Q.act (g * h) x = Q.act g (Q.act h x) :=
  congrFun (Q.act_mul g h) x

private theorem joiningShift_first
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    {n : ℕ} (f : Fin (n + 1) → BoundedObservable X)
    (F : BoundedObservable Y) (H : BoundedObservable Z) (a : G) (g : Fin n → G) :
    (∫ w, f 0 w.1.1 * joiningShift hτ (Fin.tail f) F H a g w ∂τ) =
      joiningCorrelation₃ T τ f F H (Fin.cons a g) := by
  change _ = ∫ w, joiningTest₃ T f F H (Fin.cons a g) w ∂τ
  rw [← (joiningTest₃ T f F H (Fin.cons a g)).integral_comp_of_preserving
    (hτ.invariant a⁻¹)]
  congr 1
  funext w
  simp only [joiningShift, joiningTest₃, joiningTest, translatedProduct, IsJoining.system,
    System.prodAct, BoundedObservable.comp_apply, BoundedObservable.prod_apply,
    BoundedObservable.mul_apply, System.translated_apply, Prod.map_fst, Prod.map_snd]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail, ← act_mul_at, mul_inv_cancel,
    T.act_one, id_eq]
  ring

private theorem joiningShift_pair
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    {n : ℕ} (f : Fin n → BoundedObservable X)
    (F : BoundedObservable Y) (H : BoundedObservable Z) (r t : G) (g : Fin n → G) :
    (∫ w, conj (joiningShift hτ f F H r g w) * joiningShift hτ f F H t g w ∂τ) =
      joiningCorrelation₃ T τ (fun i => orbitPair T (t⁻¹ * r) (f i))
        (orbitPair S (t⁻¹ * r) F) (orbitPair R (t⁻¹ * r) H) g := by
  let v := (joiningShift hτ f F H r g).conjugate.mul (joiningShift hτ f F H t g)
  change (∫ w, v w ∂τ) = _
  rw [← v.integral_comp_of_preserving (hτ.invariant r)]
  unfold joiningCorrelation₃
  congr 1
  funext w
  simp only [v, joiningShift, joiningTest₃, joiningTest, translatedProduct, orbitPair,
    IsJoining.system, System.prodAct, BoundedObservable.comp_apply, BoundedObservable.conjugate_apply,
    BoundedObservable.prod_apply, BoundedObservable.mul_apply, System.translated_apply,
    Prod.map_fst, Prod.map_snd, ← act_mul_at, inv_mul_cancel,
    T.act_one, S.act_one, R.act_one, id_eq]
  simp only [map_mul, map_prod, Finset.prod_mul_distrib]
  have hcomm (i : Fin n) :
      T.act ((t⁻¹ * r) * g i) w.1.1 = T.act (g i * (t⁻¹ * r)) w.1.1 := by
    rw [mul_comm (t⁻¹ * r)]
  simp only [hcomm]
  ring

private theorem tendsto_orbitPair_mean_zero
    {R : System G Z} {U : Set (Ultrafilter G)} (hMix : HasMixingCorrelations R U)
    {p : Ultrafilter G} (hp : p ∈ U) (H : BoundedObservable Z)
    (hMean : ∫ z, H z ∂R.measure = 0) (r : G) :
    Tendsto (fun t => ∫ z, orbitPair R (t⁻¹ * r) H z ∂R.measure)
      (p : Filter G) (𝓝 0) := by
  let Hr := R.translated r H
  have h := (Complex.continuous_conj.tendsto _).comp (hMix p hp Hr H)
  have heq (t : G) :
      conj (∫ z, conj (Hr z) * H (R.act t z) ∂R.measure) =
        ∫ z, orbitPair R (t⁻¹ * r) H z ∂R.measure := by
    rw [← (orbitPair R (t⁻¹ * r) H).integral_comp_of_preserving (R.preserves t)]
    rw [← integral_conj]
    congr 1
    funext z
    have hact : R.act (t⁻¹ * r) (R.act t z) = R.act r z := calc
      _ = R.act ((t⁻¹ * r) * t) z := congrFun (R.act_mul _ _).symm z
      _ = _ := by rw [mul_comm t⁻¹ r, mul_assoc, inv_mul_cancel, mul_one]
    simp only [orbitPair, Hr, BoundedObservable.mul_apply, BoundedObservable.conjugate_apply,
      System.translated_apply, map_mul, starRingEnd_self_apply, hact]
    exact mul_comm _ _
  simpa only [Function.comp_def, heq, hMean, mul_zero, map_zero] using h

/-- Factorization of the ordered scalar ultralimits of the joining correlations in Lemma 11.
The indices are ordered from the outermost limit to the innermost limit. -/
theorem tendsto_joiningCorrelation₃
    {T : System G X} {S : System G Y} {R : System G Z}
    {σ : Measure (X × Y)} {τ : Measure ((X × Y) × Z)}
    {hσ : IsJoining T S σ} (hτ : IsJoining hσ.system R τ)
    {U : Set (Ultrafilter G)} (hMix : HasMixingCorrelations R U) (hDisjoint : Disjoint S R)
    {n : ℕ} (p : Fin n → Ultrafilter G) (hp : ∀ i, p i ∈ U)
    (f : Fin n → BoundedObservable X) (F : BoundedObservable Y) (H : BoundedObservable Z) :
    Tendsto (joiningCorrelation₃ T τ f F H) (coordinateUltrafilter p : Filter _)
      (𝓝 (scalarUltralimit (coordinateUltrafilter p) (joiningCorrelation T σ f F) *
        ∫ z, H z ∂R.measure)) := by
  let := hσ.probability
  let := hτ.probability
  induction n generalizing F H with
  | zero =>
    have h := (tendsto_scalarUltralimit (coordinateUltrafilter p)
      (norm_joiningCorrelation_le T σ f F)).mul
      (tendsto_const_nhds (x := ∫ z, H z ∂R.measure))
    convert h using 1
    funext g
    exact joiningCorrelation₃_empty hτ hDisjoint f F H g
  | succ n ih =>
    let w := coordinateUltrafilter (fun i : Fin n => p i.succ)
    let c := ∫ z, H z ∂R.measure
    let H₀ := H.sub (BoundedObservable.const c)
    have hMean : ∫ z, H₀ z ∂R.measure = 0 := by
      have hH : Integrable (fun z => H z) R.measure := H.integrable _
      have hC : Integrable (fun _ : Z => c) R.measure := integrable_const c
      change (∫ z, H z - c ∂R.measure) = 0
      rw [integral_sub hH hC]
      simp [c]
    have centered : Tendsto (joiningCorrelation₃ T τ f F H₀)
        (coordinateUltrafilter p : Filter _) (𝓝 0) := by
      let Y₀ := (f 0).conjugate.comp (fun v : (X × Y) × Z => v.1.1)
        (measurable_fst.comp measurable_fst)
      let y (_ : Fin n → G) := Y₀.l2 τ
      let x (a : G) (g : Fin n → G) := (joiningShift hτ (Fin.tail f) F H₀ a g).l2 τ
      have hx (a : G) (g : Fin n → G) :
          ‖x a g‖ ≤ (∏ i : Fin n, (f i.succ).bound) * F.bound * H₀.bound :=
        (joiningShift hτ (Fin.tail f) F H₀ a g).norm_l2_le τ
      have hy (g : Fin n → G) : ‖y g‖ ≤ (f 0).bound := Y₀.norm_l2_le τ
      let A (v : G × G) :=
        scalarUltralimit w (joiningCorrelation T σ
          (fun i => orbitPair T (v.2⁻¹ * v.1) (f i.succ)) (orbitPair S (v.2⁻¹ * v.1) F))
      let B (v : G × G) := ∫ z, orbitPair R (v.2⁻¹ * v.1) H₀ z ∂R.measure
      have hA (v : G × G) :
          ‖A v‖ ≤ (∏ i : Fin n, (f i.succ).bound * (f i.succ).bound) * (F.bound * F.bound) :=
        norm_scalarUltralimit_le w (norm_joiningCorrelation_le T σ _ _)
      have hAB : Tendsto (fun v => A v * B v)
          (fubiniUltrafilter (p 0) (p 0) : Filter _) (𝓝 0) := by
        apply tendsto_fubiniUltrafilter (g := fun _ => 0) _ tendsto_const_nhds
        intro r
        exact Filter.isBoundedUnder_le_mul_tendsto_zero
          ⟨_, eventually_map.mpr (Eventually.of_forall fun t => hA (r, t))⟩
          (tendsto_orbitPair_mean_zero hMix (hp 0) H₀ hMean r)
      have hPair : Tendsto (fun v : (G × G) × (Fin n → G) =>
          inner ℂ (x v.1.1 v.2) (x v.1.2 v.2))
          (fubiniUltrafilter (fubiniUltrafilter (p 0) (p 0)) w : Filter _) (𝓝 0) := by
        apply tendsto_fubiniUltrafilter (g := fun v => A v * B v) _ hAB
        intro v
        simp only [x, BoundedObservable.inner_l2, joiningShift_pair]
        exact ih (Fin.tail p) (fun i => hp i.succ)
          (fun i => orbitPair T (v.2⁻¹ * v.1) (f i.succ))
          (orbitPair S (v.2⁻¹ * v.1) F) (orbitPair R (v.2⁻¹ * v.1) H₀)
      have hVdc := tendsto_inner_zero_of_fubini_correlations_first (p 0) w x y hx hy hPair
      rw [coordinateUltrafilter, Ultrafilter.coe_map, tendsto_map'_iff]
      simpa only [x, y, Y₀, w, BoundedObservable.inner_l2, BoundedObservable.comp_apply,
        BoundedObservable.conjugate_apply, starRingEnd_self_apply, joiningShift_first,
        Function.comp_def]
        using hVdc
    have hProd := (tendsto_scalarUltralimit (coordinateUltrafilter p)
      (norm_joiningCorrelation_le T σ f F)).mul (tendsto_const_nhds (x := c))
    have hTotal := centered.add hProd
    simpa only [H₀, diff_joiningCorrelation₃ hτ, sub_add_cancel, zero_add, c] using hTotal

end Joining

end Mixing
