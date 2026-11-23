/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.ReversibleOrbitFunctions
public import JdLG.ReversibleUnitaryRestriction
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Matrix coefficients of the reversible action -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace JdLG

section Definitions

variable {S 𝕜 E F : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The finite-sum uniform matrix-coefficient approximation in equation (5). -/
def WeaklyContained (ρ : S →ₙ* (E →L[𝕜] E)) (σ : S →ₙ* (F →L[𝕜] F)) : Prop :=
  ∀ (x : E) (f : StrongDual 𝕜 E) (ε : ℝ), 0 < ε →
    ∃ coefficients : List (F × StrongDual 𝕜 F), ∀ s : S,
      ‖f (ρ s x) - (coefficients.map (fun z ↦ z.2 (σ s z.1))).sum‖ < ε

/-- Weak equivalence means weak containment in both directions. -/
def WeaklyEquivalent (ρ : S →ₙ* (E →L[𝕜] E)) (σ : S →ₙ* (F →L[𝕜] F)) : Prop :=
  WeaklyContained ρ σ ∧ WeaklyContained σ ρ

theorem WeaklyContained.comp {T : Type*} [Semigroup T]
    {ρ : S →ₙ* (E →L[𝕜] E)} {σ : S →ₙ* (F →L[𝕜] F)} (h : WeaklyContained ρ σ)
    (i : T →ₙ* S) : WeaklyContained (ρ.comp i) (σ.comp i) := by
  intro x f ε hε
  obtain ⟨l, hl⟩ := h x f ε hε
  exact ⟨l, fun t ↦ hl (i t)⟩

theorem WeaklyEquivalent.comp {T : Type*} [Semigroup T]
    {ρ : S →ₙ* (E →L[𝕜] E)} {σ : S →ₙ* (F →L[𝕜] F)} (h : WeaklyEquivalent ρ σ)
    (i : T →ₙ* S) : WeaklyEquivalent (ρ.comp i) (σ.comp i) :=
  ⟨h.1.comp i, h.2.comp i⟩

end Definitions

section Approximation

variable {G 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]

private def leftTranslate (g : G) (f : C(G, 𝕜)) : C(G, 𝕜) :=
  ⟨fun t ↦ f (g * t), f.continuous.comp (continuous_const_mul g)⟩

/-- The value of each right translate at the identity is uniformly approximated by
one bounded functional on Haar L², given by averaging over a neighborhood of the identity. -/
theorem exists_dual_approx_rightTranslate (f : C(G, 𝕜)) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : StrongDual 𝕜 (HaarL2 G 𝕜), ∀ g : G,
      ‖L (continuousToHaarL2 (𝕜 := 𝕜) (rightTranslate g f)) - f g‖ < ε := by
  let μ := normalizedHaar G
  have hleft : Continuous fun t ↦ leftTranslate t f := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp (continuous_fst.mul continuous_snd)
  let s : Set G := (fun t ↦ leftTranslate t f) ⁻¹' Metric.ball f (ε / 2)
  have hso : IsOpen s := Metric.isOpen_ball.preimage hleft
  have h1 : 1 ∈ s := by
    change leftTranslate 1 f ∈ Metric.ball f (ε / 2)
    have heq : leftTranslate 1 f = f := by ext g; simp [leftTranslate]
    rw [heq]
    exact Metric.mem_ball_self (by positivity)
  have hsμ : μ s ≠ ∞ := measure_ne_top μ s
  have hμnz : μ s ≠ 0 := (hso.measure_pos μ ⟨1, h1⟩).ne'
  have hc : 0 < μ.real s :=
    lt_of_le_of_ne measureReal_nonneg ((measureReal_ne_zero_iff hsμ).2 hμnz).symm
  let L : StrongDual 𝕜 (HaarL2 G 𝕜) :=
    (μ.real s)⁻¹ • innerSL 𝕜 (indicatorConstLp 2 hso.measurableSet hsμ (1 : 𝕜))
  refine ⟨L, fun g ↦ ?_⟩
  let F := rightTranslate g f
  have havg : L (continuousToHaarL2 (𝕜 := 𝕜) F) = (μ.real s)⁻¹ • ∫ t in s, F t ∂μ := by
    change (μ.real s)⁻¹ •
        inner 𝕜 (indicatorConstLp 2 hso.measurableSet hsμ (1 : 𝕜))
          (continuousToHaarL2 (𝕜 := 𝕜) F) = _
    rw [L2.inner_indicatorConstLp_one]
    apply congrArg ((μ.real s)⁻¹ • ·)
    exact setIntegral_congr_ae hso.measurableSet
      ((continuousToHaarL2_coeFn (𝕜 := 𝕜) F).mono fun _ h _ ↦ h)
  have hconst : ∫ _ in s, f g ∂μ = μ.real s • f g := by
    rw [integral_const, measureReal_restrict_apply_univ]
  have hFi : IntegrableOn F s μ :=
    (F.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have hclose (t : G) (ht : t ∈ s) : ‖F t - f g‖ ≤ ε / 2 :=
    (ContinuousMap.norm_coe_le_norm (leftTranslate t f - f) g).trans
      (le_of_lt (by simpa only [s, mem_preimage, Metric.mem_ball, dist_eq_norm] using ht))
  have hnorm := norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 hsμ) hclose
  have heq : L (continuousToHaarL2 (𝕜 := 𝕜) F) - f g =
      (μ.real s)⁻¹ • (∫ t in s, (F t - f g) ∂μ) := by
    rw [havg, integral_sub hFi (integrableOn_const hsμ), hconst, smul_sub, ← mul_smul,
      inv_mul_cancel₀ hc.ne', one_smul]
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
  calc
    (μ.real s)⁻¹ * ‖∫ t in s, (F t - f g) ∂μ‖ ≤ (μ.real s)⁻¹ * (μ.real s * (ε / 2)) :=
      mul_le_mul_of_nonneg_left (hnorm.trans_eq (mul_comm _ _)) (inv_nonneg.mpr hc.le)
    _ = ε / 2 := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ < ε := by linarith

end Approximation

section WeakEquivalence

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Isometric orbit maps that are continuous on a dense set are continuous everywhere. -/
theorem continuous_orbit_of_isometricApprox {X H : Type*} [TopologicalSpace X]
    [PseudoMetricSpace H] (A : X → H → H) (hA : ∀ a, Isometry (A a)) (x : H)
    (ha : ∀ δ > 0, ∃ y : H, dist x y < δ ∧ Continuous fun a ↦ A a y) :
    Continuous fun a ↦ A a x := by
  apply continuous_iff_continuousAt.2
  intro a
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨y, hy, hyc⟩ := ha (ε / 3) (by positivity)
  filter_upwards [Metric.tendsto_nhds.1 hyc.continuousAt (ε / 3) (by positivity)] with b hb
  calc
    dist (A b x) (A a x) ≤ dist (A b x) (A b y) + dist (A b y) (A a y) +
        dist (A a y) (A a x) := by
      exact (dist_triangle _ (A a y) _).trans
        (add_le_add_left (dist_triangle _ (A b y) _) _)
    _ = dist x y + dist (A b y) (A a y) + dist y x := by rw [(hA b).dist_eq, (hA a).dist_eq]
    _ < ε := by rw [dist_comm y x]; linarith

/-- The continuous-linear operators underlying a unitary representation. -/
def unitaryAsLinearRep {S H : Type*} [Semigroup S] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (U : S →ₙ* (H ≃ₗᵢ[𝕜] H)) : S →ₙ* (H →L[𝕜] H) where
  toFun g := (U g).toContinuousLinearEquiv.toContinuousLinearMap
  map_mul' g h := by
    ext x
    change U (g * h) x = U g (U h x)
    rw [map_mul]
    rfl

/-- The Banach-space assertion of Theorem 3.6 on the compact group. In Haar L²
take the closed linear span of all matrix-coefficient functions and restrict right
translation to this invariant subspace. -/
theorem weaklyEquivalent_unitary_of_compact_group
    (ρ : G →* (E →L[𝕜] E)) (hρ : ∀ x, Continuous fun g ↦ ρ g x)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ g, ‖ρ g‖ ≤ C) :
    ∃ V : Submodule 𝕜 (HaarL2 G 𝕜), IsClosed (V : Set (HaarL2 G 𝕜)) ∧
      ∃ U : G →* (V ≃ₗᵢ[𝕜] V),
        WeaklyEquivalent ρ.toMulHom (unitaryAsLinearRep U.toMulHom) ∧
          ∀ v : V, Continuous fun g ↦ U g v := by
  let μ := normalizedHaar G
  let P := continuousToHaarL2 (𝕜 := 𝕜) (G := G) (F := 𝕜)
  let F (f : StrongDual 𝕜 E) : E →L[𝕜] C(G, 𝕜) :=
    (ContinuousLinearMap.compLeftContinuous 𝕜 G f).comp (orbitFunctionMap ρ hρ C hC hbound)
  let J (f : StrongDual 𝕜 E) : E →L[𝕜] HaarL2 G 𝕜 := P.comp (F f)
  let D : Submodule 𝕜 (HaarL2 G 𝕜) := ⨆ f, (J f).range
  let V := D.topologicalClosure
  let R := haarRightTranslation (G := G) (𝕜 := 𝕜) (F := 𝕜)
  have hj (f : StrongDual 𝕜 E) (g : G) (x : E) : R g (J f x) = J f (ρ g x) := by
    have h : rightTranslate g (F f x) = F f (ρ g x) := by
      apply ContinuousMap.ext
      intro t
      change f (ρ (t * g) x) = f (ρ t (ρ g x))
      rw [map_mul]
      rfl
    exact (haarRightTranslation_toLp (𝕜 := 𝕜) g (F f x)).trans (congrArg P h)
  have hD (g : G) : Set.MapsTo (R g) (D : Set (HaarL2 G 𝕜)) D := by
    intro d hd
    refine Submodule.iSup_induction (fun f ↦ (J f).range)
      (motive := fun a ↦ R g a ∈ D) hd ?_ ?_ ?_
    · rintro f _ ⟨x, rfl⟩
      exact Submodule.mem_iSup_of_mem f ⟨ρ g x, (hj f g x).symm⟩
    · simpa only [map_zero] using D.zero_mem
    · intro a b ha hb
      simpa only [map_add] using D.add_mem ha hb
  have hV : UnitaryInvariant R V := fun g ↦ (hD g).closure (R g).continuous
  let U := unitarySubmoduleAction R V hV
  have hclosed : IsClosed (V : Set (HaarL2 G 𝕜)) := D.isClosed_topologicalClosure
  let : CompleteSpace V := hclosed.completeSpace_coe
  have hDV : D ≤ V := D.le_topologicalClosure
  have hjmem (f : StrongDual 𝕜 E) (x : E) : J f x ∈ D :=
    Submodule.mem_iSup_of_mem f ⟨x, rfl⟩
  have happrox (v : V) (δ : ℝ) (hδ : 0 < δ) :
      ∃ d ∈ D, dist (v : HaarL2 G 𝕜) d < δ := Metric.mem_closure_iff.1 v.2 δ hδ
  refine ⟨V, hclosed, U, ⟨?_, ?_⟩, ?_⟩
  · intro x f ε hε
    obtain ⟨L, hL⟩ := exists_dual_approx_rightTranslate (F f x) ε hε
    let y : V := ⟨J f x, hDV (hjmem f x)⟩
    refine ⟨[(y, L.comp V.subtypeL)], fun g ↦ ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    change ‖f (ρ g x) - L (R g (J f x))‖ < ε
    rw [norm_sub_rev, show R g (J f x) = P (rightTranslate g (F f x)) from
      haarRightTranslation_toLp g (F f x)]
    exact hL g
  · intro v f ε hε
    let δ := ε / (‖f‖ + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨d, hd, hvd⟩ := happrox v δ hδ
    let y : V := ⟨d, hDV hd⟩
    let fext : StrongDual 𝕜 (HaarL2 G 𝕜) := f.comp V.orthogonalProjectionOnto
    have hfext (w : V) : fext (w : HaarL2 G 𝕜) = f w := by
      change f (V.orthogonalProjectionOnto (w : HaarL2 G 𝕜)) = f w
      rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    have hlist (d' : HaarL2 G 𝕜) (hd' : d' ∈ D) :
        ∃ l : List (E × StrongDual 𝕜 E), ∀ g,
          fext (R g d') = (l.map (fun z ↦ z.2 (ρ g z.1))).sum := by
      refine Submodule.iSup_induction (fun a ↦ (J a).range)
        (motive := fun y ↦ ∃ l : List (E × StrongDual 𝕜 E), ∀ g,
          fext (R g y) = (l.map (fun z ↦ z.2 (ρ g z.1))).sum) hd' ?_ ?_ ?_
      · rintro a _ ⟨x, rfl⟩
        exact ⟨[(x, fext.comp (J a))], fun g ↦ by simp [hj]⟩
      · exact ⟨[], fun _ ↦ by simp⟩
      · intro a b ha hb
        obtain ⟨l₁, hl₁⟩ := ha
        obtain ⟨l₂, hl₂⟩ := hb
        exact ⟨l₁ ++ l₂, fun g ↦ by simp [hl₁ g, hl₂ g]⟩
    obtain ⟨l, hl⟩ := hlist d hd
    refine ⟨l, fun g ↦ ?_⟩
    change ‖f (U g v) - (l.map (fun z ↦ z.2 (ρ g z.1))).sum‖ < ε
    rw [← hl g, show R g d = (U g y : HaarL2 G 𝕜) from rfl, hfext]
    rw [← map_sub, ← map_sub]
    have hvdy : ‖v - y‖ < δ := by
      change ‖(v : HaarL2 G 𝕜) - d‖ < δ
      rwa [← dist_eq_norm]
    calc
      ‖f (U g (v - y))‖ ≤ ‖f‖ * ‖U g (v - y)‖ := f.le_opNorm _
      _ = ‖f‖ * ‖v - y‖ := by rw [(U g).norm_map]
      _ ≤ (‖f‖ + 1) * ‖v - y‖ := by gcongr; linarith
      _ < (‖f‖ + 1) * δ := mul_lt_mul_of_pos_left hvdy (by positivity)
      _ = ε := by dsimp [δ]; field_simp
  · intro v
    have hDle : D ≤ P.range := iSup_le fun f ↦ by
      rintro _ ⟨x, rfl⟩
      exact ⟨F f x, rfl⟩
    have hv : Continuous fun g ↦ R g (v : HaarL2 G 𝕜) := by
      apply continuous_orbit_of_isometricApprox (fun g ↦ R g) (fun g ↦ (R g).isometry)
      intro δ hδ
      obtain ⟨d, hd, hvd⟩ := happrox v δ hδ
      obtain ⟨f, rfl⟩ := hDle hd
      refine ⟨P f, hvd, ?_⟩
      simp_rw [show ∀ g, R g (P f) = P (rightTranslate g f) from fun g ↦
        haarRightTranslation_toLp g f]
      exact P.continuous.comp (continuous_rightTranslate f)
    exact hv.subtype_mk _

end WeakEquivalence


end JdLG
