module

public import Mixing.RigidRepresentations
public import Mixing.GeneratedClosure

@[expose] public section

noncomputable section

namespace Mixing

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

universe u

variable {G : Type*} {X : Type u} [CommGroup G] [MeasurableSpace X]

private theorem norm_mul_l2_le (μ : Measure X) [IsFiniteMeasure μ] (f h : BoundedObservable X) :
    ‖(f.mul h).l2 μ‖ ≤ f.bound * ‖h.l2 μ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(f.mul h).coe_l2 μ, h.coe_l2 μ] with x hx hy
  rw [hx, hy, BoundedObservable.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (f.norm_le x) (norm_nonneg _)

private theorem dist_mul_l2_le (μ : Measure X) [IsFiniteMeasure μ]
    (f f₀ h h₀ : BoundedObservable X) :
    dist ((f.mul h).l2 μ) ((f₀.mul h₀).l2 μ) ≤
      f.bound * dist (h.l2 μ) (h₀.l2 μ) + h₀.bound * dist (f.l2 μ) (f₀.l2 μ) := by
  let a := f.mul (h.sub h₀)
  let b := h₀.mul (f.sub f₀)
  have he : (f.mul h).l2 μ - (f₀.mul h₀).l2 μ = a.l2 μ + b.l2 μ := by
    rw [← BoundedObservable.l2_sub, ← BoundedObservable.l2_add]
    apply Lp.ext
    filter_upwards [((f.mul h).sub (f₀.mul h₀)).coe_l2 μ, (a.add b).coe_l2 μ] with x hx hy
    rw [hx, hy]
    change f x * h x - f₀ x * h₀ x = f x * (h x - h₀ x) + h₀ x * (f x - f₀ x)
    ring
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, he]
  apply (norm_add_le _ _).trans
  have ha := norm_mul_l2_le μ f (h.sub h₀)
  have hb := norm_mul_l2_le μ h₀ (f.sub f₀)
  rw [BoundedObservable.l2_sub] at ha hb
  exact add_le_add ha hb

private theorem System.koopman_l2_translated (S : System G X) (g : G) (f : BoundedObservable X) :
    S.koopmanRep g (f.l2 S.measure) = (S.translated g f).l2 S.measure :=
  Lp.ext ((S.koopman_ae_observable g f).trans ((S.translated g f).coe_l2 S.measure).symm)

private theorem System.ultrafilter_fixed_mul (S : System G X) (p : Ultrafilter G)
    (f h : BoundedObservable X)
    (hf : ultrafilterOperator S.koopmanRep p (f.l2 S.measure) = f.l2 S.measure)
    (hh : ultrafilterOperator S.koopmanRep p (h.l2 S.measure) = h.l2 S.measure) :
    ultrafilterOperator S.koopmanRep p ((f.mul h).l2 S.measure) = (f.mul h).l2 S.measure := by
  have h₁ := tendsto_orbit_of_ultrafilter_fixed S.koopmanRep p (f.l2 S.measure) hf
  have h₂ := tendsto_orbit_of_ultrafilter_fixed S.koopmanRep p (h.l2 S.measure) hh
  have h₁' := tendsto_iff_dist_tendsto_zero.mp h₁
  have h₂' := tendsto_iff_dist_tendsto_zero.mp h₂
  have hlim : Tendsto (fun g ↦ S.koopmanRep g ((f.mul h).l2 S.measure)) (p : Filter G)
      (𝓝 ((f.mul h).l2 S.measure)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hUpper (g : G) : dist (S.koopmanRep g ((f.mul h).l2 S.measure)) ((f.mul h).l2 S.measure) ≤
        f.bound * dist (S.koopmanRep g (h.l2 S.measure)) (h.l2 S.measure) +
          h.bound * dist (S.koopmanRep g (f.l2 S.measure)) (f.l2 S.measure) := by
      rw [S.koopman_l2_translated g (f.mul h), S.koopman_l2_translated g h, S.koopman_l2_translated g f]
      have he : (S.translated g (f.mul h)).l2 S.measure =
          ((S.translated g f).mul (S.translated g h)).l2 S.measure := by
        apply Lp.ext
        exact ((S.translated g (f.mul h)).coe_l2 S.measure).trans
          (((S.translated g f).mul (S.translated g h)).coe_l2 S.measure).symm
      rw [he]
      simpa only [System.translated_bound] using
        dist_mul_l2_le S.measure (S.translated g f) f (S.translated g h) h
    apply squeeze_zero (fun _ ↦ dist_nonneg) hUpper
    have hd := ((tendsto_const_nhds (x := f.bound)).mul h₂').add
      ((tendsto_const_nhds (x := h.bound)).mul h₁')
    simpa only [mul_zero, add_zero] using hd
  apply ext_inner_left ℂ
  intro k
  exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff S.koopmanRep p k _)
    (((InnerProductSpace.toDual ℂ _ k).continuous.tendsto _).comp hlim)

private theorem System.ultrafilter_fixed_finsetProd {ι : Type*} (S : System G X) (p : Ultrafilter G)
    (s : Finset ι) (f : ι → BoundedObservable X)
    (hf : ∀ i ∈ s, ultrafilterOperator S.koopmanRep p ((f i).l2 S.measure) = (f i).l2 S.measure) :
    ultrafilterOperator S.koopmanRep p ((BoundedObservable.prod s f).l2 S.measure) =
      (BoundedObservable.prod s f).l2 S.measure := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : (BoundedObservable.prod ∅ f).l2 S.measure = constantOne S.measure := by
      apply Lp.ext
      filter_upwards [(BoundedObservable.prod ∅ f).coe_l2 S.measure,
        Lp.coeFn_const (p := 2) (μ := S.measure) (1 : ℂ)] with x hx hy
      change constantOne S.measure x = _ at hy
      rw [hx, hy, BoundedObservable.prod_apply, Finset.prod_empty]
      rfl
    rw [he, S.ultrafilterOperator_constantOne]
  | insert i s hi hs =>
    have he : (BoundedObservable.prod (insert i s) f).l2 S.measure =
        ((f i).mul (BoundedObservable.prod s f)).l2 S.measure := by
      apply Lp.ext
      filter_upwards [(BoundedObservable.prod (insert i s) f).coe_l2 S.measure,
        ((f i).mul (BoundedObservable.prod s f)).coe_l2 S.measure] with x hx hy
      rw [hx, hy, BoundedObservable.prod_apply, BoundedObservable.mul_apply,
        BoundedObservable.prod_apply, Finset.prod_insert hi]
    rw [he]
    exact S.ultrafilter_fixed_mul p _ _ (hf i (Finset.mem_insert_self i s))
      (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- For an idempotent ultrafilter, singleton generation forces the Koopman
ultrafilter operator to be the identity. -/
theorem System.ultrafilterOperator_eq_one_of_generated_idempotent (S : System G X)
    (p : Ultrafilter G) (hp : p * p = p) (hGen : S.IsUGenerated {p}) :
    ultrafilterOperator S.koopmanRep p = 1 := by
  let A := ultrafilterOperator S.koopmanRep p
  let W := (A - 1).ker
  have hprod : S.generatedProducts {p} ⊆ (W : Set (Lp ℂ 2 S.measure)) := by
    rintro _ ⟨n, q, f, hq, rfl⟩
    change A ((S.ultrafilterProduct q f).l2 S.measure) - (S.ultrafilterProduct q f).l2 S.measure = 0
    apply sub_eq_zero.mpr
    apply S.ultrafilter_fixed_finsetProd
    intro i _
    have he : q i = p := hq i
    rw [he, S.l2_ultrafilterTranslate]
    change (A * A) _ = A _
    rw [← ultrafilterOperator_mul, hp]
  have hsub : Submodule.span ℂ (S.generatedProducts {p}) ≤ W := Submodule.span_le.mpr hprod
  have hcl := closure_minimal (show _ ⊆ (W : Set (Lp ℂ 2 S.measure)) from hsub)
    (A - 1).isClosed_ker
  change Dense (Submodule.span ℂ (S.generatedProducts {p}) : Set (Lp ℂ 2 S.measure)) at hGen
  rw [hGen.closure_eq] at hcl
  apply sub_eq_zero.mp
  exact ContinuousLinearMap.ext fun x ↦ (hcl (mem_univ x) : (A - 1) x = 0)

/-- Theorem 1.1(iii). Separability is used for the single rigidity sequence
of the generated factor. -/
theorem theorem1_1_iii [Countable G] (S : System G X) [SeparableSpace (Lp ℂ 2 S.measure)] :
    IsMildlyMixing S.koopmanZeroRep ↔
      ∀ (Y : Type u) [MeasurableSpace Y] (T : System G Y),
        IsRigidRepresentation T.koopmanRep → Disjoint S T := by
  constructor
  · intro h _ _ T hT
    exact disjoint_rigid_of_mildlyMixing S T h hT
  · intro hdis
    apply (isMildlyMixing_iff_isUMixing_freeIdempotents S.koopmanZeroRep).mpr
    intro p hp
    let T := S.generatedFactor {p}
    let F := S.generatedFactorMap {p}
    have hT := T.ultrafilterOperator_eq_one_of_generated_idempotent p hp.2 (lemma8 S {p})
    let _ : SecondCountableTopology (Lp ℂ 2 T.measure) :=
      F.pullback.isometry.isEmbedding.secondCountableTopology
    have hRigid := isRigidRepresentation_of_ultrafilterOperator_eq_one T.koopmanRep p hp.1 hT
    by_contra hn
    have hnMix : ¬ S.IsUMixing {p} := fun h ↦ hn (h p (mem_singleton p))
    obtain ⟨B, hB, h₀, h₁⟩ := S.generatedFactor_nontrivial_of_not_isUMixing hnMix
    exact F.not_disjoint_of_event hB h₀ h₁ (hdis _ T hRigid)

end Mixing
