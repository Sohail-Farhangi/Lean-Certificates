/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CompactHomogeneousSkew
public import Mixing.CompactMeasurableSection
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Measurable coordinates for compact principal extensions -/

@[expose] public section
noncomputable section

namespace Mixing

open Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {Y K : Type*} [Group K] [MeasurableSpace Y] [MeasurableSpace K] [MeasurableMul₂ K]

/-- Haar averaging forces a probability on the product which is invariant
under all fibre right translations to be the product of its marginal and Haar. -/
theorem principalExtension_measure_eq_prod_of_rightInvariant
    (ν : Measure (Y × K)) [IsProbabilityMeasure ν]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    (hInv : ∀ r : K, MeasurePreserving (fun z : Y × K ↦ (z.1, z.2 * r)) ν ν) :
    ν = ν.fst.prod m := by
  let A : (Y × K) × K → Y × K := fun w ↦ (w.1.1, w.1.2 * w.2)
  let F : (Y × K) × K → (Y × K) × K := fun w ↦ (w.1, w.1.2 * w.2)
  let T : (Y × K) × K → Y × K := Prod.map Prod.fst id
  have hF : MeasurePreserving F (ν.prod m) (ν.prod m) :=
    measurePreserving_left_shear ν m Prod.snd measurable_snd
  have hT : MeasurePreserving T (ν.prod m) (ν.fst.prod m) :=
    (MeasurePreserving.mk measurable_fst rfl).prod (MeasurePreserving.id m)
  have hA : MeasurePreserving A (ν.prod m) (ν.fst.prod m) := hT.comp hF
  rw [← hA.map_eq]
  ext U hU
  rw [Measure.map_apply hA.measurable hU,
    Measure.prod_apply_symm (hA.measurable hU)]
  have hsection (r : K) : ν ((fun z : Y × K ↦ (z, r)) ⁻¹' (A ⁻¹' U)) = ν U :=
    (hInv r).measure_preimage hU.nullMeasurableSet
  simp_rw [hsection]
  simp

section Extension

variable {G X R : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace R]
  [MeasurableInv K] [MulAction K X] [MeasurableSMul₂ K X]
variable (E : System G X) (B : System G Y) (π : FactorMap E B)

/-- Free transitive compact-group fibres with a measurable section give a
Haar skew-product model, with its cocycle and equivariant factor map constructed. -/
theorem principalExtension_exists_skewCoordinates [StandardBorelSpace (Y × K)] [StandardBorelSpace X]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m]
    (s : Y → X) (hs : Measurable s) (hsπ : RightInverse s π.toFun)
    (hπ : ∀ k : K, ∀ x : X, π.toFun (k • x) = π.toFun x)
    (hFree : ∀ x : X, Injective (fun k : K ↦ k • x))
    (hTrans : ∀ x y : X, π.toFun x = π.toFun y → ∃ k : K, k • x = y)
    (hPres : ∀ k : K, MeasurePreserving (fun x : X ↦ k • x) E.measure E.measure)
    (hAct : ∀ (g : G) (k : K) (x : X), E.act g (k • x) = k • E.act g x) :
    ∃ (c : MeasurableSkewCocycle (K := K) B) (e : Y × K ≃ᵐ X)
      (F : FactorMap (compactGroupSkewSystem B c m) E), F.toFun = e ∧
        (∀ (y : Y) (k : K), π.toFun (e (y, k)) = y) ∧
        (∀ (y : Y) (k r : K), e (y, k * r) = r⁻¹ • e (y, k)) := by
  let f : Y × K → X := fun w ↦ w.2⁻¹ • s w.1
  have hf : Measurable f := measurable_snd.inv.smul (hs.comp measurable_fst)
  have hfπ (w : Y × K) : π.toFun (f w) = w.1 := (hπ _ _).trans (hsπ w.1)
  have hinj : Injective f := by
    rintro ⟨y, k⟩ ⟨y', k'⟩ he
    have hy : y = y' := ((hfπ _).symm.trans (congrArg π.toFun he)).trans (hfπ _)
    subst y'
    exact Prod.ext rfl (inv_injective (hFree (s y) he))
  have hsurj : Surjective f := by
    intro x
    obtain ⟨k, hk⟩ := hTrans (s (π.toFun x)) x (hsπ _)
    exact ⟨(π.toFun x, k⁻¹), by change (k⁻¹)⁻¹ • s (π.toFun x) = x; rwa [inv_inv]⟩
  let e₀ := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have he₀ : Measurable e₀.symm := (hf.measurableEmbedding hinj).measurable_comp_iff.mp (by
    change Measurable (e₀ ∘ e₀.symm)
    rw [Equiv.self_comp_symm]
    exact measurable_id)
  let e : Y × K ≃ᵐ X := ⟨e₀, hf, he₀⟩
  have e_apply (w : Y × K) : e w = w.2⁻¹ • s w.1 := rfl
  have e_first (x : X) : (e.symm x).1 = π.toFun x := by
    have h : π.toFun (e (e.symm x)) = (e.symm x).1 := hfπ _
    rw [e.apply_symm_apply] at h
    exact h.symm
  let ν := E.measure.map e.symm
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff
    e.symm.measurable.aemeasurable).mpr E.probability
  have hR (r : K) : MeasurePreserving (fun w : Y × K ↦ (w.1, w.2 * r)) ν ν := by
    let R : Y × K → Y × K := fun w ↦ (w.1, w.2 * r)
    have hRm : Measurable R := measurable_fst.prodMk (measurable_snd.mul_const r)
    have heq : R ∘ e.symm = e.symm ∘ (fun x : X ↦ r⁻¹ • x) := by
      funext x
      apply e.injective
      change e ((e.symm x).1, (e.symm x).2 * r) = e (e.symm (r⁻¹ • x))
      rw [e.apply_symm_apply, e_apply, mul_inv_rev, mul_smul]
      change r⁻¹ • e (e.symm x) = r⁻¹ • x
      rw [e.apply_symm_apply]
    refine ⟨hRm, ?_⟩
    change (E.measure.map e.symm).map R = E.measure.map e.symm
    rw [Measure.map_map hRm e.symm.measurable, heq, ← Measure.map_map e.symm.measurable
      (hPres r⁻¹).measurable, (hPres r⁻¹).map_eq]
  have hνfst : ν.fst = B.measure := by
    change (E.measure.map e.symm).map Prod.fst = B.measure
    rw [Measure.map_map measurable_fst e.symm.measurable, show Prod.fst ∘ e.symm = π.toFun
      from funext e_first, π.preserves.map_eq]
  have hν : ν = B.measure.prod m :=
    (principalExtension_measure_eq_prod_of_rightInvariant ν m hR).trans (by rw [hνfst])
  have hEmp : MeasurePreserving e (B.measure.prod m) E.measure := by
    refine ⟨e.measurable, ?_⟩
    rw [← hν]
    change (E.measure.map e.symm).map e = E.measure
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  let c (g : G) (y : Y) := (e.symm (E.act g (s y))).2
  have hc (g : G) (y : Y) : e (B.act g y, c g y) = E.act g (s y) := by
    have he : (e.symm (E.act g (s y))).1 = B.act g y := by
      rw [e_first]
      exact (congrFun (π.equivariant g) (s y)).trans (congrArg (B.act g) (hsπ y))
    have hp : (B.act g y, c g y) = e.symm (E.act g (s y)) := Prod.ext he.symm rfl
    rw [hp, e.apply_symm_apply]
  let cc : MeasurableSkewCocycle (K := K) B := {
    toFun := c
    measurable := fun g ↦ measurable_snd.comp (e.symm.measurable.comp ((E.preserves g).measurable.comp hs))
    one := fun y ↦ by
      have he : e (B.act 1 y, c 1 y) = e (y, (1 : K)) := by
        rw [hc, E.act_one, e_apply]
        simp
      exact congrArg Prod.snd (e.injective he)
    mul := fun g h y ↦ by
      have he : e (B.act (g * h) y, c (g * h) y) =
          e (B.act g (B.act h y), c g (B.act h y) * c h y) := by
        rw [hc, E.act_mul, Function.comp_apply, ← hc h y]
        rw [e_apply, hAct, ← hc g (B.act h y), e_apply, e_apply, mul_inv_rev, mul_smul]
      exact congrArg Prod.snd (e.injective he) }
  refine ⟨cc, e, ⟨e, hEmp, ?_⟩, rfl, fun y k ↦ hfπ (y, k), ?_⟩
  · intro g
    funext w
    change e (B.act g w.1, c g w.1 * w.2) = E.act g (e w)
    rw [e_apply, e_apply, hAct, ← hc g w.1, e_apply, mul_inv_rev, mul_smul]
  · intro y k r
    rw [e_apply, e_apply, mul_inv_rev, mul_smul]

/-- A compact principal extension of a base disjoint from a weakly mixing
system is itself disjoint from that system. -/
theorem principalExtension_disjoint_of_weakMixing [Countable G]
    [MetricSpace X] [CompactSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [BorelSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace (Y × K)] [StandardBorelSpace (R × (Y × K))]
    (m : Measure K) [IsProbabilityMeasure m] [IsMulLeftInvariant m] [IsMulRightInvariant m]
    (hcont : Continuous π.toFun) (hsurj : Surjective π.toFun)
    (hπ : ∀ k : K, ∀ x : X, π.toFun (k • x) = π.toFun x)
    (hFree : ∀ x : X, Injective (fun k : K ↦ k • x))
    (hTrans : ∀ x y : X, π.toFun x = π.toFun y → ∃ k : K, k • x = y)
    (hPres : ∀ k : K, MeasurePreserving (fun x : X ↦ k • x) E.measure E.measure)
    (hAct : ∀ (g : G) (k : K) (x : X), E.act g (k • x) = k • E.act g x)
    (S : System G R) (hWeak : IsWeaklyMixing S.koopmanZeroRep) (hB : Disjoint S B) :
    Disjoint S E := by
  obtain ⟨s, hs, hsπ⟩ := exists_measurable_section_of_continuous_compact π.toFun hcont hsurj
  obtain ⟨c, _, F, _⟩ := principalExtension_exists_skewCoordinates E B π m s hs hsπ hπ hFree hTrans hPres hAct
  let : Nonempty R := nonempty_of_isProbabilityMeasure S.measure
  let : Nonempty (Y × K) := nonempty_of_isProbabilityMeasure (compactGroupSkewSystem B c m).measure
  exact F.disjoint_target_of_disjoint_source (disjoint_compactGroupSkew_of_weakMixing B c m S hWeak hB)

end Extension

end Mixing
