/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.Core
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# A weakly compact representation on the WAP subspace

For a representation by contractions, the vectors with weakly relatively
compact orbit form an invariant subspace. The restricted representation
has compact weak-operator closure by the product of these compact orbit
closures and the closed equations defining linearity.
-/

@[expose] public section

namespace JdLG

open Set

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The weak closure of one vector orbit. -/
noncomputable def weakVectorOrbit (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Set (WeakSpace 𝕜 E) :=
  closure (range fun s ↦ toWeakSpace 𝕜 E (ρ s x))

/-- A vector has relatively weakly compact orbit. -/
def IsWapVector (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) : Prop :=
  IsCompact (weakVectorOrbit ρ x)

theorem IsWapVector.zero (ρ : S →ₙ* (E →L[𝕜] E)) : IsWapVector ρ (0 : E) := by
  have hc : IsCompact ({0} : Set (WeakSpace 𝕜 E)) := isCompact_singleton
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ isClosed_singleton)
  rintro _ ⟨s, rfl⟩
  simp

theorem IsWapVector.add {ρ : S →ₙ* (E →L[𝕜] E)} {x y : E}
    (hx : IsWapVector ρ x) (hy : IsWapVector ρ y) : IsWapVector ρ (x + y) := by
  let f : WeakSpace 𝕜 E × WeakSpace 𝕜 E → WeakSpace 𝕜 E := fun p ↦ p.1 + p.2
  have hc := (hx.prod hy).image (show Continuous f from continuous_fst.add continuous_snd)
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨s, rfl⟩
  refine ⟨(toWeakSpace 𝕜 E (ρ s x), toWeakSpace 𝕜 E (ρ s y)),
    ⟨subset_closure (mem_range_self s), subset_closure (mem_range_self s)⟩, ?_⟩
  simp only [f, map_add]

theorem IsWapVector.smul {ρ : S →ₙ* (E →L[𝕜] E)} {x : E}
    (hx : IsWapVector ρ x) (c : 𝕜) : IsWapVector ρ (c • x) := by
  have hc := hx.image (show Continuous ((c • ·) : WeakSpace 𝕜 E → WeakSpace 𝕜 E) from
    continuous_id.const_smul c)
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨s, rfl⟩
  exact ⟨toWeakSpace 𝕜 E (ρ s x), subset_closure (mem_range_self s), by simp only [map_smul]⟩

/-- The subspace consisting of all weakly almost periodic vectors for an
operator representation. -/
def wapVectorSubmodule (ρ : S →ₙ* (E →L[𝕜] E)) : Submodule 𝕜 E where
  carrier := {x | IsWapVector ρ x}
  zero_mem' := IsWapVector.zero ρ
  add_mem' := IsWapVector.add
  smul_mem' c _ hx := hx.smul c

theorem IsWapVector.map {ρ : S →ₙ* (E →L[𝕜] E)} {x : E}
    (hx : IsWapVector ρ x) (s : S) : IsWapVector ρ (ρ s x) := by
  refine hx.of_isClosed_subset isClosed_closure (closure_mono ?_)
  rintro _ ⟨t, rfl⟩
  refine ⟨t * s, ?_⟩
  change toWeakSpace 𝕜 E (ρ (t * s) x) = toWeakSpace 𝕜 E (ρ t (ρ s x))
  rw [map_mul]
  rfl

theorem continuous_weakLinearAction (T : E →L[𝕜] E) :
    Continuous (fun w : WeakSpace 𝕜 E ↦ toWeakSpace 𝕜 E (T ((toWeakSpace 𝕜 E).symm w))) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  exact WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (f.comp T)

theorem image_weakVectorOrbit_subset (ρ : S →ₙ* (E →L[𝕜] E)) (x : E) (s : S) :
    (fun w : WeakSpace 𝕜 E ↦ toWeakSpace 𝕜 E (ρ s ((toWeakSpace 𝕜 E).symm w))) ''
        weakVectorOrbit ρ x ⊆ weakVectorOrbit ρ x := by
  rintro _ ⟨w, hw, rfl⟩
  apply closure_minimal _ (isClosed_closure.preimage (continuous_weakLinearAction (ρ s))) hw
  rintro _ ⟨t, rfl⟩
  apply subset_closure
  refine ⟨s * t, ?_⟩
  change toWeakSpace 𝕜 E (ρ (s * t) x) =
    toWeakSpace 𝕜 E (ρ s ((toWeakSpace 𝕜 E).symm (toWeakSpace 𝕜 E (ρ t x))))
  rw [LinearEquiv.symm_apply_apply, map_mul]
  rfl

theorem IsWapVector.of_mem_weakVectorOrbit {ρ : S →ₙ* (E →L[𝕜] E)} {x y : E}
    (hx : IsWapVector ρ x) (hy : toWeakSpace 𝕜 E y ∈ weakVectorOrbit ρ x) :
    IsWapVector ρ y := by
  refine hx.of_isClosed_subset isClosed_closure (closure_minimal ?_ isClosed_closure)
  rintro _ ⟨s, rfl⟩
  apply image_weakVectorOrbit_subset ρ x s
  refine ⟨toWeakSpace 𝕜 E y, hy, ?_⟩
  change toWeakSpace 𝕜 E (ρ s ((toWeakSpace 𝕜 E).symm (toWeakSpace 𝕜 E y))) =
    toWeakSpace 𝕜 E (ρ s y)
  rw [LinearEquiv.symm_apply_apply]

/-- The original operators restricted to the WAP subspace. -/
def wapVectorRepresentation (ρ : S →ₙ* (E →L[𝕜] E)) :
    S →ₙ* (wapVectorSubmodule ρ →L[𝕜] wapVectorSubmodule ρ) where
  toFun s := (ρ s).restrict fun {x} hx ↦ IsWapVector.map hx s
  map_mul' s t := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (s * t) (x : E) = ρ s (ρ t (x : E))
    rw [map_mul]
    rfl

theorem wapVectorRepresentation_all_orbits (ρ : S →ₙ* (E →L[𝕜] E))
    (x : wapVectorSubmodule ρ) : IsWapVector (wapVectorRepresentation ρ) x := by
  let V := wapVectorSubmodule ρ
  let C := weakVectorOrbit ρ (x : E)
  let : CompactSpace C := isCompact_iff_compactSpace.1 x.property
  let f (y : C) : WeakSpace 𝕜 V := toWeakSpace 𝕜 V
    ⟨(toWeakSpace 𝕜 E).symm y.val, IsWapVector.of_mem_weakVectorOrbit x.property
      (by simpa only [LinearEquiv.apply_symm_apply] using y.property)⟩
  have hc : Continuous f := by
    apply WeakBilin.continuous_of_continuous_eval
    intro m
    obtain ⟨m', hm', -⟩ := exists_extension_norm_eq V m
    have hm : Continuous (fun y : C ↦ m' ((toWeakSpace 𝕜 E).symm y.val)) :=
      (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip m').comp continuous_subtype_val
    refine hm.congr fun y ↦ ?_
    change m' ((toWeakSpace 𝕜 E).symm y.val) = m ((toWeakSpace 𝕜 V).symm (f y))
    simpa only [f, LinearEquiv.symm_apply_apply] using hm' ((toWeakSpace 𝕜 V).symm (f y))
  have hr := isCompact_range hc
  refine hr.of_isClosed_subset isClosed_closure (closure_minimal ?_ hr.isClosed)
  rintro _ ⟨s, rfl⟩
  refine ⟨⟨toWeakSpace 𝕜 E (ρ s (x : E)), subset_closure (mem_range_self s)⟩, ?_⟩
  apply congrArg (toWeakSpace 𝕜 V)
  apply Subtype.ext
  exact (toWeakSpace 𝕜 E).symm_apply_apply _

theorem isClosed_weak_norm_le (r : ℝ) :
    IsClosed {w : WeakSpace 𝕜 E | ‖(toWeakSpace 𝕜 E).symm w‖ ≤ r} := by
  have heq : {w : WeakSpace 𝕜 E | ‖(toWeakSpace 𝕜 E).symm w‖ ≤ r} =
      ⋂ f : StrongDual 𝕜 E, ⋂ (_ : ‖f‖ ≤ 1), {w | ‖f ((toWeakSpace 𝕜 E).symm w)‖ ≤ r} := by
    ext w
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h f hf
      refine (f.le_opNorm _).trans ?_
      exact ((mul_le_mul_of_nonneg_right hf (norm_nonneg _)).trans_eq (one_mul _)).trans h
    · intro h
      obtain ⟨f, hf, hf'⟩ := exists_dual_vector'' 𝕜 ((toWeakSpace 𝕜 E).symm w)
      have hz := h f hf
      simpa only [hf', RCLike.norm_ofReal, abs_norm] using hz
  rw [heq]
  exact isClosed_iInter fun f ↦ isClosed_iInter fun _ ↦
    isClosed_le (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).norm continuous_const

/-- Pointwise weak relative compactness of a contraction representation
gives relative compactness in the weak operator topology. -/
theorem compact_weakOperatorClosure_of_wap (ρ : S →ₙ* (E →L[𝕜] E))
    (hρ : ∀ s, ‖ρ s‖ ≤ 1) (hw : ∀ x, IsWapVector ρ x) :
    IsCompact (weakOperatorClosure ρ : Set (E →WOT[𝕜] E)) := by
  let addEq (x y : E) : Set (E → WeakSpace 𝕜 E) := {u | u (x + y) = u x + u y}
  let smulEq (c : 𝕜) (x : E) : Set (E → WeakSpace 𝕜 E) := {u | u (c • x) = c • u x}
  let equations := (⋂ x, ⋂ y, addEq x y) ∩ (⋂ c, ⋂ x, smulEq c x)
  let good := Set.pi Set.univ (weakVectorOrbit ρ) ∩ equations
  have hEq : IsClosed equations :=
    (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))).inter
      (isClosed_iInter fun c ↦ isClosed_iInter fun x ↦
        isClosed_eq (continuous_apply (c • x)) ((continuous_apply x).const_smul c))
  have hc : IsCompact good := (isCompact_univ_pi hw).inter_right hEq
  have hbound (u : good) (x : E) : ‖(toWeakSpace 𝕜 E).symm (u.val x)‖ ≤ ‖x‖ := by
    apply closure_minimal _ (isClosed_weak_norm_le ‖x‖) (u.property.1 x (mem_univ x))
    rintro _ ⟨s, rfl⟩
    change ‖(toWeakSpace 𝕜 E).symm (toWeakSpace 𝕜 E (ρ s x))‖ ≤ ‖x‖
    rw [LinearEquiv.symm_apply_apply]
    simpa only [one_mul] using (ρ s).le_of_opNorm_le (hρ s) x
  let linear (u : good) : E →ₗ[𝕜] E :=
    { toFun := fun x ↦ (toWeakSpace 𝕜 E).symm (u.val x)
      map_add' := fun x y ↦ by
        have h : u.val (x + y) = u.val x + u.val y :=
          mem_iInter.1 (mem_iInter.1 u.property.2.1 x) y
        rw [h, map_add]
      map_smul' := fun c x ↦ by
        have h : u.val (c • x) = c • u.val x :=
          mem_iInter.1 (mem_iInter.1 u.property.2.2 c) x
        rw [h, map_smul]
        rfl }
  let operator (u : good) : E →WOT[𝕜] E :=
    ContinuousLinearMapWOT.ofCLM ((linear u).mkContinuous 1 (fun x ↦ by
      change ‖(toWeakSpace 𝕜 E).symm (u.val x)‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact hbound u x))
  have hcont : Continuous operator := by
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro x f
    exact (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).comp
      ((continuous_apply x).comp continuous_subtype_val)
  let : CompactSpace good := isCompact_iff_compactSpace.1 hc
  have hr := isCompact_range hcont
  refine hr.of_isClosed_subset isClosed_closure (closure_minimal ?_ hr.isClosed)
  rintro _ ⟨s, rfl⟩
  let u (x : E) := toWeakSpace 𝕜 E (ρ s x)
  have hu : u ∈ good := by
    refine ⟨fun x _ ↦ subset_closure (mem_range_self s), ?_, ?_⟩
    · exact mem_iInter.2 fun x ↦ mem_iInter.2 fun y ↦ by
        change u (x + y) = u x + u y
        simp only [u, map_add]
    · exact mem_iInter.2 fun c ↦ mem_iInter.2 fun x ↦ by
        change u (c • x) = c • u x
        simp only [u, map_smul]
  refine ⟨⟨u, hu⟩, ?_⟩
  apply ContinuousLinearMapWOT.toCLM_injective
  apply ContinuousLinearMap.ext
  intro x
  exact (toWeakSpace 𝕜 E).symm_apply_apply _

theorem compact_weakOperatorClosure_wapVectorRepresentation (ρ : S →ₙ* (E →L[𝕜] E))
    (hρ : ∀ s, ‖ρ s‖ ≤ 1) :
    IsCompact (weakOperatorClosure (wapVectorRepresentation ρ) :
      Set ((wapVectorSubmodule ρ) →WOT[𝕜] (wapVectorSubmodule ρ))) := by
  apply compact_weakOperatorClosure_of_wap _ _ (wapVectorRepresentation_all_orbits ρ)
  intro s
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  exact (ρ s).le_of_opNorm_le (hρ s) (x : E)

end JdLG
