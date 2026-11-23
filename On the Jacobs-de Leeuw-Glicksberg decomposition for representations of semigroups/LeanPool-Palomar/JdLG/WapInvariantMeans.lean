/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

public import JdLG.WapCompactification
public import JdLG.GroupAdmissibility
public import JdLG.AmenableGroup
public import JdLG.PaperExamplesWapClosed

/-! # Invariant means on real weakly almost periodic functions -/

@[expose] public section

open Set MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction Topology

namespace JdLG

section Transfer

variable {S : Type*} [Semigroup S] [TopologicalSpace S] [SeparatelyContinuousMul S]

local notation "WAP" => weaklyAlmostPeriodicSubmodule (S := S)
local notation "T" => WapCompactification S
local notation "ι" => toWapCompactification (S := S)
local notation "CL" => fun t : T ↦ continuous_const_mul t
local notation "CR" => fun t : T ↦ continuous_mul_const t

/-- A positive normalized linear functional on the real WAP functions, with
translation invariance stated separately. -/
structure WapPositiveMean (S : Type*) [Semigroup S] [TopologicalSpace S]
    [SeparatelyContinuousMul S] where
  functional : (weaklyAlmostPeriodicSubmodule (S := S)) →ₗ[ℝ] ℝ
  monotone' : ∀ f g, (∀ s : S, f.val s ≤ g.val s) → functional f ≤ functional g
  one' : functional ⟨1, isWap_one⟩ = 1

namespace WapPositiveMean

/-- Left translation invariance on WAP tests. -/
def IsLeftInvariant (m : WapPositiveMean S) : Prop :=
  ∀ (s : S) (f g : WAP), (∀ t, g.val t = f.val (s * t)) → m.functional g = m.functional f

/-- Right translation invariance on WAP tests. -/
def IsRightInvariant (m : WapPositiveMean S) : Prop :=
  ∀ (s : S) (f g : WAP), (∀ t, g.val t = f.val (t * s)) → m.functional g = m.functional f

@[ext] theorem ext {m n : WapPositiveMean S} (h : m.functional = n.functional) : m = n := by
  cases m
  cases n
  cases h
  rfl

end WapPositiveMean

/-- Forget the invariance properties of a WAP mean. -/
def WapBiInvariantMean.toPositiveMean (m : WapBiInvariantMean (S := S)) : WapPositiveMean S :=
  ⟨m.functional, m.monotone', m.one'⟩

theorem WapBiInvariantMean.toPositiveMean_leftInvariant (m : WapBiInvariantMean (S := S)) :
    m.toPositiveMean.IsLeftInvariant := m.left'

theorem WapBiInvariantMean.toPositiveMean_rightInvariant (m : WapBiInvariantMean (S := S)) :
    m.toPositiveMean.IsRightInvariant := m.right'

variable [Nonempty S]

/-- Extension of a WAP function as a continuous test on the compactification. -/
noncomputable def compactWapExtension : WAP →ₗ[ℝ] C_c(T, ℝ) where
  toFun f := compactRealFunction (extendWap f) (extendWap f).continuous
  map_add' f g := CompactlySupportedContinuousMap.ext fun t ↦
    DFunLike.congr_fun (map_add (wapCompactificationLinearIso (S := S)).symm f g) t
  map_smul' c f := CompactlySupportedContinuousMap.ext fun t ↦
    DFunLike.congr_fun (map_smul (wapCompactificationLinearIso (S := S)).symm c f) t

@[simp] theorem restrictWap_compactWapExtension (f : WAP) :
    restrictWap (compactWapExtension f).toContinuousMap = f :=
  (wapCompactificationLinearIso (S := S)).apply_symm_apply f

theorem compactWapExtension_one :
    compactWapExtension (⟨1, isWap_one⟩ : WAP) =
      compactRealFunction (fun _ : T ↦ 1) continuous_const := by
  have h := extendWap_unique (⟨1, isWap_one⟩ : WAP)
    (⟨fun _ : T ↦ 1, continuous_const⟩ : C(T, ℝ)) (fun _ ↦ rfl)
  exact CompactlySupportedContinuousMap.ext fun t ↦ (DFunLike.congr_fun h t).symm

/-- Restrict a two-sided compact-space mean to the original WAP functions. -/
noncomputable def LeftInvariantContinuousMean.toWapMean (m : LeftInvariantContinuousMean CL)
    (hm : m.IsRightInvariant CR) : WapBiInvariantMean (S := S) where
  functional := m.functional.toLinearMap.comp compactWapExtension
  monotone' f g h :=
    m.functional.monotone' fun t ↦ denseRange_toWapCompactification.induction_on t
      (isClosed_le (extendWap f).continuous (extendWap g).continuous)
      (fun s ↦ h s)
  one' := by
    change m.functional (compactWapExtension ⟨1, isWap_one⟩) = 1
    rw [compactWapExtension_one, m.normalized]
  left' s f g h := by
    have he : compactWapExtension g = compactRealFunction
        (fun t ↦ extendWap f (ι s * t)) ((extendWap f).continuous.comp (continuous_const_mul _)) :=
      CompactlySupportedContinuousMap.ext fun t ↦
        (DFunLike.congr_fun (extendWap_unique g
          ⟨fun t ↦ extendWap f (ι s * t), (extendWap f).continuous.comp (continuous_const_mul _)⟩
          (fun u ↦ by change extendWap f (ι s * ι u) = g.val u
                      rw [← map_mul, extendWap_toWapCompactification, h u])) t).symm
    change m.functional (compactWapExtension g) = m.functional (compactWapExtension f)
    rw [he]
    exact m.translate (ι s) (compactWapExtension f)
  right' s f g h := by
    have he : compactWapExtension g = compactRealFunction
        (fun t ↦ extendWap f (t * ι s)) ((extendWap f).continuous.comp (continuous_mul_const _)) :=
      CompactlySupportedContinuousMap.ext fun t ↦
        (DFunLike.congr_fun (extendWap_unique g
          ⟨fun t ↦ extendWap f (t * ι s), (extendWap f).continuous.comp (continuous_mul_const _)⟩
          (fun u ↦ by change extendWap f (ι u * ι s) = g.val u
                      rw [← map_mul, extendWap_toWapCompactification, h u])) t).symm
    change m.functional (compactWapExtension g) = m.functional (compactWapExtension f)
    rw [he]
    exact hm (ι s) (compactWapExtension f)

/-- A positive WAP functional acts on the compact space by restricting its tests. -/
noncomputable def WapPositiveMean.toCompactFunctional (m : WapPositiveMean S) :
    C_c(T, ℝ) →ₚ[ℝ] ℝ where
  toFun f := m.functional (restrictWap f.toContinuousMap)
  map_add' f g := by
    change m.functional (restrictWap (f.toContinuousMap + g.toContinuousMap)) = _
    rw [map_add, map_add]
  map_smul' c f := by
    change m.functional (restrictWap (c • f.toContinuousMap)) = _
    rw [map_smul, map_smul]
    rfl
  monotone' _ _ h := m.monotone' _ _ fun s ↦ h (ι s)

theorem WapPositiveMean.toCompactFunctional_one (m : WapPositiveMean S) :
    m.toCompactFunctional (compactRealFunction (fun _ : T ↦ 1) continuous_const) = 1 := by
  rw [← compactWapExtension_one]
  change m.functional (restrictWap (compactWapExtension ⟨1, isWap_one⟩).toContinuousMap) = 1
  rw [restrictWap_compactWapExtension, m.one']

variable [MeasurableSpace (WapCompactification S)] [BorelSpace (WapCompactification S)]

/-- Left invariance passes to the compactification. -/
noncomputable def WapPositiveMean.toCompactLeftMean (m : WapPositiveMean S)
    (hm : m.IsLeftInvariant) : LeftInvariantContinuousMean CL where
  functional := m.toCompactFunctional
  normalized := m.toCompactFunctional_one
  translate a f := by
    refine MeasuredMean.continuousFunctional_translate_of_dense ι m.toCompactFunctional
      m.toCompactFunctional_one (· * ·) CR CL denseRange_toWapCompactification ?_ a f
    intro s g
    apply hm s
    intro u
    change g (ι s * ι u) = g (ι (s * u))
    rw [map_mul ι]

/-- Right invariance passes to the compactification. -/
theorem WapPositiveMean.toCompactFunctional_right (m : WapPositiveMean S)
    (hm : m.IsRightInvariant) (a : T) (f : C_c(T, ℝ)) :
    m.toCompactFunctional (compactRealFunction (fun b ↦ f (b * a))
      (f.continuous.comp (continuous_mul_const a))) = m.toCompactFunctional f := by
  refine MeasuredMean.continuousFunctional_translate_of_dense ι m.toCompactFunctional
    m.toCompactFunctional_one (fun a b ↦ b * a) CL CR denseRange_toWapCompactification ?_ a f
  intro s g
  apply hm s
  intro u
  change g (ι u * ι s) = g (ι (u * s))
  rw [map_mul ι]

end Transfer

section CompactificationMeans

variable {S : Type*} [Semigroup S] [TopologicalSpace S] [SeparatelyContinuousMul S] [Nonempty S]

local notation "T" => WapCompactification S
local notation "CL" => fun t : T ↦ continuous_const_mul t
local notation "CR" => fun t : T ↦ continuous_mul_const t

omit [Nonempty S] in
private theorem completeSpace_wapEvaluationVectorSubmodule :
    CompleteSpace (wapVectorSubmodule (wapEvaluationAction (S := S))) := by
  apply (isClosed_wapVectorSubmodule (wapEvaluationAction (S := S)) ?_).completeSpace_coe
  intro s
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [one_mul, Prod.norm_def]
  refine max_le (le_trans (a.2.norm_coe_le_norm s) (le_max_right _ _)) ?_
  exact (BoundedContinuousFunction.norm_compContinuous_le _ _).trans (le_max_right _ _)

/-- Separate left and right invariant means on the WAP space yield a
bi-invariant WAP mean, and conversely the bi-invariant mean supplies both. -/
theorem wapBiInvariantMean_iff_left_and_right :
    Nonempty (WapBiInvariantMean (S := S)) ↔
      (∃ m : WapPositiveMean S, m.IsLeftInvariant) ∧
      (∃ m : WapPositiveMean S, m.IsRightInvariant) := by
  refine ⟨fun ⟨m⟩ ↦ ⟨⟨m.toPositiveMean, m.toPositiveMean_leftInvariant⟩,
    ⟨m.toPositiveMean, m.toPositiveMean_rightInvariant⟩⟩, ?_⟩
  rintro ⟨⟨m, hm⟩, ⟨r, hr⟩⟩
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  obtain ⟨b, hb⟩ := exists_biInvariantMean_of_left_and_right (m.toCompactLeftMean hm)
    r.toCompactFunctional r.toCompactFunctional_one (r.toCompactFunctional_right hr)
  exact ⟨b.toWapMean hb⟩

/-- Bi-invariance exists on WAP exactly when the weakly almost periodic
compactification has a compact group ideal. -/
theorem wapBiInvariantMean_iff_groupIdeal :
    Nonempty (WapBiInvariantMean (S := S)) ↔ ∃ K : GroupIdeal T, IsCompact K.carrier := by
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  constructor
  · intro ⟨m⟩
    let mT := m.toContinuousMean toWapCompactification continuous_toWapCompactification
      denseRange_toWapCompactification
    exact mT.exists_compact_groupIdeal_of_biInvariant
      (m.toContinuousMean_rightInvariant toWapCompactification continuous_toWapCompactification
        denseRange_toWapCompactification)
  · rintro ⟨K, hK⟩
    let : CompleteSpace (wapVectorSubmodule (wapEvaluationAction (S := S))) :=
      completeSpace_wapEvaluationVectorSubmodule
    obtain ⟨m, hm⟩ := K.exists_biInvariantMean hK
      (K.isTopologicalGroup_of_isCompact hK) (hleft := CL) (hright := CR)
    exact ⟨m.toWapMean hm⟩

/-- In the presence of a compact group ideal, a left-invariant WAP mean is
unique. Each such functional integrates the extension against Haar on the ideal. -/
theorem wapPositiveMean_leftInvariant_unique_of_groupIdeal (K : GroupIdeal T)
    (hK : IsCompact K.carrier) {m n : WapPositiveMean S}
    (hm : m.IsLeftInvariant) (hn : n.IsLeftInvariant) : m = n := by
  let : MeasurableSpace T := borel T
  let : BorelSpace T := ⟨rfl⟩
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K.carrier := borel K.carrier
  let : BorelSpace K.carrier := ⟨rfl⟩
  let : CompleteSpace (wapVectorSubmodule (wapEvaluationAction (S := S))) :=
    completeSpace_wapEvaluationVectorSubmodule
  let : IsTopologicalGroup K.carrier := K.isTopologicalGroup_of_isCompact hK
  let j : K.carrier →ₙ* T := ⟨Subtype.val, fun _ _ ↦ rfl⟩
  have hAbsorb (t : T) : ∃ g : K.carrier, j g = j 1 * t :=
    ⟨⟨K.identity * t, K.mul_mem_right K.identity_mem t⟩, rfl⟩
  have hValue (m : WapPositiveMean S) (hm : m.IsLeftInvariant)
      (f : weaklyAlmostPeriodicSubmodule (S := S)) :
      m.functional f = ∫ g : K.carrier, (extendWap f) g.val ∂normalizedHaar K.carrier := by
    have h := (m.toCompactLeftMean hm).apply_eq_groupIdealHaar j continuous_subtype_val
      Subtype.val_injective hAbsorb (compactWapExtension f)
    change m.functional (restrictWap (compactWapExtension f).toContinuousMap) =
      ∫ g : K.carrier, (extendWap f) g.val ∂normalizedHaar K.carrier at h
    simpa only [restrictWap_compactWapExtension] using h
  apply WapPositiveMean.ext
  exact DFunLike.ext _ _ fun f ↦ (hValue m hm f).trans (hValue n hn f).symm

/-- Whenever a WAP bi-invariant mean exists, it is the only left-invariant WAP mean. -/
theorem wapPositiveMean_leftInvariant_unique_of_biInvariant (b : WapBiInvariantMean (S := S))
    {m : WapPositiveMean S} (hm : m.IsLeftInvariant) : m = b.toPositiveMean := by
  obtain ⟨K, hK⟩ := (wapBiInvariantMean_iff_groupIdeal (S := S)).mp ⟨b⟩
  exact wapPositiveMean_leftInvariant_unique_of_groupIdeal K hK hm
    b.toPositiveMean_leftInvariant

/-- A semigroup has at most one bi-invariant mean on its real WAP functions. -/
theorem wapBiInvariantMean_unique (m n : WapBiInvariantMean (S := S)) : m = n := by
  have h := wapPositiveMean_leftInvariant_unique_of_biInvariant n m.toPositiveMean_leftInvariant
  have h₁ := congrArg WapPositiveMean.functional h
  cases m
  cases n
  cases h₁
  rfl

end CompactificationMeans

section Group

variable (G : Type*) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

local notation "T" => WapCompactification G
local notation "ι" => toWapCompactification (S := G)

/-- The WAP compactification of a group has a unique minimal idempotent. -/
theorem wapCompactification_existsUnique_minimalIdempotent_of_group :
    ∃! e : T, IsMinimalIdempotent e := by
  let e : T := ι 1
  have hLeft (t : T) : e * t = t :=
    denseRange_toWapCompactification.induction_on t
      (isClosed_eq (continuous_const_mul e) continuous_id)
      (fun g ↦ by change ι 1 * ι g = ι g; rw [← map_mul, one_mul])
  have hRight (t : T) : t * e = t :=
    denseRange_toWapCompactification.induction_on t
      (isClosed_eq (continuous_mul_const e) continuous_id)
      (fun g ↦ by change ι g * ι 1 = ι g; rw [← map_mul, mul_one])
  let : Monoid T :=
    { (inferInstance : Semigroup T) with
      one := e
      one_mul := hLeft
      mul_one := hRight
      npow := @npowRec T ⟨e⟩ (inferInstance)
      npow_zero := fun _ ↦ rfl
      npow_succ := fun _ _ ↦ rfl }
  let j : G →* T :=
    { ι with
      map_one' := rfl }
  exact existsUnique_minimalIdempotent_of_denseGroup j denseRange_toWapCompactification

/-- Every topological group has a unique bi-invariant mean on its real
weakly almost periodic functions. Only separate continuity of multiplication is used. -/
theorem existsUnique_wapBiInvariantMean_of_group :
    ∃! m : WapBiInvariantMean (S := G), m.toPositiveMean.IsLeftInvariant := by
  obtain ⟨m⟩ := (wapBiInvariantMean_iff_groupIdeal (S := G)).mpr
    (exists_compact_groupIdeal_of_existsUnique_minimalIdempotent continuous_mul_const
      (wapCompactification_existsUnique_minimalIdempotent_of_group G))
  exact ⟨m, m.toPositiveMean_leftInvariant, fun n _ ↦ wapBiInvariantMean_unique n m⟩

/-- The bi-invariant WAP mean is also the unique left-invariant WAP mean of
a topological group. -/
theorem existsUnique_wapPositiveMean_leftInvariant_of_group :
    ∃! m : WapPositiveMean G, m.IsLeftInvariant := by
  obtain ⟨m, _, _⟩ := existsUnique_wapBiInvariantMean_of_group G
  exact ⟨m.toPositiveMean, m.toPositiveMean_leftInvariant, fun n hn ↦
    wapPositiveMean_leftInvariant_unique_of_biInvariant m hn⟩

end Group

end JdLG
