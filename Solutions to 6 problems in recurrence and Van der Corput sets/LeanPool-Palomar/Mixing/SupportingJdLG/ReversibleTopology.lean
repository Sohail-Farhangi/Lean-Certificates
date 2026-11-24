/-
Adapted from the Apache-2.0 Lean certificate for arXiv:2509.24003v3
by Sohail Farhangi, in the Lean-Certificates repository.
This copy changes local imports and isolates its namespaces.
-/
module

public import Mixing.SupportingJdLG.ReversibleAction

/-! # Group operations on the compact operator ideal -/

@[expose] public section

open Filter Set Topology

namespace Mixing.JdLGBridge

section Orbits

variable {G 𝕜 E : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [SeparatelyContinuousMul G] [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- Weak and norm convergence agree on the compact norm orbit. -/
theorem continuous_normOrbit_of_wot (A : G →ₙ* (E →L[𝕜] E))
    (hA : Continuous fun a ↦ ContinuousLinearMapWOT.ofCLM (A a)) (x : E) :
    Continuous fun a ↦ A a x := by
  let orbit := range fun a ↦ A a x
  have hO : IsCompact orbit := isCompact_normOrbit_of_wot A hA x
  have hweak : Continuous fun a ↦ toWeakSpace 𝕜 E (A a x) :=
    WeakBilin.continuous_of_continuous_eval _ fun f ↦
      (ContinuousLinearMapWOT.continuous_dual_apply x f).comp hA
  apply continuous_iff_isClosed.2
  intro F hF
  have hc : IsClosed (toWeakSpace 𝕜 E '' (F ∩ orbit)) :=
    ((hO.inter_left hF).image (toWeakSpaceCLM 𝕜 E).continuous).isClosed
  convert hc.preimage hweak using 1
  ext a
  simp only [mem_preimage, mem_image, mem_inter_iff]
  exact ⟨fun h ↦ ⟨A a x, ⟨h, mem_range_self a⟩, rfl⟩,
    fun ⟨y, hy, hya⟩ ↦ (toWeakSpace 𝕜 E).injective hya ▸ hy.1⟩

end Orbits

section Evaluation

variable {X 𝕜 E : Type*} [TopologicalSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Uniformly bounded operators with continuous pointwise evaluation also
have continuous joint evaluation. -/
theorem continuous_apply_of_operatorBound (A : X → E →L[𝕜] E) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ a, ‖A a‖ ≤ C) (hnorm : ∀ x, Continuous fun a ↦ A a x) :
    Continuous fun p : X × E ↦ A p.1 p.2 := by
  apply continuous_iff_continuousAt.2
  intro p
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hfst : ∀ᶠ q : X × E in 𝓝 p, dist (A q.1 p.2) (A p.1 p.2) < ε / 2 :=
    Metric.tendsto_nhds.1 ((hnorm p.2).comp continuous_fst).continuousAt _ (by positivity)
  have hsnd : ∀ᶠ q : X × E in 𝓝 p, dist q.2 p.2 < ε / (2 * C) :=
    Metric.tendsto_nhds.1 continuous_snd.continuousAt _ (by positivity)
  filter_upwards [hfst, hsnd] with q hq₁ hq₂
  have hdist : dist (A q.1 q.2) (A q.1 p.2) ≤ C * dist q.2 p.2 := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (A q.1).le_of_opNorm_le (hbound q.1) _
  calc
    dist (A q.1 q.2) (A p.1 p.2) ≤
        dist (A q.1 q.2) (A q.1 p.2) + dist (A q.1 p.2) (A p.1 p.2) :=
      dist_triangle _ _ _
    _ ≤ C * dist q.2 p.2 + dist (A q.1 p.2) (A p.1 p.2) := add_le_add_left hdist _
    _ < C * (ε / (2 * C)) + ε / 2 := add_lt_add (mul_lt_mul_of_pos_left hq₂ hC) hq₁
    _ = ε := by field_simp; ring

end Evaluation

section Inverse

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [T2Space G]

/-- Inversion is continuous in a compact Hausdorff group whose multiplication
is jointly continuous. Its graph projects bijectively onto the first factor. -/
theorem continuous_inv_of_compact_mul (hmul : Continuous fun p : G × G ↦ p.1 * p.2) :
    Continuous (fun a : G ↦ a⁻¹) := by
  let graph : Set (G × G) := {p | p.1 * p.2 = 1}
  have hgraph : IsClosed graph := isClosed_eq hmul continuous_const
  let : CompactSpace graph := isCompact_iff_compactSpace.1 hgraph.isCompact
  let e : graph ≃ G :=
    { toFun := fun p ↦ p.1.1
      invFun := fun a ↦ ⟨(a, a⁻¹), mul_inv_cancel a⟩
      left_inv := fun ⟨⟨a, b⟩, h⟩ ↦ by
        apply Subtype.ext
        have hb : b = a⁻¹ := by
          calc
            b = a⁻¹ * (a * b) := by simp
            _ = a⁻¹ := by rw [show a * b = 1 from h, mul_one]
        exact Prod.ext rfl hb.symm
      right_inv := fun _ ↦ rfl }
  have he : Continuous e := continuous_subtype_val.fst
  exact continuous_subtype_val.snd.comp he.continuous_symm_of_equiv_compact_to_t2

end Inverse

section OperatorGroup

variable {S 𝕜 E : Type*} [Semigroup S] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {π : S →ₙ* (E →L[𝕜] E)} (K : GroupIdeal (weakOperatorClosure π))

theorem GroupIdeal.continuous_norm_eval (hK : IsCompact K.carrier) (x : E) :
    Continuous fun a ↦ K.operatorAction a x := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  let : SeparatelyContinuousMul K.carrier := IsInducing.separatelyContinuousMul
    (⟨Subtype.val, fun _ _ ↦ rfl⟩ : K.carrier →ₙ* weakOperatorClosure π)
    (IsInducing.subtypeVal (t := K.carrier))
  exact continuous_normOrbit_of_wot K.operatorAction K.continuous_wot_operatorAction x

/-- The compact group ideal of a weak operator semigroup has jointly continuous
group operations. This follows from norm continuity of its orbit maps. -/
theorem GroupIdeal.isTopologicalGroup_of_isCompact (hK : IsCompact K.carrier) :
    IsTopologicalGroup K.carrier := by
  let : CompactSpace K.carrier := isCompact_iff_compactSpace.1 hK
  obtain ⟨C, hC, hbound⟩ := exists_operatorBound_of_compact_wot
    (fun a ↦ K.operatorAction a) K.continuous_wot_operatorAction
  have hA := K.continuous_norm_eval hK
  have happly := continuous_apply_of_operatorBound (fun a ↦ K.operatorAction a) hC hbound hA
  have hind : IsInducing (fun a : K.carrier ↦ (a.1.1 : E →WOT[𝕜] E)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hm : Continuous fun p : K.carrier × K.carrier ↦ p.1 * p.2 := by
    apply hind.continuous_iff.2
    apply ContinuousLinearMapWOT.continuous_of_dual_apply_continuous
    intro x f
    have hc : Continuous fun p : K.carrier × K.carrier ↦
        K.operatorAction p.1 (K.operatorAction p.2 x) :=
      happly.comp (continuous_fst.prodMk ((hA x).comp continuous_snd))
    exact f.continuous.comp hc
  exact { continuous_mul := hm, continuous_inv := continuous_inv_of_compact_mul hm }

end OperatorGroup

end Mixing.JdLGBridge
