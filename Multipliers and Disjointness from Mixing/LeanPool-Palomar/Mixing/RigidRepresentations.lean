module

public import Mixing.MildMixing
public import Mixing.JoiningSpectrum
public import Mixing.InjectiveLimits

@[expose] public section

namespace Mixing

open Filter Set TopologicalSpace
open scoped Topology

variable {G H : Type*} [CommGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- Rigidity of an action requires one escaping sequence for all vectors. -/
def IsRigidRepresentation (U : G →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  ∃ g : ℕ → G, Tendsto g atTop cofinite ∧ ∀ x : H, IsRigidAlong U g x

/-- Whole-representation rigidity yields a single free idempotent acting as
the identity on every vector. -/
theorem exists_freeIdempotent_operator_eq_one_of_rigid
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (h : IsRigidRepresentation U) :
    ∃ p ∈ freeIdempotentUltrafilters G, ultrafilterOperator U p = 1 := by
  obtain ⟨g, hg, hrigid⟩ := h
  let S := {p : Ultrafilter G | p ∈ freeUltrafilters G ∧ ultrafilterOperator U p = 1}
  have hS : S.Nonempty := by
    obtain ⟨p, hp⟩ := exists_ultrafilter_le (Filter.map g atTop)
    refine ⟨p, hp.trans hg, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    have hlim : Tendsto (fun a : G ↦ inner ℂ y (U a x)) (Filter.map g atTop)
        (𝓝 (inner ℂ y x)) := Filter.tendsto_map'_iff.mpr (hrigid x y)
    exact tendsto_nhds_unique (tendsto_ultrafilterOperator_coeff U p y x) (hlim.mono_left hp)
  have hSclosed : IsClosed S := by
    change IsClosed (freeUltrafilters G ∩ {p | ultrafilterOperator U p = 1})
    apply isClosed_freeUltrafilters.inter
    have he : {p : Ultrafilter G | ultrafilterOperator U p = 1} =
        {p | ContinuousLinearMapWOT.ofCLM (ultrafilterOperator U p) =
          ContinuousLinearMapWOT.ofCLM (1 : H →L[ℂ] H)} := by
      ext p
      exact ⟨congrArg _, congrArg ContinuousLinearMapWOT.toCLM⟩
    rw [he]
    exact isClosed_eq (continuous_ultrafilterOperator_wot U) continuous_const
  have hmul : ∀ p ∈ S, ∀ q ∈ S, p * q ∈ S := by
    rintro p ⟨_, hp⟩ q ⟨hq, hq₁⟩
    refine ⟨mul_mem_freeUltrafilters hq, ?_⟩
    rw [ultrafilterOperator_mul, hp, hq₁, one_mul]
  obtain ⟨p, ⟨hp, hfix⟩, hidem⟩ :=
    exists_idempotent_in_compact_subsemigroup Ultrafilter.continuous_mul_left
      S hS hSclosed.isCompact hmul
  exact ⟨p, ⟨hp, hidem⟩, hfix⟩

/-- On a separable space, a free ultrafilter acting as the identity gives one
rigidity sequence for the whole representation. -/
theorem isRigidRepresentation_of_ultrafilterOperator_eq_one [Countable G] [SeparableSpace H]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (p : Ultrafilter G) (hp : p ∈ freeUltrafilters G)
    (h : ultrafilterOperator U p = 1) : IsRigidRepresentation U := by
  obtain ⟨e, he⟩ := exists_injective_nat G
  let _ : (cofinite : Filter G).IsCountablyGenerated := by
    rw [← he.comap_cofinite_eq, Nat.cofinite_eq_atTop]
    infer_instance
  let d := TopologicalSpace.denseSeq H
  let L : Filter G := cofinite ⊓ ⨅ n, comap (fun g ↦ U g (d n)) (𝓝 (d n))
  have hfix (n : ℕ) : ultrafilterOperator U p (d n) = d n := by rw [h]; rfl
  have hpL : (p : Filter G) ≤ L := le_inf hp <| le_iInf fun n ↦
    (tendsto_orbit_of_ultrafilter_fixed U p (d n) (hfix n)).le_comap
  let _ : NeBot L := neBot_of_le hpL
  obtain ⟨g, hg⟩ := Filter.exists_seq_tendsto L
  refine ⟨g, hg.mono_right inf_le_left, ?_⟩
  have hd (n : ℕ) : Tendsto (fun k ↦ U (g k) (d n)) atTop (𝓝 (d n)) :=
    tendsto_comap.comp (hg.mono_right (inf_le_right.trans (iInf_le _ n)))
  intro x y
  have hnorm : Tendsto (fun k ↦ U (g k) x) atTop (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq H) x
      (ε / 3) (by positivity)
    change dist x (d n) < ε / 3 at hn
    filter_upwards [Metric.tendsto_nhds.mp (hd n) (ε / 3) (by positivity)] with k hk
    calc
      dist (U (g k) x) x ≤ dist (U (g k) x) (U (g k) (d n)) +
          dist (U (g k) (d n)) (d n) + dist (d n) x := dist_triangle4 _ _ _ _
      _ < ε := by
        rw [(U (g k)).isometry.dist_eq, dist_comm (d n) x]
        linarith
  exact ((InnerProductSpace.toDual ℂ H y).continuous.tendsto x).comp hnorm

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The forward implication in Theorem 1.1(iii). -/
theorem disjoint_rigid_of_mildlyMixing [Countable G]
    (S : System G X) (T : System G Y)
    (hMix : IsMildlyMixing S.koopmanZeroRep) (hRigid : IsRigidRepresentation T.koopmanRep) :
    Disjoint S T := by
  obtain ⟨p, hp, hId⟩ := exists_freeIdempotent_operator_eq_one_of_rigid T.koopmanRep hRigid
  have hz := (isMildlyMixing_iff_isUMixing_freeIdempotents S.koopmanZeroRep).mp hMix p hp
  have hsub : Intertwines T.koopmanZeroRep T.koopmanRep (meanZero T.measure).subtypeL :=
    fun _ _ ↦ rfl
  have hf : ultrafilterOperator T.koopmanZeroRep p = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    exact (hsub.ultrafilter p f).trans (by rw [hId]; rfl)
  have hd := spectrallyDisjoint_of_ultrafilterOperator_injective
    T.koopmanZeroRep S.koopmanZeroRep p (by rw [hf]; exact fun _ _ he ↦ he) hz
  exact disjoint_of_spectrallyDisjoint hd.symm

end Mixing
