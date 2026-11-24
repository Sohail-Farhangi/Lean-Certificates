/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.CentralCommutatorPhases
public import Mathlib.Topology.Algebra.Group.Quotient

/-! # Multilinear phases on a compact homogeneous space -/

@[expose] public section
noncomputable section

namespace Mixing

open Filter Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def multilinearCircleHom (f : G → Circle)
    (h : ∀ x y, f (x * y) = f x * f y) : G →* Circle where
  toFun := f
  map_one' := by
    have hh := h 1 1
    rw [one_mul] at hh
    apply mul_left_cancel (a := f 1)
    simpa only [mul_one] using hh.symm
  map_mul' := h

omit [IsTopologicalGroup G] in
private theorem multilinear_dense_hom_one (L : Subgroup G)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a ^ j * d * (γ : G) = x})
    (f : G →* Circle) (hf : Continuous f) (ha : f a = 1) (hL : ∀ γ : L, f γ = 1)
    (x : G) : f x = 1 := by
  have hall (y : G) : f y = f d := by
    have hsub : {x : G | ∃ (n : ℤ) (γ : L), a ^ n * d * (γ : G) = x} ⊆
        {x : G | f x = f d} := by
      rintro _ ⟨n, γ, rfl⟩
      simp [map_mul, map_zpow, ha, hL γ]
    exact closure_minimal hsub (isClosed_eq hf continuous_const) (hd y)
  exact (hall x).trans ((hall 1).symm.trans (map_one f))

private theorem multilinear_bihom_one (L : Subgroup G) [CompactSpace (G ⧸ L)] (a : G)
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (B : G → G → Circle) (hB : Continuous (fun p : G × G ↦ B p.1 p.2))
    (hLeft : ∀ g h b, B (g * h) b = B g b * B h b)
    (hRight : ∀ g b c, B g (b * c) = B g b * B g c)
    (hL : ∀ g (b : L), B g b = 1) (ha : ∀ b, B a b = 1)
    (g b : G) : B g b = 1 := by
  let Left (b : G) := multilinearCircleHom (fun x ↦ B x b) (fun x y ↦ hLeft x y b)
  let Right (x : G) := multilinearCircleHom (B x) (hRight x)
  let Q := G ⧸ L
  let pair : G × Q → Circle := fun z =>
    Quotient.liftOn z.2 (B z.1) (by
      intro x y h
      have hxy : x⁻¹ * y ∈ L := QuotientGroup.leftRel_apply.mp h
      have he := hL z.1 ⟨x⁻¹ * y, hxy⟩
      change Right z.1 (x⁻¹ * y) = 1 at he
      rw [map_mul, map_inv, inv_mul_eq_one] at he
      exact he)
  have pair_mk (x y : G) : pair (x, QuotientGroup.mk y) = B x y := rfl
  have hpair : Continuous pair := by
    rw [← (IsOpenQuotientMap.id.prodMap
      (QuotientGroup.isOpenQuotientMap_mk (N := L))).continuous_comp_iff]
    exact hB
  let arc := Circle.centeredArc (Real.pi / 2)
  have hone : (1 : Circle) ∈ arc := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have hpairone (q : Q) : pair (1, q) = 1 := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [pair_mk]
    exact map_one (Left y)
  have hbox : pair ⁻¹' arc ∈ (𝓝 (1 : G)) ×ˢ (𝓝ˢ (univ : Set Q)) :=
    isCompact_univ.mem_prod_nhdsSet_of_forall fun q _ ↦ by
      rw [← nhds_prod_eq]
      exact ((Circle.isOpen_centeredArc _).preimage hpair).mem_nhds
        (show pair (1, q) ∈ arc from hpairone q ▸ hone)
  rw [nhdsSet_univ] at hbox
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hbox
  have hV' : V = univ := by simpa using hV
  subst V
  let K : Subgroup G := ⨅ y : G, (Left y).ker
  have hK : (K : Set G) ∈ 𝓝 (1 : G) := Filter.mem_of_superset hU fun x hx ↦ by
    change x ∈ K
    rw [Subgroup.mem_iInf]
    intro y
    change B x y = 1
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro j _
    have hm : pair (x, QuotientGroup.mk (y ^ j)) ∈ arc :=
      hUV (show (x, QuotientGroup.mk (y ^ j)) ∈ U ×ˢ (univ : Set Q) from ⟨hx, mem_univ _⟩)
    rw [pair_mk] at hm
    change Right x (y ^ j) ∈ arc at hm
    rwa [map_pow] at hm
  have ho := K.isOpen_of_mem_nhds hK
  have hc := K.isClosed_of_isOpen ho
  have hConn : Subgroup.connectedComponentOfOne G ≤ K := fun x hx ↦
    (show IsClopen (K : Set G) from ⟨hc, ho⟩).connectedComponent_subset K.one_mem hx
  have hKa : a ∈ K := by
    rw [Subgroup.mem_iInf]
    exact ha
  have hle : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a ≤ K :=
    sup_le hConn (Subgroup.zpowers_le.mpr hKa)
  exact (Subgroup.mem_iInf.mp (hle (hgen.symm ▸ Subgroup.mem_top g))) b

/-- A continuous circle-valued phase that is multiplicative in every coordinate is
trivial if it vanishes on lattice tuples and whenever the first coordinate is the
time element. The compact homogeneous space has a dense lifted time orbit, and the
identity component and the time element generate the ambient group. -/
theorem nilrotation_multilinear_eq_one {n : ℕ} (L : Subgroup G) [CompactSpace (G ⧸ L)]
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a ^ j * d * (γ : G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (F : (Fin (n + 1) → G) → Circle) (hF : Continuous F)
    (hMul : ∀ u i x y, F (Function.update u i (x * y)) =
      F (Function.update u i x) * F (Function.update u i y))
    (hL : ∀ u, (∀ i, u i ∈ L) → F u = 1)
    (ha : ∀ u, u 0 = a → F u = 1) : ∀ u, F u = 1 := by
  have hInd (s : Finset (Fin (n + 1))) (hs : 0 ∉ s) :
      ∀ u, (∀ j, j ≠ 0 → j ∉ s → u j ∈ L) → F u = 1 := by
    induction s using Finset.induction_on with
    | empty =>
      intro u hu
      let f := multilinearCircleHom (fun x ↦ F (Function.update u 0 x)) (hMul u 0)
      have hf : Continuous f := by
        change Continuous (fun x ↦ F (Function.update u 0 x))
        apply hF.comp
        apply continuous_pi
        intro j
        by_cases hj : j = 0
        · subst j
          simp only [Function.update_self]
          change Continuous (id : G → G)
          exact continuous_id
        · simpa only [Function.update_of_ne hj] using
            (continuous_const : Continuous (fun _ : G ↦ u j))
      have hfa : f a = 1 := ha _ (Function.update_self _ _ _)
      have hfL (γ : L) : f γ = 1 := by
        apply hL
        intro j
        by_cases hj : j = 0
        · subst j
          simpa only [Function.update_self] using γ.2
        · simpa only [Function.update_of_ne hj] using hu j hj (Finset.notMem_empty j)
      have he := multilinear_dense_hom_one L a d hd f hf hfa hfL (u 0)
      change F (Function.update u 0 (u 0)) = 1 at he
      simpa only [Function.update_eq_self] using he
    | @insert i s hi ih =>
      intro u hu
      have hi0 : i ≠ 0 := fun h ↦ hs (h ▸ Finset.mem_insert_self i s)
      have hs' : 0 ∉ s := fun h ↦ hs (Finset.mem_insert_of_mem h)
      let W (g x : G) (j : Fin (n + 1)) : G := if j = 0 then g else if j = i then x else u j
      have gUpd (g x y : G) : Function.update (W g x) 0 y = W y x := by
        funext j
        by_cases hj : j = 0
        · subst j
          simp [W]
        · rw [Function.update_of_ne hj]
          simp [W, hj]
      have xUpd (g x y : G) : Function.update (W g x) i y = W g y := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [W, hi0]
        · rw [Function.update_of_ne hj]
          by_cases hk : j = 0
          · simp [W, hk]
          · simp [W, hj, hk]
      let B (g x : G) := F (W g x)
      have hB : Continuous (fun p : G × G ↦ B p.1 p.2) := by
        apply hF.comp
        apply continuous_pi
        intro j
        by_cases hj : j = 0
        · simpa only [W, ite_eq_left hj] using (continuous_fst : Continuous (Prod.fst : G × G → G))
        · by_cases hk : j = i
          · simpa only [W, ite_eq_right hj, ite_eq_left hk] using
              (continuous_snd : Continuous (Prod.snd : G × G → G))
          · simpa only [W, ite_eq_right hj, ite_eq_right hk] using
              (continuous_const : Continuous (fun _ : G × G ↦ u j))
      have hLeft (g h x : G) : B (g * h) x = B g x * B h x := by
        simpa only [gUpd, B] using hMul (W 1 x) 0 g h
      have hRight (g x y : G) : B g (x * y) = B g x * B g y := by
        simpa only [xUpd, B] using hMul (W g 1) i x y
      have hBL (g : G) (x : L) : B g x = 1 := by
        apply ih hs'
        intro j hj hj'
        by_cases hj₁ : j = i
        · simpa only [W, ite_eq_right hj, ite_eq_left hj₁] using x.2
        · simpa only [W, ite_eq_right hj, ite_eq_right hj₁] using
            hu j hj (by simpa only [Finset.mem_insert, hj₁, false_or] using hj')
      have hBa (x : G) : B a x = 1 := ha _ (by simp [W])
      have he : W (u 0) (u i) = u := by
        funext j
        by_cases hj : j = 0
        · subst j
          simp [W]
        · by_cases hk : j = i
          · subst j
            simp [W, hj]
          · simp [W, hj, hk]
      have h := multilinear_bihom_one L a hgen B hB hLeft hRight hBL hBa (u 0) (u i)
      change F (W (u 0) (u i)) = 1 at h
      rwa [he] at h
  intro u
  apply hInd (Finset.univ.erase 0) (by simp) u
  intro j hj hmem
  exact (hmem (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)).elim

end Mixing
