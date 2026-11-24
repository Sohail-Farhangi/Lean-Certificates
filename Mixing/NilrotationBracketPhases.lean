/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.NilrotationBracketWords
public import Mixing.NilrotationGeometryConnectivity
public import Mixing.NilrotationMultilinearDensity

/-! # Time phases at each layer of a nilrotation -/

@[expose] public section
noncomputable section

namespace Mixing

open scoped commutatorElement

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private abbrev phaseLayer (G : Type*) [Group G] (n : ℕ) : Subgroup G :=
  (⊤ : Subgroup G).lowerCentralSeries n

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem phaseLayer_map_quotient (N : Subgroup G) [N.Normal] (n : ℕ) :
    (phaseLayer G n).map (QuotientGroup.mk' N) = phaseLayer (G ⧸ N) n := by
  unfold phaseLayer
  rw [Subgroup.map_lowerCentralSeries,
    Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem phaseLayer_quotient_bottom (n : ℕ) :
    phaseLayer (G ⧸ phaseLayer G (n + 2)) (n + 2) = ⊥ := by
  rw [← phaseLayer_map_quotient]
  apply bot_unique
  apply Subgroup.map_le_iff_le_comap.mpr
  intro x hx
  exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff _).mpr hx)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem phaseCharacter_eq_of_quotient_eq (n : ℕ) (L : Subgroup G)
    (hN : phaseLayer G (n + 2) ≤ L) (χ : phaseLayer G (n + 1) →* Circle)
    (hL : ∀ c : phaseLayer G (n + 1), (c : G) ∈ L → χ c = 1)
    (x y : phaseLayer G (n + 1))
    (h : QuotientGroup.mk' (phaseLayer G (n + 2)) (x : G) =
      QuotientGroup.mk' (phaseLayer G (n + 2)) (y : G)) : χ x = χ y := by
  let q := QuotientGroup.mk' (phaseLayer G (n + 2))
  have hq : q (((x⁻¹ * y : phaseLayer G (n + 1)) : G)) = 1 := by
    change q ((x : G)⁻¹ * (y : G)) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have he := hL (x⁻¹ * y) (hN ((QuotientGroup.eq_one_iff _).mp hq))
  rwa [map_mul, map_inv, inv_mul_eq_one] at he

private theorem continuous_nilrotationBracketWord (n : ℕ) :
    Continuous (nilrotationBracketWord (G := G) n) := by
  induction n with
  | zero =>
    exact continuous_apply 0
  | succ n ih =>
    have hx : Continuous (fun u : Fin (n + 2) → G ↦ u 0) := continuous_apply 0
    have hy : Continuous (fun u : Fin (n + 2) → G ↦ nilrotationBracketWord n (Fin.tail u)) :=
      ih.comp (continuous_pi fun i ↦ continuous_apply i.succ)
    exact ((hx.mul hy).mul hx.inv).mul hy.inv

private def phaseBracket (n : ℕ) (a : G) (b : phaseLayer G n) : phaseLayer G (n + 1) :=
  ⟨⁅a, (b : G)⁆, by
    rw [phaseLayer, Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) b.2⟩

private def bracketPhaseHom (n : ℕ) (L : Subgroup G)
    (hN : phaseLayer G (n + 2) ≤ L) (a : G) (χ : phaseLayer G (n + 1) →* Circle)
    (hL : ∀ c : phaseLayer G (n + 1), (c : G) ∈ L → χ c = 1) :
    phaseLayer G n →* Circle where
  toFun b := χ (phaseBracket n a b)
  map_one' := by
    have h : phaseBracket n a 1 = 1 := by
      apply Subtype.ext
      change ⁅a, (1 : G)⁆ = 1
      simp [commutatorElement_def]
    rw [h, map_one]
  map_mul' b e := by
    rw [← map_mul]
    apply phaseCharacter_eq_of_quotient_eq n L hN χ hL
    let q := QuotientGroup.mk' (phaseLayer G (n + 2))
    have hc : q (phaseBracket n a e) ∈ Subgroup.center (G ⧸ phaseLayer G (n + 2)) := by
      apply nilrotation_last_lowerCentral_le_center (n + 1) (phaseLayer_quotient_bottom n)
      change q (phaseBracket n a e) ∈ phaseLayer (G ⧸ phaseLayer G (n + 2)) (n + 1)
      have he : q (phaseBracket n a e) ∈ (phaseLayer G (n + 1)).map q :=
        ⟨_, (phaseBracket n a e).2, rfl⟩
      exact (phaseLayer_map_quotient (phaseLayer G (n + 2)) (n + 1)) ▸ he
    change q ⁅a, (b : G) * (e : G)⁆ = q (⁅a, (b : G)⁆ * ⁅a, (e : G)⁆)
    simp only [map_mul, map_commutatorElement]
    have hcomm : q b * ⁅q a, q e⁆ = ⁅q a, q e⁆ * q b := by
      rw [← map_commutatorElement]
      exact Subgroup.mem_center_iff.mp hc (q b)
    rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc _ (q b), hcomm]
    simp only [mul_assoc, mul_inv_cancel, mul_one]

private theorem continuous_bracketPhaseHom (n : ℕ) (L : Subgroup G)
    (hN : phaseLayer G (n + 2) ≤ L) (a : G) (χ : phaseLayer G (n + 1) →* Circle)
    (hL : ∀ c : phaseLayer G (n + 1), (c : G) ∈ L → χ c = 1) (hχ : Continuous χ) :
    Continuous (bracketPhaseHom n L hN a χ hL) := by
  have hb : Continuous (fun b : phaseLayer G n ↦ (b : G)) := continuous_subtype_val
  exact hχ.comp ((((continuous_const.mul hb).mul continuous_const).mul hb.inv).subtype_mk _)

private theorem bracketPhaseHom_nontrivial (n : ℕ) (L : Subgroup G)
    [CompactSpace (G ⧸ L)] (hN : phaseLayer G (n + 2) ≤ L)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a ^ j * d * (γ : G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (χ : phaseLayer G (n + 1) →* Circle) (hχ : Continuous χ)
    (hL : ∀ c : phaseLayer G (n + 1), (c : G) ∈ L → χ c = 1)
    (hχ' : ∃ c, χ c ≠ 1) : ∃ b, bracketPhaseHom n L hN a χ hL b ≠ 1 := by
  by_contra! ht
  let W (u : Fin (n + 2) → G) : phaseLayer G (n + 1) :=
    ⟨nilrotationBracketWord (n + 1) u, nilrotationBracketWord_mem_lowerCentral (n + 1) u⟩
  let F (u : Fin (n + 2) → G) : Circle := χ (W u)
  have hF : Continuous F := hχ.comp ((continuous_nilrotationBracketWord (n + 1)).subtype_mk _)
  have hMul (u : Fin (n + 2) → G) (i : Fin (n + 2)) (x y : G) :
      F (Function.update u i (x * y)) = F (Function.update u i x) * F (Function.update u i y) := by
    change χ (W (Function.update u i (x * y))) =
      χ (W (Function.update u i x)) * χ (W (Function.update u i y))
    rw [← map_mul]
    apply phaseCharacter_eq_of_quotient_eq n L hN χ hL
    let q := QuotientGroup.mk' (phaseLayer G (n + 2))
    have hUpdate (z : G) : q ∘ Function.update u i z = Function.update (q ∘ u) i (q z) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hj]
    change q (nilrotationBracketWord (n + 1) (Function.update u i (x * y))) =
      q (nilrotationBracketWord (n + 1) (Function.update u i x) *
        nilrotationBracketWord (n + 1) (Function.update u i y))
    simp only [map_mul, map_nilrotationBracketWord, hUpdate]
    exact nilrotationBracketWord_update_mul (n + 1) (phaseLayer_quotient_bottom n)
      (q ∘ u) i (q x) (q y)
  have hLat (u : Fin (n + 2) → G) (hu : ∀ i, u i ∈ L) : F u = 1 :=
    hL (W u) (nilrotationBracketWord_mem_subgroup L (n + 1) u hu)
  have ha (u : Fin (n + 2) → G) (hu : u 0 = a) : F u = 1 := by
    let b : phaseLayer G n :=
      ⟨nilrotationBracketWord n (Fin.tail u), nilrotationBracketWord_mem_lowerCentral n _⟩
    have he : W u = phaseBracket n a b := by
      apply Subtype.ext
      change ⁅u 0, (b : G)⁆ = ⁅a, (b : G)⁆
      rw [hu]
    change χ (W u) = 1
    rw [he]
    exact ht b
  have hAll := nilrotation_multilinear_eq_one L a d hd hgen F hF hMul hLat ha
  have hTop : phaseLayer G (n + 1) ≤ (χ.ker.map (phaseLayer G (n + 1)).subtype) := by
    refine (closure_range_nilrotationBracketWord (G := G) (n + 1)).ge.trans ?_
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨u, rfl⟩
    exact ⟨W u, hAll u, rfl⟩
  obtain ⟨c, hc⟩ := hχ'
  obtain ⟨x, hx, he⟩ := hTop c.2
  exact hc (Subtype.ext he ▸ hx)

/-- A character of the last visible layer takes every phase on time commutators.
The next layer can be nontrivial provided it is contained in the stabilizer. -/
theorem nilrotation_bracket_full_time_phases (n : ℕ) (L : Subgroup G)
    [CompactSpace (G ⧸ L)] (hN : (⊤ : Subgroup G).lowerCentralSeries (n + 2) ≤ L)
    (a d : G) (hd : Dense {x : G | ∃ (j : ℤ) (γ : L), a ^ j * d * (γ : G) = x})
    (hgen : Subgroup.connectedComponentOfOne G ⊔ Subgroup.zpowers a = ⊤)
    (χ : (⊤ : Subgroup G).lowerCentralSeries (n + 1) →* Circle) (hχ : Continuous χ)
    (hL : ∀ c : (⊤ : Subgroup G).lowerCentralSeries (n + 1), (c : G) ∈ L → χ c = 1)
    (hχ' : ∃ c, χ c ≠ 1) :
    ∀ s : UnitAddCircle, ∃ (b : G) (c : (⊤ : Subgroup G).lowerCentralSeries (n + 1)),
      ⁅a, b⁆ = (c : G) ∧ χ c = AddCircle.toCircle s := by
  let f := bracketPhaseHom n L hN a χ hL
  have hf : Continuous f := continuous_bracketPhaseHom n L hN a χ hL hχ
  have hne : ∃ b, f b ≠ 1 := bracketPhaseHom_nontrivial n L hN a d hd hgen χ hχ hL hχ'
  have hSurj : Function.Surjective f := by
    cases n with
    | zero =>
      let H := Subgroup.connectedComponentOfOne G
      let : ConnectedSpace H :=
        isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := (1 : G)))
      let incl : G →* phaseLayer G 0 :=
        { toFun := fun x ↦ ⟨x, by rw [phaseLayer, Subgroup.lowerCentralSeries_zero]; exact Subgroup.mem_top _⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl }
      let g := f.comp (incl.comp H.subtype)
      have hg : Continuous g := hf.comp ((continuous_subtype_val : Continuous (fun x : H ↦ (x : G))).subtype_mk _)
      have hng : ∃ x, g x ≠ 1 := by
        by_contra! hh
        let k := f.comp incl
        have hH : H ≤ k.ker := fun x hx ↦ hh ⟨x, hx⟩
        have ha : a ∈ k.ker := by
          change χ (phaseBracket 0 a (incl a)) = 1
          have he : phaseBracket 0 a (incl a) = 1 := by
            apply Subtype.ext
            change ⁅a, a⁆ = 1
            simp
          rw [he, map_one]
        have ht : H ⊔ Subgroup.zpowers a ≤ k.ker := sup_le hH (Subgroup.zpowers_le.mpr ha)
        obtain ⟨b, hb⟩ := hne
        exact hb (ht (hgen.symm ▸ Subgroup.mem_top (b : G)))
      intro z
      obtain ⟨x, hx⟩ := continuous_circle_hom_surjective_of_nontrivial g hg hng z
      exact ⟨incl x, hx⟩
    | succ n =>
      let := connectedSpace_lowerCentralSeries_succ_of_component_sup_zpowers a hgen n
      exact continuous_circle_hom_surjective_of_nontrivial f hf hne
  intro s
  obtain ⟨b, hb⟩ := hSurj (AddCircle.toCircle s)
  exact ⟨b, phaseBracket n a b, rfl, hb⟩

end Mixing
