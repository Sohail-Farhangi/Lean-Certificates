/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ConditionalGramSchmidt

@[expose] public section
noncomputable section

namespace Mixing

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate InnerProductSpace ProbabilityTheory

variable {G X Y : Type*} [CommGroup G] [MeasurableSpace X] [MeasurableSpace Y]
variable {E : System G X} {B : System G Y}

/-- A finite family whose generated module over the bounded observables of
the base is invariant under the extension action. -/
structure FiniteInvariantBaseModule (π : FactorMap E B) (n : ℕ) where
  vector : Fin n → Lp ℂ 2 E.measure
  translate : ∀ g i, ∃ a : Fin n → BoundedObservable Y,
    ∀ᵐ x ∂E.measure, vector i (E.act g x) = ∑ j, a j (π.toFun x) * vector j x

private theorem ae_fibrewise_translate_span {π : FactorMap E B} {n : ℕ}
    (M : FiniteInvariantBaseModule π n) {κ : Kernel Y X}
    (hκ : κ ∘ₘ B.measure = E.measure)
    (hFibre : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, π.toFun x = y) (g : G) :
    ∀ᵐ y ∂B.measure, ∀ i, ∃ (h : ∀ j, MemLp (M.vector j) 2 (κ y))
      (h' : MemLp (fun x => M.vector i (E.act g x)) 2 (κ y)),
      h'.toLp (fun x => M.vector i (E.act g x)) ∈
        Submodule.span ℂ (range fun j => (h j).toLp (M.vector j)) := by
  apply ae_all_iff.mpr
  intro i
  obtain ⟨a, he⟩ := M.translate g i
  have hAE : ae (κ ∘ₘ B.measure) = ae E.measure := congrArg ae hκ
  rw [← hAE] at he
  filter_upwards [Measure.ae_ae_of_ae_comp he, hFibre,
    ae_all_iff.mpr (fun j => ae_memLp_two_of_kernel_average hκ (M.vector j))] with y hA hF h
  let q : Lp ℂ 2 (κ y) := ∑ j, a j y • (h j).toLp (M.vector j)
  have hq : q =ᵐ[κ y] fun x => M.vector i (E.act g x) := by
    filter_upwards [ae_coe_toLp_sum_smul h (fun j => a j y), hA, hF] with x hx hAx hFx
    change q x = _ at hx
    rw [hx, hAx, hFx]
  have hMem := (memLp_congr_ae hq).mp (Lp.memLp q)
  have hToLp : hMem.toLp (fun x => M.vector i (E.act g x)) = q :=
    Lp.ext (hMem.coeFn_toLp.trans hq.symm)
  refine ⟨h, hMem, ?_⟩
  rw [hToLp]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

set_option maxHeartbeats 1200000 in
/-- A finite invariant module has orthonormal conditional generators with
the same Hilbert-space span on almost every fibre. -/
theorem FiniteInvariantBaseModule.exists_conditionalOrthogonalFrame
    {π : FactorMap E B} {n : ℕ} (M : FiniteInvariantBaseModule π n) (κ : Kernel Y X)
    (hκ : κ ∘ₘ B.measure = E.measure)
    (hFibre : ∀ᵐ y ∂B.measure, ∀ᵐ x ∂κ y, π.toFun x = y)
    (hEq : ∀ g, ∀ᵐ y ∂B.measure, MeasurePreserving (E.act g) (κ y) (κ (B.act g y))) :
    ∃ A : ConditionalOrthogonalFrame π κ n, FibreSpanEq κ B.measure A.vector M.vector := by
  obtain ⟨u, hOrth, hSpan⟩ := exists_conditionalGramSchmidt π κ hκ hFibre M.vector
  refine ⟨⟨u, hOrth, ?_⟩, hSpan⟩
  intro g i
  filter_upwards [hSpan, (B.preserves g).quasiMeasurePreserving.ae hSpan, hEq g,
    ae_fibrewise_translate_span M hκ hFibre g] with y hY hBY hInv hM
  obtain ⟨hu, hv, he⟩ := hY
  obtain ⟨hu', hv', he'⟩ := hBY
  let L : Lp ℂ 2 (κ (B.act g y)) →ₗ[ℂ] Lp ℂ 2 (κ y) :=
    Lp.compMeasurePreservingₗ ℂ (E.act g) hInv
  let U := Submodule.span ℂ (range fun j => (hu j).toLp (u j))
  have hPull (w : Lp ℂ 2 E.measure) (hw : MemLp w 2 (κ (B.act g y))) :
      L (hw.toLp w) =ᵐ[κ y] fun x => w (E.act g x) :=
    (Lp.coeFn_compMeasurePreserving (hw.toLp w) hInv).trans
      (hInv.quasiMeasurePreserving.ae_eq_comp hw.coeFn_toLp)
  have hInc : Submodule.span ℂ (range fun j => (hv' j).toLp (M.vector j)) ≤ U.comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨_, hVj, hj⟩ := hM j
    have hP : L ((hv' j).toLp (M.vector j)) =
        hVj.toLp (fun x => M.vector j (E.act g x)) :=
      Lp.ext ((hPull (M.vector j) (hv' j)).trans hVj.coeFn_toLp.symm)
    change L ((hv' j).toLp (M.vector j)) ∈ U
    rw [hP]
    change _ ∈ Submodule.span ℂ (range fun j => (hu j).toLp (u j))
    rw [he]
    exact hj
  let z := L ((hu' i).toLp (u i))
  have hz₀ : (hu' i).toLp (u i) ∈
      Submodule.span ℂ (range fun j => (hv' j).toLp (M.vector j)) := by
    rw [← he']
    exact Submodule.subset_span ⟨i, rfl⟩
  have hz : z ∈ U := hInc hz₀
  have hZ := hPull (u i) (hu' i)
  have hMem := (memLp_congr_ae hZ).mp (Lp.memLp z)
  have hToLp : hMem.toLp (fun x => u i (E.act g x)) = z :=
    Lp.ext (hMem.coeFn_toLp.trans hZ.symm)
  exact ⟨hu, hMem, hToLp.symm ▸ hz⟩

end Mixing
