module

public import Mixing.SpectralTypeDisjointness
public import Mixing.SpectralWeakMixing

@[expose] public section

noncomputable section

namespace Mixing

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

variable {G H : Type*} [CommGroup G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- Failure of weak mixing yields a nonzero joint eigenvector. -/
theorem exists_eigenvector_of_not_isWeaklyMixing [Countable G]
    (U : G →* (H ≃ₗᵢ[ℂ] H)) (h : ¬ IsWeaklyMixing U) :
    ∃ χ : G →* Circle, ∃ v : H, v ≠ 0 ∧ ∀ g, U g v = (χ g : ℂ) • v := by
  rw [isWeaklyMixing_iff_all_vector_measures_atomless] at h
  push Not at h
  obtain ⟨x, hx⟩ := h
  have hatom : ∃ χ : DiscreteDual G, dualVectorSpectralMeasure U x {χ} ≠ 0 := by
    by_contra! hzero
    exact hx ⟨hzero⟩
  obtain ⟨χ, hχ⟩ := hatom
  have hDirac : Measure.dirac χ ≪ dualVectorSpectralMeasure U x := by
    apply Measure.AbsolutelyContinuous.mk
    intro A hA hzero
    rw [Measure.dirac_apply' _ hA]
    have hnot : χ ∉ A := by
      intro hmem
      have hle := measure_mono (μ := dualVectorSpectralMeasure U x)
        (Set.singleton_subset_iff.mpr hmem)
      exact hχ (nonpos_iff_eq_zero.mp (hzero ▸ hle))
    simp [hnot]
  obtain ⟨v, hv⟩ := exists_dualVectorSpectralMeasure_eq_of_ac U x (Measure.dirac χ) hDirac
  let : TopologicalSpace G := ⊥
  let a : G →* Circle := (χ : G →ₜ* Circle).toMonoidHom
  have hcoeff (g : G) : inner ℂ v (U g v) = (a g : ℂ) := by
    rw [← spectralFourier_dualVectorSpectralMeasure, hv, spectralFourier, integral_dirac]
    rfl
  have hone : inner ℂ v v = 1 := by simpa using hcoeff 1
  refine ⟨a, v, ?_, ?_⟩
  · intro he
    rw [he, inner_zero_left] at hone
    exact zero_ne_one hone
  intro g
  let c := (a g : ℂ)
  have hc : conj c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm]
    simp [c, Circle.norm_coe]
  have hV : inner ℂ (U g v) (U g v) = 1 := ((U g).inner_map_map v v).trans hone
  have h₁ : inner ℂ (c • v) (U g v) = 1 := by rw [inner_smul_left, hcoeff, hc]
  have h₂ : inner ℂ (U g v) (c • v) = 1 := by
    rw [← inner_conj_symm, h₁, map_one]
  have h₃ : inner ℂ (c • v) (c • v) = 1 := by
    rw [inner_smul_left, inner_smul_right, hone, mul_one, hc]
  have hzero : inner ℂ (U g v - c • v) (U g v - c • v) = 0 := by
    simp only [inner_sub_left, inner_sub_right, hV, h₁, h₂, h₃, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

end Mixing
