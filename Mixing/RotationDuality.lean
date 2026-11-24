module

public import Mixing.CyclicEigenvectors
public import Mixing.EigenfunctionJoining

@[expose] public section

namespace Mixing

open Filter MeasureTheory MeasureTheory.Measure Set

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

/-- A nonzero mean-zero eigenvector can be replaced by a nonzero bounded
mean-zero eigenfunction with the same character. -/
theorem System.exists_bounded_eigenfunction (S : System G X) (χ : G →* Circle)
    (v : meanZero S.measure) (hv : v ≠ 0)
    (he : ∀ g, S.koopmanZeroRep g v = (χ g : ℂ) • v) :
    ∃ f : BoundedObservable X, (∫ x, f x ∂S.measure) = 0 ∧
      ¬ ((f : X → ℂ) =ᵐ[S.measure] (fun _ ↦ 0)) ∧
      ∀ g, ∀ᵐ x ∂S.measure, f (S.act g x) = (χ g : ℂ) * f x := by
  let w : Lp ℂ 2 S.measure := v
  let fₙ (n : ℕ) := BoundedObservable.ofLp w (n : ℝ) (by positivity)
  have hw (g : G) : ∀ᵐ x ∂S.measure, w (S.act g x) = (χ g : ℂ) * w x := by
    have h := congrArg (fun u : meanZero S.measure ↦ (u : Lp ℂ 2 S.measure)) (he g)
    change S.koopmanRep g w = (χ g : ℂ) • w at h
    have ha := Lp.coeFn_compMeasurePreserving w (S.preserves g)
    change S.koopmanRep g w =ᵐ[S.measure] w ∘ S.act g at ha
    rw [h] at ha
    exact ha.symm.trans (Lp.coeFn_smul _ w)
  have hf (n : ℕ) (g : G) :
      ∀ᵐ x ∂S.measure, fₙ n (S.act g x) = (χ g : ℂ) * fₙ n x := by
    filter_upwards [hw g] with x hx
    change (if ‖w (S.act g x)‖ ≤ (n : ℝ) then w (S.act g x) else 0) =
      (χ g : ℂ) * (if ‖w x‖ ≤ (n : ℝ) then w x else 0)
    rw [hx, norm_mul, Circle.norm_coe, one_mul]
    split_ifs <;> simp
  have hnot : ∃ n : ℕ, ¬ ∃ c : ℂ, fₙ n =ᵐ[S.measure] Function.const X c := by
    by_contra! hc
    choose c hc using hc
    have hall : ∀ᵐ x ∂S.measure, ∀ n, fₙ n x = c n := ae_all_iff.2 hc
    obtain ⟨x₀, hx₀⟩ := hall.exists
    have heq : w =ᵐ[S.measure] Function.const X (w x₀) := by
      filter_upwards [hall] with x hx
      obtain ⟨n, hn⟩ := exists_nat_gt (max ‖w x‖ ‖w x₀‖)
      have h₁ : ‖w x‖ ≤ (n : ℝ) := (le_max_left _ _).trans hn.le
      have h₂ : ‖w x₀‖ ≤ (n : ℝ) := (le_max_right _ _).trans hn.le
      have hA := hx n
      have hB := hx₀ n
      change (if ‖w x‖ ≤ (n : ℝ) then w x else 0) = c n at hA
      change (if ‖w x₀‖ ≤ (n : ℝ) then w x₀ else 0) = c n at hB
      rw [ite_eq_left h₁] at hA
      rw [ite_eq_left h₂] at hB
      exact hA.trans hB.symm
    have hz := (mem_meanZero_iff_integral _ _).mp v.property
    change (∫ x, w x ∂S.measure) = 0 at hz
    rw [integral_congr_ae heq] at hz
    change (∫ _ : X, w x₀ ∂S.measure) = 0 at hz
    simp [integral_const, measureReal_def] at hz
    apply hv
    apply Subtype.ext
    apply Lp.ext
    exact (heq.trans (by rw [hz]; rfl)).trans (Lp.coeFn_zero ℂ 2 S.measure).symm
  obtain ⟨n, hn⟩ := hnot
  let b := fₙ n
  let c := ∫ x, b x ∂S.measure
  let f := b.sub (BoundedObservable.const c)
  refine ⟨f, ?_, ?_, ?_⟩
  · simp [f, c, integral_sub (b.integrable _) (integrable_const _), measureReal_def]
  · intro hf₀
    apply hn
    refine ⟨c, ?_⟩
    filter_upwards [hf₀] with x hx
    exact sub_eq_zero.mp hx
  · intro g
    have hconst : c = (χ g : ℂ) * c := by
      calc
        c = ∫ x, b (S.act g x) ∂S.measure := (b.integral_comp_of_preserving (S.preserves g)).symm
        _ = ∫ x, (χ g : ℂ) * b x ∂S.measure := integral_congr_ae (hf n g)
        _ = (χ g : ℂ) * c := integral_const_mul _ _
    filter_upwards [hf n g] with x hx
    simp only [f, BoundedObservable.sub_apply, BoundedObservable.const_apply, mul_sub, b]
    rw [hx, ← hconst]

/-- Theorem 1.1(ii), the disjointness characterization of weak mixing by
compact abelian rotations. -/
theorem theorem1_1_ii [Countable G] (S : System G X) :
    IsWeaklyMixing S.koopmanZeroRep ↔
      ∀ (K : Type) [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
        [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
        (a : G →* K) (ν : Measure K) [IsProbabilityMeasure ν] [IsMulLeftInvariant ν]
        [ν.InnerRegularCompactLTTop], Disjoint S (compactRotation a ν) := by
  constructor
  · intro h _ _ _ _ _ _ _ _ a ν _ _ _
    exact disjoint_compactRotation_of_weaklyMixing S h a ν
  · intro hd
    by_contra h
    obtain ⟨χ, v, hv, he⟩ := exists_eigenvector_of_not_isWeaklyMixing S.koopmanZeroRep h
    obtain ⟨f, hf, hf₀, hχ⟩ := S.exists_bounded_eigenfunction χ v hv he
    exact not_disjoint_circleRotation_of_bounded_eigenfunction S χ f hf hf₀ hχ
      (hd Circle χ circleHaarProbability)

end Mixing
