module

public import Mixing.Koopman
public import Mixing.JoiningCorrelation

@[expose] public section

namespace Mixing

open MeasureTheory Filter
open scoped ComplexConjugate Topology

variable {G X : Type*} [CommGroup G] [MeasurableSpace X]

theorem System.hasMixingCorrelations {S : System G X} {P : Set (Ultrafilter G)}
    (h : S.IsUMixing P) : HasMixingCorrelations S P := by
  intro p hp f k
  have heq : (fun g ↦ inner ℂ (f.l2 S.measure) (S.koopmanRep g (k.l2 S.measure))) =
      fun g ↦ ∫ x, conj (f x) * k (S.act g x) ∂S.measure := by
    funext g
    rw [L2.inner_def]
    apply integral_congr_ae
    have hcomp : S.koopmanRep g (k.l2 S.measure) =ᵐ[S.measure] fun x ↦ k (S.act g x) :=
      (Lp.coeFn_compMeasurePreserving _ (S.preserves g)).trans
        ((S.preserves g).quasiMeasurePreserving.ae_eq_comp (k.coe_l2 S.measure))
    filter_upwards [f.coe_l2 S.measure, hcomp] with x hfx hgx
    rw [hfx, hgx, RCLike.inner_apply']
  have hlim := (S.isUMixing_iff_lp_correlations P).mp h p hp (f.l2 S.measure) (k.l2 S.measure)
  rw [heq, integral_congr_ae (f.coe_l2 S.measure), integral_congr_ae (k.coe_l2 S.measure)] at hlim
  exact hlim

end Mixing
