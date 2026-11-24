/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

public import Mixing.ChaconScaleReindex
public import Mixing.ChaconScalePeeling
public import Mixing.ChaconRemainderOperator

/-! # The checked signed factorization along varying Chacon scales -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace Mixing

/-- The moving-remainder estimate gives the required weak operator factor
for every integral normalized scale. -/
theorem chaconSmallRemainderFactorization_verified : ChaconSmallRemainderFactorization := by
  intro q m n s hn hs
  refine chaconUltrafilter_factor_of_prefix_error q m n s fun f g ↦ ?_
  let f' := chaconCenteredObservable f
  let g' := (chaconCenteredObservable g).conjugate
  obtain ⟨N, hN⟩ := chaconCenteredObservable_prefix g
  change Tendsto (fun j ↦ chaconRemainderError m (n j) (s j) f' g') (q : Filter ℕ) (𝓝 0)
  exact tendsto_chaconTower_movingRemainder_error_reindex hn hs m N
    f'.measurable g'.measurable
    (fun x b ↦ congrArg star (hN x b))
    g'.bound_nonneg f'.norm_le g'.norm_le

end Mixing
