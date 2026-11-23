/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/

module

import all JdLG.AmenableGroup
import all JdLG.AverageLimits
import all JdLG.CommonWeakDecay
import all JdLG.CompactDenseGroup
import all JdLG.CompactSeparateOscillation
import all JdLG.ContinuousTestDual
import all JdLG.ContractiveCriterion
import all JdLG.Core
import all JdLG.Decomposable
import all JdLG.DensityComplements
import all JdLG.DensityDiagonal
import all JdLG.DiscreteFolnerVariation
import all JdLG.Dual
import all JdLG.ExactBlockMeans
import all JdLG.FixedPoints
import all JdLG.FolnerBanachDensities
import all JdLG.FolnerCriteria
import all JdLG.FolnerMeasuredMeans
import all JdLG.GroupAdmissibility
import all JdLG.HilbertCompactness
import all JdLG.Largeness
import all JdLG.LeftFolnerCounterexample
import all JdLG.LeftFolnerCounterexampleCounting
import all JdLG.LpAdmissibility
import all JdLG.LpConvexity
import all JdLG.LpSmoothness
import all JdLG.LpUniformConvexity
import all JdLG.MarkovLp
import all JdLG.MarkovOperators
import all JdLG.MarkovSimple
import all JdLG.MarkovTransfer
import all JdLG.MeasuredCriteria
import all JdLG.MeasuredMeans
import all JdLG.MeasuredReturns
import all JdLG.MeasuredTransfer
import all JdLG.MonotheticL1
import all JdLG.MonotheticL1Generated
import all JdLG.MonotheticL1Mean
import all JdLG.MonotheticL1Modulus
import all JdLG.MonotheticL1Order
import all JdLG.MonotheticL1Support
import all JdLG.Orbits
import all JdLG.PaperExamplesBilateral
import all JdLG.PaperExamplesDecay
import all JdLG.PaperExamplesFinite
import all JdLG.PaperExamplesIntegerWapMean
import all JdLG.PaperExamplesParity
import all JdLG.PaperExamplesParityAmbient
import all JdLG.PaperExamplesParityAmenability
import all JdLG.PaperExamplesParityCyclic
import all JdLG.PaperExamplesParityFolner
import all JdLG.PaperExamplesParityMean
import all JdLG.PaperExamplesParityWap
import all JdLG.PaperExamplesParityWapAction
import all JdLG.PaperExamplesPowers
import all JdLG.PaperExamplesPowersWap
import all JdLG.PaperExamplesPowersWapMean
import all JdLG.PaperExamplesPowersWeak
import all JdLG.PaperExamplesRigid
import all JdLG.PaperExamplesRigidComplete
import all JdLG.PaperExamplesRigidDensity
import all JdLG.PaperExamplesRigidSum
import all JdLG.PaperExamplesRigidityAWS
import all JdLG.PaperExamplesRigidityCircle
import all JdLG.PaperExamplesRigidityExistence
import all JdLG.PaperExamplesRigidityMultiplier
import all JdLG.PaperExamplesRigidityPhases
import all JdLG.PaperExamplesRowReturns
import all JdLG.PaperExamplesRows
import all JdLG.PaperExamplesWapAction
import all JdLG.PaperExamplesWapClosed
import all JdLG.PolynomialFolner
import all JdLG.PolynomialShifts
import all JdLG.PolynomialSpectral
import all JdLG.PolynomialVdC
import all JdLG.PolynomialWeakMixing
import all JdLG.PrintedClaimCounterexample
import all JdLG.Quotient
import all JdLG.RadonWeakDecay
import all JdLG.ReflexiveAdjoints
import all JdLG.ReflexiveCompactness
import all JdLG.RepresentationNormGroup
import all JdLG.RepresentationRenorm
import all JdLG.RepresentationRenormComplete
import all JdLG.RepresentationUnitaryContinuity
import all JdLG.Restriction
import all JdLG.ReversibleAction
import all JdLG.ReversibleBasis
import all JdLG.ReversibleCircle
import all JdLG.ReversibleCircleAction
import all JdLG.ReversibleClosure
import all JdLG.ReversibleCoefficients
import all JdLG.ReversibleConvolution
import all JdLG.ReversibleFiniteSystems
import all JdLG.ReversibleHaar
import all JdLG.ReversibleHilbertSum
import all JdLG.ReversibleIrreducible
import all JdLG.ReversibleOrbitFunctions
import all JdLG.ReversibleOrbits
import all JdLG.ReversibleRegular
import all JdLG.ReversibleRepresentation
import all JdLG.ReversibleSpan
import all JdLG.ReversibleSubspace
import all JdLG.ReversibleTopology
import all JdLG.ReversibleUnitarization
import all JdLG.ReversibleUnitary
import all JdLG.ReversibleUnitaryRestriction
import all JdLG.RightZeroExample
import all JdLG.SeparableWeakDecay
import all JdLG.SeparateAveraging
import all JdLG.Stable
import all JdLG.StableBiMean
import all JdLG.StableMeans
import all JdLG.StableOperator
import all JdLG.StableReturns
import all JdLG.StoneCechSeparateContinuity
import all JdLG.Subdirect
import all JdLG.UltrafilterMore
import all JdLG.UltrafilterMoreCanonical
import all JdLG.UltrafilterMoreDelta
import all JdLG.UltrafilterMoreDeltaSequences
import all JdLG.UltrafilterMoreDensity
import all JdLG.UltrafilterMoreDiscreteMean
import all JdLG.UltrafilterMoreFractions
import all JdLG.UltrafilterMoreGroup
import all JdLG.UltrafilterMoreIdeal
import all JdLG.UltrafilterMoreMeasure
import all JdLG.UltrafilterMoreOre
import all JdLG.UltrafilterMoreQuotientFacts
import all JdLG.UltrafilterMoreResults
import all JdLG.UltrafilterMoreStable
import all JdLG.UltrafilterMoreStoneCech
import all JdLG.Ultrafilters
import all JdLG.UniformConvexReflexivity
import all JdLG.WapCompactification
import all JdLG.WapInvariantMeans
import all JdLG.WapStronglyAlmostPeriodic
import all JdLG.WapSubspace
import all JdLG.WapTranslationDecomposition
import all JdLG.WeakCompactApproximation
import all JdLG.WeakCompactCountableChain
import all JdLG.WeakCompactFragmentation
import all JdLG.WeaklyAlmostPeriodic
import all Palomar.Solution
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

#print axioms JdLG.Submission.decomposition
#print axioms JdLG.Submission.ultrafilter_projection
#print axioms JdLG.Submission.thicklySyndetic_returns
#print axioms JdLG.Submission.unique_fixed_points
#print axioms JdLG.Submission.lp_contractions
#print axioms JdLG.Submission.group_admissible
#print axioms JdLG.Submission.radon_density_one_weak_decay
#print axioms JdLG.Submission.strict_convexity_contractions
#print axioms JdLG.Submission.strict_convexity_counterexample

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  let mut privateChecked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some modName := env.allImportedModuleNames[idx.toNat]? then
        if (`JdLG).isPrefixOf modName || modName == `Palomar.Solution then
          let unexpected := (← collectAxioms name).filter (fun axiomName ↦ !allowed.contains axiomName)
          unless unexpected.isEmpty do
            throwError "Unexpected axioms of {name}: {unexpected}"
          checked := checked + 1
          if Lean.isPrivateName name then
            privateChecked := privateChecked + 1
  unless checked > 0 && privateChecked > 0 do
    throwError "Missing project declarations or private proof declarations"
  logInfo m!"Checked {checked} declarations, including {privateChecked} private names. Permitted axioms only."
