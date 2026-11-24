module

import all Mixing.System
import all Mixing.ErgodicBarycenters
import all SixProblems.Definitions
import all SixProblems.BernoulliThreshold
import all SixProblems.BernoulliErgodic
import all SixProblems.BernoulliProposition
import all SixProblems.HilbertWeakCompactness
import all Mixing.SupportingJdLG.Core
import all Mixing.SupportingJdLG.Orbits
import all Mixing.SupportingJdLG.ReversibleOrbits
import all Mixing.SupportingJdLG.ReversibleAction
import all SixProblems.OrthogonalDecomposition
import all SixProblems.RealCompactAverage
import all SixProblems.RealCompactDensity
import all Mixing.SupportingJdLG.ReversibleTopology
import all Mixing.SupportingJdLG.Stable
import all SixProblems.CompactCoefficients
import all SixProblems.CompactOrthogonalGroup
import all SixProblems.CompactRealRealization
import all SixProblems.PositiveDefinite
import all SixProblems.PartitionRegularity
import all SixProblems.NiceRecurrence
import all SixProblems.ErgodicThresholdComparison
import all SixProblems.OperatorialRecurrenceGaussianKernel
import all SixProblems.OperatorialRecurrenceGaussian
import all SixProblems.OperatorialRecurrenceGaussianCharacters
import all SixProblems.OperatorialRecurrenceGaussianDensity
import all Mixing.WeakOperatorCompactness
import all Mixing.UltrafilterAction
import all Mixing.NormalOperator
import all Mixing.MixingFamilies
import all Mixing.SpectralDisjointness
import all Mixing.Koopman
import all Mixing.NilrotationGeometryDenseAction
import all Mixing.NilrotationKoopmanAction
import all SixProblems.Koopman
import all SixProblems.ProductErgodicity
import all SixProblems.OperatorialRecurrenceGaussianMixing
import all SixProblems.OperatorialRecurrenceTruncation
import all SixProblems.RealKoopman
import all SixProblems.StableCoefficients
import all SixProblems.ErgodicPDApproximation
import all SixProblems.NiceOperatorial
import all Mixing.CyclicSpectral
import all Mixing.CyclicMeasure
import all Mixing.CyclicL2
import all Mixing.StrongMixing
import all Mixing.SpectralDual
import all SixProblems.NiceSpectral
import all SixProblems.NiceEquivalence
import all SixProblems.PartitionRegularityTheorems
import all SixProblems.BernoulliSigns
import all SixProblems.FiniteScalarization
import all SixProblems.SignWitness
import all SixProblems.HaarDifferenceMixture
import all SixProblems.CompactVdCReverse
import all Mixing.CompactRepresentationAverage
import all Mixing.FourierUniqueness
import all Mixing.MildMixing
import all Mixing.SpectralMeasureClass
import all Mixing.SpectralOrthogonality
import all Mixing.SpectralMeasureSubmodule
import all Mixing.MaximalSpectralVector
import all SixProblems.CompactRepresentationDensity
import all SixProblems.HaarRecognition
import all SixProblems.CompactVdC
import all SixProblems.CorrespondenceAverages
import all SixProblems.CorrespondenceTiling
import all SixProblems.CorrespondenceQuasiTiling
import all SixProblems.CorrespondenceQuasiTilingCover
import all SixProblems.CorrespondenceQuasiTilingCoarsen
import all SixProblems.CorrespondenceModelCoarsening
import all SixProblems.Correspondence
import all SixProblems.CorrespondenceInverse
import all SixProblems.CorrespondenceCylinder
import all SixProblems.CorrespondenceSampling
import all SixProblems.CorrespondenceLocalModels
import all SixProblems.CorrespondenceTheorem
import all SixProblems.BoundedObservableRepresentative
import all SixProblems.OperatorialRecurrence
import all SixProblems.OperatorialRecurrenceHilbert
import all SixProblems.OperatorialRecurrencePolar
import all SixProblems.OperatorialRecurrenceSheppard
import all SixProblems
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Check the transitive kernel dependencies of the project declarations,
including private declarations exported through proof bodies. -/
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  let mut privateChecked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if let some modName := env.allImportedModuleNames[idx.toNat]? then
        if (`Mixing).isPrefixOf modName || (`SixProblems).isPrefixOf modName then
          let unexpected := (← collectAxioms name).filter fun axiomName ↦ !allowed.contains axiomName
          unless unexpected.isEmpty do
            throwError "Unexpected axioms of {name}: {unexpected}"
          checked := checked + 1
          if Lean.isPrivateName name then
            privateChecked := privateChecked + 1
  unless checked > 0 && privateChecked > 0 do
    throwError "Missing project declarations or private proof declarations"
  logInfo m!"Checked {checked} declarations, including {privateChecked} private names. Permitted axioms only."
