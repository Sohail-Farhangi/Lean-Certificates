/-
Copyright (c) 2026 Sohail Farhangi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sohail Farhangi
-/
module

import all VdC.Applications
import all VdC.Basic
import all VdC.BoundedPET
import all VdC.CompactClosure
import all VdC.CompactSpectrum
import all VdC.Cube
import all VdC.CubeDifference
import all VdC.Difference
import all VdC.DigitCorrelation
import all VdC.DigitExamples
import all VdC.DigitLacunary
import all VdC.DigitSpectrum
import all VdC.DiscrepancySelection
import all VdC.Distribution
import all VdC.DuplicationBlocks
import all VdC.DuplicationDiscrepancy
import all VdC.DuplicationEstimates
import all VdC.DuplicationExample
import all VdC.DuplicationSpectrum
import all VdC.ErgodicCubeExamples
import all VdC.ErgodicDiscrete
import all VdC.ErgodicExamples
import all VdC.ErgodicWeakMixing
import all VdC.FourierTests
import all VdC.HalfFrequency
import all VdC.LagPairs
import all VdC.MixingHierarchy
import all VdC.OrbitRepresentation
import all VdC.Orthogonal
import all VdC.Periodogram
import all VdC.Permissible
import all VdC.PolynomialExample
import all VdC.PolynomialPhases
import all VdC.Realization
import all VdC.RectangleFourier
import all VdC.RectangleMeasure
import all VdC.Rectangles
import all VdC.RectangleTransfer
import all VdC.ResidueAverages
import all VdC.Selection
import all VdC.SpectralAC
import all VdC.SpectralMixing
import all VdC.SpectralOrthogonality
import all VdC.SpectralResults
import all VdC.SpectralScalars
import all VdC.SpectralSeparation
import all VdC.SpectralSequences
import all VdC.Spectrum
import all VdC.ThesisWeakMixing
import all VdC.Torus
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

#check VdC.exists_permissible_refinement
#check VdC.exists_joint_corr_spectrum
#check VdC.spectrallyLebesgue_of_limsup_square_summable
#check VdC.nearlyWeakMixing_of_upper_corr
#check VdC.cube_orthogonal_iff_lag_pairs
#check VdC.equidistributed_selected_of_sl_singular
#check VdC.equidistributed_selected_of_wm_compact
#check VdC.equidistributed_pair_of_sl_singular
#check VdC.equidistributed_pair_of_wm_compact
#check VdC.spectral_difference_from_fourier
#check VdC.weakMixing_difference_from_fourier
#check VdC.spectral_difference_theorem
#check VdC.weakMixing_difference_theorem
#check VdC.finite_fourier_rectangle_bound
#check VdC.cube_spectral_difference_theorem
#check VdC.cube_weakMixing_difference_theorem
#check VdC.cube_compact_iff_centeredHalfFrequencies
#check VdC.cube_sSingular_iff_centeredHalfFrequencies
#check VdC.hasPositiveLowerDensity_iff
#check VdC.thesis_four_characterizations_weakMixing
#check VdC.ae_tendsto_orbitCesaro
#check VdC.ae_constructingSequences_cube
#check VdC.spectrallySingular_digitResidue_enumeration
#check VdC.tendsto_digitResidue_density
#check VdC.thueMorse_positive_spectrallySingular
#check VdC.polynomialLikeCounterExample
#check VdC.equidistributed_iff_rectangleDiscrepancy_tendsto_zero
#check VdC.duplication_upper_discrepancy_ge_half
#check VdC.exampleNecessitatingPermissibleTriples

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`VdC).isPrefixOf name || name.toString.startsWith "_private.VdC." then
      let axioms ← collectAxioms name
      let unexpected := axioms.filter (fun ax => !allowed.contains ax)
      unless unexpected.isEmpty do
        throwError "Unexpected transitive axioms in {name}: {unexpected.toList}"
      checked := checked + 1
  unless checked > 0 do
    throwError "No certificate declarations were found"
  logInfo m!"Checked {checked} declarations. Only propext, Classical.choice, Quot.sound permitted."
