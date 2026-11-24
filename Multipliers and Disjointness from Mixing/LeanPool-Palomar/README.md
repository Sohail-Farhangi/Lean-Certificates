# Multipliers and Disjointness from Mixing

This project formalizes the numbered results and examples in *Multipliers and Disjointness from Mixing* by Sohail Farhangi, Joel Moreira, and Rigoberto Zelada. The table below maps the paper to the Lean declarations and describes the formulations used in the certificate. [arXiv:2604.12915v2](https://arxiv.org/abs/2604.12915v2)

The project pins Lean 4.36.0 and Mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. From the project directory, run the following commands with that toolchain available through Elan.

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

The main import is `Mixing`. The build treats warnings as errors. The audit traverses dependencies of every declaration in the imported project modules, including private names, and checks that the only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`System.lean` introduces measure-preserving group actions, joinings, and factor maps. `Koopman.lean` constructs the full and mean-zero representations. `UltrafilterAction.lean` constructs the weak limits. `GeneratedSigma.lean` specifies the generated σ-algebra modulo null sets. `MainTheorems.lean` combines the operator and joining results. `EventMixing.lean` connects the Koopman formulation of mixing to the paper's event formulation. The standalone folder contains the same imported proofs in one Lean file and a plain-text article map.

The inherited library modules are identified by their source headers. The formalization code is released under Apache-2.0. Codex produced Lean material and checked it against the pinned environment.

## Lean Pool and Palomar layout

The repository-proposal workflow for Lean Pool uses the `Mixing` library. The Palomar configuration compares Theorems 1.2, 5.1, and 6.3 and Lemma 10. The independently stated `Palomar/Challenge.lean` has the expected comparison placeholders. `Palomar/Solution.lean` gives the proved declarations. `formalization.yaml` records sources, scope, authorship, and use of Codex. [Lean Pool contribution guide](https://github.com/LeanPool/lean-pool/blob/main/CONTRIBUTING.md). [Palomar submission guide](https://palomar-registry.org/how-to-submit).

Run `lake build +Palomar.Solution` to check the comparison proofs. The four targets passed local replay of the Lean exports in Lean and NanoDa. The Windows replay used the prebuilt exports. For a Palomar submission, select the modular-only commit linked from the repository README and use the repository root as the project path. Its source-file limit applies to the whole commit. Registry review is separate from these local checks. [Palomar source and comparison rules](https://palomar-registry.org/how-to-submit)

## Paper coverage

The table follows the section-based numbering in the arXiv HTML rendition. The PDF calls Theorems 1.1, 1.2, 1.3, 2.1, 3.1, 5.1, 5.2, 6.1, 6.2, and 6.3 Theorems 1 through 10, respectively. The other result numbers agree. [arXiv v2 PDF](https://arxiv.org/pdf/2604.12915v2).

| Paper | Lean declarations and coverage |
| --- | --- |
| Theorem 1.1 | `theorem1_1_i_countableGroup` in `GroupIdentityDisjointness.lean`, `theorem1_1_ii` in `RotationDuality.lean`, `theorem1_1_iii` in `RigidGeneratedSystems.lean`, and `theorem1_1_iv` in `EntropyDuality.lean` check the four dualities. The entropy proof builds a common zero-entropy factor from the conditional event probabilities of a nonproduct joining. |
| Theorem 1.2 | `theorem1_2` in `MainTheorems.lean`, using the mean-zero Koopman definition of strong mixing. |
| Theorem 1.3 | `theorem1_3` gives all three equivalences using the mean-zero Koopman form of (iii). `theorem1_3_events` gives the event formulation. `System.isUGenerated_iff_generatedSigma_eq` identifies the density definition of a generated system with the generated σ-algebra. |
| Corollary 1 | `corollary1` in `MainTheorems.lean`, including generation and nontriviality of the resulting factor. |
| Lemma 1 | `lemma1_i` in `JoiningDisintegration.lean`, `lemma1_ii` in `ComponentExtremality.lean`, and `lemma1_iii` in `ComponentDisjointness.lean` cover all three parts. The measurable selections for (ii) and (iii) use compact Boolean orbit spaces. The selected laws pull back to kernels on the original spaces. |
| Theorem 2.1 and Lemma 2 | `theorem2_1_of_dense_finiteModules` and `lemma2_of_dense_finiteModules` in `ModuleFrameDensity.lean` use the dense finite invariant module definition from §2.1. Conditional Gram–Schmidt supplies bounded relative frames. `theorem2_1_homogeneous_quotient` in `CompactQuotientSkew.lean` checks the homogeneous skew-product case directly. |
| Corollary 2 | `corollary2_i_of_dense_finiteModules` and `corollary2_ii_of_dense_finiteModules` in `ModuleFrameDensity.lean` prove the class-level disjointness and multiplier conclusions. `corollary2_iii_of_invariantModuleTower` proves (iii) for distal systems presented by their finite-module successor stages and spanning inverse limits. |
| Lemma 3 | `lemma3` in `JoiningExtreme.lean` proves that the product measure is an extreme joining when one system is weakly mixing. |
| Lemmas 4–5 | `NormalOperator.lean` proves the range-kernel decomposition, including the formula for the closed span of the ranges of a family. |
| Propositions 1–2 | `UltrafilterLimits.lean`, `UltrafilterAction.lean`, and `NormalOperator.lean` cover the existence and algebra of the limits and the kernel identities. |
| Proposition 3 | `MixingFamilies.lean` proves the characterizations using the closed left ideal generated by the ultrafilter family. |
| Theorem 3.1 and Corollary 3 | `theorem3_1` and `corollary3` in `SpectralDisjointness.lean`. The definition of spectral disjointness is the vanishing of all bounded intertwiners. |
| Proposition 4 and Corollary 4 | `WeakMixing.lean` and `WeakMixingBridge.lean` prove the density-one, essential-idempotent, and smallest-ideal criteria. |
| Proposition 5 and Lemmas 6–7 | See `MildMixing.lean` for the idempotent-ultrafilter results. |
| Proposition 6 | `StrongMixing.lean` proves the cofinite, sequential, and free-ultrafilter characterizations. |
| Corollary 5 | `StrongMixing.lean` covers (i) and (ii). `SpectralApproximation.lean` proves the trigonometric approximation criterion in (iii). |
| Lemma 8 | `lemma8` and `System.generatedSigma_idempotent`. |
| Lemma 9 | `lemma9` and `lemma9_generatedSigma`. The joining may use a different ultrafilter family at each coordinate. |
| Example 1 | `example1_nilrotation` in `NilrotationGeneralSpectrum.lean` gives the spectral splitting, free weak limits, generated factor, distality, and Furstenberg disjointness. `nilrotationQuotient_purePoint_or_countableLebesgue` gives an actual bilateral-shift basis of countably infinite multiplicity whenever the Kronecker orthogonal complement is nonzero. `nilrotationQuotient_range_eq_purePointPart` identifies the range of every free weak limit. The theorem uses a second-countable, locally connected nilpotent topological group, a closed cocompact stabilizer, and an invariant probability. These hypotheses apply to the paper's Lie nilmanifolds with discrete cocompact stabilizer. |
| Example 2 | `chaconTowerSystem` constructs the Chacon tower over the ternary odometer. `chaconTower_weakLimit_convex_powers` shows that for every free time ultrafilter the full Koopman weak limit is either the orthogonal projection onto constants or a finite convex combination of integer powers. `example2_chaconTower` proves the resulting ultrafilter-by-ultrafilter mixing or generation and spectral-disjointness alternatives. The proof uses height-polynomial recurrences in `ChaconWeakLimitRecursion.lean`, adjacent-column estimates in `ChaconSubHeight.lean`, signed remainders in `ChaconScaleSignedFactor.lean`, and finite termination in `ChaconDecayTermination.lean`. |
| Example 3 | `ae_mem_rudinShapiroSubshift` proves support of the invariant law on the subshift. `rudinShapiro_half_rigid` proves half-rigidity for all measurable events. `rudinShapiro_phaseConditionalLaw_twoPoint` proves two-point fibres with equal weights, and `rudinShapiroPhasePullback_range_eq_purePointPart` identifies the phase factor with the Kronecker subspace. `rudinShapiro_hasLebesgueComplement` proves exact multiplicity two. `example3_rudinShapiro_generatedSigma` proves the factor identity for every nonempty family of free ultrafilters. `rudinShapiro_half_rigid_noninjective` checks the endpoint in Proposition 7(i). |
| Example 4 | `example4_alternating_binary_gaussian` in `AlternatingDigitSystems.lean` constructs the example using stationary Gaussian systems from alternating blocks of binary digits. It checks generation by two ultrafilters, failure of singleton generation, and the nonzero strongly mixing complement. `exists_common_mixingSet_prefixDensity_one` proves (10). The direct construction supplies this example independently of the cited prescribed-set theorem. |
| Example 5 | `CantorFourier.lean`, `CantorSpectral.lean`, `CantorEigenvectors.lean`, and `CantorGenerated.lean` prove the Fourier formula, eigenvectors, existence of a free generating ultrafilter, and the nonzero annihilated vector. `CantorSpeedFactor.lean` proves the exact generated σ-algebra of the speed-two factor. `example5_generated_and_mixing_spectral_overlap` in `CantorGaussianMixing.lean` constructs a stationary Gaussian system mixing along the same ultrafilter and proves spectral non-disjointness. |
| Example 6 | `CantorSpectral.lean` proves (13). `CantorLebesgueSpectrum.lean` identifies the fibre-character spectral measure with Haar measure on the circle. The two-ultrafilter generation, explicit factor map, and failure of generation by all free ultrafilters are checked in `CantorProductGeneration.lean` and `CantorSumNongeneration.lean`. |
| Example 7 | `CantorProductGeneration.lean` proves singleton generation of the source product. `example7_productFactor` and `example7SumFactor` check the factor maps to the speed-two product and the sum-coordinate factor, which fails generation by all free ultrafilters. |
| Theorem 5.1 | `theorem5_1_events` in `PartialRigidityDisjointness.lean` uses the event-correlation hypotheses on partial rigidity and partial mixing. `theorem5_1` uses the equivalent weak-operator matrix coefficients. |
| Theorem 5.2 | `theorem5_2_finiteFibres` and `theorem5_2_ergodicPointExtension` prove finite support, the common cardinality bound in the ergodic case, and equal fibre weights. `System.standardGeneratedFactorMap_completedPullbackSigma` identifies the resulting standard Borel factor with the generated σ-algebra modulo null sets. |
| Proposition 7 | `RigidInjectivity.lean` and `PartialMixingDefinitions.lean` prove (i) and (ii) from the event hypotheses. `InjectiveLimits.lean` proves the generated-factor and spectral disjointness consequences of injectivity on mean-zero L². |
| Theorem 6.1 | `theorem6_1_i` through `theorem6_1_iv` in `SystemSpectralType.lean` prove the four spectral-type formulations. `MaximalSpectralVector.lean` supplies the maximal vector. `SpectralTypeDisjointness.lean` identifies spectral disjointness with mutual singularity. |
| Theorem 6.2 and Corollary 6 | `theorem6_2` and `corollary6` in `SystemSpectralType.lean` prove the positive-measure-class multiplier implications using `SpectralMultiplier.lean`. |
| Theorem 6.3 | `System.disjoint_joining_of_isUGenerated` in `GeneratedMultiplier.lean` proves the multiplier property. The equivalence with the generated σ-algebra is checked in `MainTheorems.lean`. |
| Corollary 7 | `corollary7_i` and `corollary7_ii` in `FactorJoiningLift.lean` and `corollary7_iii` in `AtomicMultiplierExtension.lean` prove the multiplier conclusions. The last proof uses a uniform lower bound on conditional atom masses. |
| Lemma 10 | `tendsto_inner_zero_of_fubini_correlations` in `VanDerCorput.lean` proves (23)–(24), grouping the earlier and later coordinates into the first and last ultrafilters. `tendsto_weak_zero_of_fubini_correlations` gives the weak convergence consequence. |
| Lemma 11 | `lemma11` in `GeneratedMultiplier.lean` proves Eq. (25) for bounded observables in an actual joining. |

### Proofs behind the first two examples

The nilrotation proof uses closed lower-central quotient stages with compact abelian fibres. In `NilrotationBracketWords.lean` and `NilrotationMultilinearDensity.lean`, the top iterated commutator is multiplicative in each coordinate modulo the next lower-central term. Density of the time orbit and compactness of the original quotient extend the lattice identities one coordinate at a time. `NilrotationBracketPhases.lean` uses this argument to get the circle of time phases. `NilrotationVerticalDecay.lean` obtains Haar type on each nontrivial mode. `NilrotationRegularEmbedding.lean` bounds the multiplicity above, the distinct vertical modes supply the reverse embedding, and `NilrotationLebesgueBasis.lean` obtains an actual bilateral-shift basis. A quotient whose commutator action is trivial can have an empty Lebesgue complement. [Ackelsberg, Richter, and Shalom](https://arxiv.org/abs/2307.07213v1)

For Chacon, an arbitrary free ultrafilter is reduced to height multiples with smaller signed remainders. When no multiplication by a power of three makes the normalized limit an integer, the correlation bound involves both adjacent height polynomials, which decay along the corresponding ternary prefixes. In the other case the weak limit factors through a height polynomial or its adjoint. A bound on products rules out an infinite factorization of a nonzero limit. The resulting finite combination has real nonnegative weights summing to one. [Janvresse, Prikhod’ko, de la Rue, and Ryzhikov](https://arxiv.org/abs/1301.2904v1)
