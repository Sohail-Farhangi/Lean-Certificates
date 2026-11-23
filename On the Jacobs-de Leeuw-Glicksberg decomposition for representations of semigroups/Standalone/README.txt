JDLG STANDALONE CERTIFICATE

On the Jacobs-de Leeuw-Glicksberg decomposition for representations of
semigroups, by Micky Barthmann, Sohail Farhangi and Yulia Kuznetsova.

Public reference
https://arxiv.org/abs/2509.24003v3

The guide follows the public v3 numbering and covers the revised
Theorem 1.2(iv) with contractions. In Lean, the assumption that every
operator has norm at most one is written as ∀ s, ‖π s‖ ≤ 1.
Search for JdLG.admissible_of_strictConvex_contractions. The matching
Palomar entry is JdLG.Submission.strict_convexity_contractions.
The strict-convexity counterexample concerns the public v3 statement.

Start with JdLG.decomposition_of_admissible to see how the minimal
idempotent projects onto the reversible part. IsJdLGAdmissible names
compactness of the weak operator closure and uniqueness of its minimal
idempotent. See the index below for each numbered result and example.

Compile with the sibling LeanPool-Palomar project's pinned environment.
From LeanPool-Palomar, run

  lake exe cache get
  lake env lean -DwarningAsError=true -R ../Standalone ../Standalone/JdLGStandalone.lean

The project pins Lean 4.36.0 and Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842. The standalone proof file imports
Mathlib and uses the same mathematical declarations as the modular project.
The permitted axioms are propext, Classical.choice, and Quot.sound.

PAPER-TO-LEAN INDEX

The table below uses the public v3 numbering. Search for the Lean names in
JdLGStandalone.lean. The source section markers identify the corresponding
files in the modular project.

The names below are in namespace JdLG unless a different namespace is
shown. In the folder, the source is in JdLG/<module>.lean. In the standalone
file, search for the same declaration or its Source: JdLG/<module>.lean
heading. This index uses the numbering of public arXiv v3 and includes the author-reported revision of Theorem 1.2(iv).
Article (https://arxiv.org/abs/2509.24003v3).

SECTION 1


Equation (1), Theorem 1.1
  Decomposable proves isJdLGDecomposable_iff_isJdLGAdmissible and
  isJdLGDecomposable_iff_exists_biInvariantMean for closed invariant
  complementary subspaces. decomposition_of_admissible in Core constructs
  the commuting projection and gives the pointwise range and kernel
  criteria.

Theorem 1.2(i)
  Core proves admissible_of_commutative.

Theorem 1.2(ii)
  ContractiveCriterion proves admissible_of_hilbert_contractions for complex
  Hilbert spaces, including weak operator compactness in HilbertCompactness.

Theorem 1.2(iii)
  MarkovOperators proves admissible_probabilityMarkov for complex
  probability L^1. The Markov convention is positivity, preservation of the
  constant one, and preservation of the integral. The proof derives both
  contraction bounds and transfers the L^2 result along a dense inclusion.

Theorem 1.2(iv)
  ContractiveCriterion proves the revised criterion as
  admissible_of_strictConvex_contractions. The operators are contractions,
  the primal and dual norms are strictly convex, and the weak operator
  closure is compact. The comparison entry is
  JdLG.Submission.strict_convexity_contractions.
  PrintedClaimCounterexample.printed_theorem_1_2_iv_counterexample concerns
  the v3 statement without the contraction hypothesis.

Theorem 1.2(v)
  admissible_of_complexLp_contractions in LpAdmissibility proves the
  criterion for complex L^p over any measure space and 1<p<\infty.
  LpConvexity, LpUniformConvexity, and LpSmoothness prove the geometric
  hypotheses. UniformConvexReflexivity proves Goldstine's theorem and
  Milman–Pettis and derives dual strict convexity from the uniqueness of
  norming functionals.

Remark after Theorem 1.2
  isCompact_weakOperatorClosure_iff_uniformlyBounded_of_reflexive proves the
  reflexive-space remark. admissible_monotheticLpOne_of_dunfordSchwartz in
  MonotheticL1 proves the finite-measure Dunford–Schwartz criterion.
  admissible_generatedLpOne_of_meanErgodicModulus in MonotheticL1Generated
  proves the criterion on the generated subsemigroup for a supplied positive
  contractive mean-ergodic linear modulus. The same module gives the
  criterion for a Dunford–Schwartz generator.

Theorem 1.3
  WeaklyAlmostPeriodic proves admissible_of_WapBiInvariantMean for the real
  WAP function space. The operator pullback is WAP by weak continuity of
  separately continuous compact families.

Corollary 1.4
  MeasuredCriteria proves admissibility for a bi-amenable measured
  semigroup. admissible_of_group in GroupAdmissibility covers arbitrary
  groups with compact WOT closure. CompactSeparateOscillation and
  CompactDenseGroup supply the separately continuous compact-host argument.
  admissible_iff_of_equal_weakOperatorClosures handles any representation
  with the same closure in either branch.

Theorem 1.5(i)
  See Theorem 3.6 below.

Theorem 1.5(ii), equation (2)
  StableOperator.lean gives weakOrbitClosure_iff_compactMeanMoments.
  StableBiMean.lean obtains the group ideal from the bi-invariant mean, and
  the p=1 specialization gives the formula.

Theorem 1.6
  AmenableGroup proves amenable_group_decomposition_and_folner_coefficient
  for admissibility, norm-precompact group orbits, and the fixed-dual
  coefficient criterion. LeftFolnerCounterexampleCounting refutes the
  uniform claim for left Følner nets.

Remark after Theorem 1.5
  WapTranslationDecomposition proves the complex WAP direct sum for
  semitopological monoids. stable_iff_absolute_mean_eq_zero identifies the
  almost weakly stable summand with the functions whose absolute value has
  zero mean. WapStronglyAlmostPeriodic identifies the reversible summand
  with the closed span of continuous finite-dimensional unitary coefficients
  and proves the SAP direct sum.


SECTION 2


§2.1 and §2.2
  WapCompactification proves the real WAP compactification with the
  canonical continuous dense homomorphism, unique continuous extensions, and
  isometric restriction. WapInvariantMeans proves the equivalence with
  separate left and right means, uniqueness, the group-ideal criterion, and
  existence for arbitrary topological groups. Core, ReversibleTopology,
  StableMeans, and ReversibleHaar construct the compact group ideal and
  prove the Haar mean formula.

Examples 2.1 and 2.2
  PaperExamplesFinite proves the multiplication and adjoint formulas, the
  primal invariant-subspace and stable-axis descriptions, and the dual
  reversible-axis description. The axis unions are checked to fail the
  specified linearity or invariance.

Theorem 2.3(i)
  Restriction proves admissible_restriction.

Theorem 2.3(ii)–(iii)
  Quotient proves admissible_surjective_intertwiner and
  admissible_quotient_representation.

Theorem 2.3(iv)
  Dual proves decomposition_adjoint_of_admissible under the adjoint WOT
  compactness hypothesis. ReflexiveAdjoints proves the footnote that this
  additional compactness follows from primal WOT compactness when the space
  is reflexive.

Theorem 2.3(v)
  Subdirect proves subdirect_product_of_admissible, including the absorbing
  zero in the stable factor.

§2.3 and §2.4
  FolnerMeasuredMeans constructs left, right and two-sided invariant means
  on actual real L^\infty as ultrafilter limits of normalized compact
  blocks. DiscreteFolnerVariation proves the total-variation formula and the
  equivalence with the discrete strong Følner condition.
  FolnerBanachDensities realizes the limsup and liminf as values of
  generated means and proves the Følner–Banach inequalities.
  DensityComplements proves the lower–upper Banach density complement
  identity. RepresentationRenorm and RepresentationRenormComplete give the
  equivalent orbit norm and completeness. RepresentationNormGroup gives the
  norm topology on bounded subgroups of units.
  RepresentationUnitaryContinuity proves strong continuity for weakly
  continuous unitary families.

Definition 2.4 and §2.5
  Mathlib Filter with NeBot and Ultrafilter realize the paper's definitions.
  Ultrafilters formalizes compact-host extension and the piecewise-syndetic
  characterization. UltrafilterMoreStoneCech gives naturality and
  multiplicativity. UltrafilterMoreDensity, UltrafilterMoreIdeal and
  UltrafilterMoreDiscreteMean give essential ultrafilters, the ambient left-
  ideal assertions, and the equivalence of discrete set density with the
  Mathlib counting-measure mean. UltrafilterMoreDeltaSequences gives the
  iterated-difference and ultrafilter equivalences.

Right-topological extension in §2.5
  UltrafilterMoreCanonical.exists_distinct_rightTopological_extension_nat
  refutes uniqueness with right-translation continuity alone.
  ultrafilter_mul_unique_of_principal_left_continuous proves uniqueness with
  the principal-left continuity condition.
  existsUnique_continuous_surjective_ultrafilterLift verifies the universal
  extension to a compact semitopological host. StoneCechSeparateContinuity.n
  o_separatelyContinuous_ultrafilter_extension_freeMonoid exhibits a
  discrete monoid for which separate continuity is impossible.
  leftTopologicalUltrafilterMul constructs the left-topological product for
  every discrete semigroup.

Lemma 2.5
  Largeness proves thicklySyndetic_principal_right_ideal.

Proposition 2.6 and preceding Ore examples
  UltrafilterMoreFractions proves existsUnique_rightFractionLift for the
  given group of right quotients. UltrafilterMoreOre proves
  exists_groupOfRightQuotients. UltrafilterMoreQuotientFacts verifies the
  two illustrative embeddings and the ideal intersections.


SECTION 3


Theorem 3.1
  ReversibleAction proves reversible_iff_precompactOrbit_of_separated.
  ReversibleOrbits proves unconditional norm compactness of reversible
  orbits. Equation (6) is
  GroupIdeal.reversibleSubmodule_eq_irreducibleUnitarySystem_span in
  ReversibleBasis.

Corollary 3.2
  ReversibleAction proves group_reversible_iff_precompactOrbit for
  admissible group representations.

Example 3.3
  PaperExamplesDecay represents 2^{-n} on ℂ. Every norm orbit is precompact,
  every vector is almost weakly stable, and only zero is reversible.

Proposition 3.4
  FixedPoints proves decomposition_of_unique_fixed_point.

Example 3.5
  RightZeroExample gives the constant functions and the union of the
  coordinate axes. PaperExamplesFinite.rightZero_nonunique_splitting
  exhibits the two splittings.

Theorem 3.6
  ReversibleRepresentation proves
  reversible_weaklyEquivalent_unitary_hilbertSum, the Banach-space claim
  with both coefficient containments and a Hilbert direct sum.
  ReversibleUnitarization proves
  GroupIdeal.reversibleAction_equivalent_unitary for the Hilbert-space
  claim. ReversibleClosure gives the multiplicative homeomorphism with the
  reversible WOT closure.

Remark after Theorem 3.6
  ReversibleCircle classifies the irreducible invariant systems as the
  individual monomials and proves that their span is proper. It also rules
  out an orthogonal Hilbert-sum equivalence with those monomial spaces.
  ReversibleCircleAction proves admissibility and reversibility of the
  rotation action.


SECTION 4


Lemma 4.1
  WeaklyAlmostPeriodic proves stable_iff_wapCoefficientMoments on the actual
  real WAP mean, with both power quantifiers. StableOperator gives the
  compact-host criterion used in Theorem 1.5(ii).

Theorem 4.2(i)–(iv)
  MeasuredCriteria proves stable_iff_measuredCoefficientMoments,
  stable_iff_measuredWeakReturns and
  stable_iff_lowerBanachDensityWeakReturns. MeasuredTransfer pulls back
  continuous tests and takes the infimum over left-invariant means on
  L^\infty.

Theorem 4.2(v)–(vii)
  FolnerCriteria proves stable_iff_folnerCoefficientMoments and
  stable_iff_folnerWeakReturns for normalized probabilities satisfying the
  left Følner total-variation test condition.
  stable_iff_lowerFolnerDensityWeakReturns takes the infimum of the liminf
  densities over any nonempty family of these nets.

Theorem 4.2(viii)
  LeftFolnerCounterexampleCounting proves
  counting_uniform_powerAverage_counterexample with the actual normalized
  counting measures. An almost weakly stable vector has every fixed
  coefficient average tending to zero while the dual-ball supremum is one at
  every positive power. countingBiInvariantMean verifies bi-amenability of
  the finitary permutation group.

Theorem 4.2(ix)
  density_one_weak_tendsto_iff_measuredBlocks in RadonWeakDecay proves (vi)
  ↔ (ix) for compact Radon blocks of increasing mass.
  stable_iff_folner_density_one_weakDecay_of_radon connects the criterion to
  stability. WeakCompactFragmentation and WeakCompactCountableChain give the
  countable weak neighborhood basis on a common conull compact support. No
  separability of the acting Banach space is assumed.

Corollary 4.3
  CommonWeakDecay proves exists_common_weakDecay_of_measuredFolnerSequence
  for the compact Følner blocks and the norm-separable stable subspace.

Example 4.4
  PaperExamplesParity and PaperExamplesParityFolner give the paper's
  multiplication, disjoint left ideals, and left Følner sequence.
  PaperExamplesParityAmenability verifies the amenable ambient group of
  right quotients. PaperExamplesParityWap verifies the WAP mean obstruction.
  PaperExamplesParityWapAction gives the full complex WAP representation,
  the almost weakly stable vector, and equation (15).

Example 4.5
  PaperExamplesRows gives the actual row Følner net on ℤ × ℕ₀.
  PaperExamplesBilateral and PaperExamplesRowReturns give the bilateral
  shift, its almost weakly stable test vector, full weak-return density and
  the obstruction to a density-one set of weak convergence.

Examples 4.6 and 4.7
  PaperExamplesRigid, PaperExamplesRigidDensity and PaperExamplesRigidSum
  give the bounded-gap and direct-sum obstructions.
  PaperExamplesRigidityExistence proves exists_rigid_unitary_component using
  a concrete atomless probability and circle multiplication on L^2.
  PaperExamplesRigidComplete.example46 and
  PaperExamplesRigidComplete.example47 give the final examples, including
  the literal nonseparable direct sum.


SECTION 5


Lemma 5.1(i), (iii)
  UltrafilterMore proves reversible_tendsto_of_idempotent and
  stable_tendsto_of_mem_closure_smallestIdeal.

Lemma 5.1(ii), (iv)
  UltrafilterMoreResults proves reversible_tendsto_of_inverse_product.
  UltrafilterMoreStable proves stable_tendsto_of_essential, using the
  finitely additive discrete set-mean model.

Theorem 5.2(i)–(iv)
  Ultrafilters proves ultrafilter_limit_eq_jdlg_projection.
  UltrafilterMoreResults gives the inverse-product result for the closed
  smallest ideal. UltrafilterMoreStable gives
  GroupIdeal.tendsto_projection_of_essential_idempotent and
  GroupIdeal.tendsto_projection_of_inverse_product_essential. The inverse-
  product claims use a supplied group of right quotients. Essential
  ultrafilters use the discrete set-mean model.

Theorem 5.3(i)–(iii)
  reversible_iff_norm_return_isIPStar,
  stable_iff_thicklySyndetic_weak_return and
  reversible_iff_norm_return_meets_all_isDeltaSet in the JdLG namespace. The
  last uses the injective sequences of the iterated-difference test and the
  unit convention of §2.4.

Example 5.4
  PaperExamplesPowersWap gives the full complex WAP representation, the
  reversible subspace as the strongly almost periodic functions, the almost
  weak stability and constant polynomial evaluations of the literal perfect-
  power indicator. PaperExamplesPowersWapMean proves the full absolute-mean-
  zero characterization of the stable subspace.
  PolynomialSpectral.tendsto_abs_coeff_perfect_powers_of_unitaryWeakPart (in
  namespace JdLG) proves the unitary comparison (20) for every vector in the
  orthogonal complement of the eigenvectors and every test vector.


SCOPE OF CITED SUPPORTING RESULTS


The Lean proofs include the paper's numbered examples, the circle-rotation
remark, and the two examples of groups of right quotients in §2.5.2. Some
background citations extend beyond the proofs included here. These include
Banakh's automatic continuity of Haar-measurable group homomorphisms, the
separate example from Ehrenpreis–Mautner concerning the equivalent orbit norm
on a particular \mathrm{SL}(2,\mathbb R) representation, and the cited generality of the discrete amenability and Følner equivalences in §2.3. The WAP direct-sum theorem after Theorem 1.5 is checked for semitopological monoids.

COUNTEREXAMPLES TO PUBLIC V3 STATEMENTS


In Example 2.1, the two idempotents send (x,y) to (x,x) and
(y,y). Together with the identity they form a finite WOT-compact
semigroup on the complex Euclidean plane. The plane and its dual are strictly
convex. Each coordinate axis lies in the almost weakly stable set, but the
sum of the two coordinate unit vectors does not. A JdLG decomposition would
make that set the kernel of a linear projection. The contraction variant
proved in ContractiveCriterion includes an assumption absent from (iv).

For the uniform Følner claim, let H_n be the subgroup of finitary
permutations supported on {0, …, n} and F_n=H_n(0\;n+1).
Every fixed left translation eventually preserves F_n exactly. In the
coordinate representation on \ell^2(\mathbb N), all elements of F_n
send e_0 to e_{n+1}. The fixed-dual averages tend to zero by square
summability. Evaluation at coordinate n+1 has norm one and achieves the
supremum one at stage n for each positive power. The subgroup exhaustion also
produces a two-sided invariant mean on counting-measure L^\infty.

For the Stone–Čech assertion in §2.5, the alternative multiplication on
βℕ uses the standard product when the right factor is principal and
returns the right factor when it is free. Associativity and continuity of
right translations hold, and the two products agree on the natural numbers.
The standard product is unique when left translations by principal
ultrafilters are required to be continuous as well.

Introduction (https://arxiv.org/html/2509.24003v3#S1) ·
Preliminaries (https://arxiv.org/html/2509.24003v3#S2) ·
Reversible part (https://arxiv.org/html/2509.24003v3#S3) ·
Almost weakly stable part (https://arxiv.org/html/2509.24003v3#S4) ·
Ultrafilters (https://arxiv.org/html/2509.24003v3#S5)

