Solutions to 6 problems in recurrence and Van der Corput sets
Sohail Farhangi and Saúl Rodríguez Martín
Paper version arXiv:2609.07506v1
https://arxiv.org/html/2609.07506v1

SixProblems.lean contains the definitions and proofs. It uses the companion
project's pinned Lean 4.36.0 and Mathlib revision. From a terminal in that
project, the command for this presentation is

    lake env lean -DwarningAsError=true --root=../Standalone ../Standalone/SixProblems.lean

Each heading reading "Source module ..." marks a section that comes from a
modular Lean file. The table below gives names to find in the standalone
file and explains which part of the paper they correspond to.

Proposition 2.1
SixProblems.proposition2_1. The finite set J represents a tuple of distinct translates. bernoulliThreshold_pattern computes the joint event probability, and bernoulli_prod_isErgodic proves the last sentence.

Theorem 2.2(a–e)
SixProblems.theorem2_2. Each of (b), (c), (d), and (e) is equivalent to (a). nonnegativePD_of_ergodicNiceRecurrence uses hasBoundedErgodicPDApproximation, proved by the compact and weak decomposition of a real orthogonal representation. The compact part uses a finite-dimensional Haar rotation and the weak part uses a Gaussian shift.

Theorem 2.2(f)
SixProblems.theorem2_2_abelian. theorem2_2_d_iff_f relates the two printed supremum tests. DiscreteDual G is the character group of the discrete acting group and its identity is the trivial character.

Lemma 3.1
SixProblems.lemma3_1. Set the polynomial variable type to Fin 2 for the bivariate lemma. The proof uses positive semidefinite matrices.

Lemma 3.2
SixProblems.lemma3_2. It produces a natural exponent and a positive uniform margin on the two prescribed parts of the square.

Theorem 3.3
SixProblems.theorem3_3. The polynomial barrier turns witnesses for the two sets into a witness for their union.

Corollary 3.4
SixProblems.corollary3_4. The finite family is indexed by Fin m. niceRecurrence_partitionRegular also gives the consequence in Remark 3.5.

Lemma 4.2
SixProblems.lemma4_2. An independent finite factor selects a coordinate. A sign choice on that factor preserves the correlation sum and detects a nonzero coordinate mean.

Lemma 4.3
SixProblems.lemma4_3. Real and imaginary coordinates give a real witness, and a Bernoulli extension converts it to a function with values in {−1, 1}.

Proposition 4.5
SixProblems.proposition4_5_euclidean. This is the version for representations on EuclideanSpace ℂ (Fin d). The generic proposition4_5 uses all finite-dimensional complex Hilbert spaces.

Theorem 4.6
SixProblems.theorem4_6. For the reverse direction, complementary Haar perturbations and independent samples give Haar increments from a sign witness while its nonzero mean gives a non-Haar marginal.

Theorem 4.8
SixProblems.theorem4_8. LeftFolnerSequence includes nonempty blocks and convergence of the left-translate defects. hasFolnerGenericRealizations proves the inverse correspondence along the same sequence. It combines local finite models from independent samples with nested quasi-tilings and summable bounds on the exceptional block proportions. isFolnerUniformlyDistributed_iff_complex_tests connects the library's real tests to the paper's complex tests.

Lemma 5.1
SixProblems.lemma5_1. Existence and uniqueness are stated with all finite tuples, including repeated indices, and with the covariance and shift invariance in the paper.

Lemma 5.2
SixProblems.Gaussian.lemma5_2. The proof computes the angle of a Gaussian wedge and includes both singular covariance endpoints.

Theorem 5.3
SixProblems.theorem5_3. The reverse direction uses identical two-coordinate Gaussian laws for all the elements of the tested set. A single bounded odd cutoff preserves a strictly negative coefficient and a constant shift cancels it. hilbertOperatorial_iff_operatorial connects the L² criterion to the introduction's Hilbert-space criterion.
