# Jacobs–de Leeuw–Glicksberg decomposition in Lean

This project follows the 19 August 2026 public arXiv revision of Micky
Barthmann, Sohail Farhangi and Yulia Kuznetsova, *On the Jacobs-de Leeuw-Glicksberg
decomposition for representations of semigroups*. It also proves the revision
of Theorem 1.2(iv) reported by Sohail Farhangi, with the assumption that every
operator is a contraction. The guides follow the public version's numbering.
[arXiv:2509.24003v3](https://arxiv.org/abs/2509.24003v3).

[COVERAGE.md](COVERAGE.md) maps the paper's numbered results and examples to
their Lean declarations. It also records which supporting remarks are covered
and gives three counterexamples to claims in the public v3 revision.

## Navigate the proofs

Start with `JdLG.lean` for the module list. The main objects are defined in
`JdLG/Core.lean`. The type `weakOperatorClosure π` is the closure of the
represented continuous linear operators in the weak operator topology.
`IsJdLGAdmissible π` says that this closure is compact and has a unique minimal
idempotent. The multiplication on operators is composition. The theorem
`JdLG.decomposition_of_admissible` constructs the group-ideal identity and
proves that its range and kernel are the reversible and almost weakly stable
summands. Follow `JdLG.existsUnique_minimalIdempotent_iff_exists_biInvariantMean`
for the mean criterion in Theorem 1.1.

`ReversibleAction`, `ReversibleBasis` and `ReversibleRepresentation` cover
norm compactness, finite irreducible systems, and the unitary direct-sum
representation. `StableOperator`, `MeasuredReturns` and `MeasuredTransfer` cover
stability and invariant means. `Ultrafilters` and `UltrafilterMore*` cover
Section 5. The `PaperExamples*` files follow the paper's examples, with a
single example sometimes using several files.

The first two counterexamples to statements in public v3 appear as
`JdLG.PrintedClaimCounterexample.printed_theorem_1_2_iv_counterexample` and
`JdLG.LeftFolnerCounterexample.counting_uniform_powerAverage_counterexample`.
The first uses the Euclidean version of Example 2.1. The second concerns
the uniform coefficient conclusion of Theorem 1.6 and Theorem 4.2(viii).
The third, `JdLG.exists_distinct_rightTopological_extension_nat`, concerns
the uniqueness assertion in §2.5.
`JdLG.admissible_of_strictConvex_contractions` proves the revised
Theorem 1.2(iv). Its hypothesis `∀ s, ‖π s‖ ≤ 1` means that every
represented operator has operator norm at most one.

## Build and axiom audit

From the directory with `lakefile.toml`, run these commands with Lean
installed via `elan`.

```sh
lake exe cache get
lake build JdLG
lake build +Palomar.Solution
lake env lean -DwarningAsError=true Audit.lean
```

`lean-toolchain` and `lake-manifest.json` pin Lean **4.36.0** and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The default proof library builds
with warnings as errors. `Audit.lean` traverses the transitive dependencies
of every project declaration, including private declarations. The three
permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Lean Pool and Palomar

The repository-proposal path for Lean Pool uses the proof library in
`JdLG.lean` and `JdLG/`. Its entry point is `import JdLG`. The code for a
direct Lean Pool content submission goes through that service's import
and project-card layout with provenance `AI`. The current Lean Pool
content checker forbids per-file elaboration options. Some proofs in this
library use these options, so a direct content contribution still needs
proof refactoring and CI review.

The Palomar snapshot uses `Palomar/Challenge.lean`, `Palomar/Solution.lean`,
and `comparator.json` alongside the proof library. The Challenge has nine
deliberate statement placeholders and is outside the default proof build.
The comparison covers the decomposition, $L^p$ contractions, admissibility
for groups, nonseparable weak decay, the revised Theorem 1.2(iv) and
its v3 counterexample, a fixed-point criterion, and two ultrafilter and
return-time results. The
project build and axiom audit check the entire proof library.

Sohail Farhangi is the responsible human author and maintainer of the
formalization, which is released under Apache-2.0. Palomar requires a
public GitHub commit SHA. Acceptance by either service follows its own review.
The manuscript authorship is recorded separately from the Lean formalization.
OpenAI Codex produced the Lean material with local compiler feedback and
agent review.
[Lean Pool contribution guide](https://github.com/LeanPool/lean-pool/blob/main/CONTRIBUTING.md) ·
[Palomar submission guide](https://palomar-registry.org/how-to-submit).

The sibling standalone folder contains the one-file edition for reading.
For Palomar use a project-only commit whose checkout excludes that edition.
The standalone file exceeds Palomar's per-file line limit.

### Local verification

The previous build of the proof library and the prior eight Palomar
comparisons passed the transitive axiom audit and local Comparator replay.
The revised Theorem 1.2(iv) now has a ninth comparison target. The new
Solution declaration compiled in the pinned Lean environment with
only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
