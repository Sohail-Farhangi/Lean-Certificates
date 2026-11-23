# A generalization of van der Corput’s Difference Theorem

Lean 4 certificate for Sohail Farhangi’s [arXiv:2106.01123v6](https://arxiv.org/abs/2106.01123v6).
The formalization uses rectilinear discrepancy estimates, complex Fourier coefficients,
and spectral measures to relate van der Corput difference conditions to uniform distribution.

## Find a statement

[PAPER_GUIDE.txt](PAPER_GUIDE.txt) maps the public paper’s definitions, numbered statements,
and examples to exact Lean declarations. The library includes the two difference theorems
on the closed cube, the thesis theorem with the four weak-mixing characterizations, the
lag-pair criterion, and the constructive examples in Section 4.

| Paper | Lean declaration |
| --- | --- |
| Theorem 3.1(i), selected subsequences | `VdC.equidistributed_selected_of_sl_singular`, `VdC.equidistributed_selected_of_wm_compact` |
| Theorem 3.1(iii), product equidistribution | `VdC.equidistributed_pair_of_sl_singular`, `VdC.equidistributed_pair_of_wm_compact` |
| Theorem 3.2, spectral difference theorem | `VdC.cube_spectral_difference_theorem` |
| Theorem 3.3, weak-mixing difference theorem | `VdC.cube_weakMixing_difference_theorem` |
| Theorem 3.4, four characterizations | `VdC.thesis_four_characterizations_weakMixing` |
| Theorem 3.5, orthogonality and lag pairs | `VdC.cube_orthogonal_iff_lag_pairs` |
| Lemmas 4.1–4.3 | `VdC.ae_constructingSequences_cube`, `VdC.exampleNecessitatingPermissibleTriples`, `VdC.polynomialLikeCounterExample` |

The existing proof scope covers Theorem 3.1(i) and (iii). The paper guide identifies
the converse implications and supporting statements outside the proof library. The
formal spectral definitions use complex autocorrelations in the spectral-measure
identity. The finite discrepancy in Lean is the supremum over closed rectangles.

## Build and check

Run the following commands in this folder with elan and Lake. The Lake manifest pins
Mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` for Lean `v4.36.0`.

```text
lake exe cache get
lake build
lake env lean Audit.lean
```

`VdC.lean` publicly imports the proof library. `Audit.lean` checks the transitive
axioms, including those of private declarations. The allowed axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Lean Pool and Palomar

The public library entry point for Lean Pool is `VdC`. The Palomar comparison
specification selects Theorems 3.2, 3.3, and 3.5. `Palomar/Challenge.lean` states
them independently with three deliberate proof holes. `Palomar/Solution.lean`
proves them by referring to the library. To build the compared proof module, run
`lake build +Palomar.Solution`.

Use a modular-only public commit to submit if the repository also contains
other Lean source files that exceed Palomar’s file-size rules. The repository
path, commit SHA, and project folder must match the submitted snapshot.
[Palomar submission instructions](https://palomar-registry.org/how-to-submit)
and [Lean Pool contribution instructions](https://github.com/LeanPool/lean-pool/blob/main/CONTRIBUTING.md).

Sohail Farhangi is the responsible human author and maintainer. OpenAI Codex
materially generated the Lean proofs and packaging with local compiler feedback.
Credits and source alignment are recorded in [formalization.yaml](formalization.yaml).
