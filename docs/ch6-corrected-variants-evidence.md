# Chapter 6 verification and scope

The Chapter 6 statement entries and their applying wrappers are in
[Ch6.lean](../Formalization/Statements/Ch6.lean) and
[Ch6Proofs.lean](../Formalization/Statements/Ch6Proofs.lean).

This batch adds four explicitly scoped results: the commented zero-count
fallback variant of Theorem 6.1; Lemma 6.2 with `γ ≥ 1/2`; Lemma 6.4 in its
parent theorem's discount and stopping regime; and Lemma 6.5 with `N ≥ 2`
under the actual iid triple law. The fixed points, sampling-law projections,
and count events are proved dependencies. Their restrictions are recorded in
[COVERAGE.md](COVERAGE.md), [SOURCE-ISSUES.md](SOURCE-ISSUES.md), and the
[errata and deviations record](ERRATA-AND-DEVIATIONS.md). The complete
monograph remains incomplete.

## Full project check

On 2026-11-05, the unmodified `python3 scripts/check.py` completed successfully
in a clean checkout with initially empty project build artifacts. It compiled
all 938 project modules and the transitive axiom audit passed for 8,414 project
declarations. The only permitted axioms were `propext`, `Classical.choice`,
and `Quot.sound`. No project OLeans were reused. Existing dependency artifacts
were read-only, and the recorded dependency metadata and all project source
hashes matched before and after the run.

Lean was pinned to `v4.27.0-rc1` (commit
`2fcce7258eeb6e324366bc25f9058293b04b7547`), with Mathlib
`32d24245c7a12ded17325299fd41d412022cd3fe`. The check finished at
`2026-11-05T16:27:51.696331+00:00`.

The [full manifest](validation/ch6-variants-20261105/manifest.json) records
source hashes, actual commands, per-module exit codes, and timings; the
[Audit output](validation/ch6-variants-20261105/Audit.log) and
[guard summary](validation/ch6-variants-20261105/guards.json) accompany it.
The guard summary distinguishes dependency metadata checks from byte sealing.
Independent source and statement reviews preceded integration. The source
inventory check and its eight scanner tests also passed.

Reproduce the Lean check after the dependency setup described in the README:

```sh
python3 scripts/check.py
```

The book reader is checked separately against the pinned manuscript and TeX.
