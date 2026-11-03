# Statistical Foundations of Reinforcement Learning in Lean

**Work in progress. The entire monograph is not yet formalized.**

This project aims to formalize the whole of Chen, Chi, Fan, Li, Wei, and Yan,
*Statistical Foundations of Reinforcement Learning: A Non-Asymptotic Perspective*,
[arXiv:2610.41903v1](https://arxiv.org/abs/2610.41903v1).
The scope includes model-based and model-free RL with a generative model,
online RL, offline RL, the extensions, and all mathematical appendices.

Builder agents implement definitions and proofs. Independent critic agents
check the mathematics, source correspondence, hidden assumptions, and actual
proof dependencies. Compiling a smaller infrastructure library does not
establish completion of the monograph.

## Reproduce

Lean `v4.27.0-rc1` and Mathlib commit
`32d24245c7a12ded17325299fd41d412022cd3fe` are pinned.

```sh
python3 scripts/fetch_source.py
lake exe cache get
lake build
lake env lean Audit.lean
```

The source provenance and license are recorded in [source/](source/README.md).
Current work and open obligations are recorded in [docs/PROGRESS.md](docs/PROGRESS.md).
The [source checklist](docs/source-inventory.md) does not itself certify proof
coverage; the [reviewed coverage ledger](docs/COVERAGE.md) maps current results
to source statements and records their exact limits.

Only the standard foundational axioms `propext`, `Classical.choice`, and
`Quot.sound` are allowed in the transitive dependency closure. No source theorem
may be claimed by assuming its missing intermediate steps.

The GitHub Actions workflow checks the pinned source, inventory, scanner tests,
Lean build, and project axiom audit on each push. Its presence does not by itself
establish that a particular run has passed. The same commands and
`python3 scripts/check.py` can be run locally.

## Live progress

Run `python3 scripts/progress_dashboard.py` and open
`http://127.0.0.1:8765/` on the same computer. The read-only dashboard refreshes
local Lean line counts and a conservative reviewed-named-result ledger every
10 seconds. Its percentage is not an estimate of all mathematical work in the
monograph. The locally recorded `origin/main` snapshot may lag GitHub until
the next fetch or push.

## Guidance and attribution

The project uses [Scott Armstrong's LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills)
at revision `1837b95b3d5a9fd8d311367603902ad7fe261adf`.
Its complete instructions and supporting resources are retained in `skills/lean/`
with their CC BY 4.0 and third-party notices. The project also consults the
[Lean team's skills](https://github.com/leanprover/skills) and
[Cameron Freer's Lean skills](https://github.com/cameronfreer/lean4-skills).

Original Lean code and project tooling use the Apache License 2.0. The paper,
skill collection, and any third-party material retain their respective licenses.
