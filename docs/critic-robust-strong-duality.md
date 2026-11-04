# Independent source review: robust finite-row duality

**Review date:** 2026-11-04
**Source:** `source/upstream/tex/chapters/robust_RL.tex`, Lemma `lemma:dual-form`, lines 302–324; the positive-radius convention is stated at lines 31–32.
**Review scope:** source fidelity, the qualified χ² proof chain, and the expanded Chapter 7 statement/proof wrapper. This is not a new Lean run or a publication/integration approval.

## Finding

The χ² source-maximum statement and proof route match the second bullet of the source lemma. The source quantifies a finite nominal probability vector, a value vector `V ≥ 0`, and a strictly positive radius. It minimizes `⟨q,V⟩` over the χ² uncertainty ball and maximizes the clipped expectation minus the square root of radius times clipped nominal variance over the full interval `[Vmin,Vmax]`.

The formal candidate uses the support-aware Pearson convention

`sum_{p(s)>0} (q(s)-p(s))^2 / p(s) ≤ σ`

and separately requires `q(s)=0` wherever `p(s)=0`. This is the source orientation `χ²(q ‖ p)` and prevents division by zero or new mass outside nominal support. The clipped value is `min (V s) α`; its variance is expanded as `E[min(V,α)^2] - E[min(V,α)]^2`, matching the source formula. The threshold interval is over all carrier values, including zero-nominal-mass coordinates.

The source-maximum export constructs an actual feasible row and an in-interval threshold with equal primal and clipped-dual values, then proves the clipped objective at every other threshold in the interval is no larger. Its proof covers the large-radius supported-level case, zero variance, the small-radius endpoint, and the intermediate threshold-crossing case. It derives the optimizer and feasibility conditions from the finite probability row; they are not theorem premises. The combined Chapter 7 wrapper identifies its explicitly written filtered-cost primal set with the production `qChiBall` expectation set, transports the all-carrier min/max endpoints, and rewrites the production scalar objective to the source's finite sums. The TV wrapper consumes the existing event-TV/half-L1 and source-maximum results. No branch conclusion is omitted.

This review concerns only the finite-row TV and χ² duality statement at `lemma:dual-form`. It does not establish other robust-RL results.

## Reviewed source hashes

The nine qualified χ² candidate source hashes reviewed are:

| Module | SHA-256 |
| --- | --- |
| `Formalization.RobustRL.ChiSquaredDensity` | `9d691a02d3f1a063bd8f7f2d4b019d464e1b646da81dc2e84027895885289886` |
| `Formalization.RobustRL.ChiSquaredClippedMoments` | `0350a8ac31de15202c320cd26cc23eb62f2c12c0c0deef3a016fe78d04f5b57b` |
| `Formalization.RobustRL.ChiSquaredLargeRadiusWitness` | `78e10215d61a071fe4c080b4f9fd7c677c6bdc26be001e33548369350bb772c6` |
| `Formalization.RobustRL.ChiSquaredThresholdCrossing` | `bc43f7b2961635b5b789523c84a45afb1f6b7f02d3aedcaa39730002988007a7` |
| `Formalization.RobustRL.ChiSquaredPositiveRootWitness` | `11e9c4824f324bdbd36f40fbec6527fb0f119caab25deeb94df3ae062a0296d5` |
| `Formalization.RobustRL.ChiSquaredSmallRadiusWitness` | `5b433af887923c290e7316995ac26fdb27c66a63bec11fab2a93faa6a936e2db` |
| `Formalization.RobustRL.ChiSquaredSupportedLevels` | `f87d8a3c6439bfa9399178ed995c31bb0564645be619e77d6153e35fafe01c9c` |
| `Formalization.RobustRL.ChiSquaredZeroVarianceWitness` | `4b6c6804a8c22b3c4636a29b0a2146016a48e832d48726f5e765388f2c312d3f` |
| `Formalization.RobustRL.ChiSquaredSourceMaximum` | `9b8d09b0abfd17ea4f51fde9efa7b9f33601bd72bd5012594d07b283005a3148` |

The final expanded Chapter 7 index sources reviewed are:

- `Formalization/Statements/Ch7.lean` — SHA-256 `908f739cc1200f785bf16b86a676526e3078fb03f463835d3795aa5a07734622`. The only change from the previously reviewed `e390c3cc…` snapshot is syntactic relocation of the local `Classical.propDecidable` attribute above the docstring; the Prop body is unchanged.
- `Formalization/Statements/Ch7Proofs.lean` — SHA-256 `dc1cfe287edfa2156666885abf01aa0d0ac28251feda58363cee2302ee3ee474`.

The statement file directly imports definition modules only. The proof file retains the TV proof wrapper and applies it in the combined theorem, then consumes the qualified χ² source-maximum result. The expanded `Lemma7_1` contains both source bullets, including the feasible-row constraints, attained interval threshold, primal equality, and universal threshold dominance.

## Build and provenance boundary

The nine-module qualified preview and its actual-export probe previously exited successfully; the probe found only `propext`, `Classical.choice`, and `Quot.sound` for the probed maximum and helper exports. Its build reused existing project and Mathlib OLean artifacts. The recorded source/olean identity does not independently prove that each reused OLean was built from its currently hashed source, so this is focused preview evidence rather than clean source-rebuild provenance.

The final Chapter 7 source hashes above were rebuilt in a focused output: both targets exited 0, and the actual-export probe exited 0. It reports only `propext`, `Classical.choice`, and `Quot.sound` for `Lemma7_1_tv_holds` and `Lemma7_1_holds`. Canonical integration and its affected rebuild are still pending. No full-integration or full-clean-build success is claimed here.
