# Independent source review: selected-model comparator closeness chain

Status: independent source-level review plus fresh focused compile and
transitive axiom probe. The staged drafts remain quarantined; this note does
not change the coverage ledger.

## Hash-bound scope

| File | SHA-256 |
|---|---|
| `QLearningComparatorDistanceReductionDraft.lean` (private staged draft, not shipped) | `3c3a244d94bb9ddca753fdfe604bca217f156284aad1e7fa338b74d90bd5cdda` |
| `QLearningComparatorDistanceEndpointsDraft.lean` (private staged draft, not shipped) | `c2888f9bb23376ae8c95db1fe68e9912e3d134317e6d704b02cecf9b9f73ed5a` |
| `QLearningComparatorConditionalClosenessDraft.lean` (private staged draft, not shipped) | `dbc879282a61ca9de10285a9fd4cbf7b1f6ebea988af32e9e44749a802281518` |
| `Formalization/ModelFree/QLearningRobustRange.lean` | `46747fa497696120ece406e477f5a00034e9407b9bd48e3777bc7567f255a7c3` |
| `Formalization/ModelFree/QLearningRobustAttainment.lean` | `8a8d666c6a3eb1cfad7a9626f7361ae5c05c483cc112f505345c101e419150b5` |
| `Formalization/MDP/OptimalTrajectoryValue.lean` | `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7` |
| `Formalization/ModelFree/QLearningChiKL.lean` | `9c9eb98578aed95ed2142136697864231a9b2b31e9c147e739df534e390ede07` |
| `Formalization/ModelFree/QLearningChiUpper.lean` | `7da5497bf3b15475f658257b18bbdbc8927893cbbfb0533353868f08bf2ae7e9` |
| `source/upstream/tex/chapters/generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |

The source target is `Q-comparison-facts`, part (ii), lines 2658–2701,
including the randomized-stopping KL estimate and the optimal-policy
comparison. The review is against the source cited in the repository, not an
external version.

## Findings

The selected-model construction is tied to the actual robust fixed points.
`qRobustPlusModel` and `qRobustMinusModel` use per-row optimizers from the
attainment result, preserve the nominal reward and discount, and place each
actual transition row in the nominal support-aware χ² ball. Their
`qComparator_selectedModel_rowKL` result derives absolute continuity,
finite measure KL, and `toReal KL ≤ ρ` from the ball's zero-support rule and
finite `KL≤χ²` theorem. This matches the direction `KL(P' || P)` used in the
source trajectory chain rule; zero nominal atoms are retained rather than
assuming full support.

`qComparator_shifted_optimalTrajectoryQ` expresses each actual robust fixed
point using the optimal greedy trajectory Q of its own selected model. The
optimal greedy policy is constructed as a deterministic point-mass policy in
`OptimalTrajectoryValue.lean`. The plus identity is `Q⁺−b/(1−γ)=Q^{π⁺,P⁺}`;
the minus identity is `Q⁻+b/(1−γ)=Q^{π⁻,P⁻}`. Subtracting the nominal optimal
trajectory Q therefore produces opposite shift signs, as required. The norm
lifting is pointwise over the finite state/action carrier.

With the source choice `b=2ρH` and `H=1/(1−γ)`, the additive cost is exactly
`2ρ/(1−γ)^2`. The conditional stability interface uses exactly
`sqrt(γρ/(2(1−γ)^3))`; no sharper or altered constant appears. The
conditional hypothesis is visible and explicit: for every actual model with
equal reward and discount and row-wise membership in the nominal χ² balls, its
own optimal trajectory-Q norm must be within this stability radius. That
hypothesis is the imported mathematical obligation from the stopped-prefix
KL/Pinsker argument; the three reviewed files do not prove it.

The zero-discount endpoint is handled through actual optimal trajectory-Q
being immediate reward, so the selected kernels have the same optimal Q when
the discount is zero and the remaining shift is exactly `2ρ`. The zero-radius
endpoint uses the proved zero-ball expectation identity to show each robust
fixed point equals nominal optimal trajectory Q. These branches avoid a
positive-discount/positive-radius restriction leaking into the final
conditional wrapper. The positive wrapper separates `γ=0` and `ρ=0` before
applying the strictly positive stability premise.

## Scope and caveats

- The chain is conditional on the explicit actual-model stability bound. It
does not itself establish the source's uniform policy stability theorem or
unconditional comparator closeness.
- The focused build/probe below does not verify production integration.
Existing imports and proof bodies remain quarantined pending integration.
- The first closeness API carries an unused positive-radius argument while
allowing its continuation quantifier to include `ρ=0`; it is redundant but
not a mathematical premise used in the proof. The positive-radius wrapper is
the cleaner source-facing endpoint-safe interface.
- The reduction uses actual selected models and actual optimal trajectory Qs;
there is no target-shaped closeness result in its assumptions other than the
separately named stability hypothesis.

## Independent fresh build and axiom probe

The three exact staged sources above were independently compiled bottom-up
with the pinned Lean executable into
an isolated local audit directory (not shipped), with this output
first on `LEAN_PATH`, followed by the project build and pinned Mathlib
outputs. All three focused compiles succeeded. Fresh output hashes were:

| Output | SHA-256 |
|---|---|
| `QLearningComparatorDistanceReductionDraft.olean` | `a0fedb4bc68691d4e6ca65c1330b9e5b0acabb61fd153940ec0752b07b17bf80` |
| `QLearningComparatorDistanceEndpointsDraft.olean` | `c7ef68ac1551385431fe571c900cb9c05affd9acc6ecbdea25ae5d126fa8868b` |
| `QLearningComparatorConditionalClosenessDraft.olean` | `5e3ffe7052f051822f084a6a60c82f420ae9f2b065aa18a93f44702c188b857a` |

The combined probe `AxiomProbe.lean` (in an isolated local audit directory, not shipped), SHA-256 `8e43af78ffcd778953bef845c7c9e1d84264a73c1882e2b54211f51564b18dd9`, imports the final conditional-closeness module and prints axioms for all 15 exports (7 reduction, 6 endpoint, 2 conditional). Every export reports exactly `[propext, Classical.choice, Quot.sound]`. No source or production file was edited for this verification.

The fresh build confirms elaboration and the probe confirms the transitive
axioms for these exact staged exports. The source-level conclusions above
remain: both signs use the selected models' own optimal trajectory Qs; the
additive shift is exactly `2ρ/(1−γ)^2`; zero-discount and zero-radius are
derived without positive-case division; and the positive-case actual-model
stability estimate remains an explicit, unproved premise. This chain is
conditional, not an unconditional proof of Lemma 4.10(ii) or source
comparator closeness.

## Production integration

The reviewed selected-model distance reduction, zero endpoints and conditional closeness modules are integrated as corresponding `Formalization/ModelFree/QLearningComparator*.lean` modules. Positive-case model stability remains an explicit separate input. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 293 modules and audited 3,811 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
