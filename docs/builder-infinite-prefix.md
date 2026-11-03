# Infinite trajectory finite cylinders: builder handoff

**Status: PARTIAL.** The checked source is `Formalization/MDP/InfinitePrefix.lean` (SHA-256 `7f84be927abfd081e14595ad7e03aff4e9c5a353d1dcd3fabdc4058581dcf82b`). The reviewed bytes were copied unchanged into the library. It has no placeholder or assumed path-law conclusion. The requested equality with the independently constructed `DecisionStage.trajectoryLaw` is **not proved**.

Source: arXiv:2610.41903v1 `prelim.tex:89–102`, actual infinite controlled state/action trajectory and discounted return. The existing `Formalization/MDP/InfiniteTrajectory.lean` constructs `infiniteTrajectoryLaw` with initial `(a₀,s₁)` and Ionescu–Tulcea kernels whose next pair uses the current history's actual last state. `FiniteTrajectory.lean:22–26,69–76,108–113` independently defines `FinitePath` and its product-mass `trajectoryLaw`.

The staged source proves actual distributional facts, using no hypothesis of independence, a Markov property, or desired finite-law equality:

- `infiniteTrajectoryLaw_history_singleton_step`: for any history through `n` and any next action/state pair, the joint cylinder mass is the singleton history mass multiplied by the exact policy probability at its final state and the exact next-state transition probability. It uses the existing `infiniteTrajectoryLaw_history_step`, `historyKernel_apply`, and `stepMeasure_singleton`.
- `historyCylinder_succ` shows that a length `n+2` history event is exactly its length `n+1` prefix event and the recorded next pair; `infiniteTrajectoryLaw_prefix_singleton_succ` obtains the matching multiplicative recursion.
- `infiniteTrajectoryLaw_prefix_singleton_zero` identifies the first pair's mass with its actual policy-transition mass. `historyMass` is the complete finite product of the true step probabilities, indexed by `Iic n`, and `infiniteTrajectoryLaw_prefix_singleton_eq_historyMass` proves equality to the infinite law's singleton cylinder mass for **every n**. `Iic n` contains `n+1` pairs, indexed 0 through n; the zero-length prefix is not covered by this result.

All sample spaces involved use the same discrete measurable spaces as `InfiniteTrajectory.lean`. No state or action size restriction beyond the imported MDP setup is introduced.

## Verification

The final validation copied these exact source bytes to a temporary file, appended `#print axioms` for the five theorems listed above, and compiled the copy via `bash scripts/lean-local.sh <temporary-file>`. It passed without diagnostics. Every checked theorem reported only `propext`, `Classical.choice`, and `Quot.sound`; the probe was removed. `Formalization/MDP/InfiniteTrajectory.lean` used in the check had SHA-256 `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9`; `Formalization/MDP/FiniteTrajectory.lean` had SHA-256 `5b6f53bc1822729beb715ad385b74951dedf7c0596ca654cf246945593ca3130`. No full integration check or independent review was performed.

## Precise remaining bridge

Construct an explicit bijection between `Iic n → Action × State` histories and `FinitePath State Action (n+1)`, respecting order. Prove `historyMass` equals `ENNReal.ofReal (DecisionStage.pathWeight (List.replicate (n+1) (M.stationaryStage π)) s path)` under that bijection, transporting along `List.length_replicate` without assuming the result. Then use `FiniteDistribution.toPMF_apply`, singleton measure extensionality, and measurability to get equality of the finite-prefix pushforward with the actual repeated-stage `trajectoryLaw`, separately treating the empty prefix. A trial of this comparison encountered dependent casts between `n` and `(List.replicate n stage).length`; the incomplete trial was removed from the handed-off source. Until this bridge is proved, the checked cylinder product must not be described as equality to `trajectoryLaw`.
