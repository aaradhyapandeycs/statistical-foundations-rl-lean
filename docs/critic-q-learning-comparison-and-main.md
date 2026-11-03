# Q-learning comparison and accuracy: source review

Source: Chen, Chi, Fan, Li, Wei, and Yan, *Statistical Foundations of
Reinforcement Learning: A Non-Asymptotic Perspective*, arXiv:2610.41903v1,
model-free chapter, Lemma `Q-comparison-facts` and Theorem
`thm:infinite-horizon-simple`. The pinned model-free source SHA-256 is
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
The source-number inventory identifies these as Lemma 4.10 and Theorem 4.6.

Independent AI reviewers checked the source statements, the stopped-law and
reward helpers, the selected-model reduction, and the final composition. The
actual project exports compiled in the 314-module whole-project check. Its
transitive axiom audit checked 3,971 declarations and allowed only `propext`,
`Classical.choice`, and `Quot.sound`. A separate clean-copy rebuild with empty
project artifacts and the pinned dependency cache also passed all 314 modules
and the same 3,971-declaration axiom audit.

## Source statements and assumptions

The comparison exports are
`StatisticalRL.QLearning.qComparisonFacts_support_source` and
`StatisticalRL.QLearning.qComparisonFacts_stability_source` in
`Formalization/ModelFree/QLearningStabilityInfinityNorm.lean`. The first has
the two supremum and infimum inequalities for a finite probability row, a
positive radius, and the source max-minus-min span bound. The second compares
the actual optimal trajectory Q-functions of two finite discounted MDPs with
the same reward and discount, when every candidate transition row lies in the
source supported chi-square ball. Its conclusion is the finite infinity norm
bound with the printed factor `sqrt (ρ γ / (2 (1−γ)^3))`.

The main export is
`StatisticalRL.QLearning.qLearning_exists_universal_constants_source_accuracy`
in `Formalization/ModelFree/QLearningSourceTheoremClosure.lean`. Its three
positive universal constants are chosen before the model, finite state and
action types, time horizon, learning rates, accuracy, confidence and initial
values. It assumes precisely the source conditions γ≥1/2, at least two
actions, T≥2, 0<δ<1, 0<ε≤1/(1−γ), the deterministic rate schedule from time
0 through T, the bounded initialization, and the printed sample budget. The
conclusion uses the actual synchronous product sampling law and the same
sampled Q-learning iterates, simultaneously for every state-action pair.

The finite MDP structure supplies nonempty carriers, normalized nonnegative
transition rows, rewards in [0,1], and a discount in [0,1). These are source
standing assumptions. The comparator closeness, stopped-law information
bounds, and final error bound are derived in proofs; they are not additional
premises of the source-facing exports. Review found no excess input. The result
is an existential universal-constant formulation, not a claim for every
possible choice of constants.

## Mathematical correspondence

The construction starts with the actual forced-action prefix law: depth k
contains k transitions, and a geometric stop of parameter 1−γ has the source
weights. Finite prefix expectations are related to policy Bellman iterates and
the actual infinite trajectory Q. Normalization and boundedness justify the
countable reward sum. The bounded-payoff comparison centers the reward at one
half, giving half the L1 distance without losing the source factor.

The countable Pinsker result is applied to the actual supported atomic masses;
its atomic KL and half-L1 quantities are controlled by the source rowwise
chi-square condition and geometric stopping. This proof does not assert an
additional identity with a separately defined measure-theoretic KL. The two
fixed-policy comparisons use each model's own optimal greedy policy and its
counterpart evaluation in the other model, then yield the own-model optimal
Q comparison. Zero nominal transition atoms are handled by the supported
chi-square ball. Zero radius and zero discount are retained by the general
helpers without division by either.

The final accuracy theorem supplies that stability result to the independently
reviewed plus/minus selected-model reduction, with the source additive shift
`2ρ/(1−γ)^2`, and then consumes the existing conditional sampling theorem.
The resulting theorem has no assumed comparator-closeness or target-error
premise, and it uses the same data event as the sampling analysis.

## Reviewed production sources

| Module | SHA-256 |
|---|---|
| `QLearningGeometricPrefixReward` | `884f2d4affa2176d7a52023c3b20f2b0ede884652d741c54d531c02cdd6a7031` |
| `QLearningGeometricPrefixBellman` | `084ac176f94a974e0bf5b7a420348cc694fc12056fcb741abf70ed3a87269f5d` |
| `QLearningStoppedPrefixRewardMixture` | `4c45a0708954e15f5ac72abcdfd284361bc741910e6562f4b7865fb03efcfefd` |
| `QLearningStoppedPrefixRewardMeasure` | `d3851d66f4e64a759d337ee9f37ccd12557d7b6b2b78f9ddb0645fd3b29ba9f0` |
| `QLearningStoppedPrefixPayoffTV` | `8872ce7928f73009b42f7cac8bc170feb5ff561fc0d5e752d3506621e860b31c` |
| `QLearningStoppedPrefixOptimalTransfer` | `1213e8188a2e47cf4e3ea1101756490e3a139735698bf93441852132968d387e` |
| `QLearningStoppedPrefixStabilityAssembly` | `0c0140ef37adc0e131db26d660fb357117f5766509944a300470df51cb2963fa` |
| `QLearningStoppedPrefixPinskerStabilityBridge` | `58f4462f0c772008821317f91c8ad5ef614b1512503ba110799688b71ce1c528` |
| `QLearningStabilityInfinityNorm` | `df56af06016d58358a40a1f9ac667465594700b54cc270cbe3ff67c6d125eb0d` |
| `QLearningSourceTheoremClosure` | `e622c6d175e3ed4e86df8938b450d60d6d44c9de6cbba89793803395f898c72a` |

All modules are under `Formalization/ModelFree/`. The independently reviewed
production files differ from their compiled review snapshots only in qualified
module imports and their first documentation headers. The full project check
is recorded locally in `verification/20261103T125629099061Z/`. The clean-copy
check used the same 314 source hashes, reused only the pinned dependency cache,
and completed with no existing project build artifacts.
