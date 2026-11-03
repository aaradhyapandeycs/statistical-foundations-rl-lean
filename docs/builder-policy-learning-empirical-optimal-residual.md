# Actual-law residual for the empirical optimal value

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:1334–1371`, especially `eq:Phat-sa-Vhat-star-concentration-proof-mb-tight`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyLearningEmpiricalOptimalResidual.lean` proves, for every finite valid MDP, positive sample count `N`, and `0<δ<1`, that the actual product generative law assigns probability strictly greater than `1−δ/2` to the single event on which every state/action row satisfies

```text
|(P̂_{x,a}−P_{x,a}) V̂*| ≤
  √(β₁/N) √Var_{P_{x,a}}(V̂*) + 2β₁/(N(1−γ)),
β₁ = 2 log(16 S A N / ((1−γ)δ)).
```

Here `V̂*` is the project's actual empirical optimal greedy **trajectory** value `valueEstimator M N hN data`, and each row is the actual empirical frequency row versus the true transition row. This is the source's exact β, coefficient 2, all-state/action quantifier and strict probability. No good event, residual bound, variance comparison or selected-policy independence is assumed. The β arithmetic is discharged: `leaveOneOutBeta_ge_four` proves `β₁≥4` from the existing MDP/count/confidence domain; no additional hypothesis is introduced.

The proof first takes the already established **single all-row/all-grid event**. Only after fixing an outcome in that event and a state does it invoke `empirical_absorbingGrid_covers_valueEstimator` to choose a close grid index. Its fixed-grid concentration is then obtained by specializing the already universal event. The exact grid-value bridge identifies the cover's actual empirical absorbing model with the all-row event's vector. The reviewed deterministic variance-transfer lemma combines that row bound with the proved `1/[N(1−γ)]` cover. No assertion is made that the data-selected index or empirical optimal value is independent of a row; no second probabilistic event or confidence allocation is introduced. The event holds uniformly over all actions, so later selecting the empirical greedy action is logically permissible.

This result is the all-action empirical-optimal residual estimate, not the subsequent policy-transition notation identity, self-bounding variance-resolvent argument, value performance guarantee, or sharp sample-complexity theorem. It includes γ=0, N=1 and zero variance; no division by γ occurs. Independent source/semantic review and production-export validation remain outstanding.

Validation: rebuilt unchanged staged dependencies `PolicyLearningAllRowBernstein.lean` and `PolicyLearningVarianceTransfer.lean` to `.local` oleans, then `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyLearningEmpiricalOptimalResidual.lean'` passed without diagnostics. Exact-source temporary probes of β≥4 and the actual-law all-row residual theorem reported only `propext`, `Classical.choice`, and `Quot.sound`. Staged file SHA-256 `c1ac0b61d3af7c76c05d2a56f14f2dd49e1c1f6225988e35130bc128b35fe8fb`; staged all-row dependency `c28ab6963d52be915aedc7909d6ad6c894bf6666e0cb9312f33a45ce67dc1189`; staged variance-transfer dependency `b601af7ce8d8bc5935e11b299c27875ded4f50674d37867bd991c68f5464b9d0`; staged grid dependency `9eb3bb60ee40b35f5c3fb378c1db43edc0d1648d1d230c0b06b5be028063e9ef`.
