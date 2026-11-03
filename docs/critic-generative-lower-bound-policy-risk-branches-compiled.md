# Independent source review: staged policy-risk branches

**Reviewed exact staged sources:**

- `.local/GenerativeLowerBoundFanoThreshold.lean`, SHA-256
  `0e83000132861fa517f502b5aae7e4f3d11a2834d865c406e10a6f625a956ce4`.
- `.local/GenerativeLowerBoundLargeFamilyRisk.lean`, SHA-256
  `c4c6b5981c33daa673ad5d20adda286ef9cddbe4ee202cf367599ed2c058e877`.
- `.local/GenerativeLowerBoundTwoPointRisk.lean`, SHA-256
  `c1f1b8446644d2e012f97f3c12f6e5fdd5968e2e05cdcc0f25a75f94a8c63b66`.

The builder handoff reported successful focused compilation. A subsequent
independent fresh-source audit recompiled all 30 modules in the Fano/risk
closure and probed every recognized top-level declaration; details and
reproduction harness are in
`critic-generative-lower-bound-fano-risk-fresh-audit.md`. This note remains
the independent source/semantic review of the risk event transfers.

## Large-family branch

The staged theorem quantifies over one deterministic estimator of the whole
sample array into a complete state-to-action map. Its decoder is total, with
baseline fallback for policies not in the hard family. Under `m,n≥1` and
`(m+1)(n+1)≥16`, the exact family cardinality gives `K≥4`. The explicit
condition `4096 N(1−γ)^3 ε²≤log K` yields mean decoding error at least `1/4`.
The conditional decision-to-risk lemma applies to the same estimator and
actual full-array laws, so some actual indexed MDP has strict trajectory-Q
risk event probability at least `1/4`; this strictly exceeds `1/10`. The
budget scaling is consistent with the proposed correction's
`N≤log(SA)/(8192(1−γ)^3ε²)`: `K≥SA/4` and `SA≥16` imply
`log K≥(1/2)log(SA)`.

## Two-point branch

The theorem selects an available alternative `a=some (j,k)` using `m,n≥1`,
and uses the actual active-coordinate product laws `P_a` and `P_none`. Their
interior Bernoulli parameters give full support on that active finite space;
no full-support claim about reconstructed full arrays is needed. The KL
comparison is exactly in the required orientation `KL(P_a || P_none)`, and
the source sparse-KL bound plus the theorem's budget gives it at most `0.9`.

The Boolean test is `decode(estimate (familyReconstruct x)) = a`. Under the
baseline, acceptance implies decoder error because `a≠none`; under the
alternative, rejection implies decoder error. `finite_test_error_gt_one_tenth`
has this exact baseline-acceptance/alternative-rejection orientation and
gives a strict `>0.1` bound on one of those errors. For each model, the
existing pointwise decoder-error-to-risk implication is applied to the same
active-coordinate estimator, then `familySamplingLaw_eq_reconstructed_product`
and the measurable pushforward event identify its risk probability with the
actual full-array sampling law. The resulting actual trajectory-Q risk event
is strict in its threshold `ε`, and the strict `>0.1` probability survives
both monotonicity steps.

The estimator quantifier is still deterministic: it is a function of the
sample array returning a deterministic stationary policy. Thus these
compiled branches do not establish the randomized-estimator wording in the
proposed corrected statement. As recorded in the randomized-estimator plan,
that requires a common model-independent output kernel/seed and a joint-law
argument.

**Verdict:** no source-level issue found in the deterministic branch event
transfers, KL direction, or constants. These are staged exports, not yet
production imports or an author-approved correction to the disputed source
theorem. Fresh staged-source compilation and axiom probes found only the
standard axioms `propext`, `Classical.choice`, and `Quot.sound`; no production
integration claim is made.

Production integration: the relevant production module bodies match the independently reviewed staged sources, with qualified imports where needed. The complete project build compiled the actual exports and audited 2,279 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
