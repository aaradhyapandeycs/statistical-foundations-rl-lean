# True-policy variance resolvent and square-root bound

`.local/PolicyEvaluationVarianceResolvent.lean` extends the independently reviewed staged variance-budget module with exact finite-sum expansions, a finite/infinite Jensen argument, and **literal true-policy matrix inverse identities and bounds**. For positive discount it proves the source-shaped square-root resolvent bound with constant 1, sharper than the source's displayed `√2` constant. This is deterministic true-kernel infrastructure, not the sharp high-probability policy-evaluation theorem. Independent review and integration are pending.

## Source and standing objects

The relevant source is `generative_model_model_based.tex:295–350`, especially the true-kernel Jensen estimate `eq:Jensen-I-gamma-P-Var`, true variance-resolvent estimate `eq:I-gamma-P-Var-bound`, and square-root bound `eq:lemma-VarP-V-bound`. The source's motivating replacement of the empirical resolvent by the true one is expressly heuristic there; no such comparison is assumed or proved here.

Let `M` be any admissible finite discounted MDP, π any stationary randomized policy, `γ=M.discount`, `V=M.trajectoryExpectedValue π` the actual infinite-trajectory value, `P=M.policyTransition π` the true policy row kernel, `σ(s)=Var_{P(s)}(V)` the true row population variance, `B=‖V‖∞`, and `R=(I−γP)⁻¹`. The source-generated MDP assumptions provide `0≤γ<1`, bounded nonnegative rewards, normalized transitions and finite nonempty carriers. No samples, concentration event, empirical transition, or desired bound is a hypothesis.

## Finite sums, Jensen, and limits

The earlier `PolicyEvaluationVariance` module constructs `U_n` recursively as `U_0=0`, `U_{n+1}=γ²σ+γP U_n`, proves monotonicity and `0≤U_n≤B²`, and constructs its limiting unique discounted-equation solution U.

This staged extension introduces the scaled square-root recursion `T_0=0`, `T_{n+1}=γ√σ+γP T_n`. `evaluationPolicyKernelIter` implements the actual t-fold true policy kernel, and the separately proved finite-sum results are

```text
U_n(s) = Σ_{t<n} γ^(t+2) (P^t σ)(s),
T_n(s) = Σ_{t<n} γ^(t+1) (P^t √σ)(s).
```

These are Lean theorems (`discountedPolicyVariancePartial_explicit` and `discountedPolicySqrtVariancePartial_explicit`), not just interpretations of the recursions.

`evaluation_expectation_sq_le` derives finite-row Jensen from nonnegativity of the actual finite distribution's variance. `discountedPolicySqrtVariancePartial_sq_le` combines it with an exact nonnegative scalar square to prove `0≤T_n` and `(1−γ) T_n(s)²≤U_n(s)`. Therefore `T_n(s)≤B/√(1−γ)`. The recursion is increasing, hence its pointwise supremum T is the actual limit of the finite recursions. The limit satisfies `T=γ√σ+γPT` uniquely, `(1−γ)T(s)²≤U(s)`, and `‖T‖∞≤B/√(1−γ)`.

## Literal matrix inverse and source bounds

`evaluationPolicyMatrix M π` has the real probability-row entries of the actual policy transition kernel. `evaluationPolicyResolvent_isUnit` proves `I−γP` invertible from stochastic-row contraction; the inverse is not postulated. `discountedPolicyVarianceBudget_eq_inverse` and `discountedPolicySqrtVarianceBudget_eq_inverse` then identify the earlier variance budget and new square-root budget with the actual finite matrix inverses:

```text
U = R (γ² σ),       T = R (γ √σ).
```

`evaluationPolicyResolvent_jensen` proves the corresponding literal matrix statement

```text
(1−γ) [γ (R√σ)(s)]² ≤ γ² (Rσ)(s).
```

`evaluationPolicyResolvent_variance_bound` proves `0≤γ²(Rσ)(s)≤B²`, and `evaluationPolicyResolvent_sqrtVariance_bound` proves

```text
γ ‖R√σ‖∞ ≤ B/√(1−γ).
```

These scaled statements include γ=0 and avoid division by the discount. For γ>0, `evaluationPolicyResolvent_sqrtVariance_bound_of_pos` yields the source-shaped unscaled result `‖R√σ‖∞≤B/[γ√(1−γ)]`; the source displays the weaker factor `√2` on the right. The source's unscaled expression is not asserted at γ=0. No inverse positivity or Jensen inequality is assumed: the proof passes through actual finite probability rows, finite sums, the monotone limits and matrix invertibility.

The remaining sharp policy-evaluation work includes relating the empirical resolvent to this **true** resolvent, using the actual residual Bernstein event and leave-one-out or other necessary dependence control, and proving the complete sample/accuracy arithmetic. These declarations alone do not yield an empirical-resolvent bound or establish the chapter theorem.

## Validation and integration

The exact staged source was copied unchanged to a temporary probe, compiled using the staged `PolicyEvaluationVariance.olean` built from the exact independently reviewed staged dependency, and checked with eighteen appended `#print axioms`. The exact source and all eighteen probes compiled without diagnostics; every audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. This is a staged dependency-path check, not an integrated export build.

Current import is `import PolicyEvaluationVariance`, the local staging module. Integrate and build the independently reviewed budget first; update the import to its actual project module, independently review the change and rebuild/audit actual integrated exports. The exact staged source and new source-shaped results require independent review before any source-completion claim.

SHA-256:

- `.local/PolicyEvaluationVarianceResolvent.lean`: `960f10723253fa82fbea2cfce6245fa6aee22992e246b958cc4f858bdbd80166`.
- `.local/PolicyEvaluationVariance.lean`: `f25b76fadce9e452abe3375d2b8b5cf003df748ab6d737529cbe58b1b039d33d`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
