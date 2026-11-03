# Independent critic review: Bellman contractions and fixed points

Reviewer: `/root/lean_resources`, 2026-11-02. The reviewer did not author
`Basic.lean`, `FixedPoint.lean`, or `Analysis/Contraction.lean`.
Owned write set for this review: this report only. No Lean sources changed.

**Verdict: PASS for the stated finite-tabular Bellman-operator infrastructure;
PARTIAL for the corresponding source theorem family.** No implementation defect
was found in the scoped contractions, fixed-point existence/uniqueness, iteration
bounds, convergence, or interval bounds. The identification with infinite
trajectory returns and optimal policies remains unproved. In particular, the
source's combined VI-and-PI convergence lemma is not complete.

This is ordinary infrastructure review, not an author-approved frozen-anchor
audit. No author approval, frozen status, or whole-source closure is inferred.

## Pinned evidence and source-first reconstruction

The raw source was read before inspecting the reviewed implementations. Relevant
`source/upstream/tex/chapters/prelim.tex` SHA-256:
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

| Source location | Independently reconstructed obligation |
| --- | --- |
| Lines 29–55 | Finite states/actions; stationary stochastic transition; deterministic reward in `[0,1]`; discount `0 ≤ γ < 1`, including zero. |
| Lines 66–74 | A stationary policy may be randomized; the induced state transition averages the actual kernels over its action probabilities. |
| Lines 90–128 | Policy value and Q-value are expectations of infinite discounted trajectory rewards. These definitions precede Bellman characterizations. |
| Lines 135–140 | An optimal deterministic policy simultaneously maximizes policy returns; `Q*` denotes its trajectory Q-value. |
| Lines 193–222 | Policy Q backup is `r + γ E_next E_policy Q`; state-value backup averages rewards and the policy-induced next-state value. |
| Lines 235–245 | Optimality backup is `r + γ E_next max_action Q`; its identification with `Q*` requires an optimal-policy/return argument. |
| Lines 251–283, `eq:gamma-contraction-preliminary-inf` | Both Q operators are γ contractions in the complete finite sup norm, on all real Q arrays. The maximum is nonexpansive. |
| Lines 316–355 | VI iterates the optimality map. PI instead greedifies an evaluated policy. The joint lemma asserts a γ-power error bound for both relative to trajectory `Q*`; the PI proof is omitted and cited externally. |

Reviewed implementation hashes:

| File | SHA-256 |
| --- | --- |
| `Formalization/MDP/Basic.lean` | `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088` |
| `Formalization/MDP/FixedPoint.lean` | `b7c7b6338d1ec5005942e3b0f80676ed8e0e2dfb650a2cb01638642fe65f642e` |
| `Formalization/Analysis/Contraction.lean` | `a82dd82216ccbebf147c4a633bb0d575a4d47185d98accb3e7a5fd0e6f1327a9` |

## Expanded binders and meaning-carrying fields

This table inventories the shared binder families across the principal exports;
each theorem uses only its relevant rows. `StationaryPolicy` was expanded into
its actual probability vectors. `DiscountedMDP` and `FiniteDistribution` were
expanded rather than accepted as opaque assumption bundles. SOURCE means source
data or universally quantified source variables; STANDING means the model's
probability/reward/discount conventions; TYPING means finite-carrier machinery.

| Input or expanded field | Bin | Scope / source justification |
| --- | --- | --- |
| `State : Type*` | TYPING | Generic carrier representing the source's finite state indexing. |
| `Action : Type*` | TYPING | Generic carrier representing the source's finite action indexing. |
| `[Fintype State]` | TYPING | The state carrier is finite; lines 33–37. |
| `[Fintype Action]` | TYPING | The action carrier is finite; lines 33–37. |
| `M.state_nonempty` | STANDING | Nonempty state space of an MDP; compatible with the source's state/distribution conventions. |
| `M.action_nonempty` | STANDING | Nonempty available actions, required by the source's action distribution and maximum. |
| `M.transition s a : FiniteDistribution State`, expanded mass `prob t` | SOURCE | Actual `P(t | s,a)`, for every current state/action and next state; lines 39–40. |
| Each transition's `prob_nonneg t` | STANDING | Nonnegativity of the source's probability simplex. |
| Each transition's `sum_prob = 1` | STANDING | Normalization of that same probability simplex. |
| `M.reward s a` | SOURCE | Literal deterministic stationary reward; lines 44–45. |
| `M.reward_nonneg s a` | STANDING | Lower reward endpoint zero. |
| `M.reward_le_one s a` | STANDING | Upper reward endpoint one. |
| `M.discount` | SOURCE | The same scalar γ throughout the model and all iterates. |
| `M.discount_nonneg` | STANDING | Source includes γ = 0. |
| `M.discount_lt_one` | STANDING | Source requires γ < 1; no extra γ > 0 premise. |
| `π s`, expanded mass `(π s).prob a` | SOURCE | General stationary randomized policy; lines 66–67. |
| Each policy vector's `prob_nonneg a` | STANDING | Policy is an actual action probability distribution. |
| Each policy vector's `sum_prob = 1` | STANDING | Policy normalization, at every state. |
| `Q₁ : State → Action → ℝ` | SOURCE | Arbitrary real input Q array in the contraction inequality. |
| `Q₂ : State → Action → ℝ` | SOURCE | Second arbitrary real input Q array; no reward-interval restriction. |
| `Q₀ : State → Action → ℝ` | SOURCE | Arbitrary initial Q array for iteration. |
| `n : ℕ` | SOURCE | Iteration index; the proved bound also covers zero, extending the source's `k ≥ 1` harmlessly. |
| `s : State` | SOURCE | Arbitrary coordinate where a pointwise conclusion is asserted. |
| `a : Action` | SOURCE | Arbitrary action coordinate, independent of the policy's support. |
| Candidate `Q` in fixed-point characterizations | SOURCE | Arbitrary element of the full Q-function carrier, not an assumed optimal value. |

Counts for these shared families: SOURCE 11, STANDING 10, TYPING 4, RULED 0,
EXCESS 0. There is no singleton-state/action restriction in the principal
contraction or fixed-point results. The separate singleton helper in `Basic`
is not a premise or dependency of those results.

Auxiliary hypotheses were checked separately: a pointwise uniform error bound
in `abs_*_sub_le` is discharged from the actual Pi norm in each final norm
theorem. A bound on input `Q` in `*_preserves_bounds` is discharged by induction
from the actual zero iterate; it is absent from the final fixed-point bounds.
Candidate fixed-point equations in uniqueness lemmas express the property being
tested, and are supplied by proved specifications for selected fixed points.
No missing estimate, existence theorem, convergence claim, or optimal-policy
property is inserted into the final theorem premises.

## Definition and proof audit

| Component | Verdict and evidence |
| --- | --- |
| Finite expectation and mixture | PASS. `expectation` is the actual sum `Σ p(x) f(x)`. `bind` computes mixture masses and proves nonnegativity/normalization. No hidden conditional result. |
| Policy transition and Bellman operators | PASS. `policyTransition`, `qBellman`, `valueBellman`, and `qOptimality` reproduce the source operations with the correct nested order. The next policy is evaluated at the sampled next state. |
| Finite maximum | PASS. `actionMaximum` uses `Finset.univ.sup'` on the genuinely nonempty whole action carrier. It does not select an arbitrary action or assume an optimal policy. |
| Full sup norm | PASS. The default finite Pi norm is the maximum coordinate norm, twice for `State → Action → ℝ`. This is not an L1/L2 norm or a restricted subset of Q arrays. Inspected Mathlib `Analysis/Normed/Group/Constructions.lean`, finite Pi norm definition and `pi_norm_le_iff_of_nonneg`. A compiled probe established `‖Q‖ ≤ c ↔ ∀ s a, |Q s a| ≤ c` for `c ≥ 0`. |
| Completeness | PASS. A compiled probe synthesized `CompleteSpace (State → Action → ℝ)` under only finite carriers. The Q-function space contains zero, so nonemptiness for Banach is supplied without an extra model hypothesis. |
| Q-policy/optimality contractions | PASS. The finite-sum absolute-value estimates and maximum nonexpansiveness yield exactly γ times the original sup norm. Quantification is over arbitrary Q arrays. |
| Fixed-point existence and selection | PASS. Exact `∃! Q, T Q = Q` is proved using the constructed contraction on the complete full space. `Classical.choose` is applied only afterward. Specifications and iff characterizations prove the exact equation and uniqueness on that whole carrier. No fallback body or deferred Bellman characterization. |
| Iteration and convergence | PASS for policy evaluation and VI relative to their respective Bellman fixed points. The actual function iterate is used, with the exact exponent γ^n and arbitrary initialization. `Analysis.iterate_dist_le` consumes the proved Lipschitz and fixed-point specifications. |
| Interval bounds | PASS for Bellman solutions. Actual backups preserve `[0, 1/(1−γ)]`, using reward bounds, probability normalization and `1 + γ/(1−γ) = 1/(1−γ)`. Zero-start iterates remain in the interval; convergence transfers the coordinate bounds to each fixed point. No interval membership is assumed of the fixed-point object. |
| γ = 0 | PASS. No construction divides by γ. Only `1−γ` is inverted, with strict positivity proved. Additional compiled probes showed both operators and both chosen fixed points equal the reward function at γ = 0, and the VI error is zero for every positive iterate. The n = 0 bound uses the standard `0^0 = 1` convention. |

For the selected objects, BODY_MATCH, PUBLIC_CARRIER, WELL_DEFINEDNESS,
CHARACTERIZATION, and CHOICE_INDEPENDENCE all pass **as Bellman fixed-point
objects**. These verdicts do not redefine their meaning as trajectory returns.

## Compiler and transitive axiom evidence

The current source files were independently checked, with one compiler process
at a time and no dependency changes:

```sh
bash scripts/lean-local.sh Formalization/MDP/Basic.lean
bash scripts/lean-local.sh Formalization/MDP/FixedPoint.lean
```

Both exited successfully with no diagnostics. A separate `--stdin` probe
imported `Formalization.MDP.FixedPoint`, compiled the norm/completeness and γ = 0
checks described above, and inspected `#print axioms` for these actual exports:

- `norm_qBellman_sub_le`, `norm_valueBellman_sub_le`, `norm_qOptimality_sub_le`;
- `policy_fixedPoint_exists_unique`, `optimality_fixedPoint_exists_unique`;
- `policyFixedPoint_characterization`, `optimalityFixedPoint_characterization`;
- `policy_evaluation_iteration_error`, `value_iteration_error`;
- `tendsto_policy_evaluation_iteration`, `tendsto_value_iteration`;
- `policyFixedPoint_bounds`, `optimalityFixedPoint_bounds`.

All 13 inspected exports depend only on `propext`, `Classical.choice`, and
`Quot.sound`. No custom axiom or unfinished-proof axiom appeared.

## Remaining source obligations and reporting boundary

1. Construct infinite discounted trajectory returns independently and prove
   their Bellman equations. The policy Bellman solution has not yet been
   identified with source `Q^π`/`V^π` from lines 90–128.
2. Prove deterministic greedy-policy existence and genuine optimality over
   trajectory returns. The optimality Bellman solution is not yet identified
   with the source's `Q*` at lines 135–140 and 242–245.
3. Formalize PI's policy evaluation, greedy improvement, and convergence. PI is
   not iteration of the policy-evaluation map, and `value_iteration_error` is
   not a PI theorem. The combined source lemma at lines 339–343 remains partial.
4. Derive any source iteration-complexity statement with its precise epsilon
   domain and integer rounding. The displayed logarithmic expression at lines
   358–360 is not itself implemented by the geometric-error theorem.

Accordingly, passing these scoped checks permits reporting proved Bellman
infrastructure and a geometric VI bound to its Bellman fixed point. Reporting
the entire source VI/PI lemma, infinite expected-return semantics, or Chapter 2
as completed would **FAIL this review**.
