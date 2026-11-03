# Source issues and unresolved interpretation

This is a research ledger, not an author-approved errata list. The original
article remains the source of truth. A corrected result is separately identified
and must not be presented as a proof of an incorrect original statement.

## Candidate C1: singleton actions in Theorem 3.7(i)

**Source:** arXiv:2610.41903v1, printed pp. 47–48,
`chapters/generative_model_model_based.tex:1443–1464`, label `theorem:azar`.
The theorem itself quantifies over deterministic policy estimators with `SA ≥ 16` and
asserts a positive-probability event where the estimated policy's Q-value
differs from the optimal policy's Q-value by more than a positive ε. The printed
statement has no explicit exclusion for `A = 1`. The preceding policy-learning
section assumes `A ≥ 2` (`chapters/generative_model_model_based.tex:787`),
and whether that restriction carries into the next section is an unresolved
interpretation question. Under that standing assumption this singleton-action
case is outside the policy-learning domain.

Set `S = 16`, `A = 1`. Every deterministic policy is the same function, so
for every MDP and every data-dependent policy estimator, the error event is
empty. Choosing ε small enough also satisfies the sample-size upper bound for
any fixed positive constant and any chosen positive integer sample count. The
code in `Formalization/Obstructions/SingletonAction.lean` proves the relevant
policy-evaluation equality and zero event measure for arbitrary extensional
evaluation maps and confirms the cardinality inequality. It does not yet
formalize the full sample experiment or its quantifier structure.

**Status:** a contradiction under the standalone reading of the theorem was
reconstructed from raw TeX and visually checked in the PDF. The scope of the
preceding section's assumption, full formal encoding, and independent review remain
open. Treat `A ≥ 2` as an explicit interpretive choice rather than silently
introducing it or claiming an author-approved correction.

## Candidate C2: one state and known rewards in Theorem 3.7

Independent [source review](critic-one-state-review.md) finds that both parts
of the theorem are contradicted by `S = 1`, `A = 16` under the source's
known-reward convention. The only transition law returns to the sole state;
the single estimator `Q̂(a) = r(a) + γ max_b r(b)/(1−γ)` can use the known
reward and is exact for every admissible model and dataset. A fixed
tie-breaking reward-greedy policy is likewise optimal. The earlier `A ≥ 2`
policy-learning convention is satisfied by this example.

For every proposed constant `c_N > 0`, the reviewer chooses `γ = 2/3`, `N = 1`
and a sufficiently small positive ε satisfying the printed sample and accuracy
restrictions. This numerical feasibility is now proved for every positive
constant in [OneStateParameters.lean](../Formalization/Obstructions/OneStateParameters.lean)
and checked in an [independent review](critic-one-state-parameters.md). The construction used in the paper's proof also degenerates at
`S = 1`: it yields one hypothesis where the Fano step requires at least four.

`Formalization/Obstructions/OneState.lean` establishes the exact formula and
greedy policy for the Bellman fixed points; the trajectory and experiment
bridges below extend the evidence to actual infinite trajectories and a
one-sample generative experiment. An [independent Lean review](critic-one-state-lean-review.md)
checks the original Bellman-level claims. Two independent source readers have
now checked that this deterministic estimator uses only the known reward and
discount permitted by the manuscript;
see the [source-interface review](critic-theorem37-one-state-source-interface.md).
Under those conventions it contradicts the displayed domain of part (ii).
Equivalence between every possible estimator convention and the entire encoded
predicate remains separate, as does the authors' intended domain. `S ≥ 2`
excludes this example but is not asserted sufficient for the original result.
No author-approved correction or ruling is assumed.

## Candidate repair of Theorem 3.7

A [proposed correction](critic-theorem37-correction.md) adds `S ≥ 2` and
`A ≥ 2` to the combined statement and supplies a conservative constant
`c_N = 1/8192`, with separate arguments for policy learning and Q estimation.
It also repairs an incorrect expression for the optimal Q-value after a
suboptimal first action, the source's hypothesis count in its Fano step, and
the policy decoder. A separate [mathematical check](critic-theorem37-correction-independent.md)
reproduces the probability bounds and constants; a further [independent audit](critic-theorem37-final-audit.md) checks the model and estimator quantifiers. This is a proposed replacement,
not an author-approved erratum or a Lean proof of that particular common
constant. Separate Lean-verified results use the smaller common constant
`1/32768`, as described below. The
[one-state trajectory bridge](../Formalization/Obstructions/OneStateTrajectory.lean)
proves exactness of a fixed known-reward estimator and its zero error under
any data law ([review](critic-one-state-trajectory.md)). The
[one-state experiment](../Formalization/Obstructions/OneStateExperiment.lean)
constructs actual independent samples and packages the uniform estimator and
feasible parameters ([review](critic-one-state-experiment.md)); [Theorem37Negation.lean](../Formalization/Obstructions/Theorem37Negation.lean)
negates an encoded source-facing version. Its one-state deterministic
estimator's known inputs have since been independently compared with the source
([review](critic-theorem37-one-state-source-interface.md)); equivalence of all
possible estimator and policy conventions remains separate
([audit](critic-theorem37-negation.md)). The [policy experiment](../Formalization/Obstructions/OneStatePolicyExperiment.lean)
likewise gives a measurable reward-greedy estimator with zero actual Q loss
([review](critic-one-state-policy-experiment.md)). The
correct two-state Bellman values and source-range policy loss are proved in
[HardMDP.lean](../Formalization/Obstructions/HardMDP.lean), with an
[independent review](critic-hard-mdp.md). The separate
[trajectory optimality result](../Formalization/MDP/OptimalTrajectoryValue.lean)
applies to the stationary policy class. A separate [formalized corrected policy-risk result](../Formalization/Generative/GenerativeLowerBoundKernelQuarter.lean) now proves the source probability `≥1/4` on the explicit domain `S,A ≥ 2`, `SA ≥ 16`, with `c_N = 1/32768`, for randomized estimators selecting deterministic stationary policies. Its model is chosen after the estimator; the [independent review](critic-generative-lower-bound-kernel-quarter.md) records the scope and source comparison. A separate [formalized corrected Q-estimation result](../Formalization/Generative/GenerativeLowerBoundQMixtureFinalRandomized.lean) proves the same `≥1/4` probability for arbitrary randomized real-Q estimators on `S,A ≥ 2`, `SA ≥ 16`, with `c_N = 1/512`; see the [independent review](critic-generative-lower-bound-q-final-randomized.md). Neither result proves the wider printed domain or the earlier proposed `1/8192` constant for both parts. A [combined restricted wrapper](../Formalization/Generative/GenerativeLowerBoundCombinedRisk.lean) uses one common constant `1/32768` for both clauses, preserving their separate hard-model witnesses. It has passed integrated and clean-copy compilation, the project axiom audit, and [independent source review](critic-generative-lower-bound-combined-correction.md).

The initial review additionally recorded a possible reward-convention conflict
in the model-based algorithm subsection and a possible confidence/radius scaling issue in the chi-squared guarantees subsection.
A subsequent source-only review ([Chapter 7 candidate review](source-review-robust-rl-chapter7-candidate-issues.md))
found no source-internal reward conflict: the preliminaries make rewards known
and deterministic, and the model-based algorithm subsection estimates only transitions while retaining
the same reward. Compatibility of the cited TV guarantee with this known-reward
setting remains a citation/proof question. The chi-squared guarantees subsection upper/lower factors
and three radius regimes are algebraically consistent under the source macro
`\ror=\sigma`; the separate planning-accuracy remark has a different
logarithmic expression, but the source does not equate those logs. The upper
and lower theorems' discount ranges differ, so their comparison applies on the
intersection `γ ≥ 3/4`. The lower theorem does not explicitly state `ε > 0`,
although its sample bound divides by `ε²`; a formal target needs that domain
made explicit. No reward-convention or radius-scaling error has been established.

## Candidate C3: omitted sample-size case in policy evaluation proof

**Source:** `chapters/generative_model_model_based.tex:589–634`, especially
`eq:T2-bound` and `eqn:ice-cream`. The displayed intermediate bounds assume
`N ≥ 64β₁/(1−γ)`, but the final estimate is stated for
`N ≥ β₁/(1−γ)` without an explicit argument covering the intervening range.
This is a gap in the displayed derivation, not a counterexample to the final
claim. The source uses the same β₁ before and after this step.

**Proposed proof repair:** both the true and empirical policy values lie in
`[0, 1/(1−γ)]`, so their sup-norm difference is at most `1/(1−γ)`.
The printed final radius `3√(8β₁/((1−γ)³N))` is at least this bound when
`N ≤ 72β₁/(1−γ)`. A deterministic low-sample case thus covers the omitted
range, while retaining the original high-sample argument and final constants.
This repair does not by itself justify each intermediate bound under the weaker
threshold. The independent [mathematical review](critic-policy-evaluation-sample-constant.md)
checks the argument and the strict-probability issue. The resulting
[all-state source-radius repair](../Formalization/Generative/PolicyEvaluationGapRepairAllStates.lean)
has passed focused compilation and an [independent source review](critic-policy-evaluation-source-gap-repair.md):
it covers every `N > 0`, the actual policy-row sampling law, the source beta
with `C₀ ≥ 8`, and the one-state boundary. Integrated and clean-copy builds
and the project axiom audit passed. It does not establish each intermediate inequality
under the weaker threshold or replace the separate sample-complexity theorem.

## Candidate C4: strictness in the two-state testing reduction

**Source:** `chapters/generative_model_model_based.tex:1790–1835`, with the
claimed strict error conclusion at `:1551–1555`. The displayed lower bound
`p_e ≥ 0.1` and contradiction from both success probabilities `> 0.9` alone
yield only that some error probability is `≥ 0.1`, whereas the conclusion
uses `> 0.1`. This is an omitted strictness step, not a counterexample.

The stronger Pinsker branch retains enough slack: under the source bound
`β ≤ 0.9`, `(1−√(β/2))/2 > 0.1`. Using that strict testing bound and assuming
both estimation errors are at most 0.1 gives the intended contradiction.
The [source analysis and independent mathematical check](source-generative-lower-bound-testing-bottleneck.md)
record the argument. A strict testing route is now also consumed by the
formalized two-point policy-risk result for arbitrary common randomization over
deterministic stationary policies. Separate corrected randomized policy-risk
and Q-risk results prove the stronger `≥1/4` bound on the explicit domain
`S,A≥2`, `SA≥16`. An arbitrary randomized-Q extension of the standalone
two-state, one-action testing example and the source's wider original domain
remain separate; the source's strictness omission is not itself a counterexample.

## Candidate C5: missing premise in TD step-size Lemma 4.3

The printed standalone `lemma:TD-step-size` (`generative_model_model_free.tex:317–327`) omits a gamma-dependent sample-size premise used in its appendix proof, and does not explicitly bound `t` by the horizon on which the schedule is constrained. The [independent source review](critic-td-step-size-premise.md) gives a concrete admissible counterexample to the early-weight bound: take `c₁=c₂=1/4`, `T=t=100`, `γ=1−10⁻⁶`, and each learning rate equal to the printed lower endpoint. Then the initial weight is at least `0.9999`, whereas the lemma asserts it is at most `0.0001`.

The proof uses `T ≥ log²(T)/(c₁(1−γ))`; the [formal helper](../Formalization/ModelFree/TDStepSizeLate.lean) retains that condition and `t≤T`, while a [separate proof](../Formalization/ModelFree/TDStepSizeBudget.lean) derives the large-T condition from the enclosing main theorem’s sample budget for a sufficient constant relation. This is a statement gap for the standalone auxiliary lemma, not by itself a counterexample to the main TD theorem. No author-approved correction is asserted.

## Candidate C6: confidence factor in the UCBVI optimism proof

**Source:** arXiv:2610.41903v1, `chapters/onlineRL.tex`,
`lemma:opt` at lines 765–773 and its proof near lines 3370–3395.
The lemma states optimism with probability exceeding `1−2SAHKδ'`. The proof's
final paragraph instead states probability at least `1−4SAHKδ'`, after a
preceding per-coordinate `1−2δ'` bound and a union-bound discussion.

**Status:** the raw source has been checked, but the rendered PDF and a
complete independent reconstruction of the probability accounting remain to
be checked. The factor-four proof conclusion alone does not establish the
printed factor-two conclusion. This observation does not prove that the
lemma is false: a sharper common event may justify the printed factor, or the
proof/statement may need an author correction. Retain the printed statement
as the source target and do not silently replace either confidence factor.

One candidate proof repair is to use a single simultaneous concentration
event for every deterministic visit-prefix length up to K−1 for each
state-action-stage row. Each adaptive visit count is then covered without
conditioning on that random count; a union over the row/prefix pairs may
retain the factor 2. The proposed corrected implementation now has an
[isolated Lean proof](critic-online-corrected-optimism.md) using a
pre-sampled-to-sequential law bridge and an explicit zero-visit convention.
It covers one fixed deterministic tie rule; the literal printed algorithm
leaves its zero-count update undefined. Full working and clean integration builds and axiom audits passed. The
source's factor discrepancy remains documented.

## Candidate C7: degenerate domains in the robust chi-squared lower bound

**Source:** Theorem 7.5, `thm:chi2-lower-bound`,
`robust_RL.tex:461–480`. Its displayed assumptions do not explicitly exclude
`A = 1` or `S = 1`, and do not state `ε > 0` despite division by `ε²`.

For `A = 1`, every policy is the unique policy, so its robust value equals
the robust optimum under every model. The strict positive-error event is
empty, contradicting the printed positive minimax lower bound on a literal
reading of the displayed domain. For example `S = 2`, `A = 1`, `γ = 3/4`,
`σ = 1`, `N = 1`, and sufficiently small positive `ε` satisfy its numerical
conditions for any positive constants. Under the known-reward convention,
`S = 1` is also degenerate: the sole transition is known, and a
reward-maximizing action is known. See the [source audit](critic-robust-chi-square-lower-bound-degenerate-domains.md)
and [independent check](critic-robust-chi-square-lower-bound-degenerate-independent.md).

A transparent proposed correction makes `S ≥ 2`, `A ≥ 2`, and `ε > 0`
explicit. These exclusions address the displayed singleton cases; they do not
prove the cited lower bound on the remaining domain. The source's general
large-dimension discussion may indicate intended scope, but no numerical
restriction appears in the theorem. This is not an author-approved erratum,
and no complete Lean proof of the corrected robust theorem is claimed. A
[stationary-policy robust-value foundation](../Formalization/RobustRL/ChiSquaredPolicyValue.lean)
constructs actual trajectory-value infima and proves the singleton-action
zero-gap mechanism in that policy class; see its [review](critic-robust-chi-policy-value-independent-review.md).

## Candidate C8: undefined zero-visit bonus in UCBVI

**Source:** Algorithm `alg:main-ucbvi`, `onlineRL.tex:285–345`, and its
Bernstein bonus at lines 407–417. The algorithm initializes visit counts to
zero and later computes the bonus for every state-action-stage row. The printed
bonus divides by the count and does not specify a zero-count convention. Rows
can remain unvisited, so this branch arises in the actual algorithm. The proof
at lines 3311–3331 asserts `Q = H` for counts at most two.

A proposed explicit convention is to leave `Q_h(s,a) = H` when its count is
zero and retain the initialized uniform empirical row until the first visit;
for positive counts, use the printed bonus and update unchanged. With the
source's sufficiently large constants, counts one and two also saturate at
`H`. This makes the small-count branch precise without changing observations
or adding fictitious samples. An independent source review also checked the
positive-count formula and the small-count constants ([review](critic-online-zero-count-convention.md)). The complete algorithm
must use the updated count for a visited row, not its pre-episode count. This
is an interpretation of the intended algorithm, not an author-approved
correction. A [scalar version](../Formalization/Online/OnlineZeroCountOptimisticUpdate.lean)
has passed isolated compilation and an axiom check ([review](critic-online-zero-count-scalar-independent-review.md)); its connection to the complete
adaptive algorithm remains unverified.

## Candidate C9: offline lower-bound accuracy endpoint

The standalone offline minimax lower bound `thm:infinite-lwoer-bound`
(`offlineRL.tex:2367–2402`) gives an upper bound on `ε` but does not restate
`ε > 0`, although its sample threshold divides by `ε²`. The chapter's
problem setup explicitly restricts accuracy to a positive range. Its displayed
hard-instance proof uses a perturbation proportional to `ε` and degenerates at
zero. A source-facing standalone declaration should therefore make the
chapter's positive-accuracy convention explicit. This is a scope and proof
endpoint clarification, not a counterexample to the existential theorem at
zero. The theorem already requires `S > 12` and constructs two actions, so the
singleton-domain obstructions do not apply. See the [source review](critic-offline-lower-bound-domain.md).
