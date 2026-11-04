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
evaluation maps and confirms the cardinality inequality. The
[source-shaped experiment](../Formalization/Obstructions/Theorem37SingletonAction.lean)
also supplies the actual row-product sampling law, trajectory-Q equality,
and one estimator whose risk is zero for every compatible model. Its focused,
working-tree and clean-copy compilation and axiom checks passed.

**Status:** a contradiction under the standalone reading of the theorem was
reconstructed from raw TeX and visually checked in the PDF. The scope of the
preceding section's assumption and formal encoding of the full minimax theorem
remain open. Treat `A ≥ 2` as an explicit interpretive choice rather than silently
introducing it or claiming an author-approved correction. See the
[source review](critic-theorem37-singleton-action-obstruction.md).

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

The [standalone counterexample](../Formalization/ModelFree/TDStandaloneStepSizeCounterexample.lean)
formalizes the numerical schedule and strict failure of the initial-weight
bound using the project's actual step-size and weight definitions. The same
proof passed a focused check under a draft header; the current source passed
working-tree and clean-copy compilation and axiom checks. It does
not assert that the main theorem's sample budget holds for this witness.

## Candidate C6: confidence factor in the UCBVI optimism proof

**Source:** arXiv:2610.41903v1, `chapters/onlineRL.tex`,
`lemma:opt` at lines 765–773 and its proof near lines 3370–3395.
The lemma states optimism with probability exceeding `1−2SAHKδ'`. The proof's
final paragraph instead states probability at least `1−4SAHKδ'`, after a
preceding per-coordinate `1−2δ'` bound and a union-bound discussion.

**Status:** the raw source and extracted PDF text have been checked; a visual
PDF check remains open. The factor-four proof conclusion alone does not
establish the printed factor-two conclusion. This observation does not prove that the
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
leaves its zero-count update undefined. Full working and clean integration
builds and axiom audits passed. This is an alternative proof for the corrected
implementation; the source's factor discrepancy remains documented.

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
The [singleton-action counterexample](../Formalization/RobustRL/SingletonActionCounterexample.lean)
also establishes feasible parameters and zero risk for one fixed estimator
against every model pair, under their actual row-product sampling laws. It has
passed focused, working-tree and clean-copy compilation and axiom checks.
It does not encode the complete estimator infimum in the manuscript. See the
[source and evidence review](critic-robust-chi-singleton-action-v5.md).

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
has passed compilation and an axiom check
([review](critic-online-zero-count-scalar-independent-review.md)). A separately integrated
[corrected planner and optimism proof](critic-online-corrected-optimism.md)
uses this zero-count convention under the actual adaptive sequential law,
for one fixed deterministic tie rule. The printed zero-count behavior remains
undefined, and the proposed convention is not an author-approved correction.

The corrected deterministic telescope is now proved as
`StatisticalRL.Statements.Lemma5_6_corrected`: it assigns H as the finite
analysis charge at zero visits and agrees with the printed bonus at
positive counts. Its generic statement permits every greedy maximizing
tie choice. The supporting actual-law probability decomposition retains
the existing fixed deterministic tie implementation. This does not define
the original zero-count expression or prove the full regret theorem. See
[verification](online-regret-telescope-verification.md) and
[independent review](critic-online-regret-telescope.md).

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

## Candidate C10: discount endpoint in the offline VI-LCB lemma

**Source:** Lemma 6.2, `lem:monotone-contraction`,
`offlineRL.tex:872–890`; its appendix proof uses `γ ≥ 1/2` at
`offlineRL.tex:3341–3343`. The preliminary MDP definition permits
`γ ∈ [0,1)`, and no narrower chapter-wide assumption was found before the
lemma. The subsequent main Theorem 6.3 explicitly assumes `γ ≥ 1/2`.

There is a source-level counterexample to the standalone lemma at `γ=0`.
Take two states, one action, rewards `0.9` and `0.1`, and `N=2n` samples,
with `n` visits to each state. Let the first empirical row be deterministic
and the second have equal mass on the two states. These rows and counts are
realizable by an offline dataset. Fix `δ ∈ (0,1)` and any `c_b > 0`, and
write `κ = c_b log(N/δ)/n`. For sufficiently large even `n`, both `κ` and
`5/N` are small enough that the following updates are untruncated.

From `Q₀=0`, the penalty at both states is `d=2κ+5/N`, so
`Q₁=(0.9−d, 0.1−d)`. Its second-row variance is `0.16`. For sufficiently
small `κ`, the second state's next penalty is `0.4 sqrt(κ)+5/N > d`, so
`Q₂` differs from `Q₁`. But the lemma's error bound at `τ=1`, `γ=0` is zero:
it would force `Q₁` to be the fixed point and hence `Q₂=Q₁`. Its separate
iteration threshold also contains `log(1/γ)`, which needs an endpoint
interpretation at `γ=0`.

This is an independently checked mathematical counterexample, not yet a Lean
proof or author-approved erratum. Restricting the helper to the main theorem's
`γ ≥ 1/2` domain avoids this example and matches the cited appendix step; it
is not by itself a formal proof of the restricted lemma. The example does not
refute Theorem 6.3, whose displayed assumptions exclude `γ=0`.

## Candidate C12: one-episode endpoints of auxiliary online bounds

**Source:** `lem:bound-W1-W2-ucbvi-proof`, `onlineRL.tex:928–953`, and
`eq:assumption-K-proof-B`, lines 726–733. The main theorem at lines 472–480
permits `K ≥ 1`; only the reciprocal-count lemma at lines 640–644 explicitly
restricts to `K ≥ 2`. The displayed W1/W2/W3 lemma has no such restriction.

At `K = 1`, the printed factor
`iota = 40000 (log₂ K)^3 log(3SAH) log(1/δ′)` is zero. A finite source-level
counterexample takes `S = A = H = 2`, `K = 1`, and `δ = 1/2`, with both actions
identical and the initial state fixed at state 0. Every stage-1 transition goes
to state 0 with zero reward. Stage-2 reward is zero at state 0 and one at
state 1. The pre-episode empirical rows are initialized uniformly as stated
in the source. Hence the first W1 summand is `1/2 − 0`, and the terminal
summand is zero: `W1 = 1/2` deterministically. The printed right-hand side is
zero for any finite continuation tables. Here `δ′ = 1/12800`, so the source
claims its joint event has probability greater than `197/200`, whereas its
W1 inequality fails on every path in this example.

This is independently checked source-level counterevidence, **not yet a Lean
formalization of the counterexample**. The source's separate undefined bonus
at zero visits remains Candidate C8; the example persists under its intended
finite zero-count completion retaining the explicitly initialized empirical
rows. It does not refute the main regret theorem, which can handle `K = 1`
separately using the deterministic regret bound.

A second endpoint occurs in `lem:bound-T234`, lines 988–1005. At
`K = H = 1`, its displayed confidence at line 990 demands probability
strictly greater than `1 − 4 log₂(KH) δ′ = 1`, which is impossible for any
probability event. The side condition at line 1003 and the proof's large-K
condition at lines 748–751 both reduce to valid zero-logarithm inequalities.
This confidence obstruction is independent of the undefined zero-count
bonus and is source-level evidence; no Lean formalization of this subcase
or author-approved erratum is claimed. It does not refute the main regret
theorem. A corrected auxiliary theorem needs an explicit endpoint treatment
or a domain on which the confidence factor is positive.

A proposed correction restricts this auxiliary logarithmic bound to `K ≥ 2`,
or replaces the vanishing logarithm by a positive floor and treats the endpoint
explicitly. Any K≥2 formalization is a disclosed restricted result, not the
literal all-K auxiliary claim. No author-approved erratum is asserted. See the
[independent source check](critic-online-k1-iota-obstruction.md).

## Statement-index scope disclosures

These are limitations of the currently proved formalizations, not asserted
errors in the manuscript.

- Theorem 3.2 (`Thm:sample-compl-main`,
  `generative_model_model_based.tex:900–923`) and Lemma 3.5
  (`lem:policy-learning-evaluation`, lines 1306–1326) have an explicit `N > 0`
  hypothesis in their existing Lean exports. Their statement-index entries
  retain and disclose that restriction.
- Theorem 3.9 (`Thm:sample-compl-finite`,
  `generative_model_model_based.tex:2551–2570`) is proved for the causal
  backward-greedy tie rule implemented by the existing export, with positive
  sample count. The statement index records this scope; it does not claim the
  result for every possible empirical-optimal tie rule.

- The full joint Lemma 5.7 (`lem:bound-W1-W2-ucbvi-proof`,
  `onlineRL.tex:925–957`) is formalized for K≥2 with the finite
  zero-count completion and fixed greedy tie. The statement entry is
  `Lemma5_7_K2_corrected`; C12 records the missing K=1 endpoint and
  C8 the zero-count correction. The earlier W1-only entry remains available,
  while its ledger variant is superseded. The unmodified K=1 source claim
  and the final regret theorem are not certified by this result.

- Complete joint Lemma 5.8 (`lem:bound-T234`, `onlineRL.tex:988–1005`)
  is formalized as `Lemma5_8_K2_corrected`. It retains the printed iota,
  threshold, all four displayed inequalities and strict confidence. The
  explicit K≥2 restriction addresses C12, and the finite zero-count
  implementation and analysis charge H address C8. One fixed deterministic
  maximizing tie rule is used. The unrestricted endpoint, later T5/T6 bounds
  and final regret theorem are not certified by this result. See
  [independent review](critic-online-t234-joint.md).

- Complete Lemma 5.9 (`lem:bound-T56`, `onlineRL.tex:1055–1092`) is
  formalized as `Lemma5_9_K2_corrected`. All five inequalities, printed
 14/30 probability coefficients, literal T0/iota and the large-K condition
  for the last two are retained. Fixed universal c1=4,c2=16 discharge the
  coefficient-dependent T2 threshold. K≥2 is disclosed for the auxiliary
  proof route (C12); zero-count completion and H charge follow C8. A fixed
  deterministic maximizing tie rule is used. This is a corrected variant,
  not certification of the unrestricted printed algorithm or K=1 lemma.
  See [independent review](critic-online-t56-joint.md).

- Theorem 5.2 (`thm-ucbvi-regret`, `onlineRL.tex:472–482`) is formalized
  as `Thm5_2_corrected` for the C8 finite zero-count completion and one fixed
  deterministic greedy tie rule. The asymptotic rate is made explicit as
  20(√(SAH³K)+S²AH³)(1+iota), with universal bonus constants 4 and 16. All K≥1
  are covered: K=1 and small samples use the deterministic horizon bound;
  larger samples use the proved actual concentration/variance estimates.
  C12's auxiliary endpoint restriction does not restrict this main theorem.
  This establishes the corrected algorithm, while the printed zero-count
  rule remains undefined as recorded in C8. See the
  [independent review](critic-online-ucbvi-regret.md).

<a id="C13"></a>

## Candidate C13: MVP trigger notation and stored-count comparison

**Status: source trigger inconsistency and invalid intermediate argument;
a corrected power-of-two trigger variant of Lemma 5.12 is proved.**

Source: `chapters/onlineRL.tex:1570–1591`, `lem:sum-inv-Nhk-mvp`;
the factor-two claim is at line 1582. The algorithm's counter updates are
at lines 1281–1288, with doubling described at lines 1213–1217. The Lean
interpretation uses power-of-two trigger times as specified by that prose.
However, algorithm line 1280 literally lists the consecutive integers
`{1,2,...,2^(log₂K)}`, which include every positive count up to K. Under that
literal reading, one state/action/stage and K=32 give stored size 1 at every
visit: the inverse-count sum is 32, exceeding the printed 4 log₂32=20.
This is independently checked source-level arithmetic, not a Lean encoding
of the literal algorithm. The source prose and displayed trigger conflict;
the proved variant explicitly selects the prose-intended dyadic rule.

After a fixed row has been visited three times, the cumulative count is 3.
The last completed batch is the singleton second visit; the third visit is
pending, so the stored batch size remains 1. Thus the claimed pointwise
comparison `N_all ≤ 2*N` fails: 3≤2 is false. The stored sizes after n visits
are 0,1,1,1,2,2,2,2,4,...; they are not the largest power of two below n.
The displayed reduction to `2/max(N_all,1)` therefore fails at this point.

The final sum bound is true for the prose-intended power-of-two rule. A dyadic-block proof uses the
actual per-successor pending counters and resets, proves the stored-batch
closed form and chronological visit-rank budget, and sums over rows/stages.
It yields the printed `4SAH log₂K` for every K≥2. The full statement is
`StatisticalRL.Statements.Lemma5_12_powerOfTwo_corrected`; it covers arbitrary realized traces,
so it applies to the corrected dyadic algorithm without an assumed probability event
or policy restriction. The first-visit max-one charge is retained.
The corrected suffix discloses the trigger change; the alternate proof does
not validate the printed factor-two step. The profile-to-empirical-model
identity at lines 1531–1533 also requires dyadic updates. That identity and
full MVP regret are not certified by these two count/profile results.
See [independent review](critic-online-MVP-counts-profiles.md) and
[verification](online-MVP-counts-profiles-verification.md).

<a id="C14"></a>

## Candidate C14: centered-square variance for signed variables

**Status: confirmed false conclusion in the second clause; corrected general
bound proved, with an independently reviewed exact Lean counterexample.**

Source: `chapters/onlineRL.tex:3612–3615`, `lemma:sqv` (Lemma 5.22), and
its centered-fourth-moment argument at lines 3627–3631. The pinned chapter
SHA-256 is `393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.
The source calls Cmax the largest possible magnitude of X. It asserts
Var((X−E[X])²)≤Cmax²Var(X) for a general random variable.

Take X=1 with probability 1/8 and X=−1 with probability 7/8. Both values have
absolute value 1, while E[X]=−3/4, Var(X)=7/16, and Var((X−E[X])²)=63/64.
Thus 63/64>7/16 contradicts the second clause with Cmax=1. The proof's use
of |X−E[X]|≤Cmax fails: at X=1 the deviation is 7/4.

The exact probability-space refutation is
`StatisticalRL.SourceCounterexamples.centeredSquare_measure_coefficient_one_false`
in [CenteredSquareVarianceMeasure.lean](../Formalization/Counterexamples/CenteredSquareVarianceMeasure.lean).
Its actual sample is measurable, has absolute value 1 everywhere, and uses
the same measure-theoretic variance as the corrected general statement.
The first clause Var(X²)≤4Cmax²Var(X) is not refuted.

A valid repair replaces the centered-square coefficient 1 by 4. Since
|X−E[X]|≤2Cmax, its fourth centered moment is at most 4Cmax²Var(X), and
Var((X−E[X])²) is at most that fourth moment. The general probability-space
repair is proved in [SquaredVarianceBounds.lean](../Formalization/Probability/SquaredVarianceBounds.lean)
and indexed as `StatisticalRL.Statements.Lemma5_22_corrected`. Measurability
and the source absolute bound suffice; integrability is derived in Lean.
The printed source remains unchanged and its false general clause is not
certified.

The coefficient 1 special case is valid when 0≤X≤Cmax. The existing
`FiniteDistribution.centeredSquare_variance_le` explicitly has this range
premise. The current W3 implementation uses valid nonnegative bounded-value
estimates, including its own factor4 square-variance proof. Independent
consumption review found no effect on the already-published corrected UCBVI
regret theorem. See [independent review](critic-square-variance-correction.md)
and [verification](square-variance-correction-verification.md).

<a id="C15"></a>

## Candidate C15: MVP intermediate profile-family rounding

**Status: confirmed intermediate inclusion gap under a literal integer/floor
reading; the printed final Lemma 5.11 cardinality bound is proved.**

Source: profile definition `chapters/onlineRL.tex:1506–1525`,
`defn:profile`; Lemma 5.11 (`lemma:key2`) at lines 1540–1542; the comparison
family and inclusion argument at lines 1551–1563. The source does not impose
a power-of-two episode count in the lemma.

For K=3 with one row and one stage, two prior visits give profile index
`max{j∈Z:2^(j−1)≤2}=2`. This exceeds the real log₂3. Hence the literal
integer set `{0,...,log₂K}`, interpreted by its floor endpoint, omits an
attainable profile even though K≥SAH log₂K holds. An implicit ceiling
convention could address the notation, but is not written in that inclusion.
This does not refute the final cardinality conclusion.

The Lean proof uses the safe level cap `Nat.log2 (K-1)+1` and proves every
actual pre-episode cumulative count has an index below it. It counts the
finite row-table profiles inside a rowwise monotone ceiling family, applies
stars-and-bars, and proves the same printed bound
`(4SAHK)^(SAH log₂K+1)`. K=1 is handled by the all-zero profile. The full
statement `StatisticalRL.Statements.Lemma5_11` counts a superset of algorithm
profiles from all finite episode-by-stage state-action row tables; the
source large-K premise is retained. The unchanged final conclusion is
certified, while the literal printed intermediate inclusion is not.
See [independent review](critic-online-MVP-counts-profiles.md) and
[verification](online-MVP-counts-profiles-verification.md).
