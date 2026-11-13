# Source issues and unresolved interpretation

This is a research ledger, not an author-approved errata list. The original
article remains the source of truth. A corrected result is separately identified
and must not be presented as a proof of an incorrect original statement.

**Project decision 2026-11-10 (status of every entry).** Every candidate, counterexample, refutation, correction,
restriction and proof repair below is this project's proposal, found by AI-agent review; none is confirmed by the
authors. Each entry says whether its counterexample or refutation is machine-checked in Lean or a paper argument.
Where the book cites or omits a proof, the Lean proof is this project's own (recorded per result as `proof_origin`
in `named-result-status.json`). Where the book says "any estimator" and a Lean entry covers only estimators that
are deterministic functions of the data, the entry is a restriction, not the printed statement.

<a id="C1"></a>

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

<a id="C2"></a>

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

**Formal corrected entry (2026-11-06).** Under its standalone reading, Theorem 3.7 fails as printed by this project's counterexamples, checked in Lean and not author-confirmed (C1: part (i) at `A=1`, unless the earlier `A ≥ 2` convention of line 787 is read into the theorem; C2: both parts at `S=1` under the source's known-reward convention). `Thm3_7_corrected` proves the printed conclusion, with probability `≥1/4`, the printed γ and ε ranges, the printed sample bound and a uniform constant (witness `c_N=1/32768`), on the domain `S≥2`, `SA≥16`, with `A≥2` required only in part (i). Part (ii) quantifies over randomized Q-estimators (Borel probability laws given the known reward table, the known discount and the full `N`-per-pair sample array; deterministic estimators are the Dirac case); part (i) over deterministic estimators returning deterministic policies. Part (ii) is proved for every `A ≥ 1` (the randomized `2 ≤ A` premise is removed via `qMixture_log_card_lower_of_pos`). Both added conditions are necessary, by C1 and C2; part (ii) is proved for `A=1` as well (randomized estimators included). This is a corrected variant, not the printed theorem, and not an author-approved erratum. The older proposal below adds `A ≥ 2` to both parts; the formal entry needs it only for part (i).

**A = 1 policy-evaluation form (2026-11-10).** `Thm3_7_policyEvaluation_A1` specializes corrected part (ii) to one action and restates it on the policy-evaluation experiment of Theorem 3.1 and TD learning (estimator: any, randomized included, given the known rewards, discount and N draws per state; error ‖V̂ − V^{π₀}‖∞, equal to ‖Q̂ − Q⋆‖∞ at A = 1), with c_N = 1/32768 and the printed γ, ε, SA ≥ 16 (= S ≥ 16) domain. C1 and C2 are vacuous here; there is no deviation from printed part (ii) at A = 1. It closes the A = 1 comparisons (model-based :1468–1474, model-free :248–249) only for ε < 1/(32(1−γ)) and γ ≥ 2/3 ([review](critic-a1.md)). Since 2026-11-10 it has its own `COVERAGE.md` row.

**Sharpening (independently re-derived 2026-11-06).** The separation claim in the proof (`generative_model_model_based.tex:2073–2079`), `Q^⋆(s,π^⋆(s)) − Q^⋆(s,a) > 2ε`, is false at every admissible `(γ,ε)`. With the printed `p, α` and `x=4(1−γ)/3`, the true gap is `γα/(1−γ(p+α)) = 2xε/(γ−2xε) < (16/21)·2ε`; the displayed suboptimal value `1/(1−γp)` should be `(1−γα)/(1−γ(p+α))`. The data-free estimator equal to the midpoint `(H+L)/2` on active states and `0` at the absorber has error `< (8/21)ε` on every member of the printed family, so that family cannot witness part (ii). Part (i)'s reduction survives with corrected values. The formal proof of part (ii) uses a baseline-versus-one-row family instead.

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
applies to the stationary policy class. A separate [formalized corrected policy-risk result](../Formalization/Generative/GenerativeLowerBoundKernelQuarter.lean) now proves the source probability `≥1/4` on the explicit domain `S,A ≥ 2`, `SA ≥ 16`, with `c_N = 1/32768`, for randomized estimators selecting deterministic stationary policies. Its model is chosen after the estimator; the [independent review](critic-generative-lower-bound-kernel-quarter.md) records the scope and source comparison. A separate [formalized corrected Q-estimation result](../Formalization/Generative/GenerativeLowerBoundQMixtureFinalRandomized.lean) proves the same `≥1/4` probability for arbitrary randomized real-Q estimators on `S,A ≥ 2`, `SA ≥ 16`, with `c_N = 1/512`; see the [independent review](critic-generative-lower-bound-q-final-randomized.md). That `S,A ≥ 2`, `1/512` Q result is superseded by `theorem37_Q_fin_randomized` (`S ≥ 2`, `SA ≥ 16`, `c_N = 1/32768`; [review](critic-rand37.md)). Neither result proves the wider printed domain or the earlier proposed `1/8192` constant for both parts. A [combined restricted wrapper](../Formalization/Generative/GenerativeLowerBoundCombinedRisk.lean) uses one common constant `1/32768` for both clauses, preserving their separate hard-model witnesses. It has passed integrated and clean-copy compilation, the project axiom audit, and [independent source review](critic-generative-lower-bound-combined-correction.md).

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

<a id="C3"></a>

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

<a id="C4"></a>

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
`S,A≥2`, `SA≥16`. The standalone two-state, one-action example itself
(`eq:P-Mi-Q-inaccurate-lower-generative`, lines 1541–1556) is now proved with
the strict `> 0.1` for every estimator, randomized included, given the full sample
array: `StatisticalRL.Statements.Ch3.Eq_P_Mi_Q_inaccurate_lower_generative`. Because the printed
"any estimator" includes randomized estimators, the entry covers them
(`sourceHardMDP_randomized_Q_estimation_lower`; [review](critic-rand37.md)); the source's wider original domain for the
general theorem remains separate; the source's strictness omission is not
itself a counterexample.

<a id="C5"></a>

## Candidate C5: missing premise in TD step-size Lemma 4.3

**Classification (marker audit, 2026-11-11).** The failure is of the standalone statement only; under the sample-size condition of Theorem 4.1, which the appendix proof invokes, this instance is excluded, and Theorem 4.1 is not claimed to fail (ledger kind `domain`).

The printed standalone `lemma:TD-step-size` (`generative_model_model_free.tex:317–327`) omits a gamma-dependent sample-size premise used in its appendix proof, and does not explicitly bound `t` by the horizon on which the schedule is constrained. The [independent source review](critic-td-step-size-premise.md) gives a concrete admissible counterexample to the early-weight bound: take `c₁=c₂=1/4`, `T=t=100`, `γ=1−10⁻⁶`, and each learning rate equal to the printed lower endpoint. Then the initial weight is at least `0.9999`, whereas the lemma asserts it is at most `0.0001`.

The proof uses `T ≥ log²(T)/(c₁(1−γ))`; the [formal helper](../Formalization/ModelFree/TDStepSizeLate.lean) retains that condition and `t≤T`, while a [separate proof](../Formalization/ModelFree/TDStepSizeBudget.lean) derives the large-T condition from the enclosing main theorem’s sample budget for a sufficient constant relation. This is a statement gap for the standalone auxiliary lemma, not by itself a counterexample to the main TD theorem. No author-approved correction is asserted.

The [standalone counterexample](../Formalization/ModelFree/TDStandaloneStepSizeCounterexample.lean)
formalizes the numerical schedule and strict failure of the initial-weight
bound using the project's actual step-size and weight definitions. The same
proof passed a focused check under a draft header; the current source passed
working-tree and clean-copy compilation and axiom checks. It does
not assert that the main theorem's sample budget holds for this witness.

Minimality: the counterexample shows only that some sample-size premise of this kind is needed;
the retained premise `log²T ≤ c₁(1−γ)T` (with `T ≥ 2` and `t ≤ T`) is the one the appendix proof uses
and is not claimed to be minimal.

<a id="C6"></a>

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

<a id="C7"></a>

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

Originally proposed correction (superseded): make `S ≥ 2`, `A ≥ 2` and `ε > 0` explicit.

Corrected result (2026-11-07). The cited bound is proved in Lean with explicit constants (`c₃ = 1/512`, `c₄ = 1/5308416`, hence every smaller pair) and the printed shape of the ε and N conditions, by a self-contained two-point construction (the cited paper was not used; `Formalization/RobustRL/LowerBounds/LowerBound75.lean`; index entries in `Statements/Ch7.lean`):
- `Thm7_5_corrected`: the printed statement with only `2 ≤ A` added. Estimators map samples to policies and do not see the reward; the S = 1 case holds only for that reason. `ε > 0` is not needed: for ε < 0 the claim is trivial, and at ε = 0 the Lean value `c₄/0 = 0` forces N = 0 (the instance also holds for every N if `c₄/0` is read as ∞).
- `Thm7_5_corrected_knownReward`: the faithful form under the book's known-reward convention: `2 ≤ S`, `2 ≤ A`, shared reward. Both hypotheses are shown necessary in Lean (`knownReward_needs_two_states`, `knownReward_needs_two_actions`), and the printed statement is refuted for every pair of positive constants (`printed_at_fails`).
Estimator class: the entries `Thm7_5_corrected` and `Thm7_5_corrected_knownReward` take estimators that are deterministic maps from the sample array to policies. Externally randomized estimators (an independent seed `ω ~ ν` in any measurable space, estimator `π̂(ω, data)`, failure probability under `ν ⊗ P_i`, outer probability for non-measurable failure sets, printed constant 1/8) are covered by `Thm7_5_corrected_randomized` and `Thm7_5_corrected_knownReward_randomized` ([independent review](critic-rand73.md), five-bin PASS-DISCLOSED); the deterministic entries are the `Ω = Unit` case, so no estimator class remains uncovered. The remaining deviations are the ones listed above: `A ≥ 2` and, for the known-reward reading, `S ≥ 2` with shared reward. Independently reviewed in two rounds. Not author-approved. The earlier evidence below concerns the singleton-action case.

Earlier evidence: a
[stationary-policy robust-value foundation](../Formalization/RobustRL/ChiSquaredPolicyValue.lean)
constructs actual trajectory-value infima and proves the singleton-action
zero-gap mechanism in that policy class; see its [review](critic-robust-chi-policy-value-independent-review.md).
The [singleton-action counterexample](../Formalization/RobustRL/SingletonActionCounterexample.lean)
also establishes feasible parameters and zero risk for one fixed estimator
against every model pair, under their actual row-product sampling laws. It has
passed focused, working-tree and clean-copy compilation and axiom checks.
It does not encode the complete estimator infimum in the manuscript. See the
[source and evidence review](critic-robust-chi-singleton-action-v5.md).

<a id="C8"></a>

## Candidate C8: undefined zero-visit bonus in UCBVI and MVP

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
`StatisticalRL.Statements.Ch5.Lemma5_6_corrected`: it assigns H as the finite
analysis charge at zero visits and agrees with the printed bonus at
positive counts. Its generic statement permits every greedy maximizing
tie choice. The supporting actual-law probability decomposition retains
the existing fixed deterministic tie implementation. This does not define
the original zero-count expression or prove the full regret theorem. See
[verification](online-regret-telescope-verification.md) and
[independent review](critic-online-regret-telescope.md).

Remark 5.5 (`onlineRL.tex:790–802`) is indexed as `Remark5_5_corrected` for the
same C8-completed UCBVI tables; the greedy identity itself does not depend on
the bonus. The burn-in and asymptotic-regret displays `eq:burn-in-ucbvi` and
`eq:regret-asymptotic-ucbvi` (lines 491–506) are indexed as
`Eq_regret_asymptotic_ucbvi_corrected`, inheriting the premises of
`Thm5_2_corrected`. See the [review](critic-trivial-c.md). Remark 5.13
(`onlineRL.tex:3510–3524`) is indexed as `Remark5_13_corrected` because its
`T₆` quantities are those of the same C8-completed tables; its inequalities
are otherwise as printed.

MVP uses the same Bernstein bonus at `onlineRL.tex:1303–1307`,
after initializing every row count to zero in Algorithm `alg:main-mvp`
(`:1256–1310`). Its unvisited rows have the same undefined division.
The corrected MVP planner therefore uses the same explicit Q=H branch at
zero stored count and retains the initialized uniform row. Positive counts
use the printed capped bonus; counts one and two saturate under the proved
constant/logarithm conditions. The actual-law corrected displayed optimism
claim is now proved as `StatisticalRL.Statements.Ch5.MVP_optimism_corrected`.
It also discloses the C13 power-of-two trigger interpretation, C16 reciprocal
confidence allocation and fixed deterministic greedy tie. No fictitious
observation or independence-at-random-count premise is introduced. This is
not an author-approved correction or a proof of the literal zero division;
corrected fixed-profile decoupling and main MVP regret are now proved separately. See the
[MVP review](critic-online-MVP-actual-optimism.md) and
[verification](online-MVP-actual-optimism-verification.md).

The actual-law corrected MVP variance lemma is also proved as
`StatisticalRL.Statements.Ch5.Lemma5_15_corrected`. Its T2 uses the printed
bonus at positive stored counts and an explicit analysis charge H at zero.
The printed bonus divides by the zero stored count; no equivalence to an
unwritten max-one denominator convention is asserted. The final export
contains no assumed T8 tail, decomposition or variance certificate. C13,
C16 and fixed deterministic ties remain disclosed; corrected Lemma 5.14 and
main MVP regret are now proved separately. See [review](critic-online-MVP-t6.md) and
[verification](online-MVP-t6-verification.md).

The corrected actual MVP T2 and T5 displayed bounds also use the positive-count
source bonus and zero-count analysis charge H (C8), power-of-two trigger (C13),
reciprocal allocation (C16), fixed 4/16 coefficients and one fixed tie. T2 is
proved for K≥2, as in the reciprocal-budget scope (C12); T5 covers K≥1 and
uses the printed natural-log failure coefficient. Neither claim is an uncorrected
source certification or a numbered ledger addition. See
[review](critic-online-MVP-t2-t5.md) and [verification](online-MVP-t2-t5-verification.md).

<a id="C9"></a>

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

**Formal handling (2026-11-06):** `Thm6_13` keeps the printed hypotheses (no added `ε > 0`). For `ε < 0` the
event is certain; at `ε = 0` Lean's `x/0 = 0` makes the threshold `N ≤ 0`, and the entry holds via the hard
family built at the positive accuracy `1/(672(1−γ))`. The reading of the `ε = 0` threshold as "every `N`" is
not covered.

<a id="C10"></a>
## Candidate C10: discount endpoint in the offline VI-LCB lemma

**Classification (marker audit, 2026-11-11).** The failure is for γ<1/2, outside the range that the proof (and the parent Theorem 6.3) assumes; it is not a refutation within that range (ledger kind `domain`).

**Source:** Lemma 6.2, `lem:monotone-contraction`,
`chapters/offlineRL.tex:872–890`; its proof uses `γ ≥ 1/2` at
`offlineRL.tex:3341–3343`. The preliminary MDP definition permits
`γ ∈ [0,1)`, and no narrower chapter-wide assumption precedes the lemma.

A fully specified source counterexample uses `γ = 0.1`, `c_b = 1`, `δ = 0.5`,
three states `A,H,L`, and one action. The rewards are `r(A)=r(H)=1`, `r(L)=0`;
the true rows are `A→(H,L)` with probabilities `(1/2,1/2)`, `H→H`, and
`L→L`. With `N=200800`, take 400 observed `A→H` transitions, 400 `A→L`, and
200000 `H→H`, with no `L` observations. This dataset has positive probability
under the source iid sampling model with behavior probabilities
`d(A)=800/N`, `d(H)=200000/N`, and `d(L)=0`. The source uniform unseen-row rule
is used at L. The source equations give an explicit fixed point `Q̄` with
`Q̄(A)≈0.9846901842`; the literal update gives `Q̂₂(A)≈0.9862186757`.
If the printed theorem's uniqueness clause held, its fixed-point witness would
have to equal `Q̄`, contradicting the theorem's iterate-order clause at `τ=2`
by about `0.0015284915`. This refutes the printed conjunction for this instance;
it is a counterexample at `c_b=1` and does not establish failure for every
`c_b`. The printed sup-norm rate is not refuted by this instance.

The corrected formalized Lemma 6.2 adds `γ ≥ 1/2`, the condition used by the
appendix proof. This is a restricted corrected result, not a proof of the
unrestricted lemma. It does **not** refute parent Theorem 6.3, whose assumptions
already require `γ ≥ 1/2`, and it establishes no failure of Theorem 6.3's rate
or sample threshold.

The prose iteration count after the lemma (`offlineRL.tex:892`) is recorded as
`Lemma6_2_iterationCount_restricted` on `γ ≥ 1/2`. C10's instance does not refute
it: on that instance the fixed point is unique and the count holds numerically
([review](critic-trivial-a.md)). For `γ < 1/2` the count is open, neither proved
nor refuted.

<a id="C12"></a>

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

**Second endpoint machine-checked (2026-11-10):** `OnlineRL.not_Lemma5_8_printed`
(`Formalization/Online/Regret/Lemma58Refutation.lean`). Boundary case K = H = 1, not a junk value. The K = 1
failure of Lemma 5.7 / W1 above is still a paper argument.

A proposed correction restricts this auxiliary logarithmic bound to `K ≥ 2`,
or replaces the vanishing logarithm by a positive floor and treats the endpoint
explicitly. Any K≥2 formalization is a disclosed restricted result, not the
literal all-K auxiliary claim. No author-approved erratum is asserted. See the
[independent source check](critic-online-k1-iota-obstruction.md).

## Statement-index scope disclosures

These are limitations of the currently proved formalizations, not asserted
errors in the manuscript. Where an item links to a source-issue candidate, that
candidate records the asserted error.

- Definition-level conventions recorded after the 2026-11-10 definition audit:
  - LCB-Q sequences (Chapter 6; `psiSeq` and the α, θ, ξ, ψ, φ sequences used by Lemma 6.11 and
    Lemma 6.12): the ratio `d_j/d^b` is set to 0 when `d^b = 0`. That event has probability zero
    under the source's assumptions, so no statement that uses these sequences depends on the value.
  - Online VPO (Theorem 7.12; `Thm7_12_corrected`): the first policy $\pi^{(1)}$ is computed from the
    empty dataset, and $\pi^{(0)}$ never enters the regret sum. This is the indexing of the corrected
    statement; see [C44](#C44).
  - Greedy selectors (the Chapter 5 planners and `optimalGreedyPolicy` used in Chapter 6): the
    maximizer is chosen by `Classical.choose`, so each fixes one unspecified tie rule. Every
    statement entry that depends on the tie rule discloses it; entries that use only the value do
    not depend on it.

- Lemma 6.11 (`lemma:useful`, `offlineRL.tex:2292–2300`) is indexed as
  `Lemma6_11_restricted`, with the source's `≲` made explicit (constant 84) and the added
  premise `log(SAT/δ) ≥ 1`, which is sufficient for `κ = γ(1+1/H)³ < 1`. `π⋆` ranges over every
  `Q⋆`-greedy deterministic policy (every optimal deterministic policy; no tie rule is fixed;
  generalized on 2026-11-09 from the library tie choice `optimalGreedyPolicy`). The premise is not
  implied by Theorem 6.8's sample-size condition, so the entry does not formally cover that
  theorem's uses with `δ > SAT/e`; see [C22](#C22) for the source error and why Theorem 6.8 is
  unaffected.

- Lemma 6.6 (`lem:Bernstein-infinite`, `offlineRL.tex:1147–1163`) is indexed as `Lemma6_6` with the
  premise `0 < N_{s,a}` on each pair. The printed bounds divide by `N_{s,a}`; the source proof
  (`:3632`) declares the `N_{s,a} = 0` case trivial, which holds only when the right-hand sides are
  read as `+∞`. Under Lean's `x/0 = 0` the printed inequalities are false for unseen pairs (for
  example, a never-sampled pair whose uniform row `1/S` sees two states with different `V̂⋆_pe`
  values), so the entry states exactly the positive-count content. This is the domain of definition of
  the printed bounds (undefined, or trivial under the source's own convention, at `N_{s,a} = 0`), not a
  restriction: the guard is per pair inside the event, and the entry is unsuffixed. The penalty and event share
  the parameter `δ`; `V̂⋆_pe` is any fixed point of `T_pess`, which exists and is unique for
  `γ ≥ 1/2` (corrected Lemma 6.2, [C10](#C10)). The printed proof's covering-set bound assumes `N ≥ 5`
  ([C23](#C23)); the formal proof instead treats pairs with `N_{s,a} ≤ 26` deterministically and
  applies the grid argument only when `N_{s,a} ≥ 27`.

- Lemma 6.18 (`lem:Bernstein-infinite-proof`, `offlineRL.tex:3635–3662`) is indexed as `Lemma6_18`
  in its conditional-on-counts form: for a fixed `n = N_{s,a} > 0`, `P̂_{s,a}` is the empirical row of
  `n` iid draws from `P_{s,a}` on an arbitrary probability space, and `V` is independent of that row
  (`:1126–1128`, `:3970–3972`).

- Lemma 6.12 (`lem:lcbq-alpha-xi-psi-phi-bound`, `offlineRL.tex:2309–2324`) is indexed as `Lemma6_12_restricted`. It has the added premise `log(SAT/δ) ≥ 1`, which is sufficient for `κ < 1` and `H ≍ ι/(1−γ)`; the printed lemma fails for small `ι` (see [C24](#C24)). The premise is not minimal: any `ι ≥ c > 3/4` would do with a larger constant, and the excluded band requires `SAT ≤ 2`. The source's `c_b` "sufficiently large" is stated as `∃ c_b₀, ∀ c_b ≥ c_b₀` (`c_b₀ = 4`, as in [C28](#C28)). The `≲` constant is an existential `C` that depends only on `c_b` (`C = 400000 + 5600 c_b`). `α = 0` is stated as `α_j → 0`; `ξ, θ, ψ, φ` are stated as `HasSum` limits. The `θ` and `ψ+φ` bounds are stated under `C⋆ < ∞`, since otherwise the printed right sides are `+∞`. No sample-size condition on `T` is assumed, although the printed proof uses Theorem 6.8's. The hypotheses that `π⋆` is optimal and that ties are broken by a maximiser are carried as in the source but are not used.
- Lemma 6.9 (`lemma:Q-recursion-pessimistic-Q`, `offlineRL.tex:1866–1893`) is indexed as `Lemma6_9_restricted` (renamed from `Lemma6_9` on 2026-11-07 for consistency with the tie-rule convention used for Theorem 5.1). The printed algorithm (`alg:q-infinite-lcb`, `:1701–1745`) leaves the arg-max tie rule unspecified; the entry covers every deterministic tie rule that depends only on the current Q-row (for example any rule on the arg-max set), not rules depending on the state, the iteration or the history. The same tie scope applies to `Lemma6_10_restricted`, `Lemma6_12_restricted` and `Thm6_8_corrected`.
- Theorem 5.1 (`thm:bandit-pure-ucb`, `bandits.tex:258–277`) is indexed as `Thm5_1_restricted`. Both printed bounds and all printed hypotheses (2 ≤ A ≤ T, means in [0,1], 0 < δ < 1) are kept unchanged. The restriction is the tie rule: the algorithm (`:232`) leaves the choice inside the argmax unspecified, and the entry quantifies over every deterministic rule that depends only on the round and the argmax set. History-dependent and randomized tie-breaking are not covered; the mathematical repair ([C36](#C36)) extends to any non-anticipating rule, but that is not formalized. Reading conventions: an unpulled arm has index +∞ (`:387`); rounds are 0-indexed; the noise is the iid N(0,1) table over (round, arm); regret is the pseudo-regret T r⋆ − Σ $r(a_{t})$ with $r^{\star} = \max_{a}$ r(a), integrated over the noise; integrability is proved as an extra conclusion.
- Remark 5.12 (unlabeled, `onlineRL.tex:2725–2729`; numbered by the per-chapter remark counter) is an informal claim and is indexed as its formal reading. `Remark5_12_lowerBound` (unrestricted): an Ω(√(AT)) minimax lower bound, constant 1/16 and range 2 ≤ A ≤ T chosen by us, learners = seed from any probability space (`Seed : Type`) plus arm maps measurable in (seed, past (arm, reward) pairs). `Remark5_12_restricted`: the UCB optimality comparison (factor 128√log(T²/δ)) inherits the deterministic tie-rule restriction of `Thm5_1_restricted` above. No source error.
- The regret-to-PAC conversion (`onlineRL.tex:113–141`, [C46](#C46)) is indexed as `Eq_PAC_from_regret_conversion_corrected` and `Eq_PAC_from_regret_conversion_restricted`. Algorithm class: internal randomness with finite support and deployed policies that are deterministic Markov given the seed and the completed history; the source allows randomized deployed policies, which are not covered. Only `δ > 0` is assumed, as printed.
- Remark 7.1 (`remark:tv-upper`, `robust_RL.tex:361–372`) is indexed as `Remark7_1_restricted`: Õ((1−γ)²/N) is read
  as $c_{\mathsf{opt}}(1-\gamma)^{2}\log (SAN/((1-\gamma)\delta))/N$ with ∀ $c_{\mathsf{opt}}$ ∃ C₂; only deterministic stationary planner outputs are covered
  (randomized or history-dependent outputs are not), and N > 0 is assumed as in `Thm7_2_corrected`. The event is
  uniform over all such outputs, so no measurability of the planner is needed.
  Remark 7.2 (`remark:chi2-upper`, `robust_RL.tex:453–457`) is indexed as `Remark7_2_restricted` with the same
  restriction: O(log(SAN/((1−γ)δ))/N²) is read as $c_{\mathsf{opt}}\cdot \log (SAN/((1-\gamma)\delta))/N^{2}$ with ∀ $c_{\mathsf{opt}}$ ∃ c₂ (proved with
  $c_{2} = 10^{6} + 8c_{\mathsf{opt}}$); only deterministic stationary planner outputs are covered, and the premises are those of
  `Thm7_4_corrected` (N > 0). The event is uniform over all such outputs ([review](critic-trivial-b.md)).

- `eq:mdp-value-Q` (`robust_RL.tex:88–98`), `eq:bellman-equ-infinite-all` (`:102–113`) and the
  robust Bellman operator and DRVI claims (`:114–133`, `:261–262`) are indexed as
  `Eq_mdp_value_Q_restricted`, `Eq_bellman_equ_infinite_all_restricted` and
  `Eq_robust_bellman_fixedPoint_restricted` (renamed 2026-11-09 from the unsuffixed names). The
  source builds the `(s,a)`-rectangular set from an unspecified "distance-like metric" ρ
  (`:36–46`) and names the TV and χ² balls as its instances (`:52`). The entries cover the TV ball,
  the χ² ball and every row-set family in which each linear functional `q ↦ ⟨q, V⟩` attains its
  infimum on every nominal row's set. Reading "distance-like" as implying that attainment is an
  interpretation; families without attained infima are not claimed. Policies are the book's
  stationary randomized policies with a static adversary; history-dependent policies and dynamic
  adversaries are not claimed. Not an asserted source error.

- Remark 4.5 (`generative_model_model_free.tex:3455–3457`) is indexed as `Remark4_5`. Its clause
  (iii), `E ξ_{t,max} > 0`, is stated for `t ≥ τ̂`, the range of Lemma 4.15 which the remark
  follows; at `t = 0` one has `ξ₀ = 0`, so the clause is false there. Theorem 4.6's "for some
  small enough universal constants `c₁ ≥ c₂ > 0`" is read existentially, as printed; the export
  witnesses `c₁ = c₂ = 1`, and schedules with `c₂ < 1` are not covered (see the `Thm4_6`
  docstring).

- `eq:DPO` (`RLHF.tex:62–74`), `eq:policy_RBMLE` (`:115–141`) and `eq:online_RBMLE` (`:158–198`) are indexed as
  `Eq_DPO_restricted`, `Eq_policy_RBMLE_restricted` and `Eq_online_RBMLE_restricted`. The main restriction is the
  argmin domain: minimization is over full-support policies (`IsPositivePolicy`), not over all policies. In the
  source's extended-real reading a policy with π(y₋|x) = 0 has −log σ(+∞) = 0, so over all policies the minimum 0
  can be attained only at boundary policies, which are not Gibbs policies, while over full-support policies the
  infimum 0 is unattained and no reward MLE exists (e.g. a dataset whose only comparison is (x, y₁, y₂)); under
  Lean's log 0 = 0 such a boundary policy takes the junk loss −log σ(β log(π(y₁|x)/π_ref(y₁|x))) instead of 0. The
  same example shows that the printed reward–policy correspondence holds only on full-support policies: over all
  policies the DPO argmin can be a nonempty set of boundary policies while ℓ(·, D) has no minimizer. The book's
  derivation works with the Gibbs policies $\pi_{r}$, which have full support. Further: $\pi_{\mathsf{ref}}$ has full support (implicit
  in the source, where log $\pi_{\mathsf{ref}}$ appears in `eq:reward-policy-eq`), and X and Y are finite (as in
  `Thm7_12_corrected`; the source's Z(r,x) is a finite sum over Y). Existence of minimizers is not claimed (cf.
  [C44](#C44)). The online entry states the policy step with the printed uncalibrated J(r,π) of `eq:KL_reward`;
  uniqueness of its maximizer is not claimed (it fails off the support of ρ). See the [review](critic-trivial-b.md).
  `eq:reward-policy-eq` (`RLHF.tex:62–66`) and `eq:Jstar` (`:115–124`) are indexed as
  `Eq_reward_policy_eq_restricted` and `Eq_Jstar_restricted`, and the prompt-shift claims of `:90–98` as
  `Eq_calibrated_value_shiftInvariant_restricted`, with the same full-support $\pi_{\mathsf{ref}}$ and finite X, Y. For the
  prompt-shift claims the printed statements hold for every $\pi_{\mathsf{ref}}$ under the extended-real KL; the restriction
  comes from the formal KL, which equals the KL divergence only when $\pi_{\mathsf{ref}}$ has full support.
  `eq:RLHF-policy-closed-form` (`:41–59`) is indexed as `Eq_RLHF_policy_closed_form_restricted`: the Gibbs
  policy $\pi_{r}$ maximizes J(r,·) over all conditional policies, and a conditional policy is a maximizer iff it
  agrees with $\pi_{r}$ on supp ρ. The printed `π_r := arg max_π J(r,π)` treats the maximizer as unique; that holds
  exactly when ρ has full support (off supp ρ every row gives the same value; machine-checked witness with
  $\rho = \delta_{\mathsf{true}}$ in the P3a non-vacuity probe). This is a scope note, not an asserted source error. Same
  full-support $\pi_{\mathsf{ref}}$ and finite X, Y ([review](critic-p3a.md)).

- The iteration count after Lemma 6.2 (`offlineRL.tex:892`) is indexed as `Lemma6_2_iterationCount_restricted`,
  stated on γ ≥ 1/2, the domain of `Lemma6_2_corrected`. For γ < 1/2 the iteration count is open: neither proved
  nor refuted. [C10](#C10) refutes only the uniqueness-plus-order conjunction of Lemma 6.2, not the sup-norm rate,
  and its instance does not refute this count ([review](critic-trivial-a.md)).

- Remark 6.3 (`offlineRL.tex:175–185`) is indexed as `Remark6_3`. Clauses (i) and (iii) hold for every stationary
  policy. Clause (ii) ("can be as low as 1/S") is shown with a degenerate witness: zero rewards and discount 0, so
  every policy is optimal there, and the value 1/S is for the library's tie choice `optimalGreedyPolicy`; another
  optimal deterministic policy can give ∞ against the same behaviour distribution. The printed sentence is
  existential and the source's π⋆ is itself tie-ambiguous. The citation sentence at `:184` is not covered
  ([review](critic-trivial-a.md)).

- Lemma 6.14 (`lemma:value-policy-LB-inf`, `offlineRL.tex:2544–2583`) is indexed as
  `Lemma6_14_restricted`. All values, the policy upper bound with equality at `π⋆` and
  `π⋆(0|0) = 1` are proved for every `ε ≥ 0`; the claim `π⋆(θ_s|s) = 1` is proved for `ε > 0`
  only. Theorem 6.13 allows `ε ≤ 1/(672(1−γ))` without excluding `ε = 0`, where `p = q`, both
  actions at `s > 0` are optimal, and the formal optimal greedy policy (a fixed tie rule) need
  not select `θ_s`.

- Lemma 6.7 (`lem:sum-d-Var-UB`, `offlineRL.tex:1529–1537`) is indexed as
  `Lemma6_7_restricted`. The source states it for the VI-LCB output `V̂` and penalty
  `b⋆` inside the proof of Theorem 6.3, where `0 ≤ V̂ ≤ 1/(1−γ)` and the residual bound
  `eq:infinite-v-lower` hold on the theorem's high-probability event. The entry proves the
  bound for every `V` and `b ≥ 0` satisfying those displayed premises (with `γ > 0`), using
  the transition rows and actual discounted occupancy of an arbitrary stationary policy (so every
  optimal deterministic policy `π⋆` and every tie rule among optimal actions is covered; generalized
  on 2026-11-07 from the single optimal-greedy tie rule after an independent review); deriving the
  premises for `V̂` on the event is not part of this result.

- Theorem 3.2 (`Thm:sample-compl-main`,
  `generative_model_model_based.tex:900–923`) and Lemma 3.5
  (`lem:policy-learning-evaluation`, lines 1306–1326) are indexed in printed form as
  `Thm3_2` and `Lemma3_5`, with the `0 < N` witness quantified inside the event (domain of
  definition, as for `Thm3_9`): at N = 0 the printed thresholds contain log(SAN) = log 0, Lemma 3.5's
  bounds divide by N and the empirical kernel is 0/0, so N = 0 is outside the printed domain and the
  event is the whole sample space there. This is no longer a scope disclosure (2026-11-10,
  [review](critic-thm32.md)). The earlier entries `Thm3_2_positiveN` and `Lemma3_5_positiveN`, with
  an explicit `N > 0` hypothesis as in the library exports, are retained as supporting entries.
  The approximate-planner extension of Theorem 3.2 stated in prose at
  `generative_model_model_based.tex:943` (`Thm3_2_approxPlanner_positiveN`) keeps the same
  `N > 0` restriction; the companion iteration-count claim (`Thm3_2_planningIterations`)
  divides by `N`, so `N > 0` is implicit in the printed claim. Its VI clause also reads the
  unspecified initialization (`prelim.tex:316`) as any `Q₀` with entries in `[0, 1/(1−γ)]`
  (covering `Q₀ = 0`); for unbounded `Q₀` no uniform constant exists, so a bounded start is
  implicit in the printed `O(·)` claim. PI starts from an arbitrary stationary policy.
- Theorem 4.7 iteration-complexity prose (`Thm4_7_iterationLowerBound`, `generative_model_model_free.tex:992–1000`):
  the source's Ω̃ is made explicit as T log²T ≥ c_lb/((1−γ)⁴ε²) in Theorem 4.7's regime (regime constant
  max(c₃,1)); the hard instance is chosen before ε and inherits the dummy-action encoding of `Thm4_7`
  ([C31](#C31) item 5). The sentence that the bound is not a high-probability bound is a scope remark and is not
  formalized.

- Theorem 6.13 (`thm:infinite-lwoer-bound`, `offlineRL.tex:2367–2402`): the unsuffixed `Thm6_13` covers
  deterministic estimators only. The printed "all estimators" claim is proved by `Thm6_13_randomized`
  (independent external seed; outer probability when the failure set is not measurable), which is the counted
  entry; `Thm6_13` is its Dirac-seed special case and is a supporting entry.

- `eq:lemma-VarP-V-bound` with `eq:I-gamma-P-Var-bound`
  (`generative_model_model_based.tex:327–352`) is indexed as `Eq_lemma_VarP_V_bound` on the
  domain `0 < γ`: the printed bounds divide by `γ` and `γ²`, so they are undefined at `γ = 0`
  (under Lean's `x/0 = 0` they would be false there). This is the domain of definition of the
  printed display, not a source error.
- Theorem 3.9 (`Thm:sample-compl-finite`,
  `generative_model_model_based.tex:2551–2570`) is indexed as `Thm3_9` in its printed form, for every
  deterministic policy that is optimal for the empirical MDP at every stage and state (no tie rule is fixed).
  The empirical-frequency model is typed by a witness `0 < N` quantified inside the event. At N = 0 that
  event is the whole sample space. S, A ≥ 1 and H ≥ 1 are forced (nonempty stage types, 0 < ε ≤ H), so at
  N = 0 the printed threshold implies δ ≥ HSA ≥ 1 and the claim is trivial there; the entry is never vacuous
  ([review](critic-trivial-c.md), R1). `Thm3_9_positiveN` (explicit `N > 0`) and the earlier entry
  `Thm3_9_causal_positiveN`, for the concrete backward-greedy tie rule, are retained.
- `Thm3_9_minimaxLowerBound_restricted` (formal reading of the prose minimax-optimality
  claim at `generative_model_model_based.tex:2585`, context 2573–2585; renamed from
  `Thm3_9_minimaxLowerBound` on 2026-11-09 because the items below narrow the claim): domain
  S, A, H ≥ 2 and 0 < ε ≤ c₁H with existential c₁ (witness 1/4096). Each
  exclusion is a domain exclusion, not a source error: for H = 1, A = 1, S = 1
  or ε ≥ H, zero samples already give an ε-optimal policy. The "(0,H]" range of
  line 2578 belongs to the upper bound. The protocol is the book's uniform
  per-(s,a,h) non-adaptive one, so the S·A factor is inherited from the
  protocol, not tested; only copy 0 and actions {0,1} are used. R1: output
  actions must be measurable in the seed for every reward table. R2: the output
  is a deterministic nonstationary policy for each seed (seed-randomized
  estimators); stochastic-policy outputs are not covered. R3 (removed
  2026-11-09): the seed space may live in any universe. R4: the threshold is H³/ε² per tuple without the
  log(HSA/δ) factor, with fixed failure probability 1/8; no δ-dependent lower
  bound is claimed. The cited domingues2021episodic total-budget/adaptive
  theorem is not established. No source error. See [source review](critic-fhlb.md).

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

- Lemma 6.4 (`lem:offline-prelim`, `offlineRL.tex:1078–1094`) is indexed as
  `Lemma6_4`, a restricted variant: it assumes the standing assumptions of its
  parent Theorem 6.3 (γ ≥ 1/2 and τmax ≥ (1/(1−γ))log(N/(1−γ))), which the
  printed lemma leaves implicit. The fixed point and the value and bonus error
  estimates are proved; the lemma does not prove the parent policy guarantee.
  Recorded in the named-result ledger since its entry; listed here on
  2026-11-10 so that the reader can link the restriction. Not an asserted
  source error.

<a id="C13"></a>

## Candidate C13: MVP trigger notation and stored-count comparison

**Classification (marker audit, 2026-11-11).** The refutations of Theorem 5.10 and Lemma 5.12 hold only under the literal consecutive-integer reading of the trigger set; under the powers-of-two reading that the prose describes no counterexample is claimed, and Lemma 5.12 is proved (`Lemma5_12_powerOfTwo_corrected`) (ledger kind `reading`).

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
Machine-checked: `StatisticalRL.OnlineRL.not_Lemma5_12_literalTrigger_printed`
refutes `Lemma5_12_literalTrigger_printed`, the printed sum bound for count
tables that are verbatim copies of the Lean MVP tables with the trigger
`1 ≤ n ≤ 2^{Nat.log 2 K}`, at S=A=H=1, K=32 (sum 32 > 20). With one state and
one action the trace is forced, so this is every run of the literal algorithm;
for K=32 the floor, real and `{1,…,K}` readings agree
([OnlineMVPLiteralTriggerCounterexample.lean](../Formalization/Online/Regret/MVP/OnlineMVPLiteralTriggerCounterexample.lean),
[review](critic-small-batch-2a.md)). The source prose and displayed trigger conflict;
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
`StatisticalRL.Statements.Ch5.Lemma5_12_powerOfTwo_corrected`; it covers arbitrary realized traces,
so it applies to the corrected dyadic algorithm without an assumed probability event
or policy restriction. The first-visit max-one charge is retained.
The corrected suffix discloses the trigger change; the alternate proof does
not validate the printed factor-two step. The profile-to-empirical-model
identity at lines 1531–1533 also requires dyadic updates. That identity and
full MVP regret are not certified by these two count/profile results.
See [independent review](critic-online-MVP-counts-profiles.md) and
[verification](online-MVP-counts-profiles-verification.md).

Under the same literal reading the main Theorem 5.10 also fails; see [C48](#C48)
(machine-checked: `OnlineRL.not_Thm5_10_literalTrigger_printed`).

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
and indexed as `StatisticalRL.Statements.Ch5.Lemma5_22_corrected`. Measurability
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
statement `StatisticalRL.Statements.Ch5.Lemma5_11` counts a superset of algorithm
profiles from all finite episode-by-stage state-action row tables; the
source large-K premise is retained. The unchanged final conclusion is
certified, while the literal printed intermediate inclusion is not.
See [independent review](critic-online-MVP-counts-profiles.md) and
[verification](online-MVP-counts-profiles-verification.md).

<a id="C16"></a>

## Candidate C16: MVP uniform concentration at small confidence logarithms

**Classification (marker audit, 2026-11-11).** The refutation holds only in a corner regime (δ′ near 1, tiny SAHK) and under the bounded continuation-family reading; it is not a failure for non-degenerate parameters (ledger kind `reading`).

**Status: generic Lemma 5.13 refuted under the natural bounded
continuation-family interpretation; the source has an endpoint-index ambiguity.**

Source: `chapters/onlineRL.tex:1388–1391` (confidence allocation),
`:1670–1685` (Assumption `assumption-X-mvp`), `:1696–1712`
(`lemma:uniform`, Lemma 5.13), and its proof at `:4180–4280`.
Pinned chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The assumption indexes the displayed families only through H, while its
future-dependence clause and the conclusion use the continuation family
at h+1, including H+1. No generic terminal-zero restriction is stated.
The counterexample uses the natural completion in which that continuation
family also has the stated cardinality and [0,H] bounds. The fixed-profile
application's particular terminal family does not restrict the generic
quantifier. This convention is explicit in the Lean witness and its review.

Take S=2, A=H=1, K=4, and both true state rows uniform on the two states.
For every fixed profile, use the deterministic family {0,e0,e1}, where eb
is the indicator of state b. The family contains zero, has three members
(at most K+1=5), lies in [0,1], and depends on no future-stage data.
The printed condition K≥SAH log₂K holds with equality.

Set ε=(320000 log 6)⁻¹, δ′=exp(−ε), and δ=(16/25)δ′. Then 0<δ<1,
0<δ′<1, and the printed allocation 100δ/(S²A²H²K²) equals δ′. The
printed iota equals exactly 1. Even the stronger surrounding proof regime
K≥SAH·iota holds: 4≥2.

At l=2 each batch is the single second sample in its row. For every
expanded-data outcome, the simultaneous-over-all-choices event includes
the choice eb for the observed state b in each row. Each row contributes
positive deviation 1/2 and true variance 1/4. The positive-part sum is 1
and the variance sum is 1/2. The printed right side is
sqrt(1/8)+1/4<3/4<1. Thus this necessary specialization of the joint event
is empty under the actual product sampling law, although 1−δ′>0.
This example uses a positive confidence logarithm; its probability promise
is nonvacuous.

[MVPUniformConfidence.lean](../Formalization/Counterexamples/MVPUniformConfidence.lean)
proves the family bounds, true moments, batch deviations, both K-regime
conditions, exact allocation/iota, empty event and actual-law probability
refutation. The principal export is
`StatisticalRL.SourceCounterexamples.MVPUniform.printed_uniform_probability_false`.
The original generic lemma is not certified. This does not refute the main
MVP regret theorem or its particular value-function family.

The source proof absorbs a positive covering/union budget into a multiple
of log(1/δ′), which can approach zero in the printed parameter range.
The reciprocal allocation δ′=δ/(100S²A²H²K²), with explicit bounded
continuation-family indexing, now gives a proved corrected variant. It
bounds the logarithm away from zero and absorbs the covering budget with
the printed coefficient 40000. Both displayed inequalities hold under the
actual expanded product law for all K≥1 in the source K-regime. The
statement allows the stronger full strictly-future sample dependence and
the ceiling profile cover (C15), and adds no generic terminal-zero condition.
The original printed allocation is still refuted; this correction is not
certification of the actual learner-family membership or the final MVP
regret theorem. Another possible repair would enlarge iota with 1+log(1/δ′),
but that is not the variant proved here. See the original [counterexample
review](critic-online-MVP-uniform-confidence.md), the [corrected-statement
review](critic-online-MVP-corrected-uniform.md) and its
[verification](online-MVP-corrected-uniform-verification.md).

<a id="C17"></a>

## Candidate C17: fixed-profile MVP terminal value differs from the learner

**Status: confirmed failure of the auxiliary value-identification argument;
no refutation of the final MVP regret or decoupling conclusion is claimed.**

Source: actual algorithm initialization `chapters/onlineRL.tex:1267` and
updates `:1296–1308`; fixed-profile auxiliary algorithm at `:4423–4433`;
family construction `:4445–4449`; asserted actual-value equality and
membership `:4467–4472` (`eq:Vk-Itrue`). The actual learner sets V(H+1)=0.
The auxiliary algorithm instead sets V(H+1)=H for every profile/episode.

For a concrete source-level witness take S=A=1, H=2, K=2, zero rewards and
the deterministic sole-state transition. Let c2>0 and choose
q=min{1/(2c2),1/(80000 log 6)}, δ′=exp(−q), and δ=(4/25)δ′.
These give q>0, 0<δ<1 and the printed confidence allocation δ′. Iota is
40000 log 6·q≤1/2, so both K≥SAH log₂K and the stronger K≥SAH·iota hold.
The variance terms vanish for every positive c1.

At the end of the first episode both stage rows have count one, and the
trigger fires under either the literal or dyadic rule. Actual stage 2 uses
terminal zero, stored count one and bonus 2c2q. Its value is therefore
2c2q, which belongs to (0,1]. The auxiliary terminal is 2, so its stage-2
value clips to 2 for every episode/profile. Its stage-2 family is {0,2}
and excludes the actual value. That value is the continuation test at
stage 1 in the claimed coupling argument.

This calculation concerns the printed programs and their claimed
identification step. Machine-checked:
`StatisticalRL.OnlineRL.printedFixedProfile_lastStage_eq` shows that the
printed auxiliary's stage-H value is the constant H for every profile,
expanded sample set and episode (arbitrary rows, arbitrary nonnegative
rewards, arbitrary real counts n, so the printed n = 2^{j−2} = 1/2 at j = 1 is
covered), hence X_{H,I} ⊆ {H·1, 0} (`printedFixedProfileFamily_lastStage_subset`).
`onlineMVP_unit_secondEpisode_lastStage` computes the Lean learner's
pre-episode value V_2^2 = min{2c₂L, 2} for S=A=1, H=K=2, zero rewards, and
`not_eq_Vk_Itrue_printed` (with `not_eq_Vk_Itrue_printed_sourceParameters` and
the parameter lemma `onlineMVP_C17_sourceParameters`, which states K = 2 ≥ SAH·ι;
its docstring notes SAH·ι ≤ 1 < 2, so K > SAH·ι also holds) shows
V_2^2 ≠ V_2^{k,I} for every k and V_2^2 ∉ X_{2,I}. This is the H = K = 2
instance; the auxiliary family is excluded for every K. The Lean learner is
the C8/C13-corrected one; both corrections are inactive in this instance
(count 1, no zero-count row, both trigger readings fire at 1). C16 is not
involved
([OnlineMVPPrintedTerminalCounterexample.lean](../Formalization/Online/Regret/MVP/Decoupling/OnlineMVPPrintedTerminalCounterexample.lean),
[review](critic-small-batch-2a.md)). The proposed
repair sets the auxiliary terminal value to zero and then proves the
actual profile/kernel/value bridge, including initial and zero-count
cases. Changing the terminal line alone is not a proof of that bridge.
This issue is separate from C16's generic concentration counterexample.
See [independent review](critic-online-MVP-uniform-confidence.md).


The terminal-zero repair has now been implemented and proved through the
actual retained-history learner, future-dependent family membership,
per-stage row-rank identities and sequential transcript-law transport.
`StatisticalRL.Statements.Ch5.Lemma5_14_corrected` and
`StatisticalRL.Statements.Ch5.MVP_regret_corrected` consume that corrected bridge
without assuming its conclusion or probability. This does not validate the
printed terminal-H program (the printed counterexample is machine-checked above). The related final regret statement is Theorem 5.10, source label
`thm-mvp-regret` (`onlineRL.tex:1339–1352`); this auxiliary identity issue does
not refute it. See [independent review](critic-online-MVP-main-decoupling.md)
and [verification](online-MVP-main-decoupling-verification.md).

<a id="C18"></a>
## Candidate C18: zero-count branch in the offline LCB algorithm

**Source:** Algorithm `alg:MAB-LCB`, `chapters/offlineRL.tex:400–443`, and
Theorem 6.1, `thm:MAB_LCB_upper`, `:456–471`. The active pseudocode evaluates
a radius with denominator `N_a`; it does not define the zero-count case. A
commented-out branch at `:429–430` instead assigns empirical mean `0` and
radius `1`. The Lean identity `x / 0 = 0` gives radius `0`, so it does not
represent that commented branch either.

The formalized result is explicitly the commented-fallback variant, under the
actual action/noise law and the printed sample assumptions. It is not a proof of
the active undefined pseudocode. No author-intended convention is inferred.

<a id="C19"></a>
## Candidate C19: positive sample count in the offline sample-splitting lemma

**Source:** Lemma 6.5, `lem:sample-split-infinite`,
`chapters/offlineRL.tex:1104–1115`, under the iid triple sampling model
`:28–37`. The standalone statement does not state `N ≥ 2`; the formalized
sample-splitting result uses `N ≥ 2` for its union-bound endpoint. The parent
Theorem 6.3 sample-size regime implies this condition. The release statement
therefore labels this as a restricted auxiliary result; this observation is not
a counterexample to the parent theorem or a claim that its sample regime is
insufficient.

**Addendum (2026-11-09): the printed lemma is false at N = 1.** Take S = 1, A = 2, ρ uniform, N = 1 and
δ = 31/32. The single sample leaves one action with N_{s,a} = 0, and for that action
(2/3)log(SN/δ) = (2/3)log(32/31) ≤ 2/93 < 1/24 = Nρ(s,a)/12. The simultaneous event is therefore empty, although
the lemma claims probability greater than 1−δ = 1/32. The printed proof fails at `|N_large| ≤ N/(8L) ≤ N`
(`offlineRL.tex:3607–3609`), which needs L = log(SN/δ) ≥ 1/8; here both pairs are in N_large and N = 1. Whenever
SN ≥ 2, L > log 2 and that step holds, so the failure needs SN = 1. Scope: the standalone printed lemma
(`:1104–1115`), which states no restriction on N. The formal `N ≥ 2` version
(`Lemma6_5_sampleSplit_actualData_corrected`) is unaffected, and so is Theorem 6.3, whose sample regime implies
N ≥ 2. Proposed repair: add `N ≥ 2` (or `SN ≥ 2`) to the lemma. With this counterexample the earlier sentence above
("not a counterexample") describes only the parent theorem: the standalone lemma is a false printed statement, so
the formal version is a correction rather than a domain restriction. Naming note: the Lean entry carries the
`_corrected` suffix; since 2026-11-10 its `COVERAGE.md` row and named-result ledger record also call it a corrected
variant (they previously said "restricted variant"); nothing is renamed. Machine-checked (2026-11-10):
`OfflineRL.not_Lemma6_5_printed` (`Formalization/OfflineRL/Lemma65Refutation.lean`), the standalone lemma at the
boundary case S·N = 1 (no junk value); independently critic-reviewed ([review](critic-refute-batch.md)). Reported by an external review (2026-11-08), independently re-checked ([check](critic-audit-findings.md)). Not author-approved.

<a id="C20"></a>
## C20: online Q-learning completion, tie scope and proof repairs

**Source:** Algorithm `alg:main-q-ucb`, `chapters/onlineRL.tex:1930–1979`;
Theorem 5.16, `thm-ucbq-regret`, `:1911–1922`; and Lemma 5.18,
`lemma:opt_model_free`, `:2121–2150`. The pinned chapter SHA-256 is
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The algorithm initializes Q to H and the terminal value to zero at line 1943,
but leaves nonterminal V initialization unstated. The implementation derives
V=min(H,max Q), hence initially H, and uses one fixed deterministic maximizing
tie rule for the policy update at line 1947. The proof concerns that completed
implementation. It does not quantify over every randomized or adaptive
maximizing selector. These choices are visible in `Lemma5_18_restricted` and
`Thm5_16_restricted` (renamed from `Thm5_16_corrected` by project decision 2026-11-10: this entry changes no
printed statement, so it is a restricted variant, like Lemma 5.18); neither is advertised as an unrestricted
algorithm claim.

The printed beta-sum equality at lines 2245–2247 equates the previsit indices
0,...,N−1 with 1,...,N. Already for N=1, beta_0=0 and beta_1>0 can differ.
The formal proof uses the valid inequality derived from beta_0=0 and beta_N≥0.
The signed stage residuals at lines 2367–2387 retain their deterministic
geometric weights through the concentration proof; a bound on the weights
does not justify discarding them from a signed pathwise sum. Two confidence
events also receive an explicit half-budget allocation. These repairs preserve
the algorithm's bonus `2 sqrt(H³ log(SAT/delta)/n)`.

The resulting actual-law regret bound is
`max(1,19 exp(1)) sqrt(S A H⁵ K (1+log(4SAT/delta)))`, with probability
strictly exceeding 1−delta for every H,K≥1 and 0<delta<1. It implies the printed
soft-O rate for this implementation. Lemma 5.18 includes both its weighted
Q-error bound and simultaneous Q/V optimism, for every bonus coefficient
`c_b ≥ 2` with explicit residual constant `4c_b` (8 at the algorithm's `c_b = 2`;
`Lemma5_18_restricted` quantifies over all `c_b ≥ 2` since 2026-11-09). No refutation of the final printed regret rate is claimed, and no
claim is made that every printed proof step is valid.

See the [independent source-review record](critic-online-qlearning-source.md)
and [verification record](online-qlearning-source-verification.md).

<a id="C21"></a>
## Candidate C21: mis-cited Bernoulli KL step in the offline transition KL lemma

**Source:** `chapters/offlineRL.tex`, proof of `lem:transition-KL-bound-infinite`
(lemma at lines 2835–2865, proof from line 5680), display
`eq:KL-single-action-bound-infinite-proof`.

The proof bounds `KL(Bern(u) ‖ Bern(v))` by `(u−v)²/(u(1−v))` for `u > v ≥ 1/2`,
citing `lem:KL-quadratic-lower-bound` (Lemma 2.13). Lemma 2.13 gives
`(u−v)²/(v(1−v))` (first clause) or `(u−v)²/(u(1−u))` (second clause); both are at
least `(u−v)²/(u(1−v))`, and the cited inequality is false as a general statement
(for `u = 0.99`, `v = 0.5`: `KL ≈ 0.637 > 0.485`). Whether the cited inequality
holds on the proof's actual parameter region is not established here; the formal proof
does not use it. The lemma's conclusion is unaffected: using the first clause of Lemma 2.13 with reference
parameter `v` gives the same `(p−q)²`-type bound, and the formal proof
(`Formalization/OfflineRL/LowerBoundFamilyKL.lean`) takes that route with the explicit
universal constant `c₃ = 16 · 336²`. This is a printed-proof gap, not an error in the
lemma's statement.

<a id="C22"></a>
## Candidate C22: weighted propagation lemma fails when log(SAT/δ) is small

**Source:** `chapters/offlineRL.tex`, `lemma:useful` (Lemma 6.11, lines 2292–2300), with
`H = ⌈4 log(SAT/δ)/(1−γ)⌉` from `eq:defn-H-lcbq-stepsize-proof` (lines 1667–1672) and
`κ = γ(1+1/H)³` from `eq:defn-kappa-proof-lcbq` (lines 2284–2289).

The lemma is stated for every `0 < δ < 1`, and the text before it says `κ < 1` follows
"immediately" from the choice of `H`. That holds when `log(SAT/δ) ≥ 1` (equivalently
`δ ≤ SAT/e`), but not in general; failures need `SAT ≤ 2`, since `SAT ≥ 3` gives
`log(SAT/δ) > 1` for every `δ < 1`.
Counterexample: `S = A = T = 1`, `δ = 0.9`, `γ = 0.3`. Then `4 log(1/δ)/(1−γ) ≈ 0.60`, so
`H = 1` and `κ = 0.3 · 2³ = 2.4`. With `W ≡ 1` the left side `∑_j κ^j` diverges while the
right side is finite. The lemma also fails with `κ < 1`, because no universal constant works:
with the same `S, A, T, δ` and `γ = 1/8 − η` for `0 < η < 1/8`, `κ = 1 − 8η`, the left side is
`1/(8η)` while the right side stays below about `2.2·C` (with the normalised occupancy `d_ρ^⋆`).

The premise is not implied by the sample-size condition of Theorem 6.8
(`eq:sample-size-lcbq-T-thm`, line 1767): for `S = A = T = 1`, `γ = 0`, `C⋆ = ε = 1` the
condition holds for every `δ ≥ e^{−1/c₂}`, where `log(SAT/δ) < 1`. This is not a counterexample
to Theorem 6.8. In the corner `δ > SAT/e` we have `SAT ≤ 2`, so `T ≤ 2`; with
`ε ≤ 1/(1−γ)`, `S, C⋆ ≥ 1` and `log(SAT/((1−γ)δ)) ≥ log(1/(1−γ)) ≥ γ`, the condition gives
`γ ≤ T/c₂ ≤ 2/c₂`. For `c₂ ≥ 32` this makes `κ ≤ 8γ ≤ 1/2`, and since
`δ/(ST⁴) > A/(eT³) ≥ 1/(8e)`, the lemma's conclusion holds there with a constant below 84.
So, for `c₂ ≥ 32`, `κ < 1` holds on all of Theorem 6.8's hypotheses and the lemma's conclusion holds in the corner, and the theorem is unaffected.

**Proposed correction:** add the premise `log(SAT/δ) ≥ 1` (equivalently `δ ≤ SAT/e`) to the
lemma, or state it under Theorem 6.8's hypotheses. The formal statement `Lemma6_11_restricted`
states the lemma with this premise and an existential universal constant; its proof supplies
`C = 84`. **Open (formal coverage only):** the corner `δ > SAT/e` of Theorem 6.8's uses is not
covered by `Lemma6_11_restricted`; the argument above is not yet formalized.

**Formal coverage (Theorem 6.8):** closed by a different route. `Thm6_8_corrected` does not apply Lemma 6.11 in the corner `δ > SAT/e`. The theorem's own hypotheses (log² condition, `c₂ ≥ 16`) force `|A| = 1` there, and the claim then holds surely (see C24). The `γ ≤ 2/c₂`, `κ ≤ 1/2`, constant-84 argument above concerns the printed single-log condition and is not formalized. It is no longer needed, because the printed Theorem 6.8 is itself refuted (C24). Lemma 6.11 as printed still fails in the corner; `Lemma6_11_restricted` remains the formal entry.

**Machine-checked (2026-11-10):** the κ < 1 family is machine-checked for every C:
`OfflineRL.not_Lemma6_11_printed` (`Formalization/OfflineRL/Lemma611Refutation.lean`). No tsum junk value is used
(κ = 1 − 8η < 1, so the series is a genuine geometric sum). Boundary corner SAT ≤ 2; the κ ≥ 1 divergence remains a
paper argument. Independently critic-reviewed ([review](critic-refute-batch.md)).

<a id="C23"></a>
## Candidate C23: covering-set size in the offline Bernstein leave-one-out proof assumes N ≥ 5

**Source:** `chapters/offlineRL.tex`, proof of Lemma 6.6 `lem:Bernstein-infinite` (statement at lines
1147–1163; proof from line 3630), Step 3: `u_max` and `U_cover` at lines 3873–3895, their size bound in
`eq:defn-Ucover-infinite-Bernstein-cardinality` at lines 3898–3909, used in the union bound at lines 3969–3990.

The proof bounds `|U_cover| ≤ N u_max ≤ N/(1−γ) + 5 + N ≤ 2N/(1−γ)` "given that N ≥ 5 and γ ≥ 1/2"
(line 3898). `γ ≥ 1/2` is a hypothesis of Lemma 6.6; `N ≥ 5` is not, and the proof does not derive it. The
printed bound can fail only when `N ≤ 4`, and it does: for `N = 1` and every `γ ∈ [1/2, 2/3)`. Example:
`N = 1`, `γ = 1/2`, `c_b = 1`, `δ = 0.1` gives `u_max = 8` and `|U_cover| = 8 > 4 = 2N/(1−γ)`, so the union bound
gives a per-pair failure of `2δ` instead of the claimed `δ/N` (line 3974). The worst accounting factors for
`N = 2, 3, 4` are `1.375`, `1.167` and `1.0625`; a parameter sweep finds no violation for `N ≥ 5`.

The lemma's statement is unaffected. When `N ≤ 4`, every count is at most 4, and both conclusions hold
deterministically for every pair with `1 ≤ N_{s,a} ≤ 26` and every `Ṽ` with `‖Ṽ‖∞ ≤ 1/(1−γ)`: since `γ ≥ 1/2` and
`δ < 1`, `ℓ = log(4N/((1−γ)δ)) > 2`, so `|(P̂_{s,a} − P_{s,a})Ṽ| ≤ 2/(1−γ) < 26ℓ/((1−γ)N_{s,a})` and
`Var_{P̂_{s,a}}(Ṽ) ≤ 1/(1−γ)² < 24ℓ/((1−γ)²N_{s,a})`. A repaired proof splits cases: if `N ≤ 4` the conclusions
hold surely; otherwise Steps 3–5 apply unchanged. Within Theorem 6.3 the sample-size condition (line 911) already
forces `N ≥ 6` once `c₁ ≥ 4`. This is a printed-proof gap, not an error in the lemma's statement; Lemma 6.18
`lem:Bernstein-infinite-proof` is not involved.

**Formal handling:** the formal proof splits per pair. When `1 ≤ N_{s,a} ≤ 26`, both conclusions hold surely (`lem66_small_count`). When `N_{s,a} ≥ 27`, the inequality `N ≥ 27 ≥ 5` validates the printed grid bound (`uGrid_card_le`).

<a id="C24"></a>
## Candidate C24: Theorem 6.8 sample-size condition needs log² (and Lemma 6.12 needs log(SAT/δ) ≥ 1)

**Source:** `chapters/offlineRL.tex`, Theorem 6.8 `theorem:lcbq` (lines 1754–1772), condition `eq:sample-size-lcbq-T-thm` (line 1767); penalty `eq:penalty-offlineQ` and `H` (lines 1663–1689); proof Step 6 (lines 2328–2352); Lemma 6.12 `lem:lcbq-alpha-xi-psi-phi-bound` (lines 2309–2324), θ bound step (iii) in `eq:theta-bound-offlineQ`.

The printed condition `T ≥ c₂ S C⋆ log(SAT/((1−γ)δ))/((1−γ)⁵ε²)` has one logarithm, but the proof's final step `√(C⋆Sι²/((1−γ)⁵T)) ≤ ε` needs `T ≳ C⋆Sι²/((1−γ)⁵ε²)` with `ι = log(SAT/δ)`. The penalty `b_n = c_b√(Hι/(n(1−γ)²))` with `H ≍ ι/(1−γ)` is of order `ι/√n`, so the extra log is real.

**Counterexample (statement):** fix any `c_b, c₂ > 0`. Take one state, two actions, `γ = 0`, `r(a⋆) = 1`, `r(a₂) = 1/2`, `ε = 1/4`, `d^b(a⋆) = p = c₂/(64c_b²⌈4ι⌉)` (so `C⋆ = 1/p`), `T = ⌈c₂ι/(pε²)⌉` and `δ = 2Te^{−ι}` with `ι` large (`ι ≳ 2.8c₂/c_b²`). With `γ = 0` one has `Q(a) = r(a) − Σ_i η_i^n b_i ∈ [r(a) − 2b_n, r(a) − b_n]`. On `{N⋆ ≤ 2pT}` (probability ≥ 1/2 by Markov) we get `sup_t Q_t(a⋆) < Q_T(a₂)` and `Q_T(a₂) > 0`, so the last strict `V` increase selects `a₂`, whatever the initial policy and tie rule. The gap is `1/2 > ε` with probability `≥ 1/2 > δ`. Exact simulations (for example `c_b = c₂ = 1`, `T ≈ 3.7·10⁶`) return `a₂` in every run, even at 8 times the single-log threshold. Failure persists for `T ≲ c·c_b²C⋆ι²/ε²`, so `ι²` is necessary for this algorithm and sufficient given the proof's lemmas.

**Lemma 6.12:** as printed, the lemma fails when `log(SAT/δ) < 1` (only possible when `SAT ≤ 2`). With `S = A = T = 1`, `γ = 0` and `ι ≤ 1/4`: `H = 1` and `θ = min{3c_b√ι, 1}`, which is not `≲ ι`. With `γ = 1/2` and `ι ≤ 1/8`: `κ = 4`, so `α = ξ = ∞`. Under `ι ≥ 1` one has `κ < 1` and `H ≍ ι/(1−γ)`. The corner does not affect Theorem 6.8: either `A = 1`, where the theorem is trivial, or the sample-size condition is infeasible for `c₂ > 1/(log 2)²` (under log²; `2/(log 2)²` for all of `SAT = 2`). Related: C22 (Lemma 6.11).

**Proposed correction:** replace `log(SAT/((1−γ)δ))` by `log²(SAT/((1−γ)δ))` in `eq:sample-size-lcbq-T-thm`, and add `log(SAT/δ) ≥ 1` to Lemma 6.12, or state it under that premise. A formal entry should be `Thm6_8_corrected`, not `Thm6_8`.


**Formal entry:** `Thm6_8_corrected` (`Formalization/Statements/Ch6.lean`) states Theorem 6.8 with `log²(SAT/((1−γ)δ))` in place of `log(SAT/((1−γ)δ))` in `eq:sample-size-lcbq-T-thm`, quantified as `∃ c_b₀ > 0, ∀ c_b ≥ c_b₀, ∃ c₂ > 0` (the proof gives `c_b₀ = 4`, `c₂ = 16(400000 + 5600c_b)²`; `c₂` must grow with `c_b`, per the counterexample above). Other explicit hypotheses: `1 ≤ T`, `C⋆ < ∞` (when `C⋆ = ∞` the printed condition cannot hold, so nothing is lost), `π⋆` any Q⋆-greedy deterministic policy used in `C⋆`, `0 < ε ≤ 1/(1−γ)`, i.i.d. samples from `d^b ⊗ P`, conclusion with probability strictly greater than `1−δ` for the output `π_T`. Scope: arg-max ties are broken by a deterministic selector that depends only on the Q-row `Q(s,·)`; the source allows any deterministic rule. The corner `log(SAT/δ) < 1` is handled inside the proof: it forces `SAT ≤ 2`; `SAT = 2` contradicts the log² condition for `c₂ ≥ 16` (since then `T ≤ 2` and `log(SAT/((1−γ)δ)) > log 2`), and `SAT = 1` gives `|A| = 1`, where the gap is 0. (The `1/log 2` threshold above refers to the printed single-log condition; under log² the nontrivial case `S = T = 1, A = 2` is infeasible for `c₂ > 1/(log 2)²`.)

<a id="C25"></a>
## Candidate C25: Theorem 5.19 proof omits odd S

`chapters/onlineRL.tex:2443–2456` states the bound for every `S ≥ 2`, but the proof (`:3004–3290`) assumes `S` even ("for simplicity", `:3015–3016`) and never treats odd `S`. Repair: take `⌊S/2⌋ ≥ S/3` copies and one extra absorbing zero-reward state with zero initial mass; only the universal constant changes. The formalization uses this construction (`onlineLBStages`, `onlineLBRho`). The statement stays as printed; this is a proof gap.

<a id="C26"></a>
## Candidate C26: Theorem 5.19 proof, Case 1 tail bound

`chapters/onlineRL.tex:3205–3218`: (a) the cited `lem:tail-bound-sum-Bernoulli` (`chapters/prelim.tex:1010–1014`) gives `P(K_j > τ) ≤ 2exp(−0.19τ)`, but the first term is bounded by `(100K/S) exp(−19K/S)` without the factor `2`; (b) the step `≤ (111K/S) exp(−19K/S)` requires `K/S ≥ (2/0.19)/11 ≈ 0.957` and fails for `S/2 ≤ K < 0.957S` (at `K/S = 1/2`: `4.53e−3 > 4.15e−3`); (c) with the factor 2 restored, the final `≤ 0.01K/S` fails near `K/S = 1/2` (`8.27e−3 > 5e−3`). Repair: use `0.02K/S` (giving `0.99 ε₀K/192`) or the multiplicative Chernoff bound. Theorem 5.19 is unaffected. The formalization avoids the step (it bounds expected visit counts directly).

<a id="C27"></a>
## Candidate C27: Theorem 5.19 proof, omitted reductions

`chapters/onlineRL.tex:2759–2765, 2850–2858, 3085–3110`: the reduction from the MDP learner to a Lemma 5.21 bandit algorithm, and the conditioning on the initial-state sequence `J`, are asserted in prose only. The induced algorithm keeps persistent internal state (simulated steps and components), while Lemma 5.21's class is `π^t(·|x_{t−1})`, so a mixed-to-behavioral reduction is implicitly used. Both steps are true. The formalization instead proves the coordinatewise testing bound directly from the adaptive KL chain rule on the episode-history law (`HistoryKL.history_sum_KL_le`).

<a id="C28"></a>

## Candidate C28: Lemma 6.10 omits the c_b premise; Lemma 6.9 proof applies Azuma at undefined random visit times

**Classification (marker audit, 2026-11-11).** Lemma 6.10 fails only without the large-c_b premise that Lemma 6.9 and Theorem 6.8 assume as a standing condition; with it the lemma is proved (ledger kind `domain`).

**Source:** `chapters/offlineRL.tex`, Lemma 6.9 `lemma:Q-recursion-pessimistic-Q` (:1866–1893, proof :4415–4528) and Lemma 6.10 `lemma:pessimistic-Q` (:1907–1916, proof :4530–4672).

(1) Lemma 6.10 does not repeat Lemma 6.9's requirement that `c_b` be large enough, and its proof depends on Lemma 6.9. As a standalone claim for an arbitrary universal `c_b > 0`, it fails. Counterexample: `S = {0,1}`, one action, `P(·|0) = (½,½)`, `P(·|1) = δ_1`, `r = (0,1)`, `γ = ½`, `d^b` uniform, `T = 3`, `δ = 0.01`. Exact enumeration gives `P(∃t: Q_t ≰ Q⋆) = 1/16 > δ` for `c_b ≤ 10⁻³`. The premise is the standing assumption of Theorem 6.8 (:1764). The formal entry states it as `∃ c_b₀, ∀ c_b ≥ c_b₀` (`c_b₀ = 4`).

(2) The proof of Lemma 6.9 (:4476–4491) applies Azuma–Hoeffding "for fixed ℓ" to `Σ_{i≤ℓ} η_i^ℓ (P_{s,a} − P_{k_i})V_{k_i−1}`. It names no filtration, and `k_i` is undefined when `i` exceeds the number of visits within `T` iterations. The step can be repaired, by zero-padding with optional sampling or by conditioning on the state-action labels. The latter is the formal route, with the union over `(s,a,n)` at radius `2√(H log(2SAT/δ)/(n(1−γ)²))`. Separately, the absorption `log(2SAT²/δ) ≲ ι` fails for `S = A = T = 1`, `δ > ½`; the conclusion still holds there because the martingale term vanishes at `T = 1`.

Neither point changes Lemma 6.9 or Theorem 6.8.


<a id="C29"></a>
## Candidate C29: Lemma 6.12 proof — confidence budget, φ on poorly covered pairs, Freedman on a non-predictable event

Source: proof of `lem:lcbq-alpha-xi-psi-phi-bound`, `offlineRL.tex:4786–5496`.

(1) The proof combines the Lemma 6.10 event, the prefix-count event (`eq:prefix-count-lower-bound-lcbq`) and two Freedman events, each at confidence `1−δ`, but concludes `1−δ`. Rescaling is not free, because `δ` enters `H` and `b_n`. Repair: run each event at `δ/5`, absorb `log 5` into `ι ≥ 1`, and take `c_b` large enough for Lemma 6.9 at `δ/5`.

(2) The `φ` bound is omitted as "analogous" (`:5483–5485`), but the sign that disposes of poorly covered pairs in `κ₁` is reversed in `φ`. The sampled term `g_t(X_t)` enters positively, with envelope `≲ C⋆/(1−γ)² + δ/(ST⁴(1−γ)²d^b)`, which is unbounded as `d^b → 0`, because `d̃` can exceed `d⋆/(1−γ)` by `(1+1/H)^{3J}` at depth `J ≫ H`. Repair: intersect with the event that no sample hits a pair `(s,π⋆(s))` with `d^b < δ/(5ST)` (probability `≥ 1−δ/5`).

(3) Freedman (`lem:Freedman-prelim`) is applied with the conditional-variance bound `E[Z_t²|F_{t−1}] ≲ C⋆(1−γ)^{-2} E f_{t−1}`. That bound uses `Δ ≥ 0`, which holds only on the Lemma 6.10 event, not predictably. The cited lemma also conditions on the summands' own past rather than on `F_{t−1}`. Repair: gate each summand by the `F_{t−1}`-measurable predicate `V_v ≤ V⋆ ∀ v ≤ t−1` and apply Freedman with the data filtration; on the pessimism event, gated equals ungated.

The statement of Lemma 6.12 (under `ι ≥ 1`) is unaffected. The formal proof follows these repairs and needs no sample-size condition (its Freedman peeling uses `log(2T/(δ/5)) ≤ 4ι`).

<a id="C30"></a>
## Candidate C30: Theorem 4.7 case (i) (rescaled linear learning rates) is not proved in the source

Source: `thm:LB-example-Q-generative`, `generative_model_model_free.tex:969–982`; proof scope sentence `:2711`.

The theorem covers (i) `η_t = 1/(1+c_η(1−γ)t)` for any constant `c_η > 0` and (ii) constant `η_t ≡ η ∈ (0,1)`. Appendix C proves only (ii); (i) is deferred to li2024q ("similar"). The constant-rate argument does not transfer verbatim: Steps 3–5 use the closed forms `η_k^{(t)} = η(1−η(1−γp))^{t−k}`, the regime split of a single `η` against `4/((1−γ)T)` and `1/((1−γ)²T)`, and the window `t−1/η`. For order-one `c_η`, `η_T ≍ 1/(c_η(1−γ)T)`, so the state-2 variance route gives only `≍ 1/(c_η(1−γ)³T)`, and the over-estimation argument with time-varying weights is required. The printed text also makes `c_lb` "universal" while `c_η` is arbitrary; whether `c_lb` can be chosen independently of `c_η` is not settled by the source.

Formal entry: `Thm4_7_restricted` (case (ii) only). Case (i) remains an open obligation.

Resolved (2026-11-08). The source omits the argument for case (i); the printed statement is true as printed, with constants independent of c_η (c₃ = 16, c_lb = 10⁻⁹). Formal proof: `qLb_thm47_rescaledLinear` (`Formalization/ModelFree/QLearningLowerBoundRescaledTheorem.lean`), combined with case (ii) in the printed entry `Thm4_7`. No statement correction. Independently plan-checked and source-reviewed. Not author-approved.

<a id="C31"></a>
## Candidate C31: Theorem 4.7 proof (constant rates) and Lemma 4.15 proof — constant slips, an off-by-one, an unused WLOG

Source: Appendix C, `generative_model_model_free.tex:2707–3956`; `lem:lower-bound-E-xi-lower-Q` `:3429–3449`.

(1) WLOG `eq:logT_ub` (`:2711–2716`) is justified by comparison with the minimax bound of `theorem:azar`, which concerns a worst case over an MDP family under a different criterion and does not bound Q-learning on this instance. It is never used afterwards; the formal proof does not assume it.

(2) Step 4 (`:3227–3252`): the factor is `81(1−γ)²`, not `81(1−γ)²/4` (only `V⋆(2) − E V_{τ−1}(2) > 1/(4(1−γ))` is available); the bound `≤ 1/2` still holds. The final constant `(4γ−1)/192 ≥ 1/86` needs `γ ≥ 139/172`; at `γ = 3/4` it is `1/96`. The sum over `k = τ+2,…,T` needs `τ ≤ T−2`, which holds (`η_0^{(T−2)} ≤ (9/4)/100`).

(3) Lemma 4.15 proof: in `eq:square-zeta` (i) the coefficient is `(4γ−1)/(144(1−γ))`, which equals `1/(72(1−γ))` at `γ = 3/4` and is below `1/(48(1−γ))` for every `γ < 1`; (ii) becomes `η/(1728(1−γ))`. `eqn:tail-bunny` does not follow from `lem:Freedman-prelim` (K₀ = 1) with the stated variance cap `2S/(3(1−γ))`: the square-root term is `√(16 S log(2/δ)/(3(1−γ)))`, a factor `√2` larger. `τ′ = max{t − 1/η, 1}` is not an integer; summing over integers `k ≥ τ′` keeps both bounds of `eq:sum-LB-1/8-890`.

(4) Step 5.4 (`:3477–3510`): with `x_{τ̂} = 0` the closed form is `x_T = c′(1 − ρ^{T−τ̂})/(1−γp)`, `ρ = 1−η(1−γp)`, not `ρ^{T−τ̂+1}`. Maximality of `τ̂` gives `ρ^{T−τ̂} > 6/7`, so the printed `≥ 1/7` fails for every instance. Repair: `1 − ρ^{T−τ̂} ≥ 1 − (6/7)/ρ ≥ 0.137` when `c₃ ≥ 50`. The comparison `E Δ_{T,max} ≥ x_T` is valid but needs `E Δ_{t,max} ≥ 0` for all `t` (induction from `Δ₀ = 0` and `E ξ_{t,max} ≥ 0`).

(5) Encoding note: "S = 4, A = 2" uses state-dependent action sets. Padding states 0, 2, 3 by duplicating their action is not harmless at state 2 (Q-learning would take a max of two independently sampled copies); a dominated dummy action (reward 0, deterministic move to state 0) leaves every recursion and `V⋆` unchanged.

None of (1)–(5) changes the printed statements of Theorem 4.7 (ii) or Lemma 4.15; they change only the unnamed constants `c`, `c_lb` and the size of `c₃`.

Note to C31 item 5 (2026-11-07): the copied-action encoding `qHardMDP` in `QLearningHardMDPDefinitions.lean` (used by Lemma 4.14) is fine for optimal values but unsuitable for Q-learning dynamics; Theorem 4.7 and Lemma 4.15 use `qLbMDP` with dominated dummy actions (`qLbMDP_optimal_values`).

<a id="C32"></a>
## Candidate C32: Theorem 6.16 relies on an algorithm and proof outside the monograph

**Source:** `chapters/offlineRL.tex`, Theorem 6.16 `thm:finite-VI-LCB` (finite-horizon VI-LCB, around line 3095).
The monograph states the result for a "variant" of VI-LCB that it does not define, and gives no proof; it cites
li2024settling. The statement can therefore not be checked against the book alone, and a formal proof requires
reconstructing the cited algorithm and argument. No counterexample is claimed.

Restricted result (2026-11-07). Instead of pinning the cited source, the project defines one explicit variant and proves the printed guarantee for it from scratch (`Thm6_16_restricted`, `Formalization/OfflineRL/FiniteVILCB/`): two-fold sample splitting in which the first half fixes, per (stage, state), how many visits of the second half are used (our reading of `:3061`), backward pessimistic value iteration with a Bernstein-style penalty clipped at the norm of the next-stage value (so the last-stage penalty is zero), first-visit ranks, a uniform row and penalty `‖V̂_{h+1}‖` at zero count. The entry is restricted to this variant and does not assert that it is li2024settling's algorithm. It keeps the printed rate `K ≥ c_k H³ S C⋆ log(KH/δ)/ε²` with `c_k = 69120·c_b`, holds for every greedy output and every optimal π⋆, and adds only the domain conditions `0 < K` (the logarithm's domain) and `C⋆ < ∞`. Values and occupancies are the library's objects. Independently plan-checked and source-reviewed. Not author-approved.

<a id="C33"></a>
## Candidate C33: Theorem 6.17 relies on an outside proof and an under-specified algorithm

Theorem 6.17 `thm:lcbq` (`offlineRL.tex:3176–3192`) relies on shi2022pessimistic for its proof. Its algorithm
(`:3126–3148`) leaves the initialisation, the value update `V_{h+1}`, the output/tie rule, and the constant and
log power of the Θ̃ penalty `eq:lcb-q-penalty` unspecified. The algorithm box is commented out with an
`\yc{to update}` marker (`:3150–3173`).

Classification (two independent source checks, 2026-11-07): the printed statement is under-specified, not false. Write the penalty as `b_n = c_b √(H³L/n)` with `ι = log(SAK/δ)`. If the hidden factor is `L = ι^{2a}` with `a > 3/2`, the statement fails for every choice of constants: an H = 1, two-arm instance with a suitably small exit gap `p ∝ ι^{-(2a−3)}` makes the algorithm output the wrong arm (gap 1/2) with probability ≈ 1, for every initial policy and tie rule. At `a = 3/2` it fails whenever `c_a < c_b²/32` (only this counterexample direction is shown). So reading Θ̃ as "any such penalty" is false, while reading it as "some such penalty" is true (proved below).

Restricted result (2026-11-07), proved in Lean from scratch (`Thm6_17_restricted`, `Formalization/OfflineRL/FiniteLCBQ/`, export `lcbqFinite_restricted`): one explicit completion (zero initialisation, arbitrary initial policy, forward stage order within an episode, rate `(H+1)/(H+n)`, penalty `c_b √(H³L/n)` for every `ι ≤ L ≤ max(ι, ι³)` with `c_b ≥ 5`, monotone value, policy changed only on a strict value increase as in `alg:q-infinite-lcb` rather than the literal "greedy w.r.t. the final Q" of `:3145`, C⋆ defined with a deterministic optimal policy). It keeps the printed size condition `c_a H⁵ S C⋆ ι³/ε² ≤ K` with `c_a = 10⁶ c_b²` and the printed conclusion for every optimal π⋆, with values and occupancies the library objects; it adds only the domain conditions `0 < K` and `C⋆ < ∞`. The underlying export needs only `L` in place of `ι³`. Independently plan-checked and source-reviewed. Whether the final-greedy output or backward stage order also work is open. Not author-approved.

<a id="C34"></a>
## Candidate C34: Theorem 4.12 fails at T = 1 and needs μ_min > 0; proof outside the monograph

Source: `thm:infinite-horizon-asyn`, `generative_model_model_free.tex:2062–2086`; rate `:2054–2058`;
Assumption `assump:ergodicity-asyncQ` `:2012–2016`; `mumin` `:2024–2028`.

(1) T = 1: log³T = 0, so the rate is η = 0 and the first term of the T-condition vanishes. With S = A = 1,
γ = 1/2, r = 1, Q₀ = 0, ε = 1, μ_min = 1, t_mix ≤ 1 and δ ≥ exp(−1/√(2c₂)), the T-condition holds at T = 1, but
Q₁ = 0 while Q⋆ = 2. (Read with η_t ∈ (0,1) from `:1937`, the instance is instead ill-posed.) T ≥ 2 is needed.
(2) Uniform ergodicity does not give μ_min > 0 (e.g. a behavior policy that never plays some action). The rate and
the T-condition divide by μ_min; with μ_min = 0 the unvisited pair is never updated and the claim fails.
μ_min > 0 must be a hypothesis.
(3) The proof is only sketched (`:2124–2127`) and relies on li2024q and on Markov-chain concentration
(paulin2015concentration, Thm 3.14), neither of which is stated in the monograph.
Corrected result (2026-11-07). `Thm4_12_corrected` (`Formalization/ModelFree/AsyncQ/`, Markov-chain theory in `Formalization/Probability/FiniteMarkov/`) states the printed ∃c₁ ∃c₂ form with only two added premises, `0 < μ_min` and `2 ≤ T ∨ 2 ≤ S·A` (weaker than `2 ≤ T`; when SA ≥ 2 the budget already excludes T = 1), plus the domain premise `1 ≤ T` (the loop runs over t = 1..T and the budget uses log T). The proof is new and self-contained, not the monograph's: it replaces the cited Markov concentration result by a window-visit lemma proved from stationarity and d(t_mix) ≤ 1/4, from any initial state. The library export holds for every c₁ ∈ (0,1] with c₂ = max(e^{32/c₁}, 4096) and assumes less than the printed statement (no uniform-ergodicity constants). Joint satisfiability of the budget for this c₂ is argued on paper only. Independently plan-checked and source-reviewed. Not author-approved.
```

```

Remark 4.3 (`:2088–2090`, no displayed formula) is indexed as `Remark4_3_corrected`: read like Remarks 4.1/4.2 (δ = ε(1−γ)/2 in the budget, E[max|Q_T−Q⋆|] ≤ ε(1−δ)+δ/(1−γ) ≤ 2ε), it fails under the printed premises by the same T = 1 instance (ε = 1/2: mean error 2 > 1) and is proved with exactly the premises of `Thm4_12_corrected` (c₁ = 1, c₂ = max(c₂⁰, 1)).

**C34(1) machine-checked (2026-11-10):** `AsyncQ.not_Thm4_12_printed`, `AsyncQ.not_Remark4_3_printed`, and the
per-constant forms `not_Thm4_12_printedAt`, `not_Remark4_3_printedAt` for every c₁, c₂
(`Formalization/ModelFree/AsyncQ/Thm412Refutation.lean`; instance S = A = 1, γ = 1/2, r = 0, Q₀ ∈ {0, 2}, T = 1, so
log³T = 0 and Q₁ = Q₀). The Remark 4.3 refutation concerns this project's reading (the remark has no formula), at
ε = 1/4: the mean error ≥ 1 exceeds both ε(1−δ)+δ/(1−γ) = 23/64 and the bare 2ε = 1/2. This is a boundary case, not
a junk value; under η_t ∈ (0,1) (`:1937`) the instance is ill-posed. C34(2) (μ_min = 0) is still a paper argument.
Independently critic-reviewed ([review](critic-refute-batch.md)).

<a id="C35"></a>
## Candidate C35: Theorem 4.13 needs T ≥ 2; its proof is outside the monograph

**Classification (marker audit, 2026-11-11).** The printed schedule is undefined at T = 1, so the Lean witness depends on Lean's convention x/0 = 0 and is not a refutation of a well-defined printed case (ledger kind `ill-posed`).

Source: `thm:finite-horizon-simple-Q-generative`, `generative_model_model_free.tex:2215–2236`; schedule
`eq:thm:finite-horizaon-eta` `:2203–2209`; algorithm `:2181–2200`.

(1) The schedule divides by H log²T, which is 0 at T = 1, while the T-condition (log³T = 0) admits T = 1. Theorem 4.6
states T ≥ 2 (`:896`); Theorem 4.13 omits it. With junk division the schedule forces η₁ = 1, contradicting 0 < η_t < 1;
without that constraint the claim fails at T = 1 (H = 2, one action, P₁ uniform on two states with terminal
rewards 1/0: Q_{1,1} ∈ {0,1} vs Q⋆₁ = 1/2). Without `2 ≤ T` the Lean transcription of the printed statement is false;
this is machine-checked (`FiniteQLearning.not_thm4_13_from_one`, same instance). The index entry is `Thm4_13_corrected`,
which adds only 2 ≤ T.
(2) The update leaves Q_{t,H+1} implicit; the formalization uses Q_{t,H+1} ≡ 0.
(3) The monograph cites li2021tightening-icml and gives no proof. The formal proof
(`FiniteQLearning.finiteQLearning_sample_complexity`) is self-contained from monograph tools: Freedman with K₀ = 1
along each (h,s,a) coordinate, robust χ²-ball comparators V^± (finite-horizon form of `lemma:Q-comparison-facts`),
absorption of the fluctuation into the Bellman residual, and a triangular propagation recursion with
super-solution H·2^k·∏_{(T/2,t]}(1−η_j/2). The χ² stability step is proved deterministically with the
total-variance potential Ψ = 2K V⋆ − (V⋆)², not via a trajectory KL chain rule and Pinsker. Constants: every
c₁ ∈ (0, 1/64] and c₂ ∈ (0, c₁] work with c₃ = 8000/c₂. The good event has probability ≥ 1 − δ/2, so the printed
strict bound "> 1 − δ" holds. A ≥ 2 and 0 < η_t < 1 are not assumed; the schedule is used only for 1 ≤ t ≤ T.

<a id="C36"></a>
## Candidate C36: Theorem 5.1 proof Step 1 applies fixed-count tails at a random count (conclusion true)

Source: `thm:bandit-pure-ucb`, `bandits.tex:258–277`; proof `:387–501`, Step 1 `:400–429`.

The proof applies fixed-count Gaussian tails (`:188–199`) at the random count N_t(a), relying on
"r̄_t(a)−r(a) = N(0,1/N_t(a))" (`:180`, repeated at `:328`). This identity fails under adaptive sampling (A = 2, T = 3,
equal means: E[√N₃(1)(r̄₃(1)−r(1))] = (1/√2−1)/(2√π) ≠ 0), so the per-round bound (`:427`) is unjustified (not
refuted). Repair: for each fixed n an exponential-martingale bound gives P(the n-th pull exists and the first-n mean
deviates by more than √(2L/n)) ≤ δ/T²; a union over n ≤ t−A+1 at each t gives
E N_T(a) ≤ 1 + 8L/Δ² + δ(T−A)(T−A+1)/T² ≤ 8L/Δ² + 2, the printed intermediate bound. Steps 2–4 and both printed
conclusions are unchanged. Classification: invalid argument, true conclusion; no corrected statement is needed.
Exposition only: the algorithm (`:234`) divides by N(a) = 0 before the ∞ convention appears (`:387`), and no tie rule is
given (harmless: Step 1's comparison is strict).
Formal route (addendum): the Lean proof takes the union over counts 1 ≤ n ≤ t at 0-indexed round t (count ≤ t), without using the
initialization phase, so β = δ(T−1)/T ≤ δ and E N_T(a) ≤ ⌊8L/Δ²⌋ + 1 + δ ≤ 8L/Δ² + 2; the n ≤ t−A+1 route above is an equally valid,
tighter alternative. The tie-rule scope of the formal entry is disclosed under statement-index scope disclosures.

<a id="C37"></a>
## Candidate C37: Theorems 7.2 and 7.4 iterate DRVI too few times (iteration count lacks 1/(1−γ))

Theorems 7.2 and 7.4 (`robust_RL.tex:342–359`, `:437–450`) run DRVI for T = C1 log(N/(1−γ)) iterations (`:345`, `:438`),
with no 1/(1−γ) factor, from Q̂₀ = 0 (`:245`). The output clause is then false for every choice of universal constants.
A deterministic chain MDP (A = 2, S = T+3) puts reward 1 more than T steps away from s0 and a small bail reward b at s0.
The empirical kernel is exact surely, and the χ² ball around a point mass is a singleton (`intro.tex:234`; Lemma 7.1),
so Q̂_T(s0, chain) = 0 < b and DRVI bails, while the robust gap is ≥ (γ(1−σ))^{T+1}/(1−γ(1−σ)) − b, which exceeds ε with
probability 1 for γ near 1. Checked in exact arithmetic for C1, C2 ≤ 10⁶ by two independent source checks, and
machine-checked in Lean (`Formalization/RobustRL/LowerBounds/HorizonTrap.lean`): `not_thm7_2_printed` (TV) and `not_thm7_4_printed`
(χ²) refute the printed statements for every choice of constants and every rounding of T within distance < 1, both when
every greedy output must succeed and when some tie rule may be chosen (`not_thm7_2_printed_exists_tie`,
`not_thm7_4_printed_exists_tie`). Lean witness: bail reward 1/2, goal reward 1, γ = 1 − 1/k², σ = (1−γ)², δ = 1/2, ε = 1,
N = k¹⁰, S = ⌈12 C1 log k⌉ + 3, A = 2, for k large. Only the printed iteration count is refuted, in an extreme regime;
the corrected count and the statistical rate are neither proved nor refuted by the refutation itself.
Corrected result (2026-11-08). With the iteration count changed to any T ≥ C1 log(N/(1−γ))/(1−γ), both theorems are proved in Lean from scratch at the printed statistical rate (`Thm7_2_corrected` for TV, `Thm7_4_corrected` for χ²; `Formalization/RobustRL/DRVI/`), with C1 = c1 = 2 and C2 = c2 = 10⁶; the cited paper was not used. The statements differ from the printed ones only in the iteration count (machine-checked by a definitional comparison). The change is a minimal edit; tightness of the log factor is not shown. The oracle-planner remarks and history-dependent policies are not covered. Independently plan-checked and source-reviewed. Not author-approved. The book uses (1/(1−γ)) log(N/(1−γ)) iterations elsewhere
(`generative_model_model_based.tex:943`, `offlineRL.tex:901`). Proposed correction: T ≥ C1 log(N/(1−γ))/(1−γ).
The theorems themselves are cited (shi2024curious), not proved in the monograph. Not author-approved.

<a id="C38"></a>
## Candidate C38: Theorem 7.3 admits A = 1 (and S = 1 under the known-reward convention)

Theorem 7.3 (`robust_RL.tex:377–391`) quantifies over any (S, A, γ, σ, ε) with no restriction on S or A. For A = 1 every
estimator outputs the unique policy, so both error probabilities are 0 < 1/8. An admissible witness is c0 = 1/8,
γ = 1/2, σ = 1/2, ε = 1/1024 (the upper endpoint), N = 1 (the N-bound is 128 ln 2 ≈ 88.7); A = 1 fails for every c0.
Under the known-reward convention (`generative_model_model_based.tex:31`), S = 1 is also degenerate (constant data;
argmax r is optimal), the same mechanism as [C7](#C7) for Theorem 7.5. Originally proposed correction: A ≥ 2 and S ≥ 2, with M0
and M1 on S states and A actions (superseded by the proved corrections below). Confirmed by
two independent source checks and machine-checked in Lean (`Formalization/RobustRL/LowerBounds/SingletonAction73.lean`):
`not_thm7_3_printed`, `not_thm7_3_exists_c0` and `not_thm7_3_printed_small` cover the ∀c₀, ∃c₀ and "c₀ sufficiently small"
readings (witness S = 2, A = 1, γ = σ = 1/2, ε = c₀/128, N = 1).

Corrected result (2026-11-07). The cited bound is now proved in Lean with the printed constants, by a self-contained construction (the cited paper was not used), in two forms (`Formalization/RobustRL/LowerBounds/LowerBound73.lean`; index entries in `Statements/Ch7.lean`):
- `Thm7_3_corrected`: the printed statement with only `2 ≤ A` added. Here estimators map samples to policies and do not see the reward, and the two hard models may differ in reward; the S = 1 case holds only for that reason.
- `Thm7_3_corrected_knownReward`: the faithful form under the book's known-reward convention: `2 ≤ S`, `2 ≤ A`, and the two hard models share their reward. Under that convention the printed claim is false at S = 1 (`argmax r` is robust-optimal; a paper argument, not machine-checked), so S ≥ 2 is needed there.
Estimator class: the entries `Thm7_3_corrected` and `Thm7_3_corrected_knownReward` take estimators that are deterministic maps from the sample array to policies. Externally randomized estimators (an independent seed `ω ~ ν` in any measurable space, estimator `π̂(ω, data)`, failure probability under `ν ⊗ P_i`, outer probability for non-measurable failure sets, printed constant 1/8) are covered by `Thm7_3_corrected_randomized` and `Thm7_3_corrected_knownReward_randomized` ([independent review](critic-rand73.md), five-bin PASS-DISCLOSED); the deterministic entries are the `Ω = Unit` case, so no estimator class remains uncovered. The remaining deviations are the ones listed above: `A ≥ 2` and, for the known-reward reading, `S ≥ 2` with shared reward.
Both passed independent reviews. Not author-approved.

<a id="C39"></a>
## Candidate C39: Theorem 7.7 is not self-contained

Theorem 7.7 (`marl.tex:441–467`) asserts the existence of an algorithm
(Q-FTRL) whose description is omitted (`marl.tex:432`) and states its sample complexity only up to Õ(·). The symbol A
in the two-player bound (`marl.tex:454`) is never defined (presumably max{A_1,A_2} or A_1 + A_2). Without the algorithm
and an explicit form of Õ, the printed statement cannot be checked against the monograph. Proposed correction: define
A and state the algorithm and the hidden logarithmic factors, or cite the source theorem as an external input.
Found by a source preflight and confirmed by an independent source check. Not author-approved.

Restricted result (2026-11-08). The monograph omits Q-FTRL (`marl.tex:432`), so the project proves the
existential claim of Theorem 7.7 from scratch with an explicit reconstructed witness (`Thm7_7_restricted`,
`Formalization/MultiAgent/Hedge/*.lean`). The witness works as follows:
- For each step h = H, …, 1 and state s, it plays T rounds of Hedge (entropic FTRL) for every player.
- In each round, every pair (player i, action b) issues one generative query (h, s, (b, a₋ᵢ)), with a₋ᵢ drawn
  from the other players' current weights.
- It forms optimistic values with a variance bonus, clipped at H − h + 1.
- The output is the average of the round product policies, a correlated joint Markov policy, for the
  general-sum CCE claim. For two-player zero-sum games, the algorithm shifts player 2's reward internally, runs
  at accuracy ε/2, and outputs the product of the marginals. In the zero-sum case, gap(⊗ marginals) ≤ 2·gapJ is
  proved in Lean.

The witness is not shown to be Q-FTRL. It builds no empirical transition kernel, so "model-based" is not
claimed.

What is proved: one universal constant C = 20000, quantified before all sizes, such that the following holds for
every δ ∈ (0,1), ε ∈ (0,H], known reward and every transition kernel, with probability ≥ 1 − δ:
- N ≤ C·H⁴S·Σ_iA_i·ε⁻²·log(4HSΣ_iA_i/δ) adaptive, randomized generative queries give gap ≤ ε for the joint
  output (`eq:defn-NE-gap`, CCE);
- N ≤ C·H⁴S·max(A₁,A₂)·ε⁻²·log(8HS·max(A₁,A₂)/δ) queries give an ε-NE product policy for two-player
  zero-sum games (r₂ = −r₁, r₁ ∈ [0,1]).

Readings:
- The query count is deterministic.
- A is read as max(A₁,A₂), which implies the A₁+A₂ and A₁ = A₂ readings.
- Õ is read as a universal constant times one log(·/δ) factor, with no ε inside the logarithm.
- The algorithm sees the reward (`generative_model_model_based.tex:31`) but not P.
- Added domain conditions are S ≥ 1 and A_i ≥ 1. Rewards are constrained on steps 1..H only.
- The two bullets are separate existentials sharing C. That one algorithm serves both (by branching on the known
  reward, with N = 0 on the overlap r ≡ 0) is argued in prose only.

Whether Q-FTRL itself attains the rate is not checked. No falsity of the printed statement is known.
Independently reviewed. Not author-approved.

**Project decision 2026-11-10.** The proved entry `Thm7_7_restricted` is an existential witness: it is not the
printed Q-FTRL algorithm and not a special case of the printed theorem. The named result Theorem 7.7 is therefore
shown as **incomplete** (named-result record field `"status_override": "incomplete"`), with the existence result
shown as a related proved result. The Lean entry and its proof are unchanged.

**Why the printed algorithm cannot be formalized as stated (project analysis, 2026-11-10; not author-confirmed).**
The book prints no Q-FTRL algorithm: `marl.tex:423–432` is a prose sketch only (optimism bonuses, FTRL online
learning, adaptive sampling "from each agent's perspective"), and `:432` omits the algorithmic details and cites
li2022minimax. No update rule, learning-rate schedule, regularizer, bonus, output rule or per-step sample count is
given. "Model-based" is not defined for this setting, and the natural reading does not fit: a plug-in model over
joint actions must sample every (h, s, a) with a the joint action, which already costs H·S·∏_iA_i samples, the
curse of multiple agents that the book (`marl.tex:409–416`) says Q-FTRL avoids; per-agent "kernels"
P(·|h, s, a_i) depend on the opponents' changing policies and are not a model in the sense of `:355–377`. A Lean
definition of "Q-FTRL" or of "model-based" would therefore be reconstructed from outside the pinned source and
could not be checked against the book. Theorem 7.7 stays **incomplete**; `Thm7_7_restricted` (an existence result
for a different, reconstructed algorithm) is shown as related, not as the printed theorem. This paragraph is the
project's analysis, not an author ruling.

<a id="C40"></a>
## Candidate C40: Theorem 7.8 admits A_i = 1 (and S = 1 or H = 1 with known reward); "m-player zero-sum" is undefined

Theorem 7.8 (`marl.tex:487–503`) places no range on S, H or A_i. If every A_i = 1, each player has one policy, so
gap(π̂) = 0 (`marl.tex:332–340`) and P{gap > ε} = 0 < 1/4 at sample size 0, for every c1, c2. With the known-reward
convention (`generative_model_model_based.tex:31`), S = 1 or H = 1 makes the game known, and a stage-game Nash
equilibrium gives gap 0 with no samples. "m-player zero-sum" is defined only for m = 2 (`marl.tex:50–54`); read as
Σ_i r_{i,h} = 0 with r_{i,h} ∈ [0,1] (`marl.tex:41–43`), all rewards vanish and the bound fails for all parameters.
Proposed correction: max_i A_i ≥ 2, S ≥ 2, H ≥ 2 (or larger constants), and an explicit zero-sum convention.
No proof or citation is given in the monograph. Found by a source preflight and confirmed by an independent source check. Machine-checked in Lean for the A_i = 1 part only (`Formalization/MultiAgent/LowerBound/SingletonActionRefutation.lean`: `not_thm7_8_printed` for every zero-sum admissibility predicate, also with size-dependent constants and the sum-zero / sum-constant readings); this shows only that a hypothesis such as max_i A_i ≥ 2 is missing and says nothing about the lower bound. The S = 1 / H = 1 and vanishing-reward cases have no Lean evidence. Not author-approved.

Corrected result (2026-11-07). The monograph states Theorem 7.8 without citation or proof; a corrected form is proved in Lean from scratch (`Formalization/MultiAgent/LowerBound/Main.lean`; index entries `Thm7_8_corrected`, `Thm7_8_corrected_constSum`): constants c₁ = 1/2048, c₂ = 2⁻³², the printed rate N < c₂H⁴S·max_iA_i/ε², probability ≥ 1/4, estimators that may output correlated joint policies, adaptive randomized generative sampling, known shared reward (the book's convention), and hypotheses m ≥ 2, S ≥ 2, H ≥ 2, max_iA_i ≥ 2. "Zero-sum" is defined in the book only for m = 2 (`:50–53`, r₂ = −r₁ with r₁ ∈ [0,1]); for m ≥ 3 two readings are proved (rewards summing to 0, all in [−1,1], with player 1 in [0,1], and normalised constant-sum). Disclosures: learner randomness is any discrete (countably supported) seed law on an arbitrary type; measurable output kernels into the continuous policy space are not literally covered (a randomised output is a mixture of deterministic ones, so this is a modelling choice, not a mathematical loss); outputs and deviations are Markov, as in the source; the conclusion is vacuous if some A_j = 0; the hard family has two non-dummy players; necessity of S, H, m ≥ 2 and max A ≥ 2 for the corrected statement is argued in prose only (Lean refutes only the printed transcription with every A_i = 1, `not_thm7_8_printed`). The earlier transcription `Thm7_8_printed` is much weaker than the printed statement (data-independent estimators, a data law the claimant chooses, sup instead of max), so it serves only for the A_i = 1 refutation, which remains valid. Independently reviewed. Not author-approved.

<a id="C41"></a>
## Candidate C41: Theorem 7.9's learning rate can exceed 1

**Classification (marker audit, 2026-11-11).** The failure occurs only when the prescribed η exceeds 1, outside the algorithm's stated range 0<η<1; with that range read in, the statement is vacuous for large K rather than false (ledger kind `domain`).

The algorithm requires 0 < η < 1 (`federated_RL.tex:51,76`),
but the prescribed η = c_η K(1−γ)⁴ε²/log(SAKT/δ) (`federated_RL.tex:114`) is unbounded in K (and large as δ → 1).
Witness, for any constants c_T, c_η: S = A = 1, r ≡ 1, Q_0 = 0, τ = T = 1, γ = 1/2, ε = 1, δ = 1/2 and K large;
then (112–113) holds, the run is deterministic with Q_T = η, and ‖Q_T − Q*‖∞ = η − 2 > ε, so the success
probability is 0. Proposed correction: add the hypothesis c_η K(1−γ)⁴ε² < log(SAKT/δ) (the printed η lies in (0,1)),
and γ ∈ (0,1). The corrected statement is cited (woo2023blessing), not proved in the monograph. Found by a source preflight and confirmed by an independent source check. Machine-checked in Lean (`Formalization/Federated/Sync/LargeStepRefutation.lean`: `not_thm7_9_at`, `not_thm7_9_printed`): false under the literal reading, in which the algorithm's input range η ∈ (0,1) (`:51`, `:76`) is not a hypothesis of the theorem; if that range is read as tacitly assumed, the theorem is vacuous for large K rather than false. Only K depends on the constants, so constants depending on (δ, ε, Q₀, τ, T, γ, S, A) but not on K are also refuted (by inspection, not formalized). The Lean Prop lets the probability space and sample law be chosen existentially, which only weakens the printed claim (the refutation is deterministic: the output is wrong on every sample path).

Corrected result (2026-11-08). `Thm7_9_corrected` (`Formalization/Federated/Sync/Main.lean`) proves the printed statement with exactly one added hypothesis, that the prescribed η is below 1 (c_η K(1−γ)⁴ε² < log(SAKT/δ)), under the true generative sampling law and with the true optimal Q-function, for universal constants c_η = 1/216 and c_T = 10⁴ (the reading "every sufficiently small c_η with c_T fixed" is not claimed). γ > 0 is kept as a definedness convention for the τ condition, and τ ∣ T is the source's standing convention (`:70`); the export uses neither. The proof is new and self-contained (the cited woo2023blessing was not used): per-agent noise processes with Azuma–Hoeffding give the linear speedup in K. Whether η < 1 is the minimal correction is not claimed. Independently plan-checked and source-reviewed. Not author-approved.

Read-off (2026-11-10). The per-agent sample size eq:sample-size-per-agent-fedQ (`federated_RL.tex:118–129`) is proved only in the K-range c_η K(1−γ)⁴ε² ≤ log(SAK/δ), i.e. where the prescribed η is at most 1 already at T = 1 (`Eq_sample_size_per_agent_fedQ_restricted`, `Formalization/Federated/Sync/PerAgentSampleSize.lean`, with explicit Õ = 270000216·(1 + log(SAK/(δε(1−γ)²)))³). Because the corrected theorem needs η ≤ 1 and η grows linearly in K, any horizon it certifies satisfies T ≥ δ·exp(c_η K(1−γ)⁴ε²)/(SAK) for every c_η > 0 (`horizon_ge_exp_of_eta_le_one`), so for K ≫ log(SAK/δ)/((1−γ)⁴ε²) the linear-speedup read-off does not follow from the theorem. It is not refuted: whether FedSynQ (with some other step size) attains it for such K is open. Not author-approved.

<a id="C42"></a>
## Candidate C42: Theorem 7.10 is vacuous in N as printed; the placement of c0 matters

**Classification (marker audit, 2026-11-11).** The statement is refuted only if "for some universal constant" is read inside the hypothesis; with the constant chosen first (the natural reading) the printed bound is proved for exact averaging (ledger kind `reading`).

In Theorem 7.10
(`federated_RL.tex:227–239`), C_round ≥ 1 (`federated_RL.tex:196`) and the hypothesis C_round ≤ c0/((1−γ)log²N)
force log²N ≤ c0/(1−γ). So N is bounded in terms of γ and the bound follows with C_γ exponentially small in that
bound, from the r ≡ 1 instance (error ≥ γ^T/(1−γ)). This is weaker than the discussion at `federated_RL.tex:244`.
If "for some c0" is read inside the hypothesis, the hypothesis is vacuous and the statement is false (full
synchronization with K → ∞ gives error ≤ (1−η(1−γ))^T/(1−γ)). Proposed reading: a universal c0 quantified first,
with an explicit C_γ. Found by a source preflight; the reading dependence was established by an independent source check. Machine-checked in Lean: under the c₀-first reading the printed bound is proved for the exact-averaging sub-class of the algorithm (`Thm7_10_restricted`, renamed from `Thm7_10` on 2026-11-09; `Formalization/Federated/LowerBound/UniversalConstant.lean`; the export `lowerBound_of_fewRounds` holds for every c₀, with C_γ = γ^{⌊exp √(c₀/(1−γ))⌋}/(1−γ), doubly exponentially small, so the discussion at `:242–248` is not established); under the inner-c₀ reading it is refuted (`not_thm7_10_innerConstant`, `Federated/LowerBound/InnerConstantRefutation.lean`). Only exact averaging is modelled; line `:196` places any distributed mean-estimation routine (including compression) in the generic algorithm class, so the entry is a restriction of the printed algorithm class and is counted as a restricted variant. Not author-approved.

<a id="C43"></a>
## Candidate C43: Theorem 7.11's covariance Γ omits the reward variance across actions

**Classification (marker audit, 2026-11-11).** The refutation holds under the reading r(s) = E_{a~π} r(s,a) of the undefined printed r(s); under state-only rewards or a deterministic policy the statement is neither proved nor refuted (ledger kind `reading`).

Γ_{s,s} (`inference.tex:115`) uses
an undefined r(s) and averages only over s′ ∼ P_π. With rewards r(s,a) (`inference.tex:62`) and r(s) = r_π(s), it
omits Var_{a∼π(·|s)} r(s,a). The book's own estimator Γ̂ (`inference.tex:166–169`) targets the per-sample noise
covariance. Example: S = 2, uniform μ and π, r(1,·) = (0,1), r(2,·) = 0, uniform P, γ = 1/2 gives
Γ_printed = diag(1/128, 1/128) and the true noise covariance diag(17/128, 1/128). Given the classical CLT, the convex
distance tends to at least 0.57, so the printed bound fails as T → ∞. Γ must also be nonsingular (it is 0 when S = 1).
Proposed correction: Γ_{s,s} = μ(s)E_{a∼π(·|s), s′∼P(·|s,a)}[(V^π(s) − r(s,a) − γV^π(s′))²], with Γ ≻ 0 assumed.
Found by a source preflight and confirmed by an independent source check. Not author-approved.

Machine-checked (2026-11-08, `Formalization/TDInference/ZeroNoiseRefutation.lean` and `Formalization/TDInference/AnyInitRefutation.lean`): Theorem 7.11 is false under the reading in which rewards depend on (s,a) as printed at `inference.tex:62` and the undefined r(s) in Γ is r_π(s) (`prelim.tex:418`). This holds whether the bound must hold for every initialization V₀ (`not_thm7_11_printed`; also with the constants c and C̃ chosen per instance, `not_thm7_11_printed_instWise`, and over all convex sets, `not_thm7_11_printed_allConvex`) or only for one V₀ chosen per instance, such as V₀ = 0 (`not_thm7_11_printed_someInit` with a universal c, and `not_thm7_11_printed_someInit_instWise` with V₀, c and C̃ all chosen after the instance, the weakest such reading). Instance: S = A = 2, γ = 1/2, μ and π uniform, s′ = a deterministically, r = (1/2, 3/4; 0, 1/4), η₀ = 1/8. Then V^π = (1, 1/2) and r(s,a) + γV^π(s′) = V^π(s) on every sample. From V₀ = V^π the TD iterates never move, so √T Δ̄_T = 0 surely. The printed Γ is diag(1/128, 1/128) ≻ 0 and A = diag(μ)(I − γP_π) is invertible (A⁻¹ = [[3,1],[1,3]]), so N(0, A⁻¹ΓA⁻ᵀ)({0}) = 0 and the convex distance is 1 at every T ≥ 1 (on the closed convex set {0}). From any other fixed V₀, the error satisfies E‖V_t − V^π‖² ≤ ‖V₀ − V^π‖² exp(−(3/8)η₀t^{1/3}), so E|(√T Δ̄_T)(0)| = O(T^{−1/2}). The data law therefore puts mass ≥ 1 − O(T^{−1/2}) on the closed convex slab {x : |x(0)| ≤ 1/20}, while the printed Gaussian gives it mass ≤ 4/(15√π) < 1/4, so the convex distance is ≥ 3/4 − O(T^{−1/2}) (`anyInit_violates`, for every V₀, every η₀ ∈ (0,1] and every real c, C̃). In both cases the printed right-hand side tends to 0 for any finite constants. No CLT is used. The example also shows that the printed Γ omits a cross term as well as the action-reward variance: Γ_true,ss = Γ_printed,ss + μ(s)[Var_a r(s,a) + 2γ Cov(r(s,a), V^π(s′))], and here Γ_true = 0 < Γ_printed. Not refuted by this example: the reading with state-only rewards (or deterministic π), where Γ_printed equals the true noise covariance, and the corrected statement (here Γ_true = 0, so it is vacuous). Independently critic-reviewed. Not author-approved.

**Scope note (2026-11-09).** The machine-checked refutation depends on the reading r(s) = r_π(s) with
action-dependent rewards; under state-only rewards (or deterministic π) the printed statement is neither proved nor
refuted. The corrected statement (Γ replaced by the true residual covariance, assumed nonsingular) was open as of
2026-11-09; it is now machine-checked over all convex sets with an instance constant (2026-11-10, see the all-convex
result below), by this project's own argument, and the cited proof may not transfer directly. With μ = (15/16, 1/16), γ = 3/4 and
both rows of P_π uniform, xᵀdiag(μ)(I−γP_π)x = −3/16 at x = (1,3), so a Euclidean accretivity estimate is
unavailable, although diag(μ)(I−γP_π) still has positive eigenvalues; this is a gap in applying the cited argument,
not a counterexample. Two further differences are **unverified**: the cited analysis (Wu et al.,
arXiv:2410.16106v6) appears to sample states from the stationary distribution, while the book allows any
full-support μ (`inference.tex:67`), and its covariance estimator appears to use the running averages, while the
book's Γ̂_T evaluates all residuals at V̄_T (`inference.tex:166–169`). These two points were read from a summary of
the cited paper, not from the cited version itself, and need a direct check. A corrected bound may still hold by
another argument. Paper calculation, not Lean-checked. Reported by an external review (2026-11-08), independently re-checked ([check](critic-audit-findings.md)). Not author-approved.

**Half-space result (2026-11-09, `Formalization/TDInference/HalfSpace.lean`, entry
`Thm7_11_corrected_halfspace`).** The corrected statement is machine-checked on closed half-spaces at the printed
rate. With Γ replaced by the true residual covariance Γ_true ≻ 0, for every full-support μ, 0 < η₀ ≤ 1 (the entry
states the printed 0 < η₀ < 1/4) and every V₀, there is an instance-, η₀- and V₀-dependent K with
sup_{u,b} |P(uᵀ√TΔ̄_T ≤ b) − N(0, A⁻¹Γ_trueA⁻ᵀ)(uᵀx ≤ b)| ≤ K·T^(-1/3) for all T ≥ 1.
The proof does not use the cited paper. It uses a Chen–Shao nonlinear Stein bound, leave-one-out TD estimates and
a Gaussian variance comparison, so it does not depend on the unverified stationarity and estimator differences
noted in the scope note above. It is implied by the all-convex result below and kept as a supporting entry.
Independently critic-reviewed ([review](critic-thm7-11-m9.md)). Not author-approved.

**All convex sets (2026-11-10, `Formalization/TDInference/ConvexSets/Sharp.lean`, entry `Thm7_11_corrected`).**
The corrected statement is machine-checked over all convex sets at the printed rate: with Γ_true ≻ 0, full-support μ,
0 < η₀ ≤ 1 (the entry states 0 < η₀ < 1/4) and every V₀, there is an instance-, η₀- and V₀-dependent K with
sup_{C convex} |P(√TΔ̄_T ∈ C) − N(0, A⁻¹Γ_trueA⁻ᵀ)(C)| ≤ K·T^(-1/3) for all T ≥ 1 (outer measure for non-Borel C).
Our own proof (randomized concentration over polyhedral representations of convex sets plus leave-one-out TD
estimates); it does not use the cited paper, so the unverified stationarity/estimator differences do not affect it.
Still open: the printed coefficient and polynomial C̃; the printed statement under the state-only-reward reading.
The printed statement remains refuted under the action-dependent-reward reading. Independently critic-reviewed
([review](critic-711-sharp.md); components: [N1/N2](critic-nolog-N1N2.md), [N3/N4](critic-nolog-N3N4.md)).
Not author-approved.

**Classic CLT display (2026-11-09, `Formalization/TDInference/ClassicCLT.lean`, `TDInference/ClassicCLTPrintedRefutation.lean`;
entries `Eq_classic_clt_corrected`, `Eq_classic_clt_restricted`).** The same Γ issue affects `eqn:classic-clt`
(`inference.tex:98–117`). Machine-checked: with r(s) = r_π(s) and action-dependent rewards, the display is false for the
step sizes η_t = η₀t^(-2/3), both for every η₀ ∈ (0,1/4) and every V₀ (`not_eq_classic_clt_printed`) and for some
η₀ ∈ (0,1] and some V₀ per instance (`not_eq_classic_clt_printed_someInit`). Witness: the zero-noise instance above with
the bounded continuous test min(1, |x(0)|), whose expectation under the data law is O(T^(-1/2)) while under
N(0, A⁻¹Γ_printedA⁻ᵀ) it is at least 3/80. The display is existential in the schedule; the Lean refutation covers this
family only. For V₀ = V^π the iterates never move under any schedule, so that reading fails for every schedule (paper
argument, not Lean-checked). "Some schedule and some V₀" over arbitrary schedules is not refuted. Proved: with Γ replaced
by Γ_true (no nonsingularity needed) the display holds for every η₀ ∈ (0,1] and every V₀; and with the printed Γ it holds
whenever r(s,·) is constant on the support of π(·|s) for every s, since then Γ_printed = Γ_true
(`trueGamma_eq_printedGamma_of_reward_const_on_support`). This settles the state-only-reward reading for the display
(not for Theorem 7.11's convex-distance bound). Independently critic-reviewed ([review](critic-classic-clt.md)). Not
author-approved.

**Plug-in estimator (2026-11-09; `Formalization/TDInference/PluginCovariance/PrintedLambdaRefutation.lean`,
`Formalization/TDInference/PluginCovariance/CorrectedConsistency.lean`; entries `Eq_defn_hat_Lambda_corrected`,
`Eq_defn_hat_Lambda_restricted`).** Under the reading with rewards r(s,a) and r(s) = r_π(s), Λ̂_T
(`eq:defn-hat-Lambda`, `inference.tex:180–182`) is not a consistent estimator of the printed Λ⋆ = A⁻¹ΓA⁻ᵀ (`:184`;
also `:172`, "estimator of Γ").
- In the C43 two-state instance from V₀ = V^π: Γ̂_T = 0 and Λ̂_T = 0 surely, for every T ≥ 1 and every η₀,
  while Λ⋆(0,0) = 5/64 (`not_eq_defn_hat_Lambda_printed_consistent`, with η₀ in the printed range (0, 1/4)).
- The refutation is independent of the junk inverse (`pathProb_far_nonsingular_ge`).
- From every V₀ and every η₀ ∈ (0,1], the far-event probability P(∃ s s′, |Λ̂_T(s,s′) − Λ⋆(s,s′)| > 1/64) tends
  to 1 in that instance (`tendsto_pathProb_lambdaHat_far_printed_one`), so the some-V₀ reading is refuted too
  (`not_eq_defn_hat_Lambda_printed_consistent_someInit`).

Proposed correction, machine-checked: Λ̂_T is consistent for Λ = A⁻¹Γ_trueA⁻ᵀ, entrywise in probability, for
full-support sampling, every η₀ ∈ (0,1] and every V₀, without Γ_true ≻ 0 (`eq_defn_hat_Lambda_corrected`).
- The convergence is qualitative, with no rate.
- The source's own commented-out definition (`:108`, not printed), Γ = E[(A_tθ⋆ − b_t)(A_tθ⋆ − b_t)ᵀ], equals
  diag(Γ_true) at θ⋆ = V^π.
- With state-only rewards or deterministic π, Γ_true = Γ_printed, and the printed reading holds
  (`eq_defn_hat_Lambda_restricted`).

Independently critic-reviewed ([review](critic-plugin.md), [round-2 review](critic-plugin-r2.md)). Not
author-approved.

<a id="C44"></a>
## Candidate C44: Theorem 7.12 is ill-posed at T = 1 and its VPO update may have no minimizer

In Theorem 7.12
(`RLHF.tex:208–215`), α divides by min{d log T, T} = 0 when T = 1. The online update (`RLHF.tex:194–198`) can be
unbounded below. Example: Y = {y1, y2}, d = 1, φ(y1) = 1, φ(y2) = 0, π_cal = π_ref uniform; along Gibbs policies with
θ → ∞ the objective tends to −∞ for any number of y1 ≻ y2 comparisons, including none. Hence π^{(t+1)} is undefined,
and the hypothesis ‖θ^{(t)}‖ ≤ r_max constrains iterates that need not exist. δ appears in neither the bound nor α.
Proposed correction: T ≥ 2, minimization over {θ : ‖θ‖₂ ≤ r_max}, and an explicit δ-dependence. The result is
cited (cen2025vpo), not proved in the monograph. Found by a source preflight and confirmed by an independent source check. Machine-checked in Lean (`Formalization/RLHF/VPO/IllPosed.lean`): the printed α formula is undefined at T = 1 (`vpoAlpha_T_one`, `not_vpoAlpha_T_one_pos`; Lean's 0 is the junk value of x/0), and the update has no minimizer over full-support policies (`no_vpoMinimizer`, `not_vpoUpdate_exists_printed`, `no_vpoMinimizer_gibbs`). Over the closed simplex with log 0 = −∞ the value −∞ is attained at a boundary policy that no real θ induces, so ‖θ^{(t)}‖ ≤ r_max fails; the status is ill-posed or vacuous, not false. Corrected result (2026-11-08): `Thm7_12_corrected` and `Thm7_12_corrected_local` (`Formalization/RLHF/VPO/*.lean`) prove, for finite context and response sets, linear Bradley–Terry rewards with ‖θ⋆‖ ≤ r_max, and the VPO update taken over Gibbs policies with parameter in the ball (a minimizer exists by compactness), that with probability ≥ 1−δ the realized regret is at most T·B′/α + K·Γ·α (order d√(κT) at tuned α), and also at most a local-curvature bound with √(dT) scaling for large T, for every α > 0 and T ≥ 1 with explicit constants. The printed Õ(e^{2r_max + r_max/β}√(κdT)) bound is neither proved nor refuted. The ball-selection rule extends any printed run whose argmin breaks ties deterministically from the data (an informal remark; only the dataset-level extension is checked). The update's sum starts at round 1 (`:196`), so the round-0 sample is unused. Proved from scratch (cen2025vpo not used); independently plan-checked and source-reviewed. Not author-approved.

<a id="C45"></a>
## Candidate C45: Theorem 7.6 fails (refuted in Lean) when the planning oracle may return any equilibrium

**Classification (marker audit, 2026-11-11).** The refutation holds if the planning oracle may return any equilibrium in the sense of the printed definitions; for causal oracles the statement is proved (ledger kind `reading`).

Theorem 7.6 (`marl.tex:384–399`) applies an unspecified planning oracle (`:377`) to the empirical Markov game and claims that the
returned Nash equilibrium (NE) and coarse correlated equilibrium (CCE) both have gap ≤ ε with probability ≥ 1 − δ once
N ≥ C₁H³ε⁻² log(SHN∏A_i/δ). The NE and CCE definitions constrain only step 1 (`:213–238`). If the oracle may return any such
equilibrium of the empirical game, the claim is false for every C₁. Machine-checked in Lean (`not_thm7_6_printed`, and separately for the NE-only and
CCE-only conclusions `not_thm7_6_printed_ne`, `not_thm7_6_printed_cce`; `Formalization/MultiAgent/ModelBased/PrintedRefutation.lean`): in a coordination game with S = 8N states, H = 2, ε = 1/4, δ = 1/2, an oracle whose output is a
step-1 product Nash equilibrium (hence also a CCE) of the empirical game for every data set has true gap ≥ 1/3 almost surely, while the printed
sample condition holds for every C₁ (at N = n², n = ⌈896C₁⌉ + 1). The same output is subgame-perfect and a two-player zero-sum example with a
dummy player gives gap ≥ 1 − 3N/K; these two points are source checks only, not in Lean. Proposed restriction:
a causal oracle, whose policy at step h depends only on the empirical kernels from step h onward (as in Nash value iteration or
backward per-stage LP/no-regret; compare the decoupling remark at `generative_model_model_based.tex:2549`); this is not claimed to be
the weakest. Separately, `N > 0` is an implicit convention (Lean's `log 0 = 0` would make the condition hold at N = 0).
Restricted result (2026-11-08): `Thm7_6_restricted` (C₁ = 400) proves the printed rate for causal oracles in three clauses (CCE-only, NE-only,
joint), adding the domain binders 0 < S, 0 < A_i, 0 < N. The CCE clause is shown non-vacuous in Lean by a causal backward-induction CCE planner
(stage-CCE existence via Hahn–Banach separation). For two-player constant-sum games the NE and joint clauses are also non-vacuous in Lean (the
product of the marginals of that planner is a causal exact Nash equilibrium oracle, `exists_causalNEOracle_constSum`; 2026-11-10,
[review](critic-thm76b.md)). For general-sum two-player games and games with three or more players, Nash existence is not in the pinned
Mathlib, so the NE and joint clauses are proved for every causal NE oracle but not shown non-vacuous in Lean. Independently plan-checked and source-reviewed. Not author-approved.

<a id="C46"></a>
## Candidate C46: regret-to-PAC conversion has the wrong constant `C_{S,A,H+1}`

**Classification (marker audit, 2026-11-11).** The refutation uses a constant C_{S,A,H} that is not nondecreasing in H; for constants nondecreasing in H the printed form holds, and the C_{S,A,H} version is proved (ledger kind `reading`).

Source: `eq:PAC-from-regret-conversion` (`-regret`, `-pac`) and `eq:uniform-policy-pihat`,
`chapters/onlineRL.tex:113–141` (labels :116, :122, :129, :138), proof :145–183; protocol
`eq:generation-s1k-shk-online` :17–41; known reward :20, rewards in [0,1] `prelim.tex:682–683`.

**Printed claim.** If an online algorithm satisfies `E[Regret(K)] ≤ C_{S,A,H} K^{1−α}` for any MDP with S states,
A actions and horizon H, and `π̂ ~ Unif(π¹,…,π^K)`, then w.p. ≥ 1−δ,
`V₁⋆(ρ) − V₁^{π̂}(ρ) ≤ C_{S,A,H+1} K^{−α} δ^{−1}`.

**Counterevidence (machine-checked).** Primary: `StatisticalRL.OnlineRL.RegretToPAC.not_Eq_PAC_from_regret_conversion_printed`
(Prop `Eq_PAC_from_regret_conversion_printed`): one algorithm family on every finite carrier pair, the regret
hypothesis for every carrier pair, H > 0, K > 0, MDP and ρ, and strictly positive constants. Secondary:
`not_Eq_PAC_from_regret_conversion_printed_fixedCarrier`, whose hypothesis covers only the instance's carriers
(the fixed-class reading).
- Algorithm: deterministic and seedless (it ignores the seed, K, the history and the carriers), so the restricted
  algorithm class of the Lean propositions (finite seed, deterministic deployed policies) does not weaken the
  refutation; it only weakens the refuted proposition. It knows H and the reward and plays a reward-minimizing
  action when H = 1 and a reward-maximizing action at every step otherwise.
- Hypothesis: with one state, myopic play is optimal, so the regret is ≤ 0 for H ≥ 2; otherwise it is ≤ KH since
  rewards lie in [0,1]. So the hypothesis holds on every class with α = 0 and the strictly positive constants
  `C_{1,A,H} = 1/4` (H ≠ 1), `C_{S,A,H} = H + 1` otherwise.
- Instance: S = 1, A = 2, H = 1, r = (1, 0), K = 1, δ = 1/2. Every deployed policy has gap 1, but the printed
  conclusion requires gap ≤ `C_{1,2,2}/δ = 1/2` with probability ≥ 1/2.
- More generally, with `C_{1,2,H} = η` for H ≥ 2 the claim fails for every δ ∈ (η, 1).
- The refutation exploits a constant that is **not monotone in H** (`C_{1,2,2} = 1/4 < 2 = C_{1,2,1}`,
  `printedCexConst_two_lt_one`) together with deliberately bad H = 1 behaviour. The construction uses the
  known-reward convention (`onlineRL.tex:20`, `prelim.tex:682–683`) and rewards in [0,1]; whether the printed
  constant fails with unknown rewards is not determined here.

**Proof flaws.** (1) Run identity: the statement's π̂ comes from the run on the given MDP; the proof applies the
algorithm "to the augmented MDP without modification", so its π̂ comes from a different run (the augmented-run
reading is a proof artifact, not a reading of the statement). (2) A fresh state s₀ gives S+1 states and hence
`C_{S+1,A,H+1}`; the augmented MDP stays in the class only if s₀ reuses an existing state. (3) "a single action
a₀" must be read as A identical actions to stay in the class with A actions.

**The augmentation is unnecessary.** Under protocol (i)–(ii), `s₁ᵏ` is independent of `πᵏ`
(`onlineEpisode_startState_independent`), so Markov's inequality on the uniform mixture gives the bound with the
constant at the actual (S, A, H).

**True versions (Lean, statement index Ch5).**
- `Eq_PAC_from_regret_conversion_corrected`: constant `C_{S,A,H}`; regret hypothesis only at the instance; direct
  proof.
- `Eq_PAC_from_regret_conversion_restricted`: printed constant `C_{S,A,H+1}` under `C_{S,A,H} ≤ C_{S,A,H+1}`
  (C nondecreasing in H), which covers the book's Õ(√(SAH³K)) use (:184–198).

**Scope.** Both true versions cover finitely supported internal randomness and deployed policies that are
deterministic Markov given the seed and the completed history; randomized πᵏ (:35–38) are not covered.
`δ > 0` only, as printed. The follow-up at :184–198 (δ = 1/log(SAH), K = Θ̃(SAH³/ε²), and the slip `V₁⋆(s)` for
`V₁⋆(ρ)`) is not covered. Independently plan-checked, critic-reviewed and the primary refutation separately reviewed ([review](critic-regret-pac.md), [refutation review](review-regret-pac-all-carriers.md)). Not
author-approved.

<a id="C47"></a>
## Candidate C47: Chapter 7 confidence sets: data-selected convex sets, rectangle scaling, ellipsoid radius, singular plug-in

**Classification (marker audit, 2026-11-11).** The failure of "any convex set" holds only if the set may be chosen from the data (ledger kind `reading`); the rectangle scaling slip is a separate item that fails as printed.

**Source:** `\subsection{Statistical inference}` (`sec:inference`), `chapters/inference.tex:150–213`: plug-in
estimators `:156–185` (Λ̂_T = Ā_T⁻¹Γ̂_TĀ_T⁻ᵀ, `eq:defn-hat-Lambda` `:180–182`), confidence-set rule
`eq:convex.Cdelta` `:187–196` (display `:191–193`, claim `:196`), rectangles `:198–205`, ellipsoids `:207–213`;
sampling model `eq:iid-samples`
`:49–64`. Pinned chapter SHA-256: `82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2`.

**(1) Arbitrary data-selected convex sets.** The text says it suffices to choose any convex set with conditional
mass ≥ 1−α under N(V̄_T, Λ̂_T/T), and that Theorem 7.11 makes such sets approximate confidence regions (`:189–196`).
This fails even for an exactly Gaussian estimator with known variance. Witness: X ~ N(θ,1/T), z = Φ⁻¹(1−α),
0 < α < 1/2; choose [X − z/√T, ∞) if X ≥ 0 and (−∞, X + z/√T] otherwise. Both sets are convex with conditional mass
exactly 1−α, but at θ = 0 the coverage is P(|√T X| ≤ z) = 1−2α for every T. In the book's own TD model (one
state, π uniform over two actions with rewards 0 and 1, γ = 1/2), V^π = 1, Ā_T = 1/2, the true residual variance is
1/4, Λ̂_T → 1, and the same sign-selected half-lines with radius z√(Λ̂_T/T) have limiting coverage 1−2α, given the
scalar Polyak–Ruppert CLT and Slutsky's lemma (not formalized). The fixed-set bound of Theorem 7.11 is applied to a
set chosen from the same data. This item holds under either reward reading of [C43](#C43).

**(2) Rectangles.** R̂ is the ℓ∞ quantile under covariance Λ̂_T/T (`:205`), and the half-width is R̂/√T (`:202`), so
the √T scaling is applied twice: the half-width is O(1/T). Even with oracle covariance and exact Gaussian errors
(S = 1, Λ = 1, α = 0.05) the coverage is 2Φ(1.96/√T) − 1 → 0 (0.16 at T = 100). The printed set violates
`eq:convex.Cdelta` for T > 1.

**(3) Ellipsoids (confirmed with changes).** The Mahalanobis statistic is compared with R², where R is the 1−α
quantile of χ²(d) (`:210–213`). The printed set has reference mass F_{χ²_d}(R²). The external review's transcription
point is correct, but its consequence differs by α: for conventional α (R ≥ 1) the set is over-conservative (mass
0.9999 at d = 1, α = 0.05) and still satisfies `eq:convex.Cdelta`; it falls below 1−α only when R < 1, i.e.
α > 0.317 for d = 1 or α > 0.607 for d = 2 (d = 1, α = 1/2 gives mass 0.351). Also, `d` is undefined in the chapter
(the dimension is S), and Λ̂_T⁻¹ needs Λ̂_T ≻ 0.

**(4) Singular plug-in.** Row s of Ā_T is zero when state s is unsampled, an event of probability (1−μ(s))^T > 0
for S ≥ 2 (for example 2^{−T} for uniform μ and S = 2), so Λ̂_T (`:181`) is undefined there. If every state is
sampled, Ā_T is strictly diagonally dominant and invertible.

**Scope.** (1) applies to the general rule `eq:convex.Cdelta`; (2)–(4) to the literal printed formulas. Theorem
7.11 itself is not affected by this entry (see [C43](#C43)), and no Lean result is contradicted: the proved
smooth-test partial result makes no confidence-region claim.

**Proposed correction:** prescribe a confidence rule whose shape given the pivot is fixed (for example
V̄_T + T^{-1/2}Λ̂_T^{1/2}K with K a fixed convex set of standard-Gaussian mass 1−α), prove its coverage with a
covariance-perturbation bound, use half-width R̂ (not R̂/√T) in (2) and threshold R (not R²) in (3), and define the
procedure on the singular event in (4) and charge that event's probability.

The Gaussian-estimator witness is a paper calculation; the TD-model limit is now machine-checked (see below). Reported by an external review (2026-11-08), independently re-checked ([check](critic-audit-findings.md)). Not author-approved.

**Lean evidence for (1), oracle covariance (2026-11-09, `Formalization/TDInference/Confidence/HalfLineEvidence.lean`).**
In the one-state TD instance of (1) (π uniform over rewards 0 and 1, γ = 1/2: V^π = 1, Γ_true = 1/4, A = 1/2, oracle
Λ = 1, all machine-checked), the sign-selected half-lines `[V̄_T − z/√T, ∞)` if V̄_T ≥ 1 and `(−∞, V̄_T + z/√T]`
otherwise are convex (`convex_signSel`), read only the data, and each has mass exactly Φ(z) = 1 − α under
N(V̄_T, Λ/T) (`gaussianReal_signSel`). Their coverage is within 2K·T^(-1/3) of 2Φ(z) − 1 = 1 − 2α
(`oneState_signSel_coverage`, from the half-space Theorem 7.11 result, no CLT), and is eventually at most
Φ(z) − (1 − Φ(z))/2 < 1 − α for every z ≥ 0 (`oneState_signSel_coverage_eventually_lt`). The rule's threshold 1
equals V^π of this instance, as the paper witness's threshold 0 equals θ; this suffices because the printed claim is
universal over such sets. Scope: oracle Λ, not the printed Λ̂_T; the Λ̂_T version additionally needs consistency of
Λ̂_T (in this model Ā_T = 1/2 surely, so Λ̂_T = 4Γ̂_T). Line locators in this entry were corrected against the pin
(2026-11-09): rule :187–196 (display :191–193, claim :196), rectangles :198–205, ellipsoids :207–213, plug-in
:156–185, `eq:defn-hat-Lambda` :180–182. Independently critic-reviewed ([review](critic-confint.md)). Not
author-approved.

**Lean evidence for (1), printed plug-in Λ̂_T (2026-11-10, `Formalization/TDInference/Confidence/HalfLinePluginEvidence.lean`).** On the same one-state instance, for every 0 < η₀ ≤ 1, every V₀ and every z ≥ 0 (α = 1 − Φ(z)), the half-lines [V̄_T − z√(Λ̂_T/T), ∞) if V̄_T ≥ 1 and (−∞, V̄_T + z√(Λ̂_T/T)] otherwise are convex, functions of (V̄_T, Λ̂_T) only, and have mass ≥ 1 − α under the printed N(V̄_T, Λ̂_T/T) (exactly 1 − α when Λ̂_T > 0; when Λ̂_T = 0 the Gaussian is the point mass at V̄_T, mass 1). Their coverage tends to 2Φ(z) − 1 = 1 − 2α and is eventually at most Φ(z) − (1 − Φ(z))/2 < 1 − α (`c47_convex_dataSelected_undercovers_plugin`), via the plug-in two-sided limit (`oneState_tendsto_twoSided_plugin`; consistency of Λ̂_T, no CLT/Slutsky beyond the machine-checked half-space bound). This replaces the paper calculation for the TD-model part of (1); it is asymptotic only, with no rate. Independently critic-reviewed ([review](critic-c47p.md)). Not author-approved.

**Fixed-shape correction, oracle covariance (2026-11-09, `Formalization/TDInference/Confidence/Intervals.lean`, entry
`Eq_convex_Cdelta_corrected_oracle`).** The proposed correction is machine-checked for fixed shapes with the oracle
covariance Λ = A⁻¹Γ_trueA⁻ᵀ (Γ_true ≻ 0), as corollaries of the half-space result of [C43](#C43): for a direction u
and level z fixed before the data, the one-sided interval for uᵀV^π has coverage within K·T^(-1/3) of Φ(z), the
two-sided interval (z ≥ 0) within 2K·T^(-1/3) of 2Φ(z) − 1, and the Bonferroni box of half-widths z√(Λ_ss/T) has
coverage at least 1 − 2S(1 − Φ(z)) − 2SK·T^(-1/3), with one instance constant K. Still open at this paragraph: the plug-in Λ̂_T rule
(a covariance-perturbation coverage bound, now proved: see the finite-T rate paragraph below), (2), (3) and (4).
[Superseded in part by the later addenda below: the plug-in rule's coverage limits, consistency of Λ̂_T, and Lean
evidence that the printed rectangle (2) fails on one instance are now proved; see the plug-in and (2) addenda.]
Independently critic-reviewed ([review](critic-confint.md)). Not author-approved.

**Machine-checked for (4) (2026-11-09, `Formalization/TDInference/PluginCovariance/Singular.lean`).** Ā_T
(`inference.tex:166`) is invertible iff every state is sampled (`aBar_det_ne_zero_iff`; the forward direction is a
zero row, the converse is strict diagonal dominance with margin T⁻¹(1−γ)n_s). Under the i.i.d. law,
(1−μ(s))^T ≤ P(Ā_T singular) ≤ ∑_s(1−μ(s))^T (`pathProb_aBar_singular_ge`, `pathProb_aBar_singular_le`), so the
probability is positive for every T when S ≥ 2 (`pathProb_aBar_singular_pos`). In the two-state uniform instance it
is ≥ 2^{−T} (`zAbar_singular_ge`). The printed Λ̂_T (`eq:defn-hat-Lambda`, `:180–182`) is undefined there. Line
references in this item: estimators `:165–169`, display `:180–182`. Consistency is not prevented:
P(Ā_T singular) ≤ ∑_s(1−μ(s))^T → 0, and the corrected consistency theorem (`eq_defn_hat_Lambda_corrected`) holds
with Lean's junk value 0. The procedure is still undefined on that event for finite T, so any confidence rule must
define it there and charge that event's probability. Independently critic-reviewed ([review](critic-plugin.md),
[round-2 review](critic-plugin-r2.md)). Not author-approved.

**Fixed-shape correction, plug-in covariance (2026-11-09, `Formalization/TDInference/PluginCovariance/Coverage.lean`,
entry `Eq_convex_Cdelta_corrected_plugin`).** The proposed correction is machine-checked with the printed estimator
Λ̂_T = Ā_T⁻¹Γ̂_TĀ_T⁻ᵀ, asymptotically. For a direction u and level z fixed before the data, under full-support i.i.d.
sampling, 0 < η₀ < 1/4, every V₀ and Γ_true ≻ 0:

- the one-sided interval has coverage → Φ(z);
- the two-sided interval (z ≥ 0) has coverage → 2Φ(z) − 1;
- the Bonferroni box with half-widths z√(Λ̂_T(s,s)/T) has coverage eventually ≥ 1 − 2S(1 − Φ(z)) − η for every
  η > 0.

The limits are pointwise in (u, z), not uniform. Γ_true ≻ 0 is an added non-degeneracy hypothesis (it gives
uᵀΛu > 0 and is needed by the half-space result). The proof sandwiches the random threshold between deterministic
half-spaces off the event where Λ̂_T is entrywise far from A⁻¹diag(Γ_true)A⁻ᵀ. It uses the half-space result of
[C43](#C43) and the corrected consistency `eq_defn_hat_Lambda_corrected`. No rate is given.

For (4): Lean's convention Λ̂_T = 0 on the singular event (a degenerate interval) does not affect the limits.
Because that event has vanishing probability, any definition there gives the same asymptotic coverage. The printed
procedure is still undefined there for finite T.

A rate was open at this paragraph; see the finite-T rate paragraph below for the plug-in rate. (3) and the Λ̂_T version of (1) were settled later (paragraphs below); (2) now has Lean evidence of failure on one
instance (next paragraph), and its finite-T figures remain paper calculations. Independently critic-reviewed
([review](critic-pluginD.md)). Not author-approved.

**Lean evidence for (2) (2026-11-09, `Formalization/TDInference/Confidence/PrintedRectangleEvidence.lean`).** On the
one-state instance of (1) (S = 1, oracle Λ = 1; all 0 < η₀ ≤ 1, which contains the printed range
0 < η₀ < 1/4 of `:133`, and all V₀), the printed rectangle `∏_s [V̄_T(s) − R̂/√T, V̄_T(s) + R̂/√T]`
(`:201–203`), with R̂ any number at most the lower (1−α)-quantile of `‖X‖∞`, X ~ N(0, covariance/T)
(`:205`), has coverage tending to 0, for every 0 < α < 1, both with the oracle covariance Λ
(`C47_rectangle_printed_undercovers`, via the bound coverage ≤ 2Φ(z/√T) − 1 + 2K·T^(-1/3) for any z ≥ 0
with 2Φ(z) − 1 ≥ 1 − α, `oracleRectangle_coverage_le`, a corollary of the half-space result, no CLT) and with
the printed plug-in Λ̂_T taken pathwise (`C47_rectangle_printed_undercovers_plugin`, via the plug-in two-sided
limit and consistency of Λ̂_T; qualitative, no rate). The quantile hypotheses are satisfiable: R = z√v is the
exact lower quantile for every variance v ≥ 0, including the point mass v = 0
(`exists_oracle_rectangle_quantile`, `exists_plugin_rectangle_quantile`). For S = 1 the ℓ∞ quantile is the
two-sided Gaussian quantile; nothing about the S-dimensional ℓ∞ quantile is formalized, and one instance
suffices to refute the printed general claim. The finite-T figures in (2) (coverage 2Φ(1.96/√T) − 1, 0.16 at
T = 100, violation of `eq:convex.Cdelta` for T > 1) remain paper calculations. Independently critic-reviewed
([review](critic-c47r.md)). Not author-approved.


**Corrected rectangle and ellipsoid, oracle covariance (2026-11-10, `TDInference/Confidence/Regions.lean`, entries `Eq_convex_Cdelta_fixedShape_corrected_oracle`, `Eq_convex_Cdelta_ellipsoid_corrected_oracle`, `Eq_convex_Cdelta_rectangle_corrected_oracle`).** The proposed corrections of (2) (√T applied once: half-width r/√T with r an ℓ∞ level under Λ) and (3) (threshold q, not R²), and the fixed-shape rule V̄_T + T^(-1/2)K, are machine-checked with the oracle Λ = A⁻¹Γ_trueA⁻ᵀ (Γ_true ≻ 0): coverage is within K₀T^(-1/3) of the Gaussian mass, with one instance constant (rate strengthened 2026-11-10 from K₀T^(-1/3)log(2T) via the all-convex bound behind `Thm7_11_corrected`; `TDInference/Confidence/RegionsSharp.lean`, exports `*_sharp`). Exact 1−α calibration of these corrected oracle shapes is machine-checked as well (`TDInference/Confidence/Calibration.lean`, entries `Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated`, `Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated`): for every α ∈ (0,1) Gaussian levels q_α, r_α with N(0,Λ)-mass exactly 1 − α exist, and the corrected ellipsoid and rectangle cover with probability within K₀T^(-1/3) of 1 − α (one instance constant, independent of α) ([review](critic-confcalib.md)). The χ²(S) identification for the corrected ellipsoid is machine-checked too (`Formalization/Probability/ChiSquaredQuadForm.lean`, `TDInference/Confidence/ChiSquareQuantile.lean`, entry `Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared`): N(0,Λ){xᵀΛ⁻¹x ≤ q} is the χ²(S) cdf at q, so with threshold R equal to the χ²(S) (1−α)-quantile (R itself, not the printed R², confirming correction (3)) the oracle ellipsoid covers within K₀T^(-1/3) of 1 − α ([review](critic-chisq.md)). The rectangle level r_α is not identified with the printed ℓ∞-quantile formula. Still open: the plug-in Λ̂_T versions with a rate and the ℓ∞-quantile identification of the rectangle level. [Independent review](critic-confregion.md). Not author-approved.

**Lean evidence for the corrected ellipsoid with the printed plug-in Λ̂_T (2026-11-10, `Formalization/TDInference/PluginCovariance/Ellipsoid.lean`).** For full-support μ, 0 < η₀ ≤ 1, every V₀ and Γ_true ≻ 0: P(T(V^π − V̄_T)ᵀΛ̂_T⁻¹(V^π − V̄_T) ≤ R) → 1 − α for every χ²(S) (1 − α)-quantile R (`tendsto_coverage_ellipsoid_plugin_chiSquared`; for general q, → F_{χ²(S)}(q)). This is asymptotic only at this paragraph (rate: see the finite-T paragraph below). The singular-Ā_T junk value (C47(4)) lies in a vanishing-probability event. Independently critic-reviewed ([review](critic-pluginregion.md)). Not author-approved. The plug-in ℓ∞ rectangle with a random level (C47(2)) is now proved asymptotically (next paragraph); a rate remains open.

**Corrected rectangle with the printed plug-in Λ̂_T (2026-11-10, `Formalization/TDInference/PluginCovariance/Rectangle.lean`).** For full-support μ, 0 < η₀ ≤ 1, every V₀, Γ_true ≻ 0 and α ∈ (0,1): for every random level r̂_T that is, outcome by outcome, a (1−α)-quantile of ‖X‖∞ with X ~ N(0, Λ̂_T) (N(0,Σ) := law of QZ, QQᵀ = Σ; Λ̂_T is always PSD), the rectangle ∏_s[V̄_T(s) ± r̂_T/√T] has coverage → 1 − α (`tendsto_coverage_rect_plugin`; concrete lower quantile `tendsto_coverage_rect_plugin_quantile`). With R̂ the quantile under Λ̂_T/T as printed, R̂ = r̂_T/√T (scaling; not formalized), so this is the proposed correction 'half-width R̂ (not R̂/√T)'. Asymptotic only at this paragraph; the finite-T rate is in the paragraph below. Independently critic-reviewed ([review](critic-pluginrect.md)). Not author-approved.

**Plug-in Λ̂_T with a finite-T rate (2026-11-10; `TDInference/PluginCovariance/IntervalRate.lean`, `TDInference/PluginCovariance/EllipsoidRate.lean`, `TDInference/PluginCovariance/RectangleRate.lean`; via `TDInference/PluginCovariance/Rate.lean`, P(∃ s s′, ε < |Λ̂_T − Λ|) ≤ C/(ε²T) for 0 < ε ≤ 1).** For full-support μ, 0 < η₀ ≤ 1 (containing the printed (0, 1/4)), every V₀ and Γ_true ≻ 0, with ε = T^(-1/3): one instance constant K (independent of T, u, z) bounds by K·T^(-1/3) the coverage error of the plug-in one-sided and two-sided intervals for every u ≠ 0 and z, and the Bonferroni box loses at most K·T^(-1/3); the corrected plug-in ellipsoid (threshold q, all real q; χ²(S) quantile R, not R²) is within K·T^(-1/3) of F_χ²(S)(q), resp. 1 − α, with K independent of T, q, α, R; the corrected plug-in ℓ∞ rectangle (half-width r̂_T/√T, any per-outcome (1−α)-quantile r̂_T under Λ̂_T) is within K_α·T^(-1/3) of 1 − α, where K_α depends on α through min(α, 1−α) and on the instance, not on T or the quantile choice. The junk value on the singular event lies inside the charged bad event. Instance constants, not printed coefficients. Still open: (a) arbitrary or data-selected C_α (C47(1), refuted in general; no positive result beyond fixed shapes); (b) the printed rectangle scaling R̂/√T (refuted) and the formal identification R̂ = r̂_T/√T (Gaussian scaling, not formalized); (c) the ℓ∞-quantile identification of the oracle level r_α; (d) a finite-T definition of the printed procedure on the singular event (C47(4); only charged or convention-independent); (e) printed coefficients, explicit dependence of K on the instance, uniformity of K_α as α → 0 or 1, any rate better than T^(-1/3); (f) the printed Λ⋆ under action-dependent rewards (C43). Independently critic-reviewed ([review](critic-pluginrate345.md)). Not author-approved.

**Quantified irrelevance of the convention on the singular event, C47(4) (2026-11-10, `Formalization/TDInference/Confidence/SingularConvention.lean`).** For any two confidence procedures agreeing whenever Ā_T is invertible, |P(V in C1) − P(V in C2)| ≤ P(Ā_T singular) ≤ ∑_s (1−μ(s))^T ≤ S ρ^T (ρ = max_s(1−μ(s)) < 1 under full support). Hence for the plug-in two-sided interval, coverage → 2Φ(z) − 1 for every convention on the singular event (`tendsto_coverage_twoSided_plugin_anyConvention`). The printed procedure remains undefined on that event; the gap is not repaired, only shown asymptotically immaterial. Independently critic-reviewed ([review](critic-c47s.md)). Not author-approved.

<a id="C48"></a>
## Candidate C48: Theorem 5.10 fails under the literal MVP trigger

**Classification (marker audit, 2026-11-11).** The refutation holds only under the literal consecutive-integer reading of the trigger set, which we regard as a typesetting ambiguity; under the doubling reading no counterexample is claimed (ledger kind `reading`).

**Source:** Theorem 5.10 (`thm-mvp-regret`, `chapters/onlineRL.tex:1339–1352`); Algorithm `alg:main-mvp`
(`:1256–1310`), trigger `line:trigger-set-mvp` `:1280`, stored count and reset `:1281–1285`, clipped update
`eq:updateq-mvp` `:1298–1300`, greedy step `:1268`; bonus `eq:bh-defn-Bernstein-ucbvi` (`:407–417`); allocations
`:416` and `:1386–1390`; doubling prose `:1215`. Pinned chapter SHA-256:
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The displayed trigger `{1,2,…,2^{log₂K}}` contains every count up to K, while the prose (`:1215`) describes powers
of two ([C13](#C13)). Under the literal reading the main regret bound is false. **Witness:** S = H = 1, A = 2,
rewards 0 and 1, deterministic transitions, δ = 1/2. The algorithm specifies only argmax; the tie Q = (H, H) is
permanent (see below), so the run is pure tie-breaking, and for every deterministic tie rule the instance is labelled
so that the rule's choice is the reward-0 action. Every visit triggers and resets the batch, so that
action's stored count is always 1. Since V_{H+1} = 0, its updated score is min{c₂ log(1/δ′), 1} = 1 as soon as
c₂ log(1/δ′) ≥ 1, which holds for all large K under both printed allocations δ′ = δ/(100S²A²H²K²) (`:416`) and
δ′ = 100δ/(S²A²H²K²) (`:1390`), for every c₂ > 0. The unvisited action has the undefined zero-count bonus
([C8](#C8)); every completion that respects the clip at H gives it score at most 1. So the reward-0 action is played
in every episode and Regret(K) = K surely, contradicting Õ(min{√(SAH³K), HK}) = Õ(√K) for large K, for every choice
of c₁, c₂ > 0.

**Status:** confirmed false under the literal trigger reading ([C13](#C13)); machine-checked as
`OnlineRL.not_Thm5_10_literalTrigger_printed` (`Formalization/Online/Regret/MVP/Thm510LiteralRefutation.lean`), with the
per-rule form `not_Thm5_10_literalTrigger_printed_rule` (every fixed deterministic tie rule fails). Witness S = H = 1,
A = 2, δ = 1/2, large K: every visit triggers with batch size 1, the bonus c₂·H·log(1/δ′) never decays, all clipped
scores saturate at H, so the run is pure tie-breaking; for every deterministic argmax tie rule, relabelling its tie
choice as the reward-0 action gives regret exactly K surely (`thm510Literal_regret_eq`), contradicting
C·polylog·√(SAH³K). Independent of the zero-count completion (C8) and of the reading of log₂K. Relies on c₁, c₂ being
universal (printed): the refutation needs c₂ independent of K. Uniform random tie-breaking (regret about K/2 with high
probability) and history-dependent tie rules are not machine-checked. The dyadic reading is the corrected theorem
`MVP_regret_corrected`.

**Scope.** The refutation is for the algorithm as printed, with unspecified deterministic ties: a fixed tie rule
avoids failure only on instances labelled in its favour, and every deterministic rule fails on the relabelled
instance. Not affected: the dyadic-trigger corrected theorem `MVP_regret_corrected`
(power-of-two trigger, one fixed tie rule), and C13's Lean refutation of the auxiliary Lemma 5.12 bound.

**Proposed correction:** read the trigger as the prose's powers of two, `{1, 2, 4, …, 2^{⌊log₂K⌋}}`, as the
formalization does ([C13](#C13)). Under that reading, together with the other disclosed corrections (C8, C12, C15,
C16, C17 and one fixed tie rule), the bound is proved as `MVP_regret_corrected`.

Machine-checked (2026-11-10); independently critic-reviewed ([review](critic-mvp510.md)).
Reported by an external review (2026-11-08), independently re-checked ([check](critic-audit-findings.md)). Not author-approved.

<a id="C49"></a>
## C49: scope disclosure for `Thm3_2_burnInNecessary_restricted` (burn-in necessity)

**Source:** prose claim after `eq:sample-size-range-planning`, `chapters/generative_model_model_based.tex:930–940`
(claim at `:939`). This is a scope disclosure for a restricted statement-index entry, not a refutation.

`Thm3_2_burnInNecessary_restricted`: the book's "strictly better than a random guess" (MB:939) is undefined. The
entry reads it as failure probability ≥ 1/4 of value gap ‖V⋆ − V^{π̂}‖∞ > 1/(64(1−γ)) when N ≤ log(SA)/(8(1−γ));
accuracies between 1/(64(1−γ)) and 1/(1−γ) are not covered. Restrictions inherited from `Thm3_7_corrected`: S ≥ 2,
A ≥ 2, SA ≥ 16, γ ∈ [2/3,1), deterministic (non-randomized) learners returning deterministic policies (the learner is
also given the true rewards and discount, which only strengthens the bound). V⋆ is the optimal value (greedy-policy
value; tie-independent). Q-to-V transfer: ‖Q^π − Q^{π'}‖ ≤ γ‖V^π − V^{π'}‖.

Lean: `StatisticalRL.GenerativeLowerBound.burnIn_necessary_valueGap` (`Formalization/Generative/BurnInNecessity.lean`);
the entry's universal constant is c = 1/8. Independently critic-reviewed ([review](critic-p2.md)). Not author-approved.

<a id="C50"></a>
## C50: Bernstein-penalty LCB-Q sample size is not formalizable as stated (open)

**Source:** `eq:sample-size-LCBQ-bernstein`, `chapters/offlineRL.tex:1776–1789` (display `:1781–1783`), after
Theorem 6.8 (`theorem:lcbq`, `:1754–1772`). Pinned chapter SHA-256 prefix `67cf0d1ce6a3`.

The book says that if a Bernstein-style penalty replaces the Hoeffding-style penalty, the sample complexity of
LCB-Q "can be further improved to" Õ(SC⋆/((1−γ)⁴ε²)) "for sufficiently small ε", and that for near-expert data
(C⋆ ≤ Õ(1)) it reduces to Õ(S/((1−γ)⁴ε²)). This claim cannot be formalized as stated:

1. No Bernstein-style penalty is defined for LCB-Q. The book defines Bernstein-style penalties only for the
   model-based VI-LCB (`def:bonus-Bernstein-infinite`, `:808–824`) and the UCBVI/MVP bonus
   (`eq:bh-defn-Bernstein-ucbvi`, `chapters/onlineRL.tex`); both use empirical variances of an estimated
   transition model, which LCB-Q does not maintain. For LCB-Q only the Hoeffding-style penalty
   `eq:stepsize-penalty-offlineQ` (`:1666–1687`) is specified; the constants and variance estimate of a
   Bernstein variant, and any change to its learning rate, are not given.
2. "For sufficiently small ε" gives no threshold, so the range of ε the rate claims is unspecified.
3. The sentence has no citation of its own. Theorem 6.8 is attributed to Yan et al. (2022) in its header, and the
   citations at `:1799` are for the variance-reduced variant, a different claim. So it is not recorded as a cited
   result out of scope.
4. The proved corrected Theorem 6.8 (`Thm6_8_corrected`, Hoeffding penalty) gives a (1−γ)⁻⁵ dependence. It does
   not imply the (1−γ)⁻⁴ rate.

Formalizing it would require the project to choose a Bernstein-style LCB-Q (for example from the literature) and
its constants, i.e. to decide which algorithm the authors meant. **Status: open** source-fidelity finding. Recorded
by user decision 2026-11-09 as not formalizable as stated, pending the authors naming the intended algorithm. No
Lean statement, proof or refutation. Not author-approved. COVERAGE row: "Bernstein-penalty LCB-Q sample size".


---------------------------------------------------------------------------------------------------


Note to C16 (Claim 5.1, `claim:PV-l-UB`, onlineRL.tex:4340–4353, 2026-11-07): `Claim5_1_corrected` uses the
reciprocal allocation `δ′ = δ/(100S²A²H²K²)`. For this claim (with the learner's own value family) the printed
allocation is neither proved nor refuted here; C16 refutes only the generic Lemma 5.13 allocation. The printed proof
is also incomplete at level `l = 1`: it applies Lemma 5.13 at `l = 1` (:4464), but that lemma covers only
`2 ≤ l ≤ log₂K + 1`. The formal proof treats `l = 1` deterministically (each term ≤ H, total ≤ dH ≤ dHI/(2x)).
The fixed committed tie rule is a restriction of the claim to that tie rule.

<a id="C51"></a>
## C51: scope disclosure for `Remark6_5` (offline bandit LCB remark, informal claim)

**Source:** Remark 6.5, `chapters/offlineRL.tex:413–415`, Algorithm 6.1 (`alg:MAB-LCB`). This is a scope disclosure
for a statement-index entry, not a refutation.

The remark states informally (with "≈" and "with high probability") how the LCB algorithm behaves on the Example 6.1
bandit. `Remark6_5` (unsuffixed) is this project's precise reading, and its constants are ours, not the book's:
for δ ∈ (0,1) and N − 1 > 8 log(8/δ), with probability ≥ 1 − δ, r₂^lcb ≤ 0, |r₁^lcb − 1| ≤ 2√(2 log(8/δ)/(N−1)) and
r₂^lcb < r₁^lcb. The threshold 8 log(8/δ) and the factor 2 are not printed. Both counts are positive on this event, so
the zero-count branch of [C18](#C18) is not reached. The entry is indexed as the formal reading of an informal claim,
as for `Remark5_12_lowerBound`, and is not a restriction of a printed theorem. Candidate language; not author-approved.
