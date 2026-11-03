# Whole-monograph progress

Status: **active; incomplete**. Source: arXiv:2610.41903v1, 326 PDF pages.

No whole-paper or chapter completion is certified. Source-level claims need
an exact Lean statement, all mathematical prerequisites, compilation, an axiom
audit, and independent correspondence review before promotion.

## Current checked infrastructure

- A reproducible lexical inventory covers the active source include tree. It
  identifies 90 named theorem/lemma/claim environments, 17 algorithms, 1,381
  display environments, and numerous further candidate obligations. These are
  scanner counts, not a proof-coverage percentage or a semantic completeness
  claim. The generated inventory retains its initial unformalized status labels;
  the separate [coverage ledger](COVERAGE.md) records reviewed results.
- `Formalization/MDP/Basic.lean` defines finite stochastic kernels, policies,
  and Bellman maps; it proves both policy and optimality contraction bounds.
- `Formalization/MDP/FixedPoint.lean` proves Bellman fixed-point existence,
  uniqueness, geometric iteration bounds, and interval bounds. Identification
  with actual trajectory policy and optimal Q values and optimal-policy
  existence is established separately below.
- `Formalization/MDP/FiniteHorizon.lean` and `FiniteTrajectory.lean` construct
  nonstationary finite trajectories and prove that their expected cumulative
  reward equals backward evaluation. Finite-horizon optimality is addressed
  separately by `FiniteOptimal.lean` below.
- `Formalization/MDP/FiniteQTrajectory.lean` additionally constructs the
  action-conditioned trajectory law, proves both indexed finite-horizon policy
  Bellman equations, and supplies zero terminal values.
- `Formalization/MDP/FiniteOptimal.lean` constructs a greedy deterministic
  stage sequence in one common, time-varying environment, proves it dominates
  randomized Markov policies, and derives the finite optimal Bellman equations.
  The [independent review](critic-finite-optimal.md) identifies the finite
  policy representation and zero-horizon boundaries that remain to address.
- `Formalization/MDP/FiniteOccupancy.lean` constructs finite state and
  state-action occupancy laws and proves their factorization and initial-state
  identity. `OccupancyBridge.lean` proves equality with events under one full
  episode law and derives the greedy optimal-policy indicator formula. See the
  [initial review](critic-finite-occupancy.md) and the subsequent
  [bridge review](critic-occupancy-bridge.md).
- `Formalization/MDP/DiscountedFiniteTrajectory.lean` defines discounted
  rewards on actual finite trajectory laws, proves their Bellman recursion,
  and proves that finite expectations converge to the unique state Bellman
  fixed point. Its [independent review](critic-discounted-finite.md) checks
  the finite-law semantics and discount exponents. Infinite-path expectations
  and their partial-sum convergence are constructed separately below; the
  finite-prefix payoff integrals are now connected to the actual infinite law
  by `PrefixValueBridge.lean` below.
- `Formalization/MDP/PolicyValueQ.lean` proves that the state Bellman fixed
  point equals the policy average of the Q Bellman fixed point, and proves the
  corresponding reward-plus-continuation identity. Its
  [independent review](critic-policy-value-q.md) records the then-open
  infinite-trajectory interpretation, addressed in `ForcedPrefixBridge.lean`.
- `Formalization/MDP/InfiniteTrajectory.lean` constructs a normalized infinite
  controlled path law from the actual policy and transition distributions.
  It proves the first-step law and identifies arbitrary prefixes with Mathlib's
  iterated history-kernel construction. Its identification with the project's
  finite path law is established at every prefix length in
  `FinitePrefixBridge.lean` below. The
  [independent review](critic-infinite-trajectory.md) checks the law and the
  history/next-step distribution.
- `Formalization/MDP/InfinitePrefix.lean` proves the exact policy-transition
  product for every finite singleton cylinder; the separately defined finite
  path law is related below. See the
  [independent review](critic-infinite-prefix.md).
- `Formalization/MDP/FinitePrefixBridge.lean` proves that for every length,
  including zero, the actual infinite-law prefix has exactly the independently
  constructed finite path law. Transferring payoffs and their limits remains
  separate; see the [independent review](critic-finite-prefix-bridge.md).
- `Formalization/MDP/InfiniteValueBellman.lean` proves an actual-path
  first-step expectation identity for every valid discount and directly proves
  the γ = 0 Bellman specialization. Its general identification is addressed by
  `PrefixValueBridge.lean`; see the
  [independent review](critic-infinite-value-bellman.md).
- `Formalization/MDP/PrefixValueBridge.lean` identifies the actual infinite
  trajectory value with the policy state Bellman fixed point for every
  source discount and stationary randomized policy. It transports finite
  payoffs and uses the two independently established limits; see the
  [independent review](critic-prefix-value-bridge.md). The actual Q-value
  identification remains separate.
- `Formalization/MDP/ForcedActionTrajectory.lean` constructs the actual
  first-action intervention, including zero-policy-mass actions, with the
  original policy governing all subsequent steps. See the
  [independent review](critic-forced-action.md).
- `Formalization/MDP/ForcedActionReturn.lean` defines the corresponding actual
  infinite Q-return expectation and proves its integrability, geometric bounds,
  and convergence of expected partial sums. See the
  [independent review](critic-forced-return.md). Its Bellman fixed-point
  identity and V–Q averaging relation are established separately below.
- `Formalization/MDP/ForcedPrefixBridge.lean` identifies the actual forced-
  first-action infinite Q expectation with the policy Q fixed point for all
  discounts and actions, including zero policy probability. It proves the
  policy Q Bellman equation and actual V–Q averaging identity. Stationary
  optimality is addressed separately below; see the
  [independent review](critic-forced-prefix-bridge.md).
- `Formalization/MDP/OptimalTrajectoryValue.lean` constructs a deterministic
  stationary greedy policy whose actual trajectory Q attains the optimality
  Bellman fixed point and whose Q and V dominate all stationary randomized
  policies. The result does not quantify over nonstationary or history-dependent
  policies; see the [independent review](critic-optimal-trajectory-value.md).
- `Formalization/MDP/PolicyIteration.lean` proves the source γ^k trajectory-Q
  error rate for arbitrary maximizing tie choices and finite optimal-value
  attainment, including an arbitrary initial stationary randomized policy.
  A fixed tie rule also eventually stabilizes at the greedy policy. See the
  [independent review](critic-policy-iteration.md).
- `Formalization/MDP/DiscountedOccupancy.lean` constructs the source's
  discounted state and state-action occupancy laws from actual infinite path
  events and the specified initial distribution, proves normalization, the
  policy factorization and deterministic-policy indicator, and handles γ = 0.
  The explicit optimal-policy indicator is established separately below; see
  the [independent review](critic-discounted-occupancy.md).
- `Formalization/MDP/OptimalDiscountedOccupancy.lean` specializes the
  occupancy indicator to the constructed optimal greedy policy, with the same
  initial distribution and actual trajectory events. See the
  [independent review](critic-optimal-discounted-occupancy.md).
- `Formalization/MDP/InfiniteReturn.lean` defines the actual infinite discounted
  return and its expectation under that path law, and proves measurability,
  integrability, the geometric bound, and convergence of expected partial sums.
  The [independent review](critic-infinite-return.md) records the then-open
  payoff-integral bridge and Bellman identification, now established separately
  in `PrefixValueBridge.lean`.
- `Formalization/Probability/Variance.lean` proves the source's exact finite
  transition-variance perturbation bound, Lemma 2.2. See its independent
  [scoped review](critic-variance-review.md).
- [Concentration API discovery](probability-api-discovery.md) identifies a
  pinned Mathlib route for Hoeffding and the additional work needed for
  variance-sensitive Bernstein, random test families, and strict probabilities.
  Neither source concentration lemma has yet been proved.
- `Formalization/Probability/EmpiricalRow.lean` constructs actual iid finite
  transition-row samples and normalized empirical frequencies for positive
  sample count, proves the sample-mean identity, and proves unbiasedness.
  The [independent review](critic-empirical-row.md) records this scope. This is
  a prerequisite, not a proof of either concentration lemma.
- `Formalization/Probability/EmpiricalHoeffding.lean` proves the sharp
  fixed-vector two-sided Hoeffding tail for actual iid row samples, including
  a separate zero-norm case. The simultaneous source lemma for independent
  random vector families and its strict probability remain open. See the
  [independent review](critic-empirical-hoeffding.md).
- `Formalization/Probability/EmpiricalHoeffdingFamily.lean` proves the
  exact source radius simultaneously for a deterministic finite family, with
  strict success probability, and treats empty and zero-vector cases. The
  random independent-family extension remains open; see its
  [independent review](critic-empirical-hoeffding-family.md).
- `Formalization/Probability/EmpiricalHoeffdingRandomFamily.lean` proves the
  strict source-radius bound for variable-size, possibly empty random families
  independent of the actual empirical row, under an explicit family-test
  measurable structure; see the
  [independent review](critic-empirical-hoeffding-random-family.md).
- `Formalization/Probability/RandomFamilyBorel.lean` constructs a finite-family
  measurable space from injective Borel tuples and proves the source-radius
  strict bound under unordered-family/empirical-row independence. Equality
  with other hyperspace σ-algebras and a full source declaration audit remain
  separate; see the [independent review](critic-random-family-borel.md) and
  [source correspondence](source-hoeffding-correspondence.md).
- `Formalization/Probability/EmpiricalBernstein.lean` proves the actual iid
  empirical mean variance, zero-variance case and a variance-sensitive
  exponential tail with constants weaker than the source. The source Bernstein
  lemma remains open; see the [independent review](critic-empirical-bernstein.md).
- `Formalization/Probability/SharpEmpiricalBernstein.lean` derives the
  source-constant fixed-vector Bernstein tail under actual iid sampling,
  including zero range and variance. The simultaneous random-family and
  whole-matrix source bounds remain open; see the
  [independent review](critic-sharp-empirical-bernstein.md).
- `Formalization/Probability/BernsteinFamily.lean` proves the source
  Bernstein radius and strict success for a single empirical row and a
  random finite Borel family independent of that row, including empty and
  zero cases. The whole-matrix inequality remains separate; see the
  [independent review](critic-bernstein-family.md).
- `Formalization/Probability/BernsteinMatrixMarginals.lean` proves the
  source whole-matrix Bernstein bound from iid sampling within each row,
  allowing arbitrary cross-row dependence, with the correct matrix independence
  and strict success. See the [independent review](critic-bernstein-matrix-marginals.md).
- `Formalization/Probability/EmpiricalVarianceBernstein.lean` proves the
  iid empirical-variance bias correction and a source-radius bound in a
  restricted confidence regime. General self-normalized concentration remains
  open; see the [independent review](critic-empirical-variance-bernstein.md).
- `Formalization/Probability/EmpiricalVarianceConcentration.lean` proves a
  two-sided additive concentration bound for the empirical variance and a
  one-sided population-variance confidence bound on the actual iid sample law.
  The source's sharper self-normalized empirical Bernstein theorem remains
  open; see the [independent review](critic-empirical-variance-concentration.md).
- `Formalization/Probability/EmpiricalBernsteinSelfNormalized.lean` proves
  exact leave-one-out empirical-variance identities and a sharp deterministic
  sum-of-squares self-bound. The required stochastic self-bounding inequality
  and source empirical Bernstein conclusion remain open; see the
  [independent review](critic-empirical-bernstein-self-normalized.md).
- `Formalization/Probability/SelfBoundingConcentration.lean` proves an
  iid empirical-standard-deviation lower-tail bound with correct N⁻¹ᐟ² scale
  but constants weaker than the source empirical Bernstein result. The
  source's sharper self-normalized inequality and family extension remain
  open; see the [independent review](critic-self-bounding-concentration.md).
- `Formalization/Probability/EmpiricalBernsteinCombined.lean` proves a
  fixed-vector confidence bound in terms of observed empirical variance with
  explicit constants weaker than the source. Sharp constants and the random
  family statement remain open; see the [independent review](critic-empirical-bernstein-combined.md).
- `Formalization/Obstructions/SingletonAction.lean` proves a singleton-action
  policy-loss obstruction. `Obstructions/OneState.lean` proves a one-state
  Bellman fixed-point formula and optimal greedy policy. See
  [SOURCE-ISSUES.md](SOURCE-ISSUES.md) for the source review, including a
  one-state counterexample under the known-reward convention and the pending
  Lean bridge to the full statistical theorem.
- `Formalization/Obstructions/HardMDP.lean` constructs the source's two-state
  hard example and proves its correct optimal and bad-policy Bellman values,
  source-range value separation, and policy loss. Its [independent review](critic-hard-mdp.md)
  also checks a rational counterexample to the printed intermediate Q formula.
  Stationary optimal trajectory semantics are addressed separately; the full
  statistical lower bound remains open.
- `Formalization/Obstructions/OneStateTrajectory.lean` proves that one
  estimator using known rewards and discount is exact for actual stationary
  optimal trajectory Q, uniformly over one-state models and data laws.
  The formal statistical experiment is addressed separately; see the
  [independent review](critic-one-state-trajectory.md).
- `Formalization/Obstructions/OneStateExperiment.lean` constructs the actual
  one-sample-per-row generative law and proves one jointly measurable
  known-reward Q estimator has zero error uniformly across the admissible
  one-state models for each feasible source parameter choice. A literal
  source-theorem proposition and its formal negation are not yet encoded;
  see the [independent review](critic-one-state-experiment.md).
- `Formalization/Obstructions/OneStatePolicyExperiment.lean` constructs a
  measurable deterministic reward-greedy estimator whose actual trajectory
  Q-policy loss is zero across the one-state generative experiment. A literal
  source-theorem proposition and formal negation remain separate; see the
  [independent review](critic-one-state-policy-experiment.md).
- `Formalization/Generative/ModelBasedPolicyEvaluation.lean` constructs
  the genuine iid policy-row experiment and measurable empirical Bellman
  estimator, with actual empirical trajectory semantics. The literal inverse
  expression and the source sample-complexity bound are proved separately
  below. See the
  [independent review](critic-model-based-policy-evaluation.md).
- `Formalization/Generative/ModelBasedPolicyLearning.lean` constructs the iid
  state-action experiment, empirical MDP, Q estimator, and measurable
  deterministic greedy policy with empirical trajectory optimality. The
  true-model sample-complexity guarantee remains open; see the
  [independent review](critic-model-based-policy-learning.md).
- `Formalization/Obstructions/Theorem37Negation.lean` proves the negation
  of a source-facing encoded version of Theorem 3.7(ii) using the one-state
  experiment. Its estimator interface and stationary-policy interpretation
  have unresolved source-equivalence boundaries; see the
  [independent audit](critic-theorem37-negation.md). It is not an
  author-approved correction or a proof of the printed theorem.
- `Formalization/Generative/PolicyEvaluationPerturbation.lean` proves the
  exact actual-trajectory Bellman error identity and its γ/(1−γ) sup-norm
  residual bound for true and empirical models with common known reward and
  discount, including γ = 0. It is deterministic; the source statistical
  guarantee remains separate. See the [independent review](critic-policy-evaluation-perturbation.md).
- `Formalization/Generative/PolicyEvaluationInverse.lean` proves that the
  stochastic empirical matrix yields an invertible `I−γ P̂π` and that the
  empirical Bellman estimator equals the source's literal inverse expression.
  Statistical guarantees remain separate; see the
  [independent review](critic-policy-evaluation-inverse.md).
- `Formalization/Generative/PolicyEvaluationHoeffding.lean` proves a
  strict high-probability actual-sampling evaluation bound and a sufficient
  sample size scaling as (1−γ)⁻⁴. This is weaker than the source's
  (1−γ)⁻³ result; see the [independent review](critic-policy-evaluation-hoeffding.md).
- `Formalization/Generative/PolicyLearningZeroDiscount.lean` proves zero
  true-model trajectory Q and V loss for the empirical greedy policy at γ = 0,
  for every positive sample count and every outcome. The general source theorem
  remains open; see the [independent review](critic-policy-learning-zero-discount.md).
- `Formalization/Generative/PolicyLearningAbsorbing.lean` constructs the
  fixed-parameter absorbing model and proves its deterministic data-invariance
  properties. `PolicyLearningAbsorbingPreservation.lean` proves Lemma 3.3,
  preservation of actual optimal trajectory values, and its empirical
  counterpart. `PolicyLearningAbsorbingLipschitz.lean` proves exact fixed-parameter
  value stability. Statistical independence remains separate; see the
  [absorbing review](critic-policy-learning-absorbing.md),
  [preservation review](critic-policy-learning-preservation.md), and
  [stability review](critic-policy-learning-absorbing-lipschitz.md).
- `Formalization/Generative/PolicyLearningVarianceTransfer.lean` proves
  standard-deviation stability and a conditional grid-to-value transfer.
  `PolicyLearningAllRowBernstein.lean` proves the source-constant simultaneous
  all-row, all-grid event under actual sampling. Data-selected transfer and
  the policy-learning theorem remain separate; see the independent reviews
  of [variance transfer](critic-policy-learning-variance-transfer.md) and
  the [all-row event](critic-policy-learning-all-row-bernstein.md).
- `Formalization/Generative/PolicyLearningAbsorbingGrid.lean` proves the
  source finite grid and Lemma 3.4, the actual empirical optimal-value cover.
  `PolicyLearningLeaveOneOutBernstein.lean` proves a fixed-family, one-row
  concentration event; the all-row union and data-selected transfer are
  separate. See the independent reviews of the [grid](critic-policy-learning-absorbing-grid.md)
  and [Bernstein event](critic-policy-learning-leave-one-out-bernstein.md).
- `Formalization/Generative/PolicyLearningLeaveOneOutIndependence.lean`
  proves that the fixed-parameter auxiliary value family is independent of
  the omitted empirical row under the actual sampling law. It does not
  assert independence for a parameter selected from the data; see the
  [independent review](critic-policy-learning-leave-one-out-independence.md).
- `Formalization/Generative/PolicyLearningHoeffding.lean` proves a
  conservative actual-sampling policy-learning value guarantee by a finite
  union over deterministic policies, accounting for the fitted policy’s data
  dependence. Its rate is weaker than the source and does not prove its Q
  guarantee; see the [independent review](critic-policy-learning-hoeffding.md).
- `Formalization/Generative/PolicyEvaluationVariance.lean` proves a
  source-derived policy variance identity, finite and infinite discounted
  variance-budget bounds and the budget's unique Bellman equation. The
  empirical-resolvent and sharper statistical links are proved separately; see the
  [independent review](critic-policy-evaluation-variance.md).
- `Formalization/Generative/PolicyEvaluationUniversalConstant.lean` proves
  the source policy-evaluation sample theorem, Theorem 3.1, with a universal
  constant 720 chosen before all finite model and accuracy parameters. It
  uses the actual policy-row sampling law and trajectory values. Independent
  source and integrated-export reviews are recorded in the
  [theorem audit](critic-policy-evaluation-source-theorem.md),
  [second source audit](critic-policy-evaluation-source-independent.md), and
  [universal-constant audit](critic-policy-evaluation-universal-constant.md).
- `Formalization/Generative/PolicyEvaluationTerminalError.lean` proves
  the terminal auxiliary error estimate. `PolicyEvaluationHighSample.lean`
  combines it with the recursion on one actual-sampling event, while
  `PolicyEvaluationSampleAssembly.lean` proves sample-threshold arithmetic
  and one-state exactness. The source-shaped final theorem is assembled
  separately; see the independent reviews of the [terminal bound](critic-policy-evaluation-terminal-error.md),
  [high-sample bound](critic-policy-evaluation-high-sample.md), and
  [sample assembly](critic-policy-evaluation-sample-assembly.md).
- `Formalization/Generative/PolicyEvaluationFinalArithmetic.lean` proves
  the printed high-sample radius from explicit recursion, growth, and terminal
  estimates; the assumptions and statistical assembly are discharged separately. See the
  [independent review](critic-policy-evaluation-final-arithmetic.md).
- `Formalization/Generative/PolicyEvaluationBernsteinRecursion.lean` combines
  the actual-sampling simultaneous Bernstein event with the conditional
  auxiliary residual recursion. The terminal estimate and source sample bound
  are assembled separately; see the [independent review](critic-policy-evaluation-bernstein-recursion.md).
- `Formalization/Generative/PolicyEvaluationAuxiliaryGrowth.lean` derives
  the source-shaped auxiliary-value growth bound from the general-forcing
  result, with a separate zero-discount identity. Its combination with the
  concentration recursion is proved separately; see the
  [independent review](critic-policy-evaluation-auxiliary-growth.md).
- `Formalization/Generative/PolicyEvaluationGeneralForcing.lean` extends
  the true-policy variance resolvent bound to any nonnegative forcing.
  `PolicyEvaluationResidualRecursion.lean` proves the conditional residual
  recursion using actual empirical resolvent order. The concentration event,
  sharp growth and final sample bound are assembled separately; see the
  independent reviews of [general forcing](critic-policy-evaluation-general-forcing.md)
  and the [recursion](critic-policy-evaluation-residual-recursion.md).
- `Formalization/Generative/EmpiricalResolventOrder.lean` proves positivity,
  order preservation, the row-sum identity and absolute-value domination for
  the actual empirical policy resolvent; see the
  [independent review](critic-empirical-resolvent-order.md).
- `Formalization/Generative/PolicyEvaluationAuxiliary.lean` constructs the
  true and empirical recursive variance-value vectors, their defining matrix
  equations and a conservative growth bound.
  `PolicyEvaluationAuxiliaryBernstein.lean` proves an actual-sampling
  simultaneous Bernstein event over finitely many true auxiliary levels. The
  sharper recursion and statistical guarantee are proved separately; see the
  independent reviews of the [vectors](critic-policy-evaluation-auxiliary.md)
  and [event](critic-policy-evaluation-auxiliary-bernstein.md).
- `Formalization/Generative/PolicyEvaluationEmpiricalResolvent.lean` proves
  an empirical-versus-true policy resolvent identity and an actual-sampling
  Bernstein bound for the first auxiliary variance vector. The higher-order
  variance analysis and sharp rate are established separately; see the
  [independent review](critic-policy-evaluation-empirical-resolvent.md).
- `Formalization/Generative/PolicyEvaluationRecursiveUnroll.lean` proves
  a conditional finite unrolling of the source’s auxiliary recursion and a
  deterministic small-sample bound that repairs an omitted case in the
  source derivation. The high-sample concentration branch and full theorem
  are proved separately; see the [independent review](critic-policy-evaluation-recursive-unroll.md).
- `Formalization/Generative/PolicyEvaluationVarianceResolvent.lean` proves
  the true-policy matrix resolvent identities and a square-root variance
  budget bound, including a scaled zero-discount case. The empirical
  comparison and sharp statistical guarantee are proved separately; see the
  [independent review](critic-policy-evaluation-variance-resolvent.md).
- The current pinned Lean integration compiled eighty-one project modules; its
  transitive axiom audit checked 1673 project declarations, allowing only
  `propext`, `Classical.choice`, and `Quot.sound`. These checks do not replace
  source review. Current builder work and independent critic findings are
  recorded separately in `builder-*.md` and `critic-*.md`.
- The [trajectory critic review](critic-trajectory-review.md) checked path
  weights, reward order, terminal marginalization, and two concrete Lean
  examples. Its reviewer authored the imported basic MDP dependencies, whose
  separate review remains necessary. The review also confirms that the
  singleton-action obstruction depends on the source interpretation.
- A separate [fixed-point critic review](critic-fixedpoint-review.md) checked
  the source-facing model fields, finite supremum norms, Bellman contractions,
  fixed-point selection, and the γ = 0 boundary. It passes those scoped
  infrastructure claims while leaving source trajectory semantics and policy
  iteration open.
- The [finite-Q critic review](critic-finite-q-review.md) checks the indexed
  policy Bellman equations against the actual action-conditioned trajectory law.
  Whole-chapter and infinite-horizon completion remain open.

## Teams and ownership

| Role | Owned work | Current objective |
|---|---|---|
| Lead builder/integrator | project configuration, checking, analysis infrastructure | reproducible proof environment and integration |
| Source builder | `scripts/inventory.py`, `docs/source-inventory.*` | complete source traversal and explicit coverage checklist |
| MDP builder | `Formalization/MDP/Basic.lean`, `FiniteHorizon.lean` | faithful finite tabular model and Bellman foundations |
| Independent critic | `docs/critic-initial-review.md` | reconstruct claims from source and challenge semantics and coverage |

## Required coverage

1. Introduction: mathematical conventions and substantive claims.
2. Preliminaries: MDP semantics, policies, value/Q functions, occupancy,
   Bellman and planning theory, concentration and testing inequalities.
3. Generative-model model-based algorithms, upper and lower bounds, and appendices.
4. Generative-model model-free algorithms, TD, Q-learning, and appendices.
5. Online RL, bandits, UCB-VI, MVP, model-free methods, lower bounds, and appendices.
6. Offline RL, pessimism, model-based/model-free methods, lower bounds, and appendices.
7. Robust, competitive multi-agent, federated, inference, and human-feedback extensions.
8. Concluding mathematical claims and all externally cited substantive inputs.

Every chapter remains open. Algorithm and trajectory semantics must be
connected to probabilistic guarantees; abstract helper bounds alone do not
certify an RL theorem. Externally cited mathematics is an obligation to prove
or instantiate from an audited dependency, not a new project axiom.
