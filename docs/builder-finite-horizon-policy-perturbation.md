# Exact finite-horizon policy perturbation identities

Stable staged `.local/FiniteHorizonPolicyPerturbation.lean`, SHA-256 `546b25ca13cc72ed182cc55999a85a4655e39e6636948bfd257fe144f06ed4ea`.

Direct staged dependency: `FiniteHorizonEmpiricalContinuation.lean` SHA `4cdf6cc568915df0ab34ff2fff63f025f851cbe8231ab888a73939b4a39c29dc`, whose sampling dependency has SHA `c0e830fc8e3050ae0aadf8cfeec3c9d9209a72086d00a954ffa9e48024eb4e41`. Actual finite policy trajectory/Bellman semantics come from the existing production FiniteTrajectory/FiniteQTrajectory/FiniteOptimal modules.

## Scope and source relation

This is a deterministic foundational identity for the finite nonstationary empirical-model frontier, not a source sample-complexity theorem. The source model-based finite algorithm (`eq:defn-empirical-P-finite`, chapter lines2526–2548) preserves known stage rewards and changes only transitions. Chapter2 finite Bellman/actual trajectory APIs provide the exact semantic basis. The brief chapter proof referral does not itself provide a printed numbered finite perturbation lemma; this helper is independently proved algebra for the stated models. No concentration event, independence assumption, stochastic variance bound or desired value-error estimate is a premise.

## Nine exports and exact orientation

`policyRowResidual E F W s a=(F.transition s a).expectation W−(E.transition s a).expectation W`, with E the true stage and F the comparison/empirical stage. `policyRowResidual_zero` proves terminal continuation0 gives residual0, regardless of either transition kernel.

`valueBackup_difference_eq` proves, for the same current policy and rewards F.reward=E.reward,

`backup_F(W)−backup_E(V)=E_{a~π}[residual(E,F,W)+P_E(W−V)]`.

The continuation input of the row residual is W from the comparison model, while **true** P_E propagates the future error W−V. Reward cancellation is explicit, with no resolvent/inverse or discount factor. `trajectoryValue_difference_cons` instantiates W and V with actual comparison/true suffix trajectory values under the very same arbitrary nonstationary randomized policy π shifted by one step. Thus the left side is actual F-policy value minus actual E-policy value, not assumed Bellman variables.

`trajectoryQ_difference_cons` gives the corresponding actual forced-first-action Q identity for every action a. It has the same row residual and true-kernel propagated suffix error but no averaging of the intervention action by π. Current π may assign that action zero probability; the production trajectory-Q bridge still applies.

`propagatedPolicyResidual` recursively evaluates every stage's explicit residual against its actual comparison-model suffix continuation, and propagates the remaining residuals through the true transition row and same policy. A list of paired environments stores one true and one comparison stage at each time, forcing equal horizons by construction. `trajectoryValue_difference_eq_propagatedResidual` proves by finite induction that actual whole-episode policy-value difference equals this finite nested propagated-residual expression, assuming only matching reward functions for each pair. It does not define the residual as the target whole-episode error or assume that error satisfies a recursion. This is an exact finite residual recursion, not an already proved closed occupancy-weighted summation formula; no such expansion is claimed here.

`pairedEmpiricalStages` pairs each E h with its actual same-data frequency stage. `empiricalTrajectoryValue_difference_eq_residual` specializes the generic identity to the actual empirical environment list and original `List.ofFn E`. It derives every pair's reward equality by construction and proves the list-map alignment. Only N>0, the actual sample data, and an arbitrary nonstationary policy are inputs; there are no reward, kernel closeness, residual-size, confidence or planner-optimality assumptions.

## Suffixes, boundaries and statistical dependence

Each current-stage identity exposes the exact suffix values with policy k↦π(k+1). The finite recursion carries that shift at every stage, and can be instantiated with any paired suffix. There are no off-domain terminal stage defaults. Empty horizon has zero trajectory error and residual propagation; the last transition's terminal continuation residual is zero. Arbitrary finite carriers, time-varying kernels, rewards in [0,1] and nonstationary randomized Markov policies are permitted. No discounted/stationary-MDP restriction or artificial horizon lower bound is added.

The empirical specialization is pointwise in data and π, so it can be applied to a realized data-dependent policy as a deterministic identity. It does not assert that the realized policy's suffix value is independent of current data. Statistical use for empirical-optimal planners still requires the appropriate common event and proved equivalence to canonical empirical optimal suffix values. Uniform residual/norm bounds, occupancy sum expansion, cumulative variance control, arbitrary-optimal tie performance transfer and the H³ statistical rate remain separate obligations.

## Validation

Fresh exact continuation dependency was compiled into isolated `.local/finite-horizon-build`, followed by the new exact source, both exit0. The final exact-source-copy `.local/finite-horizon-build/PerturbationAudit.lean` appended axiom checks for all9 definitions/theorems; compilation exited0 without diagnostics and every export reported only `propext`, `Classical.choice`, `Quot.sound`. No placeholder, custom axiom or dependency-artifact mutation occurs. Compiler slot released immediately after the final probe.

Independent source/semantic review, qualified production landing and actual export/project checks remain separate gates. No finite-horizon learning theorem completion is claimed.
