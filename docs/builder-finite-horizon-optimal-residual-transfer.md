# Finite optimal-control comparison from common canonical residuals

Stable staged `.local/FiniteHorizonOptimalResidualTransfer.lean`, SHA-256 `9790d7beb4f697883b87fa8988a0018dba0de34107d62e9a622f13f6c5a3bea2`.

Direct staged dependency: `FiniteHorizonResidualAccumulation.lean` SHA `95aea77cc0f68596895543a453c1073fa1e8cd2e0d76275d708ca02f23536f17`, with actual finite perturbation/continuation/sampling dependencies recorded in their handoffs. No stochastic premise is hidden in this deterministic result.

## Exact algorithmic predicate and canonical witness

`SuffixOptimal fs π` means the actual trajectory value of π in comparison environment fs is exactly the proved finite optimal value at every state of every suffix. This is empirical planning optimality, not true-model performance or an assumed evaluation-error bound. It explicitly requires optimality at every suffix, rather than at only one initial state/distribution. Randomized Markov policies are allowed in the helper, so all deterministic exact optimal tie policies are covered.

`suffixOptimal_tail` proves the same property for the shifted policy after one stage. `backwardGreedyPolicy default fs` constructs a total backward-greedy nonstationary policy, using the supplied default only after the finite episode. `controlled_backwardGreedyPolicy` proves its actual controlled stages equal the existing greedyStages construction, and `backwardGreedyPolicy_suffixOptimal` derives its all-suffix empirical optimality through the actual trajectory bridge. Thus the optimizer predicate is inhabited whenever a default stationary policy is available; in the intended nonempty finite action setting any fixed action supplies one. No uniqueness/action-gap assumption is present, and the default does not affect any episode decision.

## Canonical residuals independent of tie choice

`optimalResidualCharges` has one charge per paired true/comparison stage(E,F): the supremum norm over all state/action rows of `(P_F−P_E)` applied to **canonical comparison-optimal suffix value**. It contains no selected π argument. Its length and nonnegative sum are proved.

`optimalValue_difference_abs_le` proves comparison-optimal value and true-optimal value differ by at most the charge sum. At each stage it uses true-kernel propagation of the next-stage optimal-value difference and nonexpansiveness of the finite action maximum. Known reward equality for every pair is explicit.

`suffixOptimal_evaluation_abs_le` separately proves comparison-optimal value and the true actual value of **any** comparison suffix-optimal π differ by at most exactly the same charge sum. Its proof uses the actual trajectory perturbation identity and the proved empirical optimality equality at the next suffix. No data-independence of π or of its selected actions is assumed. This equality is what permits the common concentration event to concern canonical continuation values rather than every policy.

`suffixOptimal_value_loss_le` combines these two bounds and true-model actual optimality to give `0≤V*−Vπ≤2·sum(charges)`. `suffixOptimal_performance_le` proves both this V bound and `0≤Q*−Qπ≤2·sum(charges)` for every state/action, using actual forced-first-action Q and next-suffix V loss under the true transition. The Q bound has no discounted γ factor and covers actions outside π's support.

## Actual empirical specialization and common event consumption

`empiricalSuffixOptimal_performance_uniform` pairs the true stage array with its actual frequency-model stages from the same data, proves reward equality and List.ofFn alignment internally, and consumes one premise:

`∀ c∈optimalResidualCharges(pairedEmpiricalStages E N hN data), c≤r`.

This is a common all-stage/state/action canonical transition-residual envelope. The list has H entries, each already a full state/action supremum norm. Its sum is proved≤H·r. The conclusion universally quantifies every empirical suffix-optimal policy **after** data and the common residual bound, and gives simultaneous true-model V and Q losses≤2H·r. Therefore a future high-probability event controlling those canonical charges can be reused for all data-dependent tie choices without an exponential union over policies or an assumption that fitted π is independent of the row.

The explicit empirical specialization exposes the starting episode values. The generic paired-list theorem can be instantiated on any remaining suffix with shifted π, but this file does not yet export one all-stage indexed performance event. A future full finite-horizon theorem must formalize that suffix/index packaging rather than silently claim it already appears here.

## Constants, endpoints and remaining theorem gaps

The deterministic factor2 comes from optimal-model perturbation plus fitted-policy evaluation; the factorH is a proved uniform sum bound. Empty horizon, terminal suffix and single-stage known-reward planning are handled by the underlying actual-value recursion; terminal canonical residual is zero. All models may have stage-varying kernels and known [0,1] rewards. N>0 is solely the empirical-row domain. The uniform envelope premise is a residual estimate that must be discharged, not a claimed probability statement.

No H³ or H⁴ sample theorem is proved. A coarse row scale proportional to H/sqrt(N), together with this factorH, suggests an H⁴ per-tuple sufficient sample dependence; its common event, explicit sample constants, source-log conversion and all-stage packaging remain separate proofs. The source-sharp H³ theorem additionally requires cumulative variance control. No source bound is weakened or advertised as complete. The referred external full proof remains unpinned as documented in the source plan.

## Validation

Fresh exact residual-accumulation dependency and the new source were compiled into isolated `.local/finite-horizon-build` artifacts. The final exact-source-copy `.local/finite-horizon-build/OptimalTransferAudit.lean` appended transitive axiom probes for all13 public definitions/theorems; it compiled exit0 without diagnostics. Every export reported only `propext`, `Classical.choice`, `Quot.sound`; the private row-norm helper is included transitively. No placeholder/custom axiom or dependency-artifact mutation occurs. Compiler slot released immediately after the final probe.

Pending independent semantic/source review, staged-to-production integration, actual imported-export checks and shared project build. No finite-horizon source theorem completion is claimed.
