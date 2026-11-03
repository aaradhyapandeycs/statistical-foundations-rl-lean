# Independent review: true-policy variance budget

Reviewed 2026-11-02. Stable `.local/PolicyEvaluationVariance.lean` SHA-256 `f25b76fadce9e452abe3375d2b8b5cf003df748ab6d737529cbe58b1b039d33d`, independently recomputed. Reviewer owns only this report. This is ordinary staged infrastructure, not a frozen source theorem.

## Verdict and source scope

**PASS for the exact true-value variance identity, nonnegative finite/infinite discounted budgets, their potential bound, convergence, equation and uniqueness. The horizon-three statistical policy-evaluation theorem remains open.**

I independently read the source's second-moment expansion and bound at `generative_model_model_based.tex:323–341`, and the preceding Jensen/resolvent discussion at `:295–318`. The source expands the actual population variance σ=Var_{Pπ}(Vπ) using Vπ=rπ+γPπVπ, then bounds a discounted resolvent applied to σ. The staged result proves the γ²-scaled expansion without dividing by γ and constructs a corresponding operator budget by monotone finite recursion. It does not yet identify that budget with the source's literal finite-matrix inverse or prove its square-root resolvent inequality.

For the purposes of this report write V=M.trajectoryExpectedValue π, r=evaluationPolicyReward M π, P=M.policyTransition π, B=‖V‖∞ and σ(s)=Var_{P(s)}(V).

## Actual trajectory and variance semantics

V is the actual expected infinite discounted reward under the controlled trajectory probability law, through the imported `PrefixValueBridge`/`InfiniteReturn` definitions. `evaluationTrajectory_bellman` obtains V=r+γPV through the already proved actual-trajectory/fixed-point bridge. It does not define V by an unproved Bellman characterization.

r is the original known reward averaged under π. P is the true action transition averaged under that same stationary randomized π. The variance is the actual finite probability-row second moment minus squared first moment, with its separately proved centered-square characterization and nonnegativity. There is no empirical variance, unknown sample law or data-dependent value vector in this module.

The exact identity is

`γ² σ = γ² P(V²) − V² + 2Vr − r²`.

This follows from γPV=V−r, without assuming γ>0. The signs, square on the mean, policy row and reward averaging match the source expansion. This scaled identity is equivalent to the printed expansion for γ>0 and is a meaningful endpoint extension at γ=0; it is not a proof that the source's expressions containing 1/γ² are defined there.

The next inequality uses γ²≤γ, P(V²)≥0 and r²≥0 to prove

`γ² σ ≤ γ P(V²) − V² + 2Vr`.

All three required properties are derived from source MDP inputs and the genuine row distribution. No desired variance bound is assumed.

The literal definitions r and σ have BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.

## Potential and exact discount powers

The potential is H=2BV−V². Actual rewards are nonnegative, so V≥0; finite sup norm gives V≤B. These imply `0≤H≤B²`. The proof then combines the self-bound, the Bellman equation and `(B−V)r≥0` to obtain the genuine super-solution inequality

`γ² σ + γ P H ≤ H`.

The finite recursion is W₀=0 and W_{n+1}=γ²σ+γPWₙ. Its exact mathematical unfolding is

`Wₙ = γ² ∑_{t=0}^{n−1} γ^t P^t σ`.

In particular W₁=γ²σ and W₂=γ²σ+γ³Pσ. This is a γ-discounted resolvent budget with a single prefactor γ². It is **not** a sum weighted by γ^{2t}, a squared-discount transition resolvent, or the variance of the full random discounted return. The file defines the operator recursion literally; it does not claim a separate path-integral representation of this sum.

Induction proves 0≤Wₙ≤H for every state and horizon. The upper step uses expectation monotonicity and the proved potential super-solution, while the lower step uses σ≥0, γ²≥0 and γ≥0. A separate induction proves monotonicity in n.

The infinite budget W is the real supremum of these finite budgets. Because the sequence is nonempty, monotone and bounded by B², the conditional real supremum is legitimate and the sequence converges to W. This is not an uncontrolled supremum on an unbounded family. Taking limits gives `0≤W≤H≤B²`. Passing a finite sum through the limit gives exactly

`W = γ²σ + γPW`.

Uniqueness is for every real-valued state vector, with no hidden boundedness premise (finite state space already supplies finite sup norms). Subtracting another candidate solution cancels the γ²σ forcing; the true value-Bellman contraction yields ‖difference‖≤γ‖difference‖ and hence equality. This correctly uses a value-Bellman difference, in which its ordinary reward term cancels; it does not assert that the variance forcing equals that reward.

For a future separately proved matrix inverse bridge at γ>0, uniqueness would identify W with γ²(I−γP)⁻¹σ. The current bound is actually stronger than the source's coarse `γ²(I−γP)⁻¹σ≤2B²`: it retains the potential term and proves W≤B². That improvement follows from explicit proved algebra and is not an altered source premise. Nevertheless no literal inverse identification should be marked completed from this file alone.

## Zero discount and other degeneracies

Every theorem allows γ=0; there is no division by γ. Then V=r, the exact identity has both sides zero, and the self-bound reduces to 0≤r². Every finite budget is zero directly from its recursion, and the infinite equation yields W=0. The potential may be positive, but is only an upper bound, so no zero-potential claim is needed.

The true row variance σ itself may be positive at γ=0 if immediate rewards differ across next states. The zero **scaled budget** must not be mistaken for a claim that σ=0. Likewise, if V has norm zero, the potential and all budgets are zero, consistently with variance of the zero vector. Nonnegative rewards are used substantively for V≥0, r≥0 and the chosen potential; an extension to signed rewards would require a different argument.

## Input and scope audit

All main exports take common State/Action carriers with finite instances, M, π, and where relevant a state or finite horizon. Expanded M inputs are nonempty state/action spaces, nonnegative normalized transition rows, deterministic rewards in [0,1], and 0≤γ<1. Expanded π is a stationary family of nonnegative normalized action distributions. These are STANDING/TYPING inputs already present in the source MDP setup. No variance estimate, resolvent bound, integrability gate or statistical conclusion appears as a premise.

The uniqueness theorem additionally takes a candidate W and its defining equation as the antecedent of that characterization. That equation is not assumed for the constructed budget: existence and its equation are proved beforehand. Thus no proof obligation has been moved into a source theorem premise. Relative to the explicitly scoped deterministic budget claims, EXCESS=0.

The result concerns the true value of a fixed stationary policy, not an empirical optimal policy or a value vector chosen from samples. It includes randomized π through the genuine policy-averaged transition; random reward/action variance is not added to σ, because the source object here is variance of continuation V under Pπ, not variance of the whole one-step reward-plus-return.

## Missing source work

The following remain separate: literal matrix/resolvent identification, inverse nonnegativity/row-sum semantics as used in the source, Jensen or Cauchy–Schwarz for the square-root variance resolvent, comparison of empirical and true resolvents, concentration under the actual empirical experiment, and the final sharp horizon-three policy-evaluation probability theorem with its constants, logarithm and parameter range. This module contains no samples, ε, δ or failure event and therefore cannot by itself certify that probabilistic theorem.

The builder handoff `docs/builder-policy-evaluation-variance.md` was checked against this stable implementation and states the recursion/finite-sum/inverse distinction correctly. The source's scaled second-moment identity and the staged recursion match the scope described there.

After coordinating the available compiler slot, I copied the exact reviewed source unchanged to `.local/VarianceBudgetIndependentAudit.lean`, appended eleven `#print axioms` commands and ran:

`bash scripts/lean-local.sh .local/VarianceBudgetIndependentAudit.lean`

Exit status 0 without warnings or errors. The inspected exports were `evaluationTrajectory_bellman`, `evaluationPolicyVariance_identity`, `evaluationPolicyVariance_selfBound`, `evaluationVariancePotential_bounds`, `evaluationVariancePotential_super`, `discountedPolicyVariancePartial_bounds`, `discountedPolicyVariancePartial_tendsto`, `discountedPolicyVarianceBudget_bounds`, `discountedPolicyVarianceBudget_bellman`, `discountedPolicyVarianceBudget_le_norm_sq`, and `discountedPolicyVarianceBudget_unique`. Each reports only `propext`, `Classical.choice`, `Quot.sound`. This audit includes the transitive monotonicity dependency of convergence. No `sorry`, `admit` or custom axiom occurs in the source. The temporary source was deleted. Production integration/export checks remain separate.
