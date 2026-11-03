# Source review: quarter-risk finite-kernel lower bound

Reviewed candidate `.local/GenerativeLowerBoundKernelQuarter.lean`, SHA-256 `2215af467cc7d66df7e83d34d690802e8dfb31d208ad1489d9fbdfffab681b59`. This review is source-only; no Lean compile or axiom probe was run.

## Statement and source comparison

The primary target is source Theorem 3.7(i), `source/upstream/tex/chapters/generative_model_model_based.tex:1443–1464`, which assumes `γ∈[2/3,1)`, `0<ε<1/[32(1−γ)]`, `SA≥16`, and `N≤c_N log(SA)/[(1−γ)^3 ε²]`, and concludes probability at least `1/4` of strict Q-loss greater than ε for a deterministic policy estimator.

The candidate's `sourceFamily_seeded_large_policy_risk_quarter` has the desired `1/4 ≤ risk` conclusion on the strict event `ε < ‖Q^π−Q*‖`. It uses the correct actual product law of samples and the common seed. The estimator is a single function from sample-plus-seed to a deterministic stationary policy function; no model index enters that function or the seed law. The hard index is existentially selected after both estimator and seed law are fixed and after the seed has been averaged. This covers deterministic estimators as a special case (use a point-mass kernel), and also permits random selection among deterministic policy outputs.

The finite-kernel theorem converts an arbitrary fixed sample-to-PMF map into a product seed `X→Y`, independent of the samples and common across models. `finiteKernelSeed_joint_law` supplies the actual `(sample, output)` law, and the wrapper transports the same strict Q-loss event to that law. Thus the probability in the result includes estimator randomization; the returned policy at each outcome is still deterministic and stationary.

## Assumptions and arithmetic

The candidate assumes `m,n≥1`, so the constructed model has `S=m+1≥2` states and `A=n+1≥2` actions. It also assumes `SA≥16`, matching the source large-family regime but retaining the stated corrected `S,A≥2` scope. It does not claim coverage of degenerate `S=1` or `A=1` source instances.

The source-style budget is instantiated with `c_N=1/32768`: `32768 N(1−γ)^3 ε²≤log(SA)`. Under `SA≥16`, the reviewed `correctedFamily_common_budget` large branch gives `4096 N(1−γ)^3 ε²≤log K`, where the exact hard-family size is `K=1+mn`; multiplying the Fano budget by the coefficient relation gives the quarter-risk premise. The existing family Fano estimate then gives fixed-seed average decoder error at least `1/4`, and the shared-seed averaging theorem preserves that lower bound for one model. The decoder-error event is included in the strict policy Q-risk event by the existing pointwise gap theorem, with norm symmetry aligning `‖Q^π−Q*‖` and `‖Q*−Q^π‖`.

## Difference from the weaker unified wrapper

The earlier `.local/GenerativeLowerBoundKernelRisk.lean` exports only `>1/10` and includes an `SA<16` two-point branch. This candidate is restricted to `SA≥16` and exports the source-level `≥1/4` conclusion. It therefore closes that probability-threshold gap for the corrected large-family scope, subject to independent compile/axiom audit and production integration. It still concerns randomized estimation over deterministic stationary output policies; the action-randomizing policy counterexample in `docs/critic-generative-lower-bound-stochastic-policy-gap.md` remains outside this statement.

## Independent exact-source audit

The candidate was included in the fresh 37-module staged closure rebuild at `.local/seeded-kernel-independent-9sjP1f/out`. Its source hash matched this review. `sourceFamily_seeded_large_policy_risk_quarter` and `sourceFamily_kernel_policy_risk_quarter` both compiled from exact copies, and the import probe reported only `propext`, `Classical.choice`, and `Quot.sound` for each. No compile failed. This is a staged-source audit against existing read-only project dependency artifacts, not a production integration check.

Production integration: the reviewed source bodies compile in the project export, with qualified imports. In the seeded two-point risk module only, two local instance names were renamed to prevent collisions; the theorem statement and proof are unchanged. The full project check audited 2,373 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
