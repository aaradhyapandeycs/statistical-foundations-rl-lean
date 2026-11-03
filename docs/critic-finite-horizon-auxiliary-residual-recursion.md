# Independent review: finite-horizon auxiliary residual recursion

Reviewed staged source `.local/FiniteHorizonAuxiliaryResidualRecursion.lean`, SHA-256 `a0d565123dd0458b4db4ce10c2234f50de77c338eaa89ccf5100dd8f494ecc09`. Exact staged dependencies: `.local/FiniteHorizonAuxiliaryGrowth.lean` SHA-256 `9df2d4d8bbeaf8ca5f9c47d66e6e06c85d161a90fb65082530b8eccb5a9bd1c3`, which depends on `.local/FiniteHorizonAuxiliaryVariance.lean` SHA-256 `19f843f138314e21a14d5b29eef88e758add4389dbbcfa7eb225e496bc68d4ee`; and `Formalization/Generative/PolicyEvaluationRecursiveUnroll.lean` SHA-256 `65c60bebfc05de1b07abd78569e1d9f19f0363e72a3d31990e29044693451109`. The variance module's imported production sources are `Formalization/Generative/FiniteHorizonPolicyPerturbation.lean` SHA-256 `3e76d105323d8118763f0a2959e07666d2bb38d9ccd8d888dce40341cd8dc370` and `Formalization/Probability/Variance.lean` SHA-256 `541714ed6173402131bece633476308c1c832f31d0cbb46534cc55f48dcd9553`.

This is a source/semantic review only; no Lean compiler was run. The comparator is Li et al., [*Breaking the Sample Size Barrier in Model-Based Reinforcement Learning with a Generative Model*, arXiv:2005.12900v8](https://arxiv.org/pdf/2005.12900v8), Section 7.2, equations (61)–(64), Lemma 9, and Appendix C.1, equations (113)–(119), especially equations (113), (115), and (117).

## Recursion and transition orientation

`policyRowResidual E F V s a` is `F.transition` expectation minus `E.transition` expectation, i.e. `(P̂−P)V` when F is the empirical row and E is the true row. The residual condition is stated rowwise for the true next-stage value `V_{h+1}^{(l)}`. Its right side is

`a · auxiliaryPolicyReward(..., l+1) + b · ‖V_{h+1}^{(l)}‖∞`.

By the reviewed auxiliary definition, `auxiliaryPolicyReward(...,l+1)` is exactly `sqrt(Var_P(V_{h+1}^{(l)}))`; therefore `a=√(β₁/N)` and `b=β₁/N` instantiate the paper's (63). The true sequence propagates with E's true transition. The comparison/empirical sequence uses the identical true-derived forcing at every level and propagates with F's comparison transition. In `auxiliary_difference_cons`, the shared forcing cancels and the continuation error is propagated by F, exactly matching the source's telescoping through empirical matrices in C.1. No empirical variance is substituted for the source variance.

## Coefficients, level and horizon indices

The helper `auxiliary_error_le_comparison_successor` is the pointwise version of the source one-step bound (113)/(115): it bounds the level-l true/comparison difference by `a` times the level-(l+1) comparison value plus `b` times the number of remaining stages times the source growth envelope for level l. The residual is applied to level l, while the variance forcing is level l+1; this is the required off-by-one relationship.

Using `‖V^{(l)}‖∞≤H c^l`, where `c=√(3H)` comes from the separately reviewed Lemma 12 module, the code's `auxiliaryErrorNorm_level_recursion` yields

`E_l ≤ a E_{l+1} + a H c^(l+1) + b H² c^l`

for `E_l=‖V̂^{(l)}−V^{(l)}‖∞`. The first additional term is from replacing the nonnegative comparison successor by true successor plus error; the linear term is `b · H` stage accumulation times `H c^l` true-value growth. This is the source recursion structure of (117). The unrolling coefficient is correctly factored as `C c^l`, with `C=a H c+b H²`, and the geometric ratio is `a c`; `auxiliaryErrorNorm_unroll` retains the terminal error `a^m E_m` and assumes the explicit residual condition for exactly `l<m`, so it does not omit an endpoint estimate or assert a log-depth choice.

The finite list convention is consistent: a list with at most H stages is compared stage-by-stage; the empty suffix contributes zero. The `pairs.length` accumulation is bounded by H, and the source growth bound is instantiated for every suffix. The result is pointwise for a fixed deterministic nonstationary policy parameter and applies at every stage suffix through the list formulation.

## Scope and remaining obligations

The module does not prove the residual condition (63), a probability event, policy-suffix independence, the chosen level depth m, a terminal-level bound, sample-size arithmetic, or the final Lemma 9 conclusion (64). `auxiliaryErrorNorm_unroll` deliberately keeps its terminal error premise visible. The data-dependent empirical optimizer application still needs the separate future-only policy-selection/independence argument and a single simultaneous residual event; the source's growth factor and C.1 recursion do not supply those probabilistic inputs. The source review found no coefficient, propagation-orientation, or level-index mismatch.


## Independent exact-source compile and axiom evidence

After source review and explicit slot allocation, I copied the exact reviewed residual, growth, and variance sources into `.local/finite-horizon-residual-independent-mprSzj/src/` and compiled the variance dependency first, then growth, then residual recursion, into the fresh sibling `out/` directory. The variance compile used `bash scripts/lean-local.sh -o`; subsequent staged imports resolved from the fresh output path. The recursive-unroll import resolved from the existing production artifact whose source hash is recorded above; no dependency rebuild occurred. All three compile logs are empty. A separate probe imported the fresh residual artifact and ran `#print axioms` for all 42 exports across the three staged modules (23 variance, 10 growth, 9 residual recursion). Every export uses only `propext`, `Classical.choice`, and `Quot.sound`. This is staged exact-source validation against the pinned existing unroll/project artifacts, not a production integration build. The earlier `.local/finite-auxiliary-audit/ResidualImportAudit.lean` log was not relied upon.

Production integration: the actual production module matches the independently reviewed source body, with qualified imports. The full project check compiled the exports and audited 2,406 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
