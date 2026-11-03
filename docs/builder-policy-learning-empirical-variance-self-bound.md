# Empirical-value variance self-bound: bounded helper and source-first plan

`.local/PolicyLearningEmpiricalVarianceSelfBound.lean` proves the exact pointwise expansion and upper inequality in `generative_model_model_based.tex:2637–2665` (`eq:empirical-value-variance-identity`), including its actual fitted-policy specialization. It also proves the numerical AM-GM closure used at `:2696–2715`. The intervening true-resolvent order/Jensen/norm bridge is explicitly **not** assumed or proved. Independent source review and integration remain pending.

## Actual values and exact expansion

Let M be the true model, H any other valid discounted model sharing its reward and discount, π the same stationary randomized policy in both, γ=M.discount, h=1−γ,

`W = H.trajectoryExpectedValue π`,

`r(s) = E_(π(s))[M.reward(s,·)]`,

`z(s) = E_(H.policyTransition π s)[W] − E_(M.policyTransition π s)[W]`.

The only model comparison premises are the unchanged known reward and discount; no kernel closeness or value approximation is assumed. `empiricalPolicyValue_bellman` consumes the actual trajectory Bellman theorem for H. `empiricalPolicyValue_variance_identity` proves exactly

`γ² Var_P(W) = γ²P(W²) − W² + 2Wr − r² + 2γ(W−r)z − γ²z²`.

This expands `γPW=W−r−γz`, which is proved from H's actual Bellman equation. Every residual sign, square and γ power is explicit. No desired variance estimate or resolvent bound is an input.

`empiricalPolicyValue_continuation_bounds` derives

`0≤W−r≤γ/h`

from the empirical Bellman equation, normalized empirical policy rows and H's actual trajectory bounds. Those are not supplied as extra hypotheses. Using these bounds, γ²≤γ, r≤1, W≤1/h and nonnegative discarded squares, `empiricalPolicyValue_variance_selfBound` proves the literal source inequality

`γ² Var_P(W) ≤ (γP−I)W² + 2/h + (2γ²/h)|z|`.

This is the precise source constant 2, rather than an unspecified universal factor. Its derivation uses `Wr≤1/h` and `2γ(W−r)z≤(2γ²/h)|z|`; the two negative square terms are discarded only after their nonnegativity is established.

## Actual empirical-optimal specialization

`policyEstimator_empiricalVariance_selfBound` instantiates the result with H equal to the **actual sample-built empirical policy-learning MDP** and π equal to the actual data-dependent empirical greedy point-mass policy. Reward/discount agreement is discharged by reflexivity. H's actual trajectory value under that same policy is definitionally the actual `valueEstimator`. Consequently the variance is under the original true policy row, applied to the actual fitted empirical optimal value, exactly as in the source.

The result is pointwise for every positive sample count and every observation array. It makes no independence or probability claim, so selecting this data-dependent π introduces no illicit fixed-policy concentration step. The source's earlier all-row event is what will eventually control z under this selection; that event is not assumed by this pointwise inequality.

## Source-first plan for the missing true-resolvent bridge

Let R=(I−γPπ)⁻¹ and σ=Var_P(W). The remaining proof obligations are:

1. Prove/use true-resolvent positivity, monotonicity and `R1=(1/h)1` on arbitrary vectors, then apply R to the **proved** pointwise inequality. Exact inverse cancellation gives

   `γ² Rσ ≤ −W² + 2/h² + (2γ²/h)R|z| ≤ 2/h² + (2γ²/h)R|z|`.

2. Prove Jensen for arbitrary nonnegative σ under the actual true resolvent, not just for variance of its own true value. One route constructs the normalized row distribution `h*R(s,·)` from positivity and unit row sum. Finite-row Cauchy/Jensen then gives `(R sqrt(σ))²≤Rσ/h` pointwise. This is the precise bridge still absent from the new helper.

3. Take finite sup norms, use γ≤1, and set `S=γ‖R|z|‖∞`. The preceding bounds should produce

   `γ²‖R sqrt(σ)‖∞² ≤ 2/h³ + 2S/h²`.

4. Consume the all-row Bernstein/variance-transfer event, then select the empirical greedy action inside that event. True-resolvent order/row sum give

   `S ≤ γ sqrt(β/N) ‖R sqrt(σ)‖∞ + 2β/(Nh²)`.

   Combining with the squared variance inequality and square-root subadditivity yields

   `S ≤ A + 2B + sqrt(2BS)`,

   with `A=sqrt(2β/(Nh³))` and `B=β/(Nh²)`.

No step here may simply apply the earlier true-value/general-nonnegative-forcing variance-resolvent bound to W: W solves the **empirical** Bellman equation, and its forcing relative to the true P is r+γz, which need not be nonnegative. The residual correction is essential. Likewise the generic arbitrary-σ Jensen statement must be supplied; the previously reviewed actual-true-value specialized Jensen theorem is not automatically that statement.

## Proved numerical closure and precise scope

`policyLearning_selfBound_amgm` proves `sqrt(2BS)≤B+S/2` for B,S≥0. `policyLearning_selfBound_solve` then proves

`S≤A+2B+sqrt(2BS)  →  S≤2A+6B`.

These are explicitly conditional **numerical lemmas**. They do not claim the unresolved stochastic/resolvent relation as a theorem about the model. Substitution of A and B gives exactly the source Lemma `lem:empirical-value-residual` constants `2sqrt(2β/(Nh³))+6β/(Nh²)` after the missing bridge is proved. No extra high-sample regime is needed for this numerical closure.

The later policy suboptimality comparison still requires the separately controlled evaluation error of a true optimal policy and the empirical-optimal value error, as in the source decomposition. This file does not prove that final policy-learning theorem, its Q consequence, probability bound, universal sample constant or N-dependent logarithm. It establishes the exact pointwise deterministic ingredient and the scalar last step, not the complete named residual lemma.

## Endpoints and assumptions

All pointwise identities and bounds hold for 0≤γ<1, including γ=0, and divide only by h>0. At γ=0, W=r and the scaled identity is still exact. The unscaled population variance and transition residual can remain nonzero, but their γ-scaled contributions vanish. No positive variance or value norm is required. The actual empirical corollary includes N=1 and excludes N=0 solely because empirical frequencies require a positive count.

The numerical closure requires B≥0 and S≥0, both automatic for the intended source substitutions. It needs no assumed A positivity or final estimate. All other premises are source finite-MDP validity, stationary policy typing and the explicit same-known-reward/discount conditions of the deterministic model comparison.

## Verification

The file imports integrated actual policy-learning and true-variance modules. It was compiled after an explicit lead slot allocation. `bash scripts/lean-local.sh .local/PolicyLearningEmpiricalVarianceSelfBound.lean` passed without diagnostics after routine denominator normalization. An exact unchanged-source copy `.local/EmpiricalVarianceSelfBoundAxioms.lean` with eight appended `#print axioms` commands also compiled without warnings/errors. The residual definition and all seven theorem exports reported only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs. The probe was deleted, and the compiler slot released immediately.

SHA-256 of `.local/PolicyLearningEmpiricalVarianceSelfBound.lean`: `55c8045d77c988c70228066f28f485e134de5ca1a78ebf8ce6a760bd7e24c95c`.

This is staged builder evidence. Independent review must check the exact empirical residual sign, γ powers, actual-value bounds and conditional numerical scope. Production integration and actual imported-export checks remain separate.
