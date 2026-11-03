# Independent review: general nonnegative forcing

**Verdict: pass for the stated true-resolvent intermediate result.** The staged theorem applies the already established actual-trajectory variance bound to any fixed nonnegative state forcing, without imposing an upper bound on that forcing. It does not prove the paper's full policy-evaluation sample theorem.

## Source and exact meaning

The relevant source is `source/upstream/tex/chapters/generative_model_model_based.tex:295–350` (true-policy variance-resolvent bound) and `:413–455` (the auxiliary reward/value sequence). On finite state and action types, with the existing admissible discounted MDP M and stationary randomized policy π, let P be the true policy transition matrix, γ the discount, and R=(I−γP)⁻¹. The literal definition `forcingPolicyValue M π f` is Rf. The existing `evaluationPolicyResolvent_isUnit` establishes invertibility for these inputs; the argument does not rely on the value of matrix inverse at a singular matrix.

For every real state vector f with f(s)≥0 for all s, setting W=Rf, `forcingPolicyValue_varianceResolvent_bound` proves

    γ ‖R sqrt(Var_P(W))‖∞ ≤ ‖W‖∞ / sqrt(1−γ).

The variance and square root are taken rowwise. The norm is the finite state sup norm. No concentration event, empirical kernel, bound on f, or candidate solution to the desired inequality is assumed. `forcingPolicyValue_bellman` and `forcingPolicyValue_unique` hold for arbitrary real f; the candidate Bellman equation in the uniqueness lemma is a characterization premise, not a premise of the bound. The separate positive-discount corollary divides by γ and gives constant 1, stronger than the source's displayed √2 constant.

The source's successive auxiliary rewards are square roots of row variances and therefore nonnegative. An independent Lean probe importing the existing auxiliary module checked by definitional equality that each successor `auxiliaryValue` is exactly `forcingPolicyValue` applied to the corresponding successor `auxiliaryReward`. This establishes the object-level fit; this file does not itself export an induction giving the full auxiliary sequence growth bound.

## Normalization and scale audit

The proof sets C=max(1,‖f‖∞), so C>0 even for f=0. `normalizedForcingModel` is a genuine bounded-reward MDP with the original transitions and discount and action-independent reward f(s)/C. Its lower reward bound uses f≥0; its upper bound follows from |f(s)|≤‖f‖∞≤C. Thus the policy transition matrix and the resolvent have the same orientation and entries as for M, and the existing actual-trajectory variance result legitimately applies to the constructed model.

`normalizedForcingModel_value` derives its actual expected trajectory value as R(f/C), using the actual Bellman equation and invertibility. Matrix linearity yields W=C V_H, not merely an assumed relation. `forcing_variance_const_mul` proves Var_d(cV)=c²Var_d(V) for every real c, and the square-root identity assumes c≥0. Applying these identities with C>0, including inverse and sup-norm scaling, transfers the normalized trajectory inequality with precisely the scale shown above. The proof introduces no new probability law or statistical independence assumption.

All scaled statements cover the MDP's full 0≤γ<1 range. At γ=0, R=I and W=f; the scaled inequality is trivial but the row variance can remain nonzero. The unscaled corollary correctly requires γ>0 and makes no division-by-zero claim.

## Boundary of the result

This is a true-policy resolvent estimate, not an empirical-versus-true comparison, joint concentration result, recursive closure, terminal estimate, or H³ sample-complexity theorem. The source auxiliary recursion and its statistical analysis require their own proved connections. The normalization construction is internal to the proof; the exported forcing value remains the true literal inverse Rf.

## Independent verification

Reviewed staged source SHA-256: `082412791d8577add90e6a97cd74f286a0d7bbfde6c2f0ae11dfc51b4ddb3323`. Its integrated variance-resolvent dependency SHA-256: `d971ae8c37d878fc3a64ed10f0c87ec4a9883abc6c2c210d6492b9e7bbe734de`. Source TeX SHA-256: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

An exact copy of the staged source, retaining its original imports and with twelve appended `#print axioms` commands, compiled using `scripts/lean-local.sh`, exit 0. The definition, scale positivity, normalized model and value, trajectory scaling, nonnegativity, both variance-scaling identities, main bound, Bellman equation, uniqueness, and positive-discount corollary use only `propext`, `Classical.choice`, and `Quot.sound`. A separate copy with an additional auxiliary-module import compiled the definitional successor specialization and the independent γ=0 identity. That extra-import probe is distinguished from the original-import audit. The builder's own handoff reports a clean exact-source compile and thirteen axiom checks. This review concerns the staged source; integrated export verification remains separate.

## Integrated export verification

The production `Formalization/Generative/PolicyEvaluationGeneralForcing.lean` has the identical reviewed SHA-256 `082412791d8577add90e6a97cd74f286a0d7bbfde6c2f0ae11dfc51b4ddb3323`. The actual production module was rebuilt, then an import-only audit checked all thirteen declarations, each with only `propext`, `Classical.choice`, and `Quot.sound`.

The production `Formalization/Generative/PolicyEvaluationResidualRecursion.lean` has SHA-256 `e367e73e26e5219fbcd57314ec557bb3c2b9164f7391a759400cea842e098ca7`. Its only difference from staged SHA `860c81d21b55b58df3b9eefe66c341ee3a60f7edd9cfd67c66e1b089be0c8c4d` is qualification of the two project import paths. The actual integrated module compiled, and an import-only audit of `auxiliary_residual_identity` and `auxiliary_residual_recursion_conditional` reported the same three standard axioms. This paragraph records integration and axiom checks; its source/semantic review is separate.
