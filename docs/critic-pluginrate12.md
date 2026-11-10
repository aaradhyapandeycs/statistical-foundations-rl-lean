# Critic report: plug-in rate stages 1-2, matrix-inverse perturbation and entrywise concentration (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/Analysis/MatrixInversePerturbation.lean` and `Formalization/Ch7Rest/TDInferencePluginRate711.lean` (exports `exists_pathProb_lambdaHat_sub_gt_le`, `exists_pathProb_lambdaHat_inv_sub_gt_le` and the perturbation lemmas). Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT. Both modules are imported from `Formalization.lean`. No statement-index entry yet: the stage-2 bound holds only for `0 < ε ≤ 1` and targets the corrected `trueLambda` (SOURCE-ISSUES C43), so any later entry or prose must keep those restrictions and must not label it the printed Λ*.


Files (sha256 match builder STATUS):
- Formalization/Analysis/MatrixInversePerturbation.lean a0c522dd...
- Formalization/Ch7Rest/TDInferencePluginRate711.lean 40de0bee...

Commands: bash scripts/lean-local.sh on each file (no -o): both clean, no warnings/errors.
<local probe>: #print axioms on abs_inv_mul_mul_inv_transpose_sub_le,
abs_inv_sub_inv_apply_le, isUnit_det_of_abs_sub_le, norm_inv_sub_inv_le, exists_pathProb_lambdaHat_sub_gt_le,
exists_pathProb_lambdaHat_inv_sub_gt_le -> [propext, Classical.choice, Quot.sound]. No sorry/admit/axiom/set_option.

## Stage 1: ACCEPT
1. Invertibility of X is derived (kernel argument via (A^-1(X-A))v = -v, ||A^-1|| ||X-A|| < 1), never assumed.
2. Decomposition X^-1 Y X^-T - A^-1 G A^-T = (X^-1-A^-1)Y X^-T + A^-1(Y-G)X^-T + A^-1 G (X^-1-A^-1)^T checked by hand.
   Term bounds 4a^3 d(g+dY), 2a^2 dY, 2a^3 g d; sum <= 6a^3 S(g+dY)dX + 2a^2 dY with d <= S dX. Constants 6, 2 correct.
3. Norm is Mathlib linfty op norm (local instance); entry (s,s') of P Q R^T uses row s of P, row s' of R -> row sums,
   correct. Entry <= norm, norm <= S * max entry: correct. Smallness S a dX <= 1/2 implies a||X-A|| <= 1/2.
4. Minor: hypotheses g, dX, dY nonnegativity derived from abs bounds; fine.

## Stage 2: ACCEPT
5. Moments used: pathProb_exists_abs_aBar_sub_gt_le (S^2/(d^2 T)); exists_sum_pathWeight_mul_sq_gammaHat_sub_oracle_le
   (exists C, forall T>=1, i: <= C/T -- C uniform in T, i); sum_pathWeight_mul_sq_oracleGammaHat_sub_le (2B^4/T).
   Chebyshev via pathProb_lt_abs_le_div; union bound over EA, ES i, EO i via pathProb_union_le / pathProb_exists_le.
6. Off-diagonal Gamma-hat entries are exactly 0 (gammaHatAt_apply), so entrywise closeness to diag(Gamma_true) holds.
7. Junk inverse: complement of bad event gives entrywise d-closeness with S a d <= 1/2, so stage 1 forces Abar
   invertible; singular event is inside the bad event. Same for Lambda-hat^-1 (abs_inv_sub_inv_apply_le derives
   invertibility of Lambda-hat). Bound does not depend on the junk convention.
8. C = K^2 D + 1 (and C1 K^2) depends only on M, pi, mu, eta0, V0 (via Csub); independent of T and eps. Confirmed by
   quantifier order in the #check.
9. eps <= 1 is used only to get d <= 1 and S a d <= 1/2. It is a genuine restriction (bound for eps > 1 is NOT
   derivable by monotonicity, since C/(eps^2 T) shrinks); harmless for consistency/rate use, but any statement-index
   entry or prose must keep "0 < eps <= 1" and not claim all eps > 0.
10. Hypotheses: full-support mu, 0 < eta0 <= 1, V0 arbitrary, [Nonempty State] (inherited from substitution lemma);
   Gamma_true > 0 only in the inverse theorem. No hidden hypotheses. Target is the corrected trueLambda (C43);
   must not be labelled as the printed Lambda*.
11. Cosmetic: g = sum |Gamma_true| is loose (max suffices); not a correctness issue.
