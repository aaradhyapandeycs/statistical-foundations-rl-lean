# Independent review: conditional auxiliary residual recursion

Reviewed 2026-11-02. Exact staged target `.local/PolicyEvaluationResidualRecursion.lean` SHA-256 `860c81d21b55b58df3b9eefe66c341ee3a60f7edd9cfd67c66e1b089be0c8c4d`. This reviewer owns only this report. Exact path and builder handoff `docs/builder-policy-evaluation-residual-recursion.md` were confirmed directly by the builder and lead.

## Verdict and source scope

**PASS for the exact auxiliary residual identity and the explicitly conditional deterministic recursion. Neither source step (iv), a high-probability recursion nor the sharp source theorem is established by these two declarations.**

I independently checked raw `generative_model_model_based.tex:461–495`: the perturbation identity `eq:Vl-Vhat-l-perturbation`, Bernstein residual `eq:Bernstein-Vl`, and steps (i)–(iii) of `eq:upper-bound-Vl-Vhatl`. Write P=Pπ, P̂ the actual empirical policy-row matrix, Rhat=(I−γP̂)⁻¹, V_l the true auxiliary value, and Vhat_l=Rhat r_l with the same **true** auxiliary reward r_l.

The exact first theorem is

`Vhat_l−V_l = γ Rhat (P̂−P) V_l`.

Given nonnegative coefficients a,c and the explicit pointwise antecedent

`|(P̂−P)V_l|(s) ≤ a sqrt(Var_{P(s)}(V_l)) + c‖V_l‖∞`,

the second theorem proves

`‖Vhat_l−V_l‖∞ ≤ γa(‖Vhat_(l+1)−V_(l+1)‖∞ + ‖V_(l+1)‖∞) + γc‖V_l‖∞/(1−γ)`.

For source choices a=sqrt(β₁/N), c=β₁/N, these are exactly steps (i)–(iii), retaining rather than prematurely discarding the γ coefficient of the linear term. The theorem treats a and c generically and does not claim the source probability event supplying them.

## Actual objects and algebra

The auxiliary definitions were inspected directly. V₀ is the actual true trajectory value, with proved equality to the inverse applied to the known policy reward. At later levels V_(l+1)=R sqrt(Var_P(V_l)); r_(l+1) is that same fixed true standard-deviation vector. Vhat_l applies the **same empirical matrix at every level** to r_l. The empirical matrix is the actual frequency kernel, with reward/discount and data arguments unchanged. These are source auxiliary analysis objects, not an independently sampled empirical variance sequence.

The exact identity consumes the reviewed arbitrary-vector empirical/true inverse identity with f=r_l, then the proved equality Rr_l=V_l. Multiplication order, empirical-minus-true sign and factor γ match the source. Both inverses are justified by genuine finite-matrix nonsingularity from probability-row contraction; no inverse assumption or singular fallback enters the new declarations.

The recursion proof sets g=sqrt(Var_P(V_l)), z=(P̂−P)V_l and b=c‖V_l‖∞. It uses the actual empirical inverse's proved absolute-value domination and monotonicity to obtain `|Rhat z|≤Rhat|z|≤Rhat(ag+b1)`. Matrix linearity and the exact row-sum theorem give `Rhat(ag+b1)=a Rhat g + b/(1−γ)`. Crucially Rhat g is **definitionally Vhat_(l+1)**, since the next reward is the same true variance vector. It is not replaced with the true next value before the triangle inequality.

The coordinate estimate bounds Vhat_(l+1)(s) by its finite sup norm, multiplies by a≥0, and yields `‖Rhat z‖∞≤a‖Vhat_(l+1)‖∞+b/(1−γ)`. The final triangle bound `‖Vhat_(l+1)‖≤‖Vhat_(l+1)−V_(l+1)‖+‖V_(l+1)‖`, followed by multiplication by γ≥0, proves precisely the displayed conclusion. Denominator 1−γ is strictly positive. No square root or norm scaling constant is lost.

## Positivity and conditional-input audit

The imported empirical order proof is based on a true minimum principle: for f≥0, the inverse solution u of u−γP̂u=f cannot have a negative minimum when P̂ is stochastic and 0≤γ<1. This proves nonnegative inverse action. Applying it to differences yields monotonicity; applying monotonicity to ±z≤|z| yields absolute-value domination. The row-sum identity follows from solving the inverse equation on the constant vector 1. These source-relevant facts are produced proofs, not hypotheses of the recursion.

Expanded input families are:

| Input | Classification for this conditional helper |
|---|---|
| State, Action; finite instances | TYPING/STANDING source finite MDP |
| M nonempty carriers, normalized nonnegative transition rows | STANDING |
| M deterministic known reward in [0,1], 0≤γ<1 | STANDING |
| π and its normalized nonnegative action rows | SOURCE/TYPING fixed stationary policy |
| N and hN:0<N | SOURCE empirical frequency domain |
| data, level l | TYPING arbitrary sample/auxiliary index |
| a,c | TYPING generic residual coefficients |
| ha:0≤a, hc:0≤c | SOURCE domain of the conditional coefficient statement |
| hres: displayed rowwise residual inequality | CONDITIONAL proof-step antecedent; not a premise of the source main theorem |

The antecedent is visible and matches the source's intermediate concentration result. It is appropriate in a separately named conditional helper. If the same antecedent were retained as a premise of a claimed main sample-complexity theorem, it would be EXCESS and the source audit would fail. The current file does not make that claim or hide hres in a bundle. No target-shaped bound is assumed elsewhere in the proof.

All three nonnegative inputs are meaningfully used: γ for norm scaling/inequality preservation, a for replacing a next-value coordinate by its norm and applying the triangle bound, c for a nonnegative uniform bound in the finite pi-norm argument. The true auxiliary values need not have normalized rewards at every level; this helper uses only their literal inverse/reward definitions, not a false assertion that all auxiliary rewards are ≤1.

## Zero discount, data dependence and remaining work

Both declarations hold at γ=0. Then true and empirical matrices are I and their auxiliary values use the same reward, so the left difference is zero at every level and outcome; the recursion right side is also zero. The proof divides only by 1−γ, never by γ. Positive γ is needed only in later source-shaped growth estimates that explicitly divide by γ, not in this helper.

The result is deterministic and pointwise in data. hres may be supplied from an actual concentration event, but this file neither constructs that event nor asserts the vector is independent. The true auxiliary V_l depends only on M,π,l and is fixed before data, making the source fixed-vector Bernstein strategy plausible. A rigorous high-probability recursion still needs a simultaneous event for every required level/row, explicit coefficients, and term-level application of this helper on that event.

Step (iv) requires the general nonnegative-forcing variance-resolvent estimate at every level and its connection to these exact auxiliaries. The original specialization only to actual Vπ is insufficient. A separately proved general-forcing module now exists as staged builder work; this review does not certify that new module (the reviewer authored it), nor does this recursion file consume it. Geometric unrolling, terminal control, sample arithmetic and the final source theorem remain separate obligations. The factor-64 transition in that later argument has its own reviewed deterministic low-sample repair.

## Identity and independent verification

Staged dependency hashes independently recomputed: `PolicyEvaluationAuxiliary.lean` `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95`; `EmpiricalResolventOrder.lean` `bed62174679d0a11f0778702e29f77a004d144a26d5e8f5b4661644ffafd0bf5`. These match the builder handoff. The source chapter hash is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

After source review and the lead's explicit compiler-slot allocation, I independently compiled the exact staged `PolicyEvaluationAuxiliary.lean` and `EmpiricalResolventOrder.lean` sources into a fresh temporary directory, preserving their expected module names. With that directory plus the ordinary project/dependency artifact paths in `LEAN_PATH`, I ran `.local/lean .local/ResidualRecursionIndependentAudit.lean`. The probe copied the exact reviewed recursion source unchanged and appended two `#print axioms` commands.

Both dependency compilations and the exact-source probe exited 0 without diagnostics. `auxiliary_residual_identity` and `auxiliary_residual_recursion_conditional` each reported exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs in the reviewed file. The fresh staged dependency artifacts and temporary probe were deleted, and the compiler slot released immediately. This does not trust preexisting staged `.olean` files and establishes the actual staged transitive axiom scope. Production import changes and integrated-export checks remain separate.
