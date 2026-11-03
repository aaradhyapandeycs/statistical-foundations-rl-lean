# General nonnegative Bellman forcing: variance-resolvent handoff

`.local/PolicyEvaluationGeneralForcing.lean` extends the reviewed true-policy variance-resolvent result from actual values of bounded-reward MDPs to the literal inverse value of **any fixed nonnegative real state forcing**, with no upper bound on that forcing. This addresses the domain issue in the source's repeated application of the variance-resolvent estimate to auxiliary rewards/values (`generative_model_model_based.tex:410–450`, especially `eqn:superV-true` and `eq:Vl-inf-norm-bound-0`). Independent review and production integration remain pending.

## Source object and theorem

For a finite source MDP M, fixed stationary randomized π, P=Pπ, γ=M.discount and R=(I−γP)⁻¹, the new definition is literally

`forcingPolicyValue M π f = R f`.

`forcingPolicyValue_bellman` and `forcingPolicyValue_unique` prove its complete Bellman equation and uniqueness over all real state vectors. `forcingPolicyValue_nonneg` proves it nonnegative when f≥0. No arbitrary candidate solution, presumed inverse property, positivity result or variance bound is supplied as a theorem premise.

For every fixed f≥0, writing W=Rf, the main theorem proves

`γ ‖R sqrt(Var_P(W))‖∞ ≤ ‖W‖∞/sqrt(1−γ)`.

For γ>0, the source-shaped corollary proves

`‖R sqrt(Var_P(W))‖∞ ≤ ‖W‖∞/(γ sqrt(1−γ))`.

The constant is 1, stronger than the source's displayed sqrt(2). The result applies to each source auxiliary level because every next forcing is the square root of a genuine row variance and hence nonnegative. It does not require these auxiliary rewards to remain bounded by 1. The source recursive sequence and its joint statistical analysis are not defined or closed in this file.

## Construction and actual-trajectory semantics

A direct search of the project's variance/forcing/resolvent declarations found the existing theorem specialized to `trajectoryExpectedValue`; the finite project's variance API had no scalar-scaling theorem. Pinned Mathlib has measure-theoretic variance scaling but does not directly target the project's finite expectation definition. The file proves the needed finite variance scaling from its literal second-moment definition and existing expectation linearity.

The proof uses a positive normalization C=max(1,‖f‖∞). Define a genuine MDP H with **the same transition as M**, the same discount, and action-independent reward f(s)/C. Its rewards lie in [0,1], proved from f≥0 and the finite sup norm. Thus the already reviewed actual-trajectory variance-resolvent theorem legitimately applies to H with no changed assumptions.

`normalizedForcingModel_value` proves H's actual trajectory value is R(f/C), by its proved trajectory Bellman equation and the genuine nonsingular matrix inverse. The same policy kernel and true matrix are unchanged definitionally. Matrix linearity yields W=C V_H, and actual-return nonnegativity yields W≥0.

The two proved scaling identities are

`Var_d(cV)=c² Var_d(V)`

and, for c≥0,

`sqrt(Var_d(cV))=c sqrt(Var_d(V))`.

Together with inverse linearity and norm scaling, multiplying H's reviewed resolvent inequality by C gives exactly the general inequality above. The normalization is an internal proved reduction, not an invented off-domain definition for the source forcing value; that exported value is Rf everywhere. No f≤1 or hypothetical bounded-normalized-value premise is added to the main theorem.

The new literal definition is meaningful because integrated `evaluationPolicyResolvent_isUnit` proves I−γP nonsingular for every admissible M and π. No singular inverse fallback is reached. The auxiliary normalized model is used only to transfer the already proved actual-trajectory theorem; no new random experiment or concentration assumption is introduced.

## Endpoints and scope

C≥1 covers f=0 without any division by its norm. All scaled results hold on 0≤γ<1. At γ=0, R=I and W=f; the scaled inequality is valid and no division by γ occurs. The unscaled corollary explicitly requires γ>0. The variance itself may remain nonzero at γ=0, and the file does not assert otherwise.

M still has the source normalized original rewards, but the theorem's arbitrary f need not equal them, be action-averaged, or be bounded by 1. The sole substantive additional premise is f≥0, exactly the property of every source auxiliary forcing. Finite carriers, MDP validity and fixed π are the existing source setting. The optional uniqueness helper's candidate equation is a characterization antecedent, not an assumption used to define W or prove the variance bound.

This module does not provide empirical/true comparison for every level, joint Bernstein concentration, recursive unrolling or terminal control, or the source's sharp sample-complexity theorem. Those remain distinct. It is builder evidence and requires independent source/semantic review.

## Verification

`bash scripts/lean-local.sh .local/PolicyEvaluationGeneralForcing.lean` compiled cleanly. An exact unchanged source copy `.local/GeneralForcingAxiomAudit.lean` with thirteen appended `#print axioms` commands also compiled via the same wrapper, exit 0 with no warnings/errors. Every definition/theorem export reports only `propext`, `Classical.choice`, `Quot.sound`; the temporary source was deleted. No `sorry`, `admit` or custom axiom occurs. Compiler use waited for an explicit lead slot and was coordinated within the two-compiler limit.

SHA-256:

- `.local/PolicyEvaluationGeneralForcing.lean`: `082412791d8577add90e6a97cd74f286a0d7bbfde6c2f0ae11dfc51b4ddb3323`.
- Integrated `Formalization/Generative/PolicyEvaluationVarianceResolvent.lean`: `d971ae8c37d878fc3a64ed10f0c87ec4a9883abc6c2c210d6492b9e7bbe734de`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

This is a staged builder check against existing integrated dependencies, not independent certification or production export integration.
