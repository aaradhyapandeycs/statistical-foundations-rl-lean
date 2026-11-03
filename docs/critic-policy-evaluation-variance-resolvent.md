# Independent review: true-policy variance resolvents

Reviewed 2026-11-02. Exact stable `.local/PolicyEvaluationVarianceResolvent.lean` SHA-256 `960f10723253fa82fbea2cfce6245fa6aee22992e246b958cc4f858bdbd80166`, independently recomputed. This reviewer owns only this report. The dependency is the previously reviewed staged `PolicyEvaluationVariance.lean`, hash `f25b76fadce9e452abe3375d2b8b5cf003df748ab6d737529cbe58b1b039d33d`.

## Verdict and exact constants

**PASS for the finite expansions, infinite square-root budget, literal true-matrix inverse identifications, scaled Jensen comparison and source-shaped positive-discount norm bound. The empirical comparison and horizon-three statistical theorem remain open.**

I independently checked the source at `generative_model_model_based.tex:295–350`, especially `eq:Jensen-I-gamma-P-Var`, `eq:I-gamma-P-Var-bound` and `eq:lemma-VarP-V-bound`. Let V be the actual true trajectory value, P the true policy kernel, σ=Var_P(V), B=‖V‖∞, γ the source discount and R=(I−γP)⁻¹. The final scaled norm statement is

`γ ‖R sqrt(σ)‖∞ ≤ B/sqrt(1−γ)`.

For γ>0, the separately proved unscaled statement is

`‖R sqrt(σ)‖∞ ≤ B/(γ sqrt(1−γ))`.

The source's stated upper bound is `sqrt(2/(1−γ)) B/γ`. The improved constant 1 follows from the already proved stronger potential bound on the variance budget; it is a valid strengthening, not an extra premise or a silent change to the source constant. A source closure annotation should identify that the stronger result implies the printed bound on the positive-discount domain. The unscaled theorem explicitly assumes γ>0, as required for division by γ.

## Correct powers and finite/infinite semantics

`evaluationPolicyKernelIter` is exactly repeated application of the true probability-row expectation, starting at f. `evaluationDiscountedKernelPartial` starts at zero and recursively adds f+γP(previous). Its proved finite expansion is `∑_{t<n}γ^t P^t f`.

The file now proves, rather than merely describing, the explicit expansions

`U_n = ∑_{t<n} γ^{t+2} P^t σ`

and

`Z_n = ∑_{t<n} γ^{t+1} P^t sqrt(σ)`.

Thus U has one γ² prefactor and Z one γ prefactor. The transition weighting is γ^t in both; no accidental γ^{2t} or (I−γ²P) inverse is substituted. The scalar-commutation lemma justifies moving the forcing's scalar through each repeated expectation. These are literal finite operator sums, not unproved trajectory-return variance formulas.

The new Z recursion is nonnegative and monotone, and is bounded uniformly by B/sqrt(1−γ). Its real supremum is taken only after proving finite boundedness, and monotone convergence identifies the limit. Passing a finite expectation sum through this limit yields Z=γsqrt(σ)+γPZ. Uniqueness uses the established value-Bellman contraction on differences; its ordinary reward term cancels. This does not assume the variance forcing is that reward.

The imported U budget is the actual monotone limit of its finite variance recursion. The limit comparison is `(1−γ)Z²≤U`, retaining the same powers and kernels as the finite result. No interchange of an unsupported infinite matrix series with an integral is used.

## Jensen weights and inequalities

The base finite-row Jensen lemma `(E f)²≤E(f²)` is derived from actual nonnegative row variance. It applies to each true policy transition row with unit normalization.

In the finite induction write d=1−γ, A=γsqrt(σ(s)) and C=PZ_n(s). The scalar inequality is

`d(A+γC)²≤A²+γd C²`.

Its exact nonnegative remainder is `γ(A−dC)²`. This is the correct weighted Jensen/Cauchy–Schwarz step with d+γ=1, d>0 and γ≥0; it does not incorrectly assign total weight one to a truncated geometric sum. Combining it with row Jensen and the prior induction inequality gives `(1−γ)Z_n²≤U_n`. All signs needed for nonnegativity and square roots come from actual variance, the positive denominator and nonnegative recursion. The limit preserves this inequality.

The literal matrix comparison then reads

`(1−γ) (γ R sqrt(σ)(s))² ≤ γ² R σ(s)`.

For γ>0 this is the source's squared Jensen comparison after cancellation; γ=0 is handled only in its scaled form. The proof need not separately postulate the inverse's stochastic row weights: it derives the relevant comparison through the real probability rows and the proved budget/inverse equality. No generic inverse-positivity theorem is assumed.

## Literal true matrix and trajectory semantics

`evaluationPolicyMatrix M π s t` is `(M.policyTransition π s).prob t`, with current-state rows and next-state columns. Its multiplication lemma identifies multiplication of a column value vector with the true row expectation definitionally. Consequently the matrix is the actual true Pπ with the source orientation.

`evaluationPolicyResolvent_isUnit` proves invertibility of I−γP by injectivity: equality on two vectors implies their difference has norm at most γ times itself. The finite probability-row bound and 0≤γ<1 force zero difference; the pinned finite-square-matrix injectivity theorem gives a matrix unit. All inverse instances in the bridge are produced from this proof. Mathlib's total nonsingular inverse cannot take its singular fallback on these inputs.

The two inverse identifications prove exactly

`R (γ²σ)=U` and `R (γsqrt(σ))=Z`.

They use the already proved infinite equations and actual nonsingular matrix cancellation. Matrix-vector linearity gives the separate pointwise scaled equalities. The final norm estimate correctly converts ‖γ⋅vector‖ to γ‖vector‖ using γ≥0, then applies the nonnegative Z budget bound. No absolute value or additional power of γ is lost.

V throughout is `M.trajectoryExpectedValue π`, the actual expected infinite discounted return under the controlled trajectory law, with the reviewed Bellman bridge. σ is its population variance under the true policy-induced transition row, not empirical variance or the variance of the total return. The source standing policy carrier is stationary randomized; the theorem handles that carrier directly.

For the literal matrix definition: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. The new supremum-defined budget has proved bounded existence, its defining equation and uniqueness, and no arbitrary choice or deferred meaning is used.

## Endpoint and inputs

All scaled theorems allow γ=0 and contain no division by γ. Then every finite U and Z term has a positive exponent of γ and is zero; their limits are zero, the true matrix is I, and the scaled inverse identities and Jensen bound remain valid. This does not imply σ=0 at γ=0, since next states can have different immediate rewards. The unscaled positive-discount corollary does not purport to cover zero. Zero value norm and zero variance also require no forbidden division and give zero budgets.

Input inventory: State/Action and finite instances are TYPING/STANDING; M expands to nonempty carriers, nonnegative normalized transition rows, reward in [0,1] and 0≤γ<1; π expands to stationary normalized probability action rows. A finite horizon/state query, arbitrary test vector, scalar or finite index set is TYPING for the corresponding algebra lemma. Candidate W plus its displayed equation is the defining antecedent of uniqueness, not a supplied equation for the constructed budget. Only the final unscaled corollary adds γ>0, explicitly matching its nonzero-discount source domain. No concentration certificate, empirical closeness, inverse assumption, or desired source bound is supplied as a premise. EXCESS=0 for these stated deterministic results.

## Remaining source and integration obligations

The source's informal empirical-versus-true resolvent approximation at lines 295–300 is not proved or assumed here. There are no samples, ε, δ or stochastic error event in this module. A source sample-complexity theorem still needs a rigorous empirical comparison, concentration for the actual algorithm and residual, and the sharp horizon-three arithmetic with all source constants/logarithms and precision range. The true-model square-root bound alone does not establish those claims or handle a policy chosen from the same data.

The file currently imports the staged variance dependency by its staging name. Production import changes, project compilation and imported-export axiom inspection remain separate integration tasks. Generic nonnegative inverse/row-sum theorems are not established by this file, although its required applications are proved without them.

The builder handoff `docs/builder-policy-evaluation-variance-resolvent.md` was checked against the stable source and correctly distinguishes proved true-kernel resolvent results from the unproved empirical comparison.

After coordinating one compiler slot, I copied the exact reviewed source unchanged to `.local/VarianceResolventIndependentAudit.lean` and appended `#print axioms` for **all 29 theorem exports**. I independently compiled the exact staged variance dependency into a fresh temporary directory as `PolicyEvaluationVariance.olean`, then ran `.local/lean .local/VarianceResolventIndependentAudit.lean` with that directory and the ordinary project/dependency artifact directories in `LEAN_PATH`. This avoided trusting a preexisting staged dependency artifact and changed no dependency artifact.

Both dependency compilation and the exact source/axiom probe exited 0 without diagnostics. Every one of the 29 theorem exports reported exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs in the reviewed source. The temporary dependency artifact and audit source were deleted. This verifies the stable staged implementation and its transitive axioms; future production integration still requires its own export check.

## Integrated import and actual export recheck

Independently recomputed the integrated source SHA-256 as `d971ae8c37d878fc3a64ed10f0c87ec4a9883abc6c2c210d6492b9e7bbe734de` for `Formalization/Generative/PolicyEvaluationVarianceResolvent.lean`. An exact byte comparison against the reviewed staged file passed: the **only** change is `import PolicyEvaluationVariance` becoming `import Formalization.Generative.PolicyEvaluationVariance`. All theorem, definition and proof bytes are unchanged. The semantic verdict above therefore applies to this precise integrated file.

The actual integrated `PolicyEvaluationVariance.olean` was present; the new resolvent object was not yet present. I compiled the exact integrated source to its own project artifact using:

`bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/PolicyEvaluationVarianceResolvent.olean Formalization/Generative/PolicyEvaluationVarianceResolvent.lean`

This exited 0 without diagnostics. I then ran `bash scripts/lean-local.sh .local/IntegratedVarianceResolventAudit.lean`; the temporary audit imported **only** `Formalization.Generative.PolicyEvaluationVarianceResolvent` and printed axioms for all 29 theorem exports listed in the staged source. It exited 0 without diagnostics, and every imported theorem reported exactly `propext`, `Classical.choice`, `Quot.sound`. This checks the actual built integrated export and its integrated dependencies, rather than redeclaring copied proof bodies. The temporary source was deleted. Compiler slots were coordinated with the other workers. This closes the import-only integration/export recheck; the missing empirical/statistical obligations above remain open.
