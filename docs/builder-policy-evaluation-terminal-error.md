# Exact terminal auxiliary error: Step 4 handoff

`.local/PolicyEvaluationTerminalError.lean` proves the actual terminal error estimate required in source Step 4 (`generative_model_model_based.tex:550–582`), rather than assuming that estimate as a terminal input to recursive unrolling. It uses the actual empirical inverse norm, genuine auxiliary values and proved true-value growth. It also supplies terminal and weighted-terminal probability corollaries under the actual direct policy-row experiment. Independent review and integration remain pending.

## Deterministic terminal estimate

Write h=1−γ, e_l=‖Vhat_l−V_l‖∞ and b₃=sqrt(2)/(γ sqrt(h)). For arbitrary nonnegative residual coefficients a,c, the explicit conditional premise is the source intermediate rowwise bound

`|(P̂−P)V_l|(s) ≤ a sqrt(Var_{P(s)}(V_l)) + c‖V_l‖∞`.

`auxiliary_terminal_error_conditional` proves

`e_l ≤ γ/h * (a+c) * ‖V_l‖∞`.

The premise is a pointwise concentration event, not the desired terminal estimate. The proof uses the genuine empirical/true inverse comparison `e_l≤γ/h‖(P̂−P)V_l‖∞`. Population variance of V_l under any actual probability row is at most ‖V_l‖∞²; the existing proved next-reward bound therefore controls every coordinate of its square root by ‖V_l‖∞. This yields the residual norm ≤(a+c)‖V_l‖∞ and hence the result. No positivity of an arbitrary terminal value or assumed sharp terminal rate is used.

For γ>0, `auxiliary_terminal_error_growth_conditional` consumes the separately proved source geometric bound `‖V_m‖∞≤h⁻¹ b₃^m` and derives

`e_m ≤ γ/h² * (a+c) * b₃^m`.

`auxiliary_terminal_contribution_conditional` multiplies this proved error by the actual nonnegative unrolling weight `(γa)^m`, obtaining exactly

`(γa)^m e_m ≤ (γa b₃)^m * γ/h² * (a+c)`.

For the source intermediate choice a=sqrt(β₁/N), c=β₁/N, these instantiate to the terminal and raw α₁ bounds at lines 565–575. The factor γ is retained, every power is explicit, and no terminal estimate is assumed in any export.

## Actual-law corollaries with exact Bernstein constants

Let `L=log(4S(m+1)/δ)`, `a=sqrt(2L/N)` and `c=2L/(3N)`. For every valid finite MDP, fixed stationary randomized π, N>0, m∈ℕ and 0<δ<1, `auxiliary_terminal_error_bernstein` proves with probability **strictly greater than 1−δ** under the actual policy-row product law that

`e_m ≤ γ/h * (a+c) * ‖V_m‖∞`.

Its proof applies the already reviewed simultaneous Bernstein event through levels 0..m and selects the terminal coordinate `⟨m, m<m+1⟩`. It rewrites the actual empirical-minus-true expectation as the literal matrix residual and supplies it to the deterministic terminal lemma. It assumes neither a good event nor the terminal bound. Its radius retains the exact population Bernstein coefficient 1/3; setting β=2L gives c=β/(3N), tighter than the source's constant-absorbed β/N.

For γ>0, `auxiliary_terminal_contribution_bernstein` then proves, on an event with the same strict probability,

`(γa)^m e_m ≤ (γa b₃)^m * γ/h² * (a+c)`.

It composes the actual terminal event with source growth and multiplication by `(γa)^m`. No new concentration event, independence claim or extra confidence allocation is introduced. These are literal high-probability statements, not source-shaped conditional shells.

The true auxiliary values are fixed before sampling and are the source inverse/variance constructions; the empirical auxiliaries use the same true rewards and the same sampled matrix at every level. The original trajectory interpretation at level zero is inherited from the reviewed auxiliary module. The proof never treats a fitted empirical value as a fixed independent test vector.

## Endpoints and remaining arithmetic

The direct terminal estimate and its actual-law probability corollary allow γ=0: both inverse matrices are I, the shared auxiliary reward gives zero error and the right side is zero. The geometric-growth and weighted-contribution exports explicitly require γ>0 because b₃ divides by γ. They do not infer vanishing population variance at γ=0. N=1 and m=0 are covered; N=0 is excluded by empirical frequencies. Zero residual coefficients or zero auxiliary norm cause no invalid division.

The numerical source simplification `γa b₃=sqrt(2β₁/(hN))` and its `≤1/e` decay under `N>2e²β₁/h`, followed by simplification of the remaining prefactor, are assigned to the separate arithmetic builder. They are not assumed or asserted by this module. Geometric-sum control, final choice of m, logarithm comparison and the complete sharp policy-evaluation theorem likewise remain separate. This handoff supplies the exact raw weighted terminal contribution needed for that arithmetic.

## Verification

The module imports the actual integrated auxiliary growth, simultaneous Bernstein, residual recursion and empirical-resolvent modules. The lead explicitly allocated one compiler slot before compilation. `bash scripts/lean-local.sh .local/PolicyEvaluationTerminalError.lean` compiled without diagnostics after routine coefficient/denominator normalization fixes. An exact unchanged-source copy `.local/TerminalErrorAxiomAudit.lean` with five appended `#print axioms` commands compiled without warnings or errors using the same wrapper. All five theorem exports reported only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs. The temporary probe was deleted, and the compiler slot released immediately.

SHA-256 of `.local/PolicyEvaluationTerminalError.lean`: `29c50df335bf18e75083d8628817f16d5f076f6eb32e63465ed227752e306145`.

This is staged builder evidence against integrated dependencies. An independent reviewer must audit the exact source, conditional and probability scopes and imported objects before integration. An eventual integrated export needs its own byte comparison, build and imported-axiom check.
