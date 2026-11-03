# Independent review: generic true-resolvent Jensen bridge

Reviewed 2026-11-03. Exact staged `.local/PolicyLearningTrueResolventJensen.lean` SHA-256 `0adf2b1d01b4c4463f5c6fec291e1fe549afc76be242374a2d744f72b2d00a2e`, independently recomputed. Handoff: `docs/builder-policy-learning-true-resolvent-jensen.md`. Reviewer owns only this report.

## Verdict and source correspondence

**PASS for deterministic true-inverse positivity/order, normalized row construction, generic nonnegative-input Jensen/norm comparison and the explicitly conditional residual transport. No fitted-value self-bounding or policy-learning probability theorem is established by this file.**

I independently compared the exact definitions/proofs with `generative_model_model_based.tex:305–318` (`eq:Jensen-I-gamma-P-Var` and its generic nonnegative-vector explanation), `:1381–1390` (residual transport), and `:2667–2693` (the later fitted-value variance application). Write h=1−γ>0, P=Pπ and R=(I−γP)⁻¹. The construction proves the source's actual normalized stochastic row hR(s,·), then Jensen for **arbitrary** nonnegative z. This is the genericity required for the empirical-value variance input; it does not falsely identify that empirical value as the true value of M.

The exact pointwise comparison is

`(h (R sqrt(z))(s))² ≤ h (Rz)(s)`,

and the norm consequence is

`‖R sqrt(z)‖∞ ≤ sqrt(‖Rz‖∞/h)`.

These constants and h powers match the source. The conditional row-residual result is

`γ‖R|f|‖∞ ≤ γ a sqrt(‖Rz‖∞/h) + γ b/h`

from the explicit antecedents z≥0, a,b≥0 and |f|≤a sqrt(z)+b. It keeps the γ factor on the linear term, a valid refinement before the source later uses γ≤1.

## Literal true matrix and produced positivity

`truePolicyResolvent` is literally the inverse of the **actual true-policy** matrix from `evaluationPolicyMatrix M π`, with current-state rows and next-state columns. It is not an empirical matrix or an arbitrary operator supplied with order assumptions. The integrated `evaluationPolicyResolvent_isUnit` proves the original finite matrix nonsingular for every valid M and π. All local `Invertible` instances are produced from that theorem; the total matrix-inverse singular fallback is unreachable.

The nonnegative-image proof uses a genuine minimum principle: if u−γPu=f≥0 and u(t) is a minimum, probability-row monotonicity gives Pu(t)≥u(t), hence (1−γ)u(t)≥f(t)≥0. Since h>0, u(t)≥0 and all coordinates are nonnegative. The argument uses the actual normalized nonnegative Pπ rows, not an assumed inverse sign. Finite nonemptiness is supplied by M.

The all-ones image is proved by solving `(I−γP)((1/h)1)=1` and applying the actual inverse. Monotonicity follows from nonnegativity of R(g−f), and entry nonnegativity follows from applying R to the nonnegative coordinate vector `Pi.single t 1`. The finite matrix multiplication gives R(s,t), with no transposition error.

## Normalized probability row and Jensen weights

`trueResolventProbabilityRow M π s` has literal mass `h R(s,t)`. Its nonnegative-mass proof uses h≥0 and the produced entry nonnegativity; its normalization uses the proved exact row sum R1=1/h. The factor is **h**, not 1/h. All fields of the genuine `FiniteDistribution` are proved; it is not merely a codomain standing in for an unproved stochastic object.

The expectation identity is exactly `E_(hR(s,·))[f]=h(Rf)(s)`. The generic finite-row inequality `(E sqrt(z))²≤E z` is obtained from the already proved actual finite variance nonnegativity, and z≥0 justifies `sqrt(z)²=z`. Applying it to the constructed row gives the literal h²-on-left/h-on-right comparison above. No probability assumption or empirical-value characterization is used in this Jensen step.

For the norm bound, R sqrt(z) is nonnegative by the produced inverse positivity, so its coordinate norm is its value. The pointwise Jensen inequality gives h²U(s)²≤hV(s); positive h cancels once to hU(s)²≤V(s)≤‖V‖∞. Division by h and monotonic square root give the stated uniform bound. The proof neither loses an h factor nor assumes a positive variance to cancel it.

Definition audit for R and the normalized row: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK for the genuine nonsingular inverse and row normalization; CHARACTERIZATION OK via the inverse theorem and proved row expectation identity; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. No default row or arbitrary selected family is introduced.

## Conditional transport and exact premises

The final helper applies actual inverse monotonicity to |f|≤a sqrt(z)+b1, then uses matrix linearity and R1=(1/h)1. Each coordinate of the result is at most a‖R sqrt(z)‖∞+b/h. Positivity of R|f| permits the coordinate-to-sup-norm step. Multiplication by γ≥0 and substitution of the proved Jensen norm bound finish the displayed inequality.

The expanded input families are the source finite nonempty MDP (nonnegative normalized transitions, known [0,1] reward, 0≤γ<1), a stationary normalized randomized policy, and arbitrary finite state vectors. z≥0 is the natural domain of the generic source square-root/Jensen statement. The conditional helper's a,b≥0 and row inequality are visible premises of that proof-step statement and are actually consumed. They are not inverse positivity, row-sum, Jensen, desired norm estimate or final source-error assumptions. EXCESS=0 for the declared deterministic/conditional scope.

In a source application, z will be the true-policy population variance of the realized empirical value, whose nonnegativity is separately proved for actual rows. f will be its actual empirical-minus-true residual. The required all-row event must still be supplied and its fitted-policy selection justified. No such stochastic conclusion is claimed here.

## Endpoints, data dependence and remaining bridge

All results allow γ=0. Then R=I, the normalized row is the coordinate point mass, and the generic Jensen inequality is valid (indeed equality pointwise for z≥0). The norm and conditional bounds divide only by h=1, while the γ-scaled transport is zero. Zero z/variance, constant functions and signed f are allowed; no division by variance, a norm or γ occurs. Discount approaching one remains finite as h>0.

The declarations are deterministic in M,π and their input vectors. They can be applied pointwise to a realized data-selected policy and variance without assuming policy independence, but doing so supplies no concentration theorem for those selected objects. The same actual true-policy kernel must be used in the fitted-value variance expansion, R and the residual; replacing it by another policy/model would not be justified.

This fills the generic arbitrary-σ true-resolvent Jensen/order ingredient missing from the earlier specialized actual-true-value module. It does **not** itself transport the fitted empirical-variance pointwise inequality, prove the resulting squared norm self-bound, identify actual true-vs-empirical trajectory error, solve the scalar self-bound as a model theorem, or establish policy suboptimality/sample complexity. Those source obligations remain distinct.

## Independent verification

Source review preceded the lead's separate compiler allocation. The imported integrated `PolicyEvaluationVarianceResolvent.lean` is the previously independently reviewed hash `d971ae8c37d878fc3a64ed10f0c87ec4a9883abc6c2c210d6492b9e7bbe734de`. With the explicitly allocated slot, I compiled `.local/TrueResolventJensenIndependentAudit.lean`, an exact unchanged copy of the reviewed source with `#print axioms` for all ten definitions/theorems, via `bash scripts/lean-local.sh`. It exited 0 without warnings or errors. Every export reported exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs in the source. The temporary probe was deleted, and the compiler slot was immediately released. This confirms the stable staged implementation/transitive axiom closure; production import/export integration remains a separate check.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningTrueResolventJensen.lean` is byte-identical to reviewed staged SHA-256 `0adf2b1d01b4c4463f5c6fec291e1fe549afc76be242374a2d744f72b2d00a2e`. The actual integrated module compiled; an import-only audit of its ten exported definitions/theorems succeeded with only `propext`, `Classical.choice`, and `Quot.sound`.
