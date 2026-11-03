# Independent review: empirical-optimal all-row residual

Reviewed 2026-11-03. Exact staged `.local/PolicyLearningEmpiricalOptimalResidual.lean` SHA-256 `c1ac0b61d3af7c76c05d2a56f14f2dd49e1c1f6225988e35130bc128b35fe8fb`, independently recomputed. Builder handoff: `docs/builder-policy-learning-empirical-optimal-residual.md`. Reviewer owns only this report.

## Verdict and exact source scope

**PASS for the stated actual-law all-state/action residual estimate. This completes the staged transfer step corresponding to `eq:Phat-sa-Vhat-star-concentration-proof-mb-tight`, not the subsequent self-bounding lemma or full policy-learning theorem.**

I independently checked raw `generative_model_model_based.tex:1334–1378`. The source first obtains one simultaneous fixed-grid event, chooses a close grid member only inside that event, transfers its population-standard-deviation radius to the actual empirical optimal value, simplifies using β₁≥4 and N≥1, and only then may select an empirical greedy action. The implementation follows that order and retains the exact source β and final constant:

`β₁ = 2 log(16SAN/((1−γ)δ))`,

`|(P̂_(x,a)−P_(x,a))Vhat*| ≤ sqrt(β₁/N) sqrt(Var_(P_(x,a))(Vhat*)) + 2β₁/(N(1−γ))`.

The probability statement is a **single event** with probability strictly greater than 1−δ/2 and universal quantification over every x,a. It is not an expectation bound, one-row marginal claim, separately chosen event per action, or concentration of an independent surrogate substituted for Vhat*.

## Actual definitions and common event

The underlying `samplingLaw M N` is the actual joint product of true state-action transition rows, indexed by ((x,a),i). The empirical row is its actual observed frequency vector. `valueEstimator M N hN data` is the actual trajectory value of the empirical model's chosen optimal greedy policy, with previously proved empirical trajectory optimality. It is not a true optimal value or an abstract fixed-point placeholder.

The imported `leaveOneOutGrid_allRows_bernstein` is bound to one event quantifying simultaneously over x,a and all fixed grid indices i∈Fin(N+1). Its actual fixed-u absorbing value family may depend on retained off-state data, and its independence from the removed row is proved through the actual product law; it is not assumed independent of the whole empirical matrix. The new module does not redo or weaken that experiment. The independently reviewed all-row handoff/report is bound to hash `c28ab6963d52be915aedc7909d6ad6c894bf6666e0cb9312f33a45ce67dc1189`.

Within an outcome in this event, the proof invokes the actual empirical value-cover theorem at state x. That supplies an index i with distance at most 1/[N(1−γ)] from the actual fitted value. `leaveOneOutGridValue_eq_gridValue` identifies the event's vector with the cover's absorbing optimal trajectory vector of the **same empirical MDP, data, state, parameter and sample count**. This is term-level object consumption, not a similarly named theorem or assumed closeness.

The resulting grid inequality is obtained by specializing the already universal event to i. No claim that this selected index is independent of row samples is made. The choice may depend on the full data; universal control before selection is exactly what makes it legitimate. There is no second confidence event or intersection loss at this transfer stage.

## Exact variance transfer and constants

The reviewed deterministic transfer is applied with p=M.transition x a, q=empiricalRow data x a, f=valueEstimator data, and g=the selected actual absorbing grid value. Both the supplied cover inequality and grid concentration inequality are real proved inputs from the previous steps.

The transfer uses the sharp standard-deviation stability `sqrt(Var_p(g))≤sqrt(Var_p(f))+ε` and the two-probability-row residual approximation ≤2ε. At ε=1/(Nh), with a=sqrt(β₁/N), b=β₁/(3Nh), this gives `a sqrt(Var_p(f))+(2+a)ε+b`. The reviewed arithmetic bounds the final two terms by **exactly** 2β₁/(Nh), not an unspecified or changed constant. The true population row p is used for both variances, rather than swapping to the empirical distribution. No variance positivity, horizon restriction beyond h>0 or asymptotic sample-size assumption is added.

The standard-deviation/grid modules were authored by this reviewer but independently reviewed by distinct critics; their reports are `docs/critic-policy-learning-variance-transfer.md` and `docs/critic-policy-learning-absorbing-grid.md`, tied to the exact hashes below. This review checks the differently authored composition rather than replacing those independent dependency reviews with self-certification.

## Beta lower bound is proved

`leaveOneOutBeta_ge_four` supplies the numerical premise that the earlier transfer helper correctly left explicit. Nonempty finite state/action carriers and N>0 give S,A,N≥1. The MDP and confidence domain give 0<h≤1 and 0<δ<1, hence hδ≤1 and `16SAN/(hδ)≥16`. The proof applies log monotonicity and the exact identity `log16=4log2`. The pinned Mathlib theorem `Real.log_two_gt_d9` is a proved rigorous numerical bound, yielding log16≥2; this is not an assumed decimal approximation. Therefore β₁=2log(argument)≥4.

No extra β≥4 hypothesis appears in the main probability declaration. The proof uses the same deterministic β in the all-grid event, transfer and final conclusion, with no redefinition or sample-dependent parameter. The source's N inside this policy-learning logarithm is retained, unlike the different policy-evaluation theorem.

## Postselection, measurability and endpoints

After this theorem, choosing a=`policyEstimator data x` for each state on the same all-actions event is logically valid. The new file does not yet export the policy-induced-row notation rewrite or the subsequent resolvent guarantee. It need not assert independence of the resulting fitted policy or value. A proof applying a fixed-vector tail directly to that selected value would be invalid; that is not what occurs here.

All sample domains are finite with discrete measurable structure. The success event, including its universally quantified state/action statements and data-dependent fitted value, is measurable. No unproved joint measurable selection over continuous parameters is used. Event inclusion and finite probability monotonicity preserve the single strict success bound >1−δ/2. Probability normalization comes from the actual sampling-law instance.

The result permits every source γ∈[0,1), including zero, and N=1. It divides by N and 1−γ, never by γ, a variance or the fitted-value norm. Zero/constant values and zero row variance are handled by the reviewed deterministic standard-deviation result and original Bernstein theorem. No favorable support event or sample-accuracy condition is assumed. The finite cover includes both horizon endpoints.

Expanded main inputs are State/Action and their finite instances, M's nonempty carriers, normalized nonnegative transition rows, known rewards in [0,1], 0≤γ<1, positive natural N, and δ∈(0,1). These are source standing/typing and explicit algorithm/confidence domains. No policy, residual bound, covering witness, conditional concentration, β lower bound, variance estimate or conclusion-shaped premise is supplied. EXCESS=0 for the stated source proof-step event.

## Missing source work and verification boundary

This is the source all-row residual proof step through line 1371, with the uniform event enabling the later greedy-action selection. It does not establish the true-resolvent self-bounding norm inequality, the named `lem:empirical-value-residual`, the full `lem:policy-learning-evaluation`, the true-policy suboptimality comparison, the source V/Q theorem or its sample-complexity constant. Those require their own actual objects, probability composition and source audits.

Exact staged dependencies recomputed: all-row Bernstein `c28ab6963d52be915aedc7909d6ad6c894bf6666e0cb9312f33a45ce67dc1189`; variance transfer `b601af7ce8d8bc5935e11b299c27875ded4f50674d37867bd991c68f5464b9d0`; grid `9eb3bb60ee40b35f5c3fb378c1db43edc0d1648d1d230c0b06b5be028063e9ef`. Source chapter hash is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

After source review and explicit lead allocation, I freshly rebuilt the exact staged independence, one-row Bernstein, grid, all-row Bernstein and variance-transfer sources sequentially into an isolated project-owned artifact directory. With that directory plus ordinary integrated project/dependency paths in `LEAN_PATH`, I compiled `.local/OptimalResidualIndependentAudit.lean`, an exact unchanged copy of the reviewed top source with both exported axiom commands appended.

All dependency builds and the exact-source probe exited 0 without diagnostics. `leaveOneOutBeta_ge_four` and `empiricalOptimalValue_allRows_residual` each reported exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or custom axiom occurs in the reviewed source. The temporary artifacts/probe were deleted and the compiler slot immediately released. This independently checks the exact staged transitive closure rather than trusting preexisting staged `.olean` files. Production integration/imported-export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningEmpiricalOptimalResidual.lean` SHA-256 `8478cb5df8e0298ff7a0b27460975a5c0993ed2b04d9d82baaa8f12f0dd9875f` differs from reviewed staged SHA-256 `c1ac0b61d3af7c76c05d2a56f14f2dd49e1c1f6225988e35130bc128b35fe8fb` only by qualification of its two staged imports. The actual integrated module compiled; an import-only audit of both theorem exports succeeded with only `propext`, `Classical.choice`, and `Quot.sound`.
